//! Flow-sensitive (side-effect) analysis framework.

use crate::func_at::{FuncAt, FuncAtMut};
use crate::qptr::QPtrOp;
use crate::{
    AttrSet, ConstDef, ConstKind, Context, ControlNodeOutputDecl, ControlRegion, ControlRegionDef,
    ControlRegionInputDecl, DataInst, DataInstDef, DataInstKind, Diag, FuncDefBody, FxIndexMap,
    FxIndexSet, Type,
};
use crate::{ControlNode, Value};
use crate::{ControlNodeKind, DataInstFormDef};
use smallvec::SmallVec;
use std::cell::Cell;
use std::collections::VecDeque;
use std::rc::Rc;
use std::{mem, slice};

// FIXME(eddyb) make the whole newtyped indexing situation better
// (using `EntityDefs` may make sense, but those are unique `Context`-wide).

// FIXME(eddyb) switch to `u32` once the logic is shown to work.
type Idx = usize;

// FIXME(eddyb) consider shortening to "Cap" and even maybe "Obj".

/// Handle for a "capability" (see [`CapabilityDef`]).
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
struct Capability(Idx);

/// "Capabilities" are [`Value`]s used to symbolically refer to [`Object`]s,
/// e.g. pointers referring to memory (sub)objects (aka "provenance").
enum CapabilityDef {
    // HACK(eddyb) singleton "escaped object set" quasi-capability.
    Ambient {
        // FIXME(eddyb) this should probably be a bitset.
        reachable_objects: FxIndexSet<Object>,
    },

    WholeObject(Object),
    //
    // FIXME(eddyb) implement more cases, including "object slicing" but also
    // merging capabilities across selects/loops into conservative sets.
}

/// Handle for an "object" (see [`ObjectDef`]).
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
struct Object(Idx);

/// "Objects" are statically known (and analyzable) disjoint "partitions" of the
/// state (in the (R)VSDG sense) during execution, e.g. the memory of a variable.
struct ObjectDef {
    known_state: Option<ObjectState>,

    /// Whether this object (its allocation and any instructions operating on it),
    /// needs to be preserved for any reason whatsoever.
    ///
    /// This flag starts out `false` and will (permanently) become `true` after
    /// *any* operation other than writes and reads that can be rewritten away.
    //
    // FIXME(eddyb) ththis name is somewhat arbitrary and suboptimal.
    // FIXME(eddyb) much more detailed state-oriented tracking should be possible.
    keep_alive: bool,
    //
    // FIXME(eddyb) also track other objects (or even capabilities) reachable
    // through this object, due to writes into it, instead of making them ambient.
}

/// Handle for an "object state" (see [`ObjectStateDef`]).
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
struct ObjectState(Idx);

// FIXME(eddyb) should this use `Rc`? should this try to be flatter?
// should it have "version"/"revision"/"snapshot" etc. in the name?
#[derive(PartialEq, Eq, Hash)]
enum ObjectStateDef {
    AfterInst {
        prev: Option<ObjectState>,
        inst: DataInst,
        // HACK(eddyb) parent block of `inst`, only needed to be able to delete it.
        parent_block: ControlNode,
    },
    AfterSelect {
        select_node: ControlNode,
        state_before_select: Option<ObjectState>,
        per_case_states: SmallVec<[ObjectState; 2]>,
    },
    // HACK(eddyb) the `ObjectState`s for before-loop/after-body are kept
    // in a side table (`loop_object_state_initial_and_after_body`), and
    // the information here only serves as a key for interning, so that
    // the whole loop can be repeatedly processed to arrive at a fixpoint.
    BeforeLoopBody {
        loop_node: ControlNode,
        object: Object,
    },
}

// FIXME(eddyb) move stuff over to this.
struct InstInOutEffects {
    // FIXME(eddyb) will these need to be dynamic?
    inputs: &'static [Option<InputSink>],
    outputs: &'static [Option<OutputSource>],
}

// FIXME(eddyb) should this be like a bitmask?
enum InputSink {
    // FIXME(eddyb) implement object slicing.
    Capability {
        object_read: bool,
        object_write: bool,
    },

    /// Value being written to an [`Object`] (referenced via a [`Capability`] input).
    ObjectWriteValue,
}

enum OutputSource {
    /// Allocate a new [`Object`] to output as a [`Capability`].
    NewObjectCapability,

    /// Value being read from an [`Object`] (referenced via a [`Capability`] input).
    ObjectReadValue,
}

/// Apply some flow analysis to `func_def_body`.
pub fn flow_func(cx: Rc<Context>, func_def_body: &mut FuncDefBody) {
    // Avoid having to support unstructured control-flow.
    //
    // FIXME(eddyb) it should be possible to actually implement this, using
    // classic dataflow techniques, and φ/BB args for value propagation.
    if func_def_body.unstructured_cfg.is_some() {
        return;
    }

    let (objects, object_states, loop_object_state_initial_and_after_body, replaceable_insts) = {
        let mut flow_cx = FlowContext {
            cx: &cx,
            ambient_capability: Capability(0),
            value_to_capability: FxIndexMap::default(),
            capabilities: vec![CapabilityDef::Ambient { reachable_objects: FxIndexSet::default() }],
            objects: vec![],
            object_state_interner: FxIndexSet::default(),
            loop_object_state_initial_and_after_body: FxIndexMap::default(),
            change_log: vec![],
            replaceable_insts: FxIndexMap::default(),
        };
        flow_cx.flow_through_control_region(func_def_body.at_mut_body());
        (
            flow_cx.objects,
            flow_cx.object_state_interner,
            flow_cx.loop_object_state_initial_and_after_body,
            flow_cx.replaceable_insts,
        )
    };

    let mut remove_inst =
        |inst, parent_block| match &mut func_def_body.control_nodes[parent_block].kind {
            ControlNodeKind::Block { insts } => {
                insts.remove(inst, &mut func_def_body.data_insts);
            }
            _ => unreachable!(),
        };
    for (original_inst, (_, parent_block)) in replaceable_insts {
        remove_inst(original_inst, parent_block);
    }

    // HACK(eddyb) queue + set to safely visit all the `ObjectState`s used
    // by non-`keep_alive` `Object`s.
    let mut state_visiting_queue = VecDeque::new();
    let mut visited_states = FxIndexSet::default();
    state_visiting_queue.extend(
        objects.into_iter().filter(|obj| !obj.keep_alive).filter_map(|obj| obj.known_state),
    );
    while let Some(state) = state_visiting_queue.pop_front() {
        if !visited_states.insert(state) {
            continue;
        }
        match &object_states[state.0] {
            &ObjectStateDef::AfterInst { prev, inst, parent_block } => {
                remove_inst(inst, parent_block);
                state_visiting_queue.extend(prev);
            }
            ObjectStateDef::AfterSelect { state_before_select, per_case_states, .. } => {
                state_visiting_queue.extend(
                    (*state_before_select).into_iter().chain(per_case_states.iter().copied()),
                );
            }
            ObjectStateDef::BeforeLoopBody { .. } => {
                if let Some(&(initial_state, state_after_body)) =
                    loop_object_state_initial_and_after_body.get(&state)
                {
                    state_visiting_queue.extend([initial_state, state_after_body]);
                }
            }
        }
    }
}

struct FlowContext<'a> {
    cx: &'a Context,

    // FIXME(eddyb) this will always be `Capability(0)` anyway, use constant?
    ambient_capability: Capability,

    // FIXME(eddyb) use a much denser (or at least more efficient) representation,
    // and/or reuse this for non-capability values as well.
    value_to_capability: FxIndexMap<Value, Capability>,

    capabilities: Vec<CapabilityDef>,
    objects: Vec<ObjectDef>,

    object_state_interner: FxIndexSet<ObjectStateDef>,

    // HACK(eddyb) see `ObjectStateDef::BeforeLoopBody` docs for more details.
    loop_object_state_initial_and_after_body: FxIndexMap<ObjectState, (ObjectState, ObjectState)>,

    // HACK(eddyb) this allows a flat representation, and handling `Select`
    // control nodes at a cost proportional only to the number of changes
    // in any of the child regions (not the total number of e.g. objects).
    change_log: Vec<Change>,

    /// Object read instructions with known output `Value`s, and also tracking
    /// their parent `Block` control node for later removal.
    //
    // FIXME(eddyb) it should be possible to remove these as they are seen.
    replaceable_insts: FxIndexMap<DataInst, (SmallVec<[Option<Value>; 2]>, ControlNode)>,
}

enum Change {
    // FIXME(eddyb) does this only exist to detect allocations in loops?
    AllocateNewObject {
        new_object: Object,
        alloc_inst: DataInst,
    },

    /// This [`Object`] is new in [`CapabilityDef::Ambient`]'s reachable set.
    EscapeObjectToAmbient(Object),

    ObjectState {
        object: Object,

        /// Previous value of the `known_state` field of `ObjectDef`.
        prev_known_state: Option<ObjectState>,
    },
}

// HACK(eddyb) helper for `query_past_value`.
enum QueryStep<V> {
    Done(V),

    /// This write does not overlap with the queried part of the object at all.
    DisjointWrite,
    // FIXME(eddyb) add some way to handle partially overlapping reads with writes,
    // where another callback has to combine multiple partial values together.
}

/// Error type for `query_past_value` (or the callback it takes) failing to find
/// known states that are usable (i.e. containing compatible writes).
#[derive(Copy, Clone)]
struct UnknowableValue;

// HACK(eddyb) this avoids using a map in some places.
struct ChainedMiniCache<'a, K, V> {
    key: K,
    value: Cell<Option<V>>,
    // FIXME(eddyb) this is only used when `value` is `None`, maybe use a
    // two-state `enum` instead, so this field is only used for "lazy init"?
    prev: Option<&'a Self>,
}

impl FlowContext<'_> {
    fn intern_object_state(&mut self, object_state_def: ObjectStateDef) -> ObjectState {
        ObjectState(match self.object_state_interner.get_full(&object_state_def) {
            Some((idx, _)) => idx,
            None => self.object_state_interner.insert_full(object_state_def).0,
        })
    }

    /// Extract and/or synthesize a [`Value`], of type `value_type`, if possible,
    /// from past [`Object`] writes, relative to the `current` [`ObjectState`],
    /// using a caller-provided `DataInst`-level filter/map `step` callback.
    fn query_past_value(
        &self,
        func: FuncAtMut<'_, ()>,
        current: ObjectState,
        value_type: Type,
        step: impl Fn(FuncAt<'_, DataInst>) -> Result<QueryStep<Value>, UnknowableValue>,
    ) -> Result<Value, UnknowableValue> {
        self.query_past_value_inner(func, current, value_type, None, &step)
    }

    // HACK(eddyb) implementation detail of `query_past_value`.
    // FIXME(eddyb) figure out some kind of localized "undo log" or similar,
    // for any additions this makes to the function, so in case of errors
    // it's all removed without leaving any unused inputs/outputs around.
    fn query_past_value_inner(
        &self,
        mut func: FuncAtMut<'_, ()>,
        current: ObjectState,
        value_type: Type,
        mini_cache: Option<&ChainedMiniCache<'_, ObjectState, Result<Value, UnknowableValue>>>,
        step: &impl Fn(FuncAt<'_, DataInst>) -> Result<QueryStep<Value>, UnknowableValue>,
    ) -> Result<Value, UnknowableValue> {
        if let Some(mini_cache) = mini_cache {
            if mini_cache.key == current {
                return mini_cache.value.get().unwrap_or_else(|| {
                    // HACK(eddyb) this is easier than `try {...}`-ing the rest of the code.
                    let r = self.query_past_value_inner(
                        func,
                        current,
                        value_type,
                        mini_cache.prev,
                        step,
                    );
                    mini_cache.value.set(Some(r));
                    r
                });
            }
        }

        // FIXME(eddyb) avoid recursion, ideally find a good way to do caching!
        match &self.object_state_interner[current.0] {
            &ObjectStateDef::AfterInst { prev, inst, .. } => {
                match step(func.reborrow().freeze().at(inst))? {
                    QueryStep::Done(v) => Ok(v),
                    QueryStep::DisjointWrite => self.query_past_value_inner(
                        func,
                        prev.ok_or(UnknowableValue)?,
                        value_type,
                        mini_cache,
                        step,
                    ),
                }
            }
            ObjectStateDef::AfterSelect { select_node, state_before_select, per_case_states } => {
                let select_node = *select_node;

                // FIXME(eddyb) represent the list of child regions without having them
                // in a `Vec` (or `SmallVec`), which requires workarounds like this.
                let get_case = |func: FuncAtMut<'_, ()>, i| match &func.at(select_node).def().kind {
                    ControlNodeKind::Select { cases, .. } => cases[i],
                    _ => unreachable!(),
                };

                let mini_cache_before_select =
                    state_before_select.map(|state_before_select| ChainedMiniCache {
                        key: state_before_select,
                        value: Cell::new(None),
                        // HACK(eddyb) this ensures that once `state_before_select`
                        // is encountered, the caching switching to some outer
                        // *even earlier* state (e.g. before an outer select).
                        prev: mini_cache,
                    });
                let mini_cache = mini_cache_before_select.as_ref().or(mini_cache);

                let per_case_values: SmallVec<[_; 2]> = per_case_states
                    .iter()
                    .map(|&state| {
                        self.query_past_value_inner(
                            func.reborrow(),
                            state,
                            value_type,
                            mini_cache,
                            step,
                        )
                    })
                    .collect::<Result<_, _>>()?;

                // HACK(eddyb) do not create outputs if all cases agree.
                let v0 = per_case_values[0];
                if per_case_values[1..].iter().all(|&v| v == v0) {
                    return Ok(v0);
                }

                let select_output_decls = &mut func.reborrow().at(select_node).def().outputs;
                let output_idx = u32::try_from(select_output_decls.len()).unwrap();
                select_output_decls
                    .push(ControlNodeOutputDecl { attrs: Default::default(), ty: value_type });

                for (case_idx, per_case_value) in per_case_values.into_iter().enumerate() {
                    let case = get_case(func.reborrow(), case_idx);
                    let per_case_outputs = &mut func.reborrow().at(case).def().outputs;
                    assert_eq!(per_case_outputs.len(), output_idx as usize);
                    per_case_outputs.push(per_case_value);
                }

                Ok(Value::ControlNodeOutput { control_node: select_node, output_idx })
            }
            &ObjectStateDef::BeforeLoopBody { loop_node, .. } => {
                let &(initial_state, state_after_body) = self
                    .loop_object_state_initial_and_after_body
                    .get(&current)
                    .ok_or(UnknowableValue)?;

                let initial_value = self.query_past_value_inner(
                    func.reborrow(),
                    initial_state,
                    value_type,
                    mini_cache,
                    step,
                )?;

                let (initial_inputs, body) = match &mut func.reborrow().at(loop_node).def().kind {
                    ControlNodeKind::Loop { initial_inputs, body, .. } => (initial_inputs, *body),
                    _ => unreachable!(),
                };
                let input_idx = u32::try_from(initial_inputs.len()).unwrap();
                initial_inputs.push(initial_value);

                let body_input_decls = &mut func.reborrow().at(body).def().inputs;
                assert_eq!(body_input_decls.len(), input_idx as usize);
                body_input_decls
                    .push(ControlRegionInputDecl { attrs: Default::default(), ty: value_type });

                let new_body_input = Value::ControlRegionInput { region: body, input_idx };

                let value_after_body = self.query_past_value_inner(
                    func,
                    state_after_body,
                    value_type,
                    // HACK(eddyb) this avoids infinite recursion by caching
                    // the same value being later returned, with the same key.
                    Some(&ChainedMiniCache {
                        key: current,
                        value: Cell::new(Some(Ok(new_body_input))),
                        prev: None,
                    }),
                    step,
                )?;

                // HACK(eddyb) ignore the loop entirely if its body isn't relevant.
                // FIXME(eddyb) this should result in `new_body_input` being removed.
                if value_after_body == new_body_input {
                    return Ok(initial_value);
                }

                Ok(new_body_input)
            }
        }
    }

    /// Apply active rewrites (i.e. `replaceable_insts`) to all `values`.
    fn flow_into_values(&mut self, values: &mut [Value]) {
        for v in values {
            // FIXME(eddyb) should this run in a loop?
            if let Value::DataInstOutput { inst, output_idx } = *v {
                if let Some((replacement_values, _)) = self.replaceable_insts.get(&inst) {
                    if let Some(rv) = replacement_values[output_idx as usize] {
                        *v = rv;
                    }
                }
            }
        }
    }

    // HACK(eddyb) this (somewhat inefficiently?) erases all known states from
    // ambiently reachable ("escaped") objects.
    fn unanalyzable_effects(&mut self) {
        let ambiently_reachable_objects = match &self.capabilities[self.ambient_capability.0] {
            CapabilityDef::Ambient { reachable_objects } => reachable_objects,
            _ => unreachable!(),
        };
        for &obj in ambiently_reachable_objects {
            let prev = self.objects[obj.0].known_state.take();
            if prev.is_some() {
                self.change_log.push(Change::ObjectState { object: obj, prev_known_state: prev });
            }
        }
    }

    fn escape_object_to_ambient(&mut self, obj: Object) {
        let ambiently_reachable_objects = match &mut self.capabilities[self.ambient_capability.0] {
            CapabilityDef::Ambient { reachable_objects } => reachable_objects,
            _ => unreachable!(),
        };
        if ambiently_reachable_objects.insert(obj) {
            self.change_log.push(Change::EscapeObjectToAmbient(obj));
        }

        // HACK(eddyb) the persistent/"sticky" behavior goes against
        // state snapshotting / the change log, but this is safer
        // for now, and the value is only read at the very end anyway.
        self.objects[obj.0].keep_alive = true;
    }

    fn unanalyzable_value_uses(&mut self, values: &[Value]) {
        for &v in values {
            let cap = match v {
                Value::Const(_) => continue,
                _ => match self.value_to_capability.get(&v) {
                    None => continue,
                    Some(&cap) => cap,
                },
            };
            // FIXME(eddyb) this could be more fine-grained wrt the object graph.
            match self.capabilities[cap.0] {
                CapabilityDef::Ambient { .. } => unreachable!(),
                CapabilityDef::WholeObject(obj) => {
                    self.escape_object_to_ambient(obj);
                }
            }
        }
    }

    fn flow_through_data_inst(
        &mut self,
        mut func_at_inst: FuncAtMut<'_, DataInst>,
        parent_block: ControlNode,
    ) {
        let cx = self.cx;

        let data_inst = func_at_inst.position;

        let DataInstDef { attrs: _, form, inputs } = func_at_inst.reborrow().def();

        let DataInstFormDef { kind, output_types } = &cx[*form];

        self.flow_into_values(inputs);

        match *kind {
            // FIXME(eddyb) turn this into uses of the declarative metadata.
            DataInstKind::QPtr(QPtrOp::FuncLocalVar(_)) => {
                assert!(inputs.len() <= 1);

                let new_obj_def = ObjectDef {
                    keep_alive: false,
                    known_state: Some(self.intern_object_state(ObjectStateDef::AfterInst {
                        prev: None,
                        inst: data_inst,
                        parent_block,
                    })),
                };
                // HACK(eddyb) allocate new object
                let new_obj = {
                    let idx = self.objects.len();
                    self.objects.push(new_obj_def);
                    Object(idx)
                };

                self.change_log
                    .push(Change::AllocateNewObject { new_object: new_obj, alloc_inst: data_inst });

                let new_cap_def = CapabilityDef::WholeObject(new_obj);
                // HACK(eddyb) allocate new capability
                let new_cap = {
                    let idx = self.capabilities.len();
                    self.capabilities.push(new_cap_def);
                    Capability(idx)
                };

                self.value_to_capability
                    .insert(Value::DataInstOutput { inst: data_inst, output_idx: 0 }, new_cap);
            }

            // FIXME(eddyb) turn this into uses of the declarative metadata.
            DataInstKind::QPtr(QPtrOp::Store { .. }) => {
                assert_eq!(inputs.len(), 2);
                let dst_ptr = inputs[0];
                let stored_value = inputs[1];

                if let Some(cap) = self.value_to_capability.get(&dst_ptr) {
                    if let CapabilityDef::WholeObject(obj) = self.capabilities[cap.0] {
                        // FIXME(eddyb) if the object is escaped i.e. ambiently
                        // reachable, this could still be considered to soundly
                        // overwrite any other state, because it's unsynchronized,
                        // so even if concurrent accesses could be performed,
                        // data races are still UB so we can assume unaliasing.

                        let new_state = self.intern_object_state(ObjectStateDef::AfterInst {
                            prev: self.objects[obj.0].known_state,
                            inst: data_inst,
                            parent_block,
                        });

                        // FIXME(eddyb) avoid redundant `change_log` pushes,
                        // it should be possible to keep track of snapshot
                        // "watermarks", and "`Change` slot for this snapshot",
                        // within `ObjectDef`, to reuse `Change` slots.
                        self.change_log.push(Change::ObjectState {
                            object: obj,
                            prev_known_state: self.objects[obj.0].known_state.replace(new_state),
                        });

                        // Only visit the value input, not the destination pointer.
                        self.unanalyzable_value_uses(&[stored_value]);

                        return;
                    }
                }
            }

            // FIXME(eddyb) reify this so the search is only triggered by a use
            // of the result of the load, not the load itself!
            // FIXME(eddyb) this has no caching, could consider at least merge
            // caching (to avoid adding duplicate region outputs etc.), and/or
            // deduplicating the `qptr.load` itself if the object hadn't changed.
            DataInstKind::QPtr(QPtrOp::Load { offset }) => {
                assert_eq!(inputs.len(), 1);
                let src_ptr = inputs[0];

                let known_state = self.value_to_capability.get(&src_ptr).and_then(|cap| match self
                    .capabilities[cap.0]
                {
                    CapabilityDef::WholeObject(obj) => self.objects[obj.0].known_state,
                    _ => None,
                });

                // HACK(eddyb) avoid accumulating orphan side-effects while
                // trying to fix-point loops, if some things aren't monotonic.
                // FIXME(eddyb) this is not perfect, because `flow_into_values`
                // may have already used this by the time it's invalidated, so
                // loops should ideally not be mutating the IR until outermost
                // loops are complete (or if everything can be made monotonic).
                self.replaceable_insts.remove(&data_inst);

                if let Some(known_state) = known_state {
                    let const_undef = |ty| {
                        Value::Const(cx.intern(ConstDef {
                            attrs: AttrSet::default(),
                            ty,
                            kind: ConstKind::Undef,
                        }))
                    };

                    let access_type = output_types[0];
                    let loaded_value = self.query_past_value(
                        func_at_inst.reborrow().at(()),
                        known_state,
                        access_type,
                        |func_at_write_inst| {
                            let func = func_at_write_inst.at(());
                            let write_inst_def = func_at_write_inst.def();
                            match (&cx[write_inst_def.form].kind, &write_inst_def.inputs[..]) {
                                (DataInstKind::QPtr(QPtrOp::FuncLocalVar(_)), []) => {
                                    Ok(QueryStep::Done(const_undef(access_type)))
                                }
                                (DataInstKind::QPtr(QPtrOp::FuncLocalVar(_)), &[init_value])
                                    if offset == 0
                                        && func.at(init_value).type_of(cx) == access_type =>
                                {
                                    Ok(QueryStep::Done(init_value))
                                }

                                // FIXME(eddyb) move this so it can do layout,
                                // and filter by disjoint access ranges.
                                (
                                    &DataInstKind::QPtr(QPtrOp::Store { offset: store_offset }),
                                    &[_, stored_value],
                                ) if offset == store_offset
                                    && func_at_write_inst.at(stored_value).type_of(cx)
                                        == access_type =>
                                {
                                    Ok(QueryStep::Done(stored_value))
                                }

                                _ => Err(UnknowableValue),
                            }
                        },
                    );
                    if let Ok(loaded_value) = loaded_value {
                        self.replaceable_insts.insert(
                            data_inst,
                            ([Some(loaded_value)].into_iter().collect(), parent_block),
                        );
                        return;
                    }
                }
            }

            _ => {}
        }

        self.unanalyzable_value_uses(&func_at_inst.def().inputs);

        // FIXME(eddyb) have a way to describe instructions as side-effect-free.
        self.unanalyzable_effects();
    }

    fn flow_through_control_region(&mut self, mut func_at_region: FuncAtMut<'_, ControlRegion>) {
        let mut children = func_at_region.reborrow().at_children().into_iter();
        while let Some(func_at_control_node) = children.next() {
            self.flow_through_control_node(func_at_control_node);
        }

        let ControlRegionDef { inputs: _, children: _, outputs } = func_at_region.def();
        self.flow_into_values(outputs);
        self.unanalyzable_value_uses(outputs);
    }

    fn flow_through_control_node(&mut self, func_at_control_node: FuncAtMut<'_, ControlNode>) {
        let control_node = func_at_control_node.position;

        // FIXME(eddyb) is this a good convention?
        let mut func = func_at_control_node.at(());

        match &mut func.reborrow().at(control_node).def().kind {
            &mut ControlNodeKind::Block { insts } => {
                let mut func_at_inst_iter = func.at(insts).into_iter();
                while let Some(func_at_inst) = func_at_inst_iter.next() {
                    self.flow_through_data_inst(func_at_inst, control_node);
                }
            }
            ControlNodeKind::Select { kind: _, scrutinee, cases } => {
                self.flow_into_values(slice::from_mut(scrutinee));
                self.unanalyzable_value_uses(&[*scrutinee]);

                let num_cases = cases.len();

                // FIXME(eddyb) represent the list of child regions without having them
                // in a `Vec` (or `SmallVec`), which requires workarounds like this.
                let get_case = |func: FuncAtMut<'_, ()>, i| match &func.at(control_node).def().kind
                {
                    ControlNodeKind::Select { cases, .. } => cases[i],
                    _ => unreachable!(),
                };

                // HACK(eddyb) degenerate `Select`s do not actually need merges.
                if num_cases <= 1 {
                    if num_cases == 1 {
                        let case = get_case(func.reborrow(), 0);
                        self.flow_through_control_region(func.at(case));
                    }
                    return;
                }

                // HACK(eddyb) this is how we can both roll back changes to
                // `ObjectDef`s' `known_state`, and know which objects changed
                // in the first place (to merge their changed states, together).
                let change_log_start = self.change_log.len();

                let mut all_escaped_objects = FxIndexSet::default();
                let mut obj_to_per_case_states = FxIndexMap::<Object, SmallVec<[_; 2]>>::default();
                for case_idx in 0..num_cases {
                    let case = get_case(func.reborrow(), case_idx);
                    self.flow_through_control_region(func.reborrow().at(case));

                    // NOTE(eddyb) we traverse the change log forwards, as we
                    // already have a way to determine whether we've seen any
                    // changes for each object, and only the oldest change
                    // is needed to roll back the object to its original state.
                    for change in self.change_log.drain(change_log_start..) {
                        match change {
                            Change::AllocateNewObject { .. } => {
                                // FIXME(eddyb) should this be banned in some way?
                            }
                            Change::EscapeObjectToAmbient(obj) => {
                                let ambiently_reachable_objects =
                                    match &mut self.capabilities[self.ambient_capability.0] {
                                        CapabilityDef::Ambient { reachable_objects } => {
                                            reachable_objects
                                        }
                                        _ => unreachable!(),
                                    };
                                assert!(ambiently_reachable_objects.remove(&obj));
                                all_escaped_objects.insert(obj);
                            }
                            Change::ObjectState { object: obj, prev_known_state } => {
                                let original_state = prev_known_state;

                                let per_case_states =
                                    obj_to_per_case_states.entry(obj).or_insert_with(|| {
                                        let mut per_case_states =
                                            SmallVec::with_capacity(num_cases);

                                        // This case may be the first to change this
                                        // object - thankfully we know the original
                                        // state (which will be common across all cases).
                                        per_case_states
                                            .extend((0..case_idx).map(|_| original_state));

                                        per_case_states
                                    });

                                if per_case_states.len() <= case_idx {
                                    let new_state = mem::replace(
                                        &mut self.objects[obj.0].known_state,
                                        original_state,
                                    );
                                    per_case_states.push(new_state);
                                }
                                assert_eq!(per_case_states.len() - 1, case_idx);
                            }
                        }
                    }

                    // Some objects may only have been changed in previous cases.
                    for (&object, per_case_states) in &mut obj_to_per_case_states {
                        if per_case_states.len() <= case_idx {
                            per_case_states.push(self.objects[object.0].known_state);
                            assert_eq!(per_case_states.len() - 1, case_idx);
                        }
                    }
                }

                for escaped_obj in all_escaped_objects {
                    self.escape_object_to_ambient(escaped_obj);
                }

                // Objects changed in at least one case can now be merged,
                // by creating `ObjectStateDef::AfterSelect`s for all of them.
                for (obj, per_case_states) in obj_to_per_case_states {
                    assert_eq!(per_case_states.len(), num_cases);

                    // HACK(eddyb) do not create a new state if all cases agree.
                    let s0 = per_case_states[0];
                    let merged_state = if per_case_states[1..].iter().all(|&s| s == s0) {
                        s0
                    } else {
                        // FIXME(eddyb) bail out of storing `None::<Value>`s sooner.
                        per_case_states.into_iter().collect::<Option<_>>().map(|per_case_states| {
                            self.intern_object_state(ObjectStateDef::AfterSelect {
                                select_node: control_node,
                                state_before_select: self.objects[obj.0].known_state,
                                per_case_states,
                            })
                        })
                    };
                    let prev_known_state =
                        mem::replace(&mut self.objects[obj.0].known_state, merged_state);
                    self.change_log.push(Change::ObjectState { object: obj, prev_known_state });
                }
            }
            ControlNodeKind::Loop { initial_inputs, body, repeat_condition: _ } => {
                self.flow_into_values(initial_inputs);
                self.unanalyzable_value_uses(initial_inputs);

                // HACK(eddyb) this may get expensive, as most objects may not
                // end up being changed at all, but further optimizing this while
                // remaining sound is an exercise for another day.
                struct LoopObjectState {
                    initial: Option<ObjectState>,
                    before_body: ObjectState,
                    after_body: Option<ObjectState>,
                }
                let mut loop_object_states: FxIndexMap<Object, LoopObjectState> =
                    (0..self.objects.len())
                        .map(Object)
                        .map(|obj| {
                            (
                                obj,
                                LoopObjectState {
                                    initial: self.objects[obj.0].known_state,
                                    before_body: self.intern_object_state(
                                        ObjectStateDef::BeforeLoopBody {
                                            loop_node: control_node,
                                            object: obj,
                                        },
                                    ),
                                    after_body: None,
                                },
                            )
                        })
                        .collect();

                let body = *body;

                let body_change_log_start = self.change_log.len();

                // FIXME(eddyb) this risks monotonic runaway (and e.g. OOM),
                // but ideally all that happens is taking the fixpoint of the
                // loop body by repeatedly (re)processing it, with interning of
                // `ObjectState`s providing some of the "saturating" behavior.
                let mut states_changed;
                loop {
                    states_changed = false;

                    let replaceable_insts_len = self.replaceable_insts.len();

                    // Reset to the start of the loop body (like region inputs).
                    for (&obj, state) in &loop_object_states {
                        self.objects[obj.0].known_state = Some(state.before_body);
                    }

                    self.flow_through_control_region(func.reborrow().at(body));

                    // NOTE(eddyb) the repeat condition is technically part of
                    // the loop body, as if it were an extra region output.
                    let repeat_condition = match &mut func.reborrow().at(control_node).def().kind {
                        ControlNodeKind::Loop { repeat_condition, .. } => repeat_condition,
                        _ => unreachable!(),
                    };
                    self.flow_into_values(slice::from_mut(repeat_condition));
                    self.unanalyzable_value_uses(&[*repeat_condition]);

                    // HACK(eddyb) reduce work on future iterations by pruning
                    // entries which don't actually correspond to any changes.
                    loop_object_states.retain(|obj, state| {
                        let new_after_body = self.objects[obj.0].known_state;
                        if new_after_body != state.after_body {
                            state.after_body = new_after_body;
                            states_changed = true;

                            if let (Some(initial), Some(after_body)) =
                                (state.initial, state.after_body)
                            {
                                self.loop_object_state_initial_and_after_body
                                    .insert(state.before_body, (initial, after_body));
                            } else {
                                self.loop_object_state_initial_and_after_body
                                    .remove(&state.before_body);
                            }
                        }
                        state.after_body != Some(state.before_body)
                    });

                    // FIXME(eddyb) this isn't even needed for `ObjectState`
                    // changes, because those are handled specially above/below.
                    let mut attempted_dynamic_object_allocation = false;
                    for change in self.change_log.drain(body_change_log_start..) {
                        match change {
                            Change::AllocateNewObject { alloc_inst, .. } => {
                                func.reborrow().at(alloc_inst).def().attrs.push_diag(
                                    self.cx,
                                    Diag::bug(["loops cannot allocate objects".into()]),
                                );
                                attempted_dynamic_object_allocation = true;
                                break;
                            }
                            Change::EscapeObjectToAmbient(_) => {
                                // NOTE(eddyb) not undone because we want to
                                // *accumulate* escapes, not reduce them.
                                // FIXME(eddyb) this is bad because unlike the
                                // regular state tracking, this starts maximally
                                // permissive and becomes more restrictive with
                                // more iterations (as escapes are discovered).
                                // HACK(eddyb) for now, `replaceable_insts` slots
                                // are manually cleared in `flow_through_data_inst`
                                // but it should either use the change log or
                                // make escape tracking conservative.
                                states_changed = true;
                            }
                            Change::ObjectState { object: obj, prev_known_state: _ } => {
                                // HACK(eddyb) sanity check, just in check the
                                // `retain` above is overeager.
                                assert!(loop_object_states.contains_key(&obj));
                            }
                        }
                    }

                    if attempted_dynamic_object_allocation
                        || !states_changed && replaceable_insts_len == self.replaceable_insts.len()
                    {
                        break;
                    }
                }

                // NOTE(eddyb) this is needed to preserve the original states of
                // changed objects - it could've been earlier, but that may bloat
                // the change log (before pruning unchanged objects, at least).
                for (obj, state) in loop_object_states {
                    self.change_log
                        .push(Change::ObjectState { object: obj, prev_known_state: state.initial });
                }
            }
        }
    }
}
