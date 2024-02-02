use arrayvec::ArrayVec;
use itertools::Itertools;
use lazy_static::lazy_static;
#[cfg(feature = "rayon")]
use rayon::prelude::*;
use rustc_hash::FxHashMap;
use smallvec::SmallVec;
use spirt::func_at::FuncAt;
use spirt::{
    scalar, spv, vector, AddrSpace, Attr, Const, ConstKind, Context, ControlNode, ControlNodeDef,
    ControlNodeKind, ControlRegion, ControlRegionDef, DataInst, DataInstDef, DataInstFormDef,
    DataInstKind, DeclDef, EntityOrientedDenseMap, ExportKey, Exportee, Func, GlobalVar,
    InternedStr, Module, SelectionKind, Type, TypeKind, Value,
};
use std::ops::Range;
use std::path::Path;
use std::rc::Rc;

// HACK(eddyb) `spv::spec::Spec` with extra `WellKnown`s.
macro_rules! def_spv_spec_with_extra_well_known {
    ($($group:ident: $ty:ty = [$($entry:ident),+ $(,)?]),+ $(,)?) => {
        struct SpvSpecWithExtras {
            __base_spec: &'static spv::spec::Spec,

            well_known: SpvWellKnownWithExtras,
        }

        #[allow(non_snake_case)]
        pub struct SpvWellKnownWithExtras {
            __base_well_known: &'static spv::spec::WellKnown,

            $($(pub $entry: $ty,)+)+
        }

        impl std::ops::Deref for SpvSpecWithExtras {
            type Target = spv::spec::Spec;
            fn deref(&self) -> &Self::Target {
                self.__base_spec
            }
        }

        impl std::ops::Deref for SpvWellKnownWithExtras {
            type Target = spv::spec::WellKnown;
            fn deref(&self) -> &Self::Target {
                self.__base_well_known
            }
        }

        impl SpvSpecWithExtras {
            #[inline(always)]
            #[must_use]
            pub fn get() -> &'static SpvSpecWithExtras {
                lazy_static! {
                    static ref SPEC: SpvSpecWithExtras = {
                        #[allow(non_camel_case_types)]
                        struct PerWellKnownGroup<$($group),+> {
                            $($group: $group),+
                        }

                        let spv_spec = spv::spec::Spec::get();
                        let wk = &spv_spec.well_known;

                        let storage_classes = match &spv_spec.operand_kinds[wk.StorageClass] {
                            spv::spec::OperandKindDef::ValueEnum { variants } => variants,
                            _ => unreachable!(),
                        };
                        let decorations = match &spv_spec.operand_kinds[wk.Decoration] {
                            spv::spec::OperandKindDef::ValueEnum { variants } => variants,
                            _ => unreachable!(),
                        };

                        let execution_models = match &spv_spec.operand_kinds[spv_spec.operand_kinds.lookup("ExecutionModel").unwrap()] {
                            spv::spec::OperandKindDef::ValueEnum { variants } => variants,
                            _ => unreachable!(),
                        };
                        let builtins = match &spv_spec.operand_kinds[spv_spec.operand_kinds.lookup("BuiltIn").unwrap()] {
                            spv::spec::OperandKindDef::ValueEnum { variants } => variants,
                            _ => unreachable!(),
                        };

                        let glsl_std_450_ops = spv_spec
                            .get_ext_inst_set_by_lowercase_name("glsl.std.450")
                            .unwrap()
                            .instructions
                            .iter()
                            .map(|(&op, inst_desc)| (&inst_desc.name[..], op))
                            .collect::<FxHashMap<_, _>>();

                        let lookup_fns = PerWellKnownGroup {
                            opcode: |name| spv_spec.instructions.lookup(name).unwrap(),
                            operand_kind: |name| spv_spec.operand_kinds.lookup(name).unwrap(),
                            storage_class: |name| storage_classes.lookup(name).unwrap().into(),
                            decoration: |name| decorations.lookup(name).unwrap().into(),
                            execution_model: |name| execution_models.lookup(name).unwrap().into(),
                            builtin: |name| builtins.lookup(name).unwrap().into(),
                            glsl_std_450_op: |name| glsl_std_450_ops.get(name).copied().unwrap(),
                        };

                        SpvSpecWithExtras {
                            __base_spec: spv_spec,

                            well_known: SpvWellKnownWithExtras {
                                __base_well_known: &spv_spec.well_known,

                                $($($entry: (lookup_fns.$group)(stringify!($entry)),)+)+
                            },
                        }
                    };
                }
                &SPEC
            }
        }
    };
}
def_spv_spec_with_extra_well_known! {
    opcode: spv::spec::Opcode = [
        OpConstantComposite,

        // FIXME(eddyb) maybe make a macro for most of these to be mentioned
        // only once, at their use site in `eval_data_inst`.
        OpSelect,
        OpCompositeConstruct,
        OpCompositeExtract,
        OpCompositeInsert,
    ],
    operand_kind: spv::spec::OperandKind = [
        ExecutionModel,
    ],
    storage_class: u32 = [
        PushConstant,
    ],
    decoration: u32 = [
        BuiltIn,
    ],
    execution_model: u32 = [
        Vertex,
        Fragment,
    ],
    builtin: u32 = [
        FragCoord
    ],
    glsl_std_450_op: u32 = [
        FAbs,
        Exp,
        Sqrt,
        Sin,
        Cos,

        FMin,
        FMax,
        Pow,

        Fma,
    ],
}

fn main() {
    let (in_file_path, out_file_path) = match &std::env::args().collect::<Vec<_>>()[..] {
        [_, in_file, out_file] => {
            (Path::new(in_file).to_path_buf(), Path::new(out_file).to_path_buf())
        }
        args => {
            eprintln!("Usage: {} IN_FILE OUT_FILE", args[0]);
            std::process::exit(1);
        }
    };

    let wk = &SpvSpecWithExtras::get().well_known;

    let mut module = Module::lower_from_spv_file(Rc::new(Context::new()), in_file_path).unwrap();
    spirt::passes::legalize::structurize_func_cfgs(&mut module);

    let h = 1080;
    let w = h * 16 / 9;

    // FIXME(eddyb) allow customizing this in-depth (via CLI).
    // FIXME(eddyb) some kind of interpolation could allow generating an animation,
    // by feeding time & mouse coords etc. for e.g. the mouse shader example.
    let push_constants = &{
        let u = |x| DynScalar::U32(DynLeaf::Uniform(x));
        let f = |x| DynScalar::F32(DynLeaf::Uniform(x));
        [
            u(w).into(),
            u(h).into(),
            f(0.0).into(),
            f(0.0).into(),
            f(0.0).into(),
            f(0.0).into(),
            f(0.0).into(),
            f(0.0).into(),
            f(0.0).into(),
            u(0).into(),
            DynVal::Vector([f(0.0), f(0.0), f(0.0)].into_iter().collect()),
        ]
    };

    let cx = module.cx();
    let mut interpreter = Interpreter {
        wk,
        glsl_std_450: cx.intern("GLSL.std.450"),
        ty_u32: cx.intern(scalar::Type::U32),
        ty_s32: cx.intern(scalar::Type::S32),

        module: &module,
        push_constants,
        launch: Launch::FragRect { width: w.try_into().unwrap(), height: h.try_into().unwrap() },
        invocations: u32::checked_mul(w, h).unwrap().try_into().unwrap(),

        inst_counter: 0,

        global_vars: Default::default(),
        call_stack: Default::default(),
    };
    let (fragment_entry, fragment_interface_global_vars) = module
        .exports
        .iter()
        .find_map(|(export_key, exportee)| match (export_key, exportee) {
            (ExportKey::SpvEntryPoint { imms, interface_global_vars }, &Exportee::Func(func))
                if imms.starts_with(&[spv::Imm::Short(wk.ExecutionModel, wk.Fragment)]) =>
            {
                Some((func, interface_global_vars))
            }
            _ => None,
        })
        .expect("no fragment entry-point");

    let start = std::time::Instant::now();
    interpreter.eval_call(fragment_entry, SmallVec::new());
    let elapsed = start.elapsed();
    eprintln!(
        "{:8.3}ms for {} instructions ({w}px × {h}px = {} invocations each)",
        elapsed.as_secs_f64() * 1e3,
        interpreter.inst_counter,
        interpreter.invocations,
    );
    eprintln!(
        "={:7.3}ms per instruction",
        elapsed.as_secs_f64() * 1e3 / (interpreter.inst_counter as f64),
    );
    eprintln!(
        "={:7.1}ns per invocation",
        elapsed.as_secs_f64() * 1e9 / (interpreter.invocations as f64),
    );
    eprintln!(
        "={:7.1}ns per instruction per invocation",
        elapsed.as_secs_f64() * 1e9
            / (interpreter.inst_counter as f64)
            / (interpreter.invocations as f64),
    );

    for &gv in fragment_interface_global_vars {
        let gv_decl = &module.global_vars[gv];
        if gv_decl.addr_space == AddrSpace::SpvStorageClass(wk.Output) {
            if let Some(DynVal::Vector(elems)) = interpreter.global_vars.get(gv) {
                if let [
                    DynScalar::F32(r),
                    DynScalar::F32(g),
                    DynScalar::F32(b),
                    DynScalar::F32(a),
                ] = &elems[..]
                {
                    // FIXME(eddyb) use `rayon` to build a `Vec<u8>` here.
                    image::RgbaImage::from_fn(w, h, |x, y| {
                        let i = usize::try_from(y.checked_mul(w).unwrap().checked_add(x).unwrap())
                            .unwrap();
                        let get = |x: &DynLeaf<f32>| {
                            let x = match x {
                                &DynLeaf::Uniform(x) => x,
                                DynLeaf::PerInvocation(xs) => xs[i],
                            }
                            .clamp(0.0, 1.0);

                            // apply the srgb OETF (i.e. do "linear to sRGB")
                            fn srgb_oetf(x: f32) -> f32 {
                                if x <= 0.0031308 {
                                    x * 12.92
                                } else {
                                    1.055 * x.powf(1.0 / 2.4) - 0.055
                                }
                            }

                            // FIXME(eddyb) do not convert alpha.
                            (srgb_oetf(x).clamp(0.0, 1.0) * 255.0) as u8
                        };
                        image::Rgba([get(r), get(g), get(b), get(a)])
                    })
                    .save(out_file_path)
                    .unwrap();
                    return;
                }
            }
        }
    }
    unreachable!("`f32x4` output global var not found");
}

#[derive(Clone)]
enum DynLeaf<T> {
    Uniform(T),
    // FIXME(eddyb) make this hierarchical to allow "subgroup-uniform" etc.
    PerInvocation(Rc<Vec<T>>),
    // HACK(eddyb) consider some "linear interpolation" for that doesn't store
    // the values, or some "min"/"max" tracking, to potentially uniformize conditions.
}

// FIXME(eddyb) test perf vs rayon (also, consider batching that LLVM may vectorize).
impl<T: Copy + Send + Sync> DynLeaf<T> {
    fn map<U: Send>(self, f: impl Fn(T) -> U + Send + Sync) -> DynLeaf<U> {
        match self {
            DynLeaf::Uniform(x) => DynLeaf::Uniform(f(x)),
            // FIXME(eddyb) also consider making uniform if all the results are
            // all equal, but that may be too expensive to check? (maybe it'd
            // make more sense if it were hierarchical, since it would already
            // be trying to group invocations, and have more impact on average)
            //
            // FIXME(eddyb) take advantage of by-value `self` to re-use the `Rc`
            // allocation in-place, whenever possible (would require knowing that
            // `T == U`, or some kind of "scalars all made of `u32` chunks" repr).
            #[cfg(feature = "rayon")]
            DynLeaf::PerInvocation(xs) => {
                DynLeaf::PerInvocation(Rc::new(xs.par_iter().copied().map(f).collect()))
            }
            #[cfg(not(feature = "rayon"))]
            DynLeaf::PerInvocation(xs) => {
                DynLeaf::PerInvocation(Rc::new(xs.iter().copied().map(f).collect()))
            }
        }
    }
    fn map2<U: Copy + Send + Sync, V: Send>(
        self,
        other: DynLeaf<U>,
        f: impl Fn(T, U) -> V + Send + Sync,
    ) -> DynLeaf<V> {
        match (self, other) {
            (x, DynLeaf::Uniform(y)) => x.map(move |x| f(x, y)),
            (DynLeaf::Uniform(x), y) => y.map(move |y| f(x, y)),
            (DynLeaf::PerInvocation(xs), DynLeaf::PerInvocation(ys)) => {
                DynLeaf::PerInvocation(Rc::new(
                    {
                        #[cfg(feature = "rayon")]
                        {
                            xs.par_iter().zip_eq(&ys[..])
                        }
                        #[cfg(not(feature = "rayon"))]
                        {
                            xs.iter().zip_eq(&ys[..])
                        }
                    }
                    .map(|(&x, &y)| f(x, y))
                    .collect(),
                ))
            }
        }
    }
    fn map3<U: Copy + Send + Sync, V: Copy + Send + Sync, W: Send>(
        self,
        other: DynLeaf<U>,
        other2: DynLeaf<V>,
        f: impl Fn(T, U, V) -> W + Send + Sync,
    ) -> DynLeaf<W> {
        match (self, other, other2) {
            (x, y, DynLeaf::Uniform(z)) => x.map2(y, move |x, y| f(x, y, z)),
            (x, DynLeaf::Uniform(y), z) => x.map2(z, move |x, z| f(x, y, z)),
            (DynLeaf::Uniform(x), y, z) => y.map2(z, move |y, z| f(x, y, z)),
            (
                DynLeaf::PerInvocation(xs),
                DynLeaf::PerInvocation(ys),
                DynLeaf::PerInvocation(zs),
            ) => DynLeaf::PerInvocation(Rc::new(
                {
                    #[cfg(feature = "rayon")]
                    {
                        xs.par_iter().zip_eq(&ys[..]).zip_eq(&zs[..])
                    }
                    #[cfg(not(feature = "rayon"))]
                    {
                        xs.iter().zip_eq(&ys[..]).zip_eq(&zs[..])
                    }
                }
                .map(|((&x, &y), &z)| f(x, y, z))
                .collect(),
            )),
        }
    }
}

// HACK(eddyb) traits to call the `map2`/`map3` methods, but as `map`, on tuples.
trait LeafMap2<A: Copy + Send + Sync, B: Copy + Send + Sync> {
    fn map<R: Send>(self, f: impl Fn(A, B) -> R + Send + Sync) -> DynLeaf<R>;
}
trait LeafMap3<A: Copy + Send + Sync, B: Copy + Send + Sync, C: Copy + Send + Sync> {
    fn map<R: Send>(self, f: impl Fn(A, B, C) -> R + Send + Sync) -> DynLeaf<R>;
}

impl<A: Copy + Send + Sync, B: Copy + Send + Sync> LeafMap2<A, B> for (DynLeaf<A>, DynLeaf<B>) {
    fn map<R: Send>(self, f: impl Fn(A, B) -> R + Send + Sync) -> DynLeaf<R> {
        let (xs, ys) = self;
        xs.map2(ys, f)
    }
}
impl<A: Copy + Send + Sync, B: Copy + Send + Sync, C: Copy + Send + Sync> LeafMap3<A, B, C>
    for (DynLeaf<A>, DynLeaf<B>, DynLeaf<C>)
{
    fn map<R: Send>(self, f: impl Fn(A, B, C) -> R + Send + Sync) -> DynLeaf<R> {
        let (xs, ys, zs) = self;
        xs.map3(ys, zs, f)
    }
}

#[derive(Clone, derive_more::From, derive_more::TryInto)]
enum DynScalar {
    Undef,

    // FIXME(eddyb) this should really use a bitset!
    #[from]
    #[try_into]
    Bool(DynLeaf<bool>),

    // FIXME(eddyb) have a single repr that does whole `u32` chunks?
    #[from]
    #[try_into]
    U32(DynLeaf<u32>),
    #[from]
    #[try_into]
    S32(DynLeaf<i32>),
    #[from]
    #[try_into]
    F32(DynLeaf<f32>),
}

macro_rules! op_closure {
    // HACK(eddyb) notation shorthand, allowing e.g. `(+)` instead of `|x, y| x + y`.
    (! $op:tt) => { |x, y| !(x $op y) };
    ($op:tt) => { |x, y| x $op y };

    // HACK(eddyb) adapter shorthand (used with specialized `U`/`S` for integers).
    ($ctor:ident($($closure:tt)+)) => { $ctor(op_closure!($($closure)+)) };

    ($closure:expr) => { $closure };
}

// FIXME(eddyb) come up with a better syntax, and ideally unify the cases.
macro_rules! dispatch_scalar {
    ($inputs:ident.match $op:ident => ($T:ty) -> _: $($pat:pat => ($($closure:tt)+)),+ $(,)?) => {{
        let (x,) = $inputs.into_iter().collect_tuple().unwrap();
        match $op {
            $($pat => {
                // HACK(eddyb) closure somewhat used as `try` block.
                None.or_else(|| {
                    let x: DynLeaf<$T> = x.try_into().ok()?;
                    Some(DynScalar::from(x.map(op_closure!($($closure)+))))
                }).unwrap()
            })+
        }
    }};
    // FIXME(eddyb) use for int binops too.
    ($inputs:ident.match $op:ident => ($T:ty, $U:ty) -> _: $($pat:pat => ($($closure:tt)+)),+ $(,)?) => {{
        let (x, y) = $inputs.into_iter().collect_tuple().unwrap();
        match $op {
            $($pat => {
                // HACK(eddyb) closure somewhat used as `try` block.
                None.or_else(|| {
                    let x: DynLeaf<$T> = x.try_into().ok()?;
                    let y: DynLeaf<$U> = y.try_into().ok()?;
                    Some(DynScalar::from((x, y).map(op_closure!($($closure)+))))
                }).unwrap()
            }),+
        }
    }};
    ($inputs:ident.match $op:ident => ($T:ty, $U:ty, $V:ty) -> _: $($pat:pat => ($($closure:tt)+)),+ $(,)?) => {{
        let (x, y, z) = $inputs.into_iter().collect_tuple().unwrap();
        match $op {
            $($pat => {
                // HACK(eddyb) closure somewhat used as `try` block.
                None.or_else(|| {
                    let x: DynLeaf<$T> = x.try_into().ok()?;
                    let y: DynLeaf<$U> = y.try_into().ok()?;
                    let z: DynLeaf<$U> = z.try_into().ok()?;
                    Some(DynScalar::from((x, y, z).map(op_closure!($($closure)+))))
                }).unwrap()
            }),+
        }
    }};
}

#[derive(Clone)]
enum DynPtrBase {
    GlobalVar(GlobalVar),
}

#[derive(Clone, derive_more::From, derive_more::TryInto)]
enum DynVal {
    #[from]
    #[try_into]
    Scalar(DynScalar),

    Vector(ArrayVec<DynScalar, 4>),

    // FIXME(eddyb) make this cheap by disaggregation.
    Ptr {
        base: DynPtrBase,
        access_chain: SmallVec<[u32; 4]>,
    },

    LazyUninitAggregate,
    Aggregate(Rc<[DynVal]>),

    SpvStringLiteralForExtInst(InternedStr),
}

// FIXME(eddyb) this is all over the place, reorganize!
fn vec_distribute<VDS: FromIterator<DynScalar>, VDV: IntoIterator<Item = DynVal>>(
    per_elem: impl Fn(VDS) -> DynScalar,
) -> impl Fn(VDV) -> DynVal {
    move |inputs| {
        let mut inputs: SmallVec<[_; 4]> = inputs
            .into_iter()
            .map(|v| match v {
                DynVal::Vector(xs) => xs.into_iter(),
                _ => unreachable!(),
            })
            .collect();
        let elem_count = inputs[0].len();
        inputs.iter().for_each(|xs| assert_eq!(xs.len(), elem_count));

        DynVal::Vector(
            (0..elem_count)
                .map(|_| per_elem(inputs.iter_mut().map(|xs| xs.next().unwrap()).collect()))
                .collect(),
        )
    }
}
fn scalar_or_vec_distribute<VDS: FromIterator<DynScalar>, VDV: IntoIterator<Item = DynVal>>(
    per_scalar: impl Fn(VDS) -> DynScalar,
) -> impl Fn(VDV) -> DynVal {
    move |inputs| {
        let mut inputs = inputs.into_iter().peekable();
        match inputs.peek().unwrap() {
            DynVal::Scalar(_) => {
                DynVal::Scalar(per_scalar(inputs.map(|x| x.try_into().unwrap()).collect()))
            }
            DynVal::Vector(_) => vec_distribute(&per_scalar)(inputs),
            _ => unreachable!(),
        }
    }
}

struct Interpreter<'a> {
    wk: &'static SpvWellKnownWithExtras,
    // FIXME(eddyb) group this into something like an `interned` field.
    glsl_std_450: InternedStr,
    ty_u32: Type,
    ty_s32: Type,

    module: &'a Module,
    // FIXME(eddyb) this feels weird here now that it's not `[u32]` anymore.
    push_constants: &'a [DynVal],
    launch: Launch,
    // FIXME(eddyb) compute this from `launch` more automatedly.
    // FIXME(eddyb) use this.
    #[allow(dead_code)]
    invocations: usize,

    inst_counter: usize,

    global_vars: EntityOrientedDenseMap<GlobalVar, DynVal>,
    call_stack: Vec<CallFrame>,
}

enum Launch {
    // FIXME(eddyb) use this.
    #[allow(dead_code)]
    VertIndices(Range<u32>),
    FragRect {
        width: u16,
        height: u16,
    },
}

#[derive(Default)]
struct CallFrame {
    region_inputs: EntityOrientedDenseMap<ControlRegion, SmallVec<[DynVal; 4]>>,
    control_node_outputs: EntityOrientedDenseMap<ControlNode, SmallVec<[DynVal; 4]>>,
    data_inst_outputs: EntityOrientedDenseMap<DataInst, DynVal>,
}

impl<'a> Interpreter<'a> {
    fn cx(&self) -> &'a Context {
        self.module.cx_ref()
    }
    fn eval_call(&mut self, f: Func, args: SmallVec<[DynVal; 4]>) -> SmallVec<[DynVal; 4]> {
        let func_def_body = match &self.module.funcs[f].def {
            DeclDef::Imported(import) => unreachable!(
                "calling import {:?}",
                match import {
                    &spirt::Import::LinkName(name) => &self.cx()[name],
                }
            ),
            DeclDef::Present(def) => def,
        };

        self.call_stack.push(CallFrame::default());
        let ret_vals = self.eval_region(func_def_body.at_body(), args);
        self.call_stack.pop().unwrap();
        ret_vals
    }
    fn eval_region(
        &mut self,
        func_at_region: FuncAt<ControlRegion>,
        input_vals: SmallVec<[DynVal; 4]>,
    ) -> SmallVec<[DynVal; 4]> {
        let ControlRegionDef { inputs, children: _, outputs } = func_at_region.def();

        assert_eq!(input_vals.len(), inputs.len());
        if !input_vals.is_empty() {
            self.call_stack
                .last_mut()
                .unwrap()
                .region_inputs
                .insert(func_at_region.position, input_vals);
        }

        for func_at_node in func_at_region.at_children() {
            self.eval_control_node(func_at_node);
        }

        outputs.iter().map(|&v| self.eval_value(v)).collect()
    }
    fn eval_control_node(&mut self, func_at_control_node: FuncAt<ControlNode>) {
        let ControlNodeDef { kind, outputs } = func_at_control_node.def();
        match kind {
            &ControlNodeKind::Block { insts } => {
                assert_eq!(outputs.len(), 0);
                for func_at_inst in func_at_control_node.at(insts) {
                    self.eval_data_inst(func_at_inst);
                }
            }
            ControlNodeKind::Select { kind, scrutinee, cases } => match kind {
                SelectionKind::BoolCond => {
                    self.inst_counter += 1;

                    let cond = match self.eval_value(*scrutinee) {
                        DynVal::Scalar(DynScalar::Bool(cond)) => cond,
                        _ => unreachable!(),
                    };

                    // HACK(eddyb) try really hard to avoid per-invocation decisions.
                    let cond = match cond {
                        DynLeaf::Uniform(cond) => cond,
                        DynLeaf::PerInvocation(conds)
                            if {
                                let first = conds[0];
                                #[cfg(feature = "rayon")]
                                {
                                    conds[1..].par_iter().all(|&c| c == first)
                                }
                                #[cfg(not(feature = "rayon"))]
                                {
                                    conds[1..].iter().all(|&c| c == first)
                                }
                            } =>
                        {
                            conds[0]
                        }
                        DynLeaf::PerInvocation(_) => todo!("per-invocation `if`-`else` decision"),
                    };
                    let case = cases[if cond { 0 } else { 1 }];

                    let output_vals =
                        self.eval_region(func_at_control_node.at(case), SmallVec::new());

                    assert_eq!(output_vals.len(), outputs.len());
                    if !output_vals.is_empty() {
                        self.call_stack
                            .last_mut()
                            .unwrap()
                            .control_node_outputs
                            .insert(func_at_control_node.position, output_vals);
                    }
                }
                SelectionKind::Switch { .. } => todo!(),
            },
            ControlNodeKind::Loop { initial_inputs, body, repeat_condition } => {
                let mut loop_state = initial_inputs.iter().map(|&v| self.eval_value(v)).collect();

                loop {
                    loop_state = self.eval_region(func_at_control_node.at(*body), loop_state);

                    self.inst_counter += 1;

                    let rep_cond = match self.eval_value(*repeat_condition) {
                        DynVal::Scalar(DynScalar::Bool(cond)) => cond,
                        _ => unreachable!(),
                    };

                    // HACK(eddyb) try really hard to avoid per-invocation decisions.
                    let rep_cond = match rep_cond {
                        DynLeaf::Uniform(cond) => cond,
                        DynLeaf::PerInvocation(conds)
                            if {
                                let first = conds[0];
                                #[cfg(feature = "rayon")]
                                {
                                    conds[1..].par_iter().all(|&c| c == first)
                                }
                                #[cfg(not(feature = "rayon"))]
                                {
                                    conds[1..].iter().all(|&c| c == first)
                                }
                            } =>
                        {
                            conds[0]
                        }
                        DynLeaf::PerInvocation(_) => todo!("per-invocation `loop` repeat decision"),
                    };
                    if !rep_cond {
                        break;
                    }
                }
            }
        }
    }
    fn eval_data_inst(&mut self, func_at_inst: FuncAt<DataInst>) {
        self.inst_counter += 1;

        let start = std::time::Instant::now();

        let DataInstDef { attrs: _, form, inputs } = func_at_inst.def();
        let DataInstFormDef { kind, output_type } = &self.cx()[*form];

        let inputs: SmallVec<[_; 4]> = inputs.iter().map(|&v| self.eval_value(v)).collect();

        macro_rules! float_unop {
            ($($f:tt)+) => {
                scalar_or_vec_distribute(|inputs: ArrayVec<_, 1>| {
                    let op = ();
                    dispatch_scalar! { inputs.match op => (f32) -> _:
                        () => ($($f)+)
                    }
                })(inputs)
            };
        }
        macro_rules! float_binop {
            ($($f:tt)+) => {
                scalar_or_vec_distribute(|inputs: ArrayVec<_, 2>| {
                    let op = ();
                    dispatch_scalar! { inputs.match op => (f32, f32) -> _:
                        () => ($($f)+)
                    }
                })(inputs)
            };
        }
        // FIXME(eddyb) this is a silly name, find a better one (`op3`? overload macro?).
        macro_rules! float_triop {
            ($($f:tt)+) => {
                scalar_or_vec_distribute(|inputs: ArrayVec<_, 3>| {
                    let op = ();
                    dispatch_scalar! { inputs.match op => (f32, f32, f32) -> _:
                        () => ($($f)+)
                    }
                })(inputs)
            };
        }

        let output = match kind {
            &DataInstKind::Scalar(op) => Some(
                self.eval_scalar_op(
                    op,
                    inputs.into_iter().map(|x| x.try_into().unwrap()).collect(),
                )
                .into(),
            ),
            &DataInstKind::Vector(op) => Some({
                match op {
                    vector::Op::Distribute(op) => {
                        vec_distribute(|inputs| self.eval_scalar_op(op, inputs))(inputs)
                    }
                    vector::Op::Reduce(op) => match op {
                        vector::ReduceOp::Dot => todo!(),
                        vector::ReduceOp::Any => todo!(),
                        vector::ReduceOp::All => todo!(),
                    },
                    vector::Op::Whole(op) => match op {
                        vector::WholeOp::New => DynVal::Vector(
                            inputs.into_iter().map(|x| x.try_into().unwrap()).collect(),
                        ),
                        vector::WholeOp::Extract { elem_idx } => {
                            match inputs.into_iter().collect_tuple().unwrap() {
                                (DynVal::Vector(elems),) => DynVal::Scalar(
                                    elems.into_iter().nth(usize::from(elem_idx)).unwrap(),
                                ),
                                _ => unreachable!(),
                            }
                        }
                        vector::WholeOp::Insert { elem_idx } => {
                            let (new_elem, val) = inputs.into_iter().collect_tuple().unwrap();
                            match val {
                                DynVal::Vector(mut elems) => {
                                    elems[usize::from(elem_idx)] = new_elem.try_into().unwrap();
                                    DynVal::Vector(elems)
                                }
                                _ => unreachable!(),
                            }
                        }
                        vector::WholeOp::DynExtract => todo!(),
                        vector::WholeOp::DynInsert => todo!(),
                        vector::WholeOp::Mul => todo!(),
                    },
                }
            }),
            &DataInstKind::FuncCall(callee) => {
                let mut ret_vals = self.eval_call(callee, inputs);
                assert!(ret_vals.len() <= 1);
                ret_vals.pop()
            }
            DataInstKind::QPtr(_) => todo!(),
            DataInstKind::SpvInst(spv_inst) => {
                if spv_inst.opcode == self.wk.OpStore {
                    // FIXME(eddyb) deduplicate between `OpStore` and `OpLoad`.
                    let (ptr, val) = inputs.into_iter().collect_tuple().unwrap();
                    let (ptr_base, ptr_access_chain) = match ptr {
                        DynVal::Ptr { base, access_chain } => (base, access_chain),
                        _ => unreachable!(),
                    };
                    let mut slot = match ptr_base {
                        DynPtrBase::GlobalVar(gv) => {
                            // FIXME(eddyb) get the pointee type to generate a `ConstKind::Undef`.
                            self.global_vars.entry(gv).get_or_insert(DynVal::LazyUninitAggregate)
                        }
                    };
                    // FIXME(eddyb) lazily initialize structure based on type.
                    for i in ptr_access_chain {
                        let components = match slot {
                            DynVal::LazyUninitAggregate => {
                                todo!("OpStore wants typed lazy uninit init")
                            }
                            // HACK(eddyb) this reimplements `Rc::make_mut` for `Rc<[T]>`.
                            DynVal::Aggregate(components) => {
                                // FIXME(eddyb) this works around pre-polonius borrowck.
                                if Rc::get_mut(components).is_none() {
                                    let cloned = components.iter().cloned().collect();
                                    *components = cloned;
                                }
                                Rc::get_mut(components).unwrap()
                            }
                            _ => unreachable!(),
                        };
                        slot = &mut components[usize::try_from(i).unwrap()];
                    }

                    *slot = val;
                    None
                } else if spv_inst.opcode == self.wk.OpLoad {
                    // FIXME(eddyb) deduplicate between `OpStore` and `OpLoad`.
                    let (ptr,) = inputs.into_iter().collect_tuple().unwrap();
                    let (ptr_base, ptr_access_chain) = match ptr {
                        DynVal::Ptr { base, access_chain } => (base, access_chain),
                        _ => unreachable!(),
                    };
                    let mut val = match ptr_base {
                        DynPtrBase::GlobalVar(gv) => {
                            // FIXME(eddyb) get the pointee type to generate a `ConstKind::Undef`.
                            self.global_vars.get(gv).cloned().unwrap_or(DynVal::LazyUninitAggregate)
                        }
                    };
                    for i in ptr_access_chain {
                        val = match val {
                            DynVal::Vector(elems) => {
                                DynVal::Scalar(elems[usize::try_from(i).unwrap()].clone())
                            }
                            DynVal::Aggregate(components) => {
                                components[usize::try_from(i).unwrap()].clone()
                            }
                            DynVal::LazyUninitAggregate => DynVal::LazyUninitAggregate,
                            _ => unreachable!(),
                        };
                    }
                    Some(val)
                } else if spv_inst.opcode == self.wk.OpAccessChain {
                    let mut inputs = inputs.into_iter();
                    let mut ptr = inputs.next().unwrap();
                    let ptr_access_chain = match &mut ptr {
                        DynVal::Ptr { base: _, access_chain } => access_chain,
                        _ => unreachable!(),
                    };
                    for i in inputs {
                        let i = match i {
                            DynVal::Scalar(DynScalar::U32(i)) => match i {
                                DynLeaf::Uniform(i) => i,
                                _ => todo!("non-uniform OpAccessChain"),
                            },
                            _ => unreachable!(),
                        };
                        ptr_access_chain.push(i);
                    }
                    Some(ptr)
                } else if spv_inst.opcode == self.wk.OpSelect {
                    let (cond, t, e) = inputs.into_iter().collect_tuple().unwrap();
                    let cond = match cond {
                        DynVal::Scalar(DynScalar::Bool(cond)) => cond,
                        _ => unreachable!(),
                    };
                    // FIXME(eddyb) support composites (or, wait for deaggregate).
                    fn select<T>(cond: bool, t: T, e: T) -> T {
                        if cond { t } else { e }
                    }
                    Some(match (t, e) {
                        (DynVal::Scalar(t), DynVal::Scalar(e)) => DynVal::Scalar(match (t, e) {
                            (DynScalar::Bool(t), DynScalar::Bool(e)) => {
                                DynScalar::Bool((cond, t, e).map(select))
                            }
                            (DynScalar::F32(t), DynScalar::F32(e)) => {
                                DynScalar::F32((cond, t, e).map(select))
                            }
                            _ => unreachable!(),
                        }),
                        _ => unreachable!(),
                    })
                } else if spv_inst.opcode == self.wk.OpCompositeConstruct {
                    // FIXME(eddyb) update for `disaggregate`.
                    Some(DynVal::Aggregate(inputs.into_iter().collect()))
                } else if spv_inst.opcode == self.wk.OpCompositeExtract {
                    // FIXME(eddyb) update for `disaggregate`.
                    let (mut val,) = inputs.into_iter().collect_tuple().unwrap();
                    for &imm in &spv_inst.imms {
                        val = match (imm, val) {
                            (spv::Imm::Short(_, i), DynVal::Aggregate(components)) => {
                                components[usize::try_from(i).unwrap()].clone()
                            }
                            _ => unreachable!(),
                        };
                    }
                    Some(val)
                } else if spv_inst.opcode == self.wk.OpCompositeInsert {
                    // FIXME(eddyb) update for `disaggregate`.
                    let (new_leaf, mut val) = inputs.into_iter().collect_tuple().unwrap();
                    let mut slot = &mut val;
                    for &imm in &spv_inst.imms {
                        let i = match imm {
                            spv::Imm::Short(_, i) => i,
                            _ => unreachable!(),
                        };
                        let components = match slot {
                            DynVal::LazyUninitAggregate => {
                                todo!("OpCompositeInsert wants typed lazy uninit init")
                            }
                            // HACK(eddyb) this reimplements `Rc::make_mut` for `Rc<[T]>`.
                            DynVal::Aggregate(components) => {
                                // FIXME(eddyb) this works around pre-polonius borrowck.
                                if Rc::get_mut(components).is_none() {
                                    let cloned = components.iter().cloned().collect();
                                    *components = cloned;
                                }
                                Rc::get_mut(components).unwrap()
                            }
                            _ => unreachable!(),
                        };
                        slot = &mut components[usize::try_from(i).unwrap()];
                    }
                    *slot = new_leaf;
                    Some(val)
                } else if spv_inst.opcode == self.wk.OpBitcast {
                    Some(match inputs.into_iter().collect_tuple().unwrap() {
                        (DynVal::Scalar(DynScalar::U32(x)),)
                            if *output_type == Some(self.ty_s32) =>
                        {
                            DynVal::Scalar(DynScalar::S32(x.map(|x| x as i32)))
                        }
                        (DynVal::Scalar(DynScalar::S32(x)),)
                            if *output_type == Some(self.ty_u32) =>
                        {
                            DynVal::Scalar(DynScalar::U32(x.map(|x| x as u32)))
                        }
                        _ => unreachable!(),
                    })
                } else {
                    todo!(
                        "unsupported instruction {} {}",
                        spv_inst.opcode.name(),
                        spv::print::inst_operands(
                            spv_inst.opcode,
                            spv_inst.imms.iter().copied(),
                            inputs.iter().enumerate().map(|(i, _)| format!("<input #{i}>"))
                        )
                        .map(|operand| operand.concat_to_plain_text())
                        .collect::<Vec<_>>()
                        .join(" ")
                    )
                }
            }

            &DataInstKind::SpvExtInst { ext_set, inst }
                if ext_set == self.glsl_std_450 && inst == self.wk.FAbs =>
            {
                Some(float_unop!(|x| x.abs()))
            }
            &DataInstKind::SpvExtInst { ext_set, inst }
                if ext_set == self.glsl_std_450 && inst == self.wk.Exp =>
            {
                Some(float_unop!(|x| x.exp()))
            }
            &DataInstKind::SpvExtInst { ext_set, inst }
                if ext_set == self.glsl_std_450 && inst == self.wk.Sqrt =>
            {
                Some(float_unop!(|x| x.sqrt()))
            }
            &DataInstKind::SpvExtInst { ext_set, inst }
                if ext_set == self.glsl_std_450 && inst == self.wk.Sin =>
            {
                Some(float_unop!(|x| x.sin()))
            }
            &DataInstKind::SpvExtInst { ext_set, inst }
                if ext_set == self.glsl_std_450 && inst == self.wk.Cos =>
            {
                Some(float_unop!(|x| x.cos()))
            }

            &DataInstKind::SpvExtInst { ext_set, inst }
                if ext_set == self.glsl_std_450 && inst == self.wk.FMin =>
            {
                Some(float_binop!(|x, y| x.min(y)))
            }
            &DataInstKind::SpvExtInst { ext_set, inst }
                if ext_set == self.glsl_std_450 && inst == self.wk.FMax =>
            {
                Some(float_binop!(|x, y| x.max(y)))
            }
            &DataInstKind::SpvExtInst { ext_set, inst }
                if ext_set == self.glsl_std_450 && inst == self.wk.Pow =>
            {
                Some(float_binop!(|x, y| x.powf(y)))
            }

            &DataInstKind::SpvExtInst { ext_set, inst }
                if ext_set == self.glsl_std_450 && inst == self.wk.Fma =>
            {
                Some(float_triop!(|x, y, z| x.mul_add(y, z)))
            }

            &DataInstKind::SpvExtInst { ext_set, inst } => {
                let ext_set = &self.cx()[ext_set];
                todo!(
                    "unsupported extended instruction {ext_set} {inst} ({:?})",
                    spv::spec::Spec::get()
                        .get_ext_inst_set_by_lowercase_name(&ext_set.to_ascii_lowercase())
                        .and_then(|ext_inst_set_desc| Some(
                            &ext_inst_set_desc.instructions.get(&inst)?.name
                        )),
                )
            }
        };
        if let Some(output) = output {
            self.call_stack
                .last_mut()
                .unwrap()
                .data_inst_outputs
                .insert(func_at_inst.position, output);
        }
        let elapsed = start.elapsed();
        let ns_per_invocation = elapsed.as_secs_f64() * 1e9 / (self.invocations as f64);
        #[allow(clippy::overly_complex_bool_expr)]
        if ns_per_invocation >= 0.01 && false {
            let name = match kind {
                DataInstKind::Scalar(op) => op.name(),
                DataInstKind::Vector(op) => match op {
                    vector::Op::Distribute(op) => op.name(),
                    vector::Op::Reduce(op) => op.name(),
                    vector::Op::Whole(op) => op.name(),
                },
                DataInstKind::FuncCall(_) => "call",
                DataInstKind::QPtr(_) => unreachable!(),
                DataInstKind::SpvInst(spv_inst) => spv_inst.opcode.name(),
                &DataInstKind::SpvExtInst { ext_set, inst } => {
                    &spv::spec::Spec::get()
                        .get_ext_inst_set_by_lowercase_name(
                            &self.cx()[ext_set].to_ascii_lowercase(),
                        )
                        .unwrap()
                        .instructions[&inst]
                        .name
                }
            };
            eprint!("{ns_per_invocation:8.1}ns × {}: {name}", self.invocations);
            if let &Some(ty) = output_type {
                // HACK(eddyb) hope the type is self-contained.
                let ty = spirt::print::Plan::for_root(self.cx(), &ty).pretty_print().to_string();
                let ty = if !ty.contains('\n') && ty.len() < 8 { &ty } else { "⋯" };
                eprint!(" → {ty}");
            }
            eprintln!();
        }
    }
    fn eval_scalar_op(&self, op: scalar::Op, inputs: SmallVec<[DynScalar; 4]>) -> DynScalar {
        // HACK(eddyb) see `scalar::Op::FloatBinary` (needed for `CmpOrUnord`).
        #[allow(clippy::neg_cmp_op_on_partial_ord)]
        match op {
            scalar::Op::BoolUnary(op) => {
                // FIXME(eddyb) move import into macro.
                use scalar::BoolUnOp::*;
                dispatch_scalar! { inputs.match op => (bool) -> _:
                    Not => (|x| !x)
                }
            }
            scalar::Op::BoolBinary(op) => {
                // FIXME(eddyb) move import into macro.
                use scalar::BoolBinOp::*;
                dispatch_scalar! { inputs.match op => (bool, bool) -> _:
                    Eq => (==),
                    Ne => (!=),
                    Or => (|),
                    And => (&),
                }
            }
            scalar::Op::IntUnary(op) => match op {
                scalar::IntUnOp::Neg => todo!(),
                scalar::IntUnOp::Not => todo!(),
                scalar::IntUnOp::CountOnes => todo!(),
                scalar::IntUnOp::TruncOrZeroExtend => todo!(),
                scalar::IntUnOp::TruncOrSignExtend => todo!(),
            },
            // FIXME(eddyb) wrap everything in `Wrapping`.
            scalar::Op::IntBinary(op) => {
                // FIXME(eddyb) maybe use `num-traits` to automate away a lot of this?
                trait Int {}
                trait CastTo<T: Int>: Int {
                    fn cast_to(self) -> T;
                }
                impl<T: Int> CastTo<T> for T {
                    fn cast_to(self) -> T {
                        self
                    }
                }

                macro_rules! int_cast_impls {
                    ($($U:ident <=> $S:ident),+ $(,)?) => {$(
                        impl Int for $U {}
                        impl Int for $S {}
                        impl CastTo<$U> for $S { fn cast_to(self) -> $U { self as $U } }
                        impl CastTo<$S> for $U { fn cast_to(self) -> $S { self as $S } }
                    )+}
                }
                int_cast_impls! {
                    u32 <=> i32,
                }

                // HACK(eddyb) comparison ops make this necessary at all.
                trait MaybeReverseCastOutput<I: CastTo<T>, T: Int> {
                    type Output;
                    fn maybe_reverse_cast_output(self) -> Self::Output;
                }
                impl<I: CastTo<T>, T: Int> MaybeReverseCastOutput<I, T> for bool {
                    type Output = Self;
                    fn maybe_reverse_cast_output(self) -> Self {
                        self
                    }
                }
                impl<I: CastTo<T>, T: CastTo<I>> MaybeReverseCastOutput<I, T> for T {
                    type Output = I;
                    fn maybe_reverse_cast_output(self) -> I {
                        self.cast_to()
                    }
                }

                // HACK(eddyb) allow forcing a signedness.
                #[allow(non_snake_case)]
                fn U<I: CastTo<u32>, R: MaybeReverseCastOutput<I, u32>>(
                    f: impl Fn(u32, u32) -> R,
                ) -> impl Fn(I, I) -> <R as MaybeReverseCastOutput<I, u32>>::Output
                {
                    move |x, y| f(x.cast_to(), y.cast_to()).maybe_reverse_cast_output()
                }
                #[allow(non_snake_case)]
                fn S<I: CastTo<i32>, R: MaybeReverseCastOutput<I, i32>>(
                    f: impl Fn(i32, i32) -> R,
                ) -> impl Fn(I, I) -> <R as MaybeReverseCastOutput<I, i32>>::Output
                {
                    move |x, y| f(x.cast_to(), y.cast_to()).maybe_reverse_cast_output()
                }

                macro_rules! dispatch_int_binop {
                    ($inputs:ident.match $op:ident: $($pat:pat => ($($f:tt)+)),+ $(,)?) => {{
                        let (x, y) = $inputs.into_iter().collect_tuple().unwrap();
                        match $op {
                            $($pat => {
                                // HACK(eddyb) closures somewhat used as `try` blocks.
                                None.or_else(|| {
                                    // FIXME(eddyb) remove the clones by using
                                    // something better than `TryInto` here.
                                    let x: DynLeaf<u32> = x.clone().try_into().ok()?;
                                    let y: DynLeaf<u32> = y.clone().try_into().ok()?;
                                    Some(DynScalar::from((x, y).map(op_closure!($($f)+))))
                                }).or_else(|| {
                                    let x: DynLeaf<i32> = x.clone().try_into().ok()?;
                                    let y: DynLeaf<i32> = y.clone().try_into().ok()?;
                                    Some(DynScalar::from((x, y).map(op_closure!($($f)+))))
                                }).unwrap()
                            }),+
                        }
                    }};
                }

                use scalar::IntBinOp::*;
                dispatch_int_binop! { inputs.match op:
                    Add => (+),
                    Sub => (-),
                    Mul => (*),
                    DivU => (U(/)),
                    DivS => (S(/)),
                    ModU => (U(|_, _| -> u32 { todo!() })),
                    RemS => (S(%)),
                    ModS => (S(|_, _| -> i32 { todo!() })),
                    ShrU => (U(>>)),
                    ShrS => (S(>>)),
                    Shl => (<<),
                    Or => (|),
                    Xor => (^),
                    And => (&),
                    CarryingAdd => (|_, _| -> u32 { todo!() }),
                    BorrowingSub => (|_, _| -> u32 { todo!() }),
                    WideningMulU => (U(|_, _| -> u32 { todo!() })),
                    WideningMulS => (S(|_, _| -> i32 { todo!() })),
                    Eq => (==),
                    Ne => (!=),
                    GtU => (U(>)),
                    GtS => (S(>)),
                    GeU => (U(>=)),
                    GeS => (S(>=)),
                    LtU => (U(<)),
                    LtS => (S(<)),
                    LeU => (U(<=)),
                    LeS => (S(<=)),
                }
            }
            scalar::Op::FloatUnary(op) => {
                use scalar::FloatUnOp::*;
                dispatch_scalar! { inputs.match op => (_) -> _:
                    Neg => (|x: f32| -x),
                    IsNan => (|x: f32| x.is_nan()),
                    IsInf => (|x: f32| x.is_infinite()),
                    // FIXME(eddyb) handle both signed and unsigned here.
                    FromUInt => (|x: u32| x as f32),
                    FromSInt => (|x: i32| x as f32),
                    ToUInt => (|x: f32| x as u32),
                    ToSInt => (|x: f32| x as i32),
                    Convert => (|_: f32| -> f32 { todo!() }),
                    QuantizeAsF16 => (|_: f32| -> f32 { todo!() }),
                }
            }
            scalar::Op::FloatBinary(op) => {
                // FIXME(eddyb) move import into macro.
                use scalar::{FloatBinOp::*, FloatCmp::*};
                dispatch_scalar! { inputs.match op => (f32, f32) -> _:
                    Add => (+),
                    Sub => (-),
                    Mul => (*),
                    Div => (/),
                    Rem => (%),
                    Mod => (|_, _| -> f32 { todo!() }),
                    Cmp(Eq) => (==),
                    Cmp(Ne) => (!=),
                    Cmp(Lt) => (<),
                    Cmp(Gt) => (>),
                    Cmp(Le) => (<=),
                    Cmp(Ge) => (>=),
                    // HACK(eddyb) all of these negate the opposite comparison,
                    // which flips unordered from always `false` to always `true`.
                    CmpOrUnord(Eq) => (! ==),
                    CmpOrUnord(Ne) => (! !=),
                    CmpOrUnord(Lt) => (! <),
                    CmpOrUnord(Gt) => (! >),
                    CmpOrUnord(Le) => (! <=),
                    CmpOrUnord(Ge) => (! >=),
                }
            }
        }
    }
    fn eval_scalar_const(&self, ct: scalar::Const) -> DynScalar {
        match ct {
            scalar::Const::FALSE => DynScalar::Bool(DynLeaf::Uniform(false)),
            scalar::Const::TRUE => DynScalar::Bool(DynLeaf::Uniform(true)),
            _ => match ct.ty() {
                scalar::Type::U32 => DynScalar::U32(DynLeaf::Uniform(ct.int_as_u32().unwrap())),
                scalar::Type::S32 => DynScalar::S32(DynLeaf::Uniform(ct.int_as_i32().unwrap())),
                scalar::Type::F32 => DynScalar::F32(DynLeaf::Uniform(f32::from_bits(
                    u32::try_from(ct.bits()).unwrap(),
                ))),
                _ => {
                    let ct: Const = self.cx().intern(ct);
                    todo!(
                        "unsupported const `{}`",
                        spirt::print::Plan::for_root(self.cx(), &ct).pretty_print()
                    )
                }
            },
        }
    }
    fn eval_value(&mut self, value: Value) -> DynVal {
        match value {
            Value::Const(ct) => {
                let ct_def = &self.cx()[ct];
                match &ct_def.kind {
                    ConstKind::Undef => match self.cx()[ct_def.ty].kind {
                        TypeKind::Scalar(_) => DynVal::Scalar(DynScalar::Undef),
                        TypeKind::Vector(ty) => DynVal::Vector(
                            (0..ty.elem_count.get()).map(|_| DynScalar::Undef).collect(),
                        ),
                        _ => DynVal::LazyUninitAggregate,
                    },
                    &ConstKind::Scalar(ct) => DynVal::Scalar(self.eval_scalar_const(ct)),
                    ConstKind::Vector(ct) => {
                        DynVal::Vector(ct.elems().map(|ct| self.eval_scalar_const(ct)).collect())
                    }
                    &ConstKind::PtrToGlobalVar(gv) => {
                        self.lazy_init_global_var(gv);
                        DynVal::Ptr {
                            base: DynPtrBase::GlobalVar(gv),
                            access_chain: SmallVec::new(),
                        }
                    }
                    // FIXME(eddyb) update for `disaggregate`.
                    ConstKind::SpvInst { spv_inst_and_const_inputs } => {
                        let (spv_inst, const_inputs) = &**spv_inst_and_const_inputs;
                        if spv_inst.opcode == self.wk.OpConstantComposite {
                            DynVal::Aggregate(
                                const_inputs
                                    .iter()
                                    .map(|&ct| self.eval_value(Value::Const(ct)))
                                    .collect(),
                            )
                        } else {
                            todo!("unsupported {}", spv_inst.opcode.name())
                        }
                    }
                    &ConstKind::SpvStringLiteralForExtInst(s) => {
                        DynVal::SpvStringLiteralForExtInst(s)
                    }
                }
            }
            Value::ControlRegionInput { region, input_idx } => {
                self.call_stack.last().unwrap().region_inputs[region][input_idx as usize].clone()
            }
            Value::ControlNodeOutput { control_node, output_idx } => {
                self.call_stack.last().unwrap().control_node_outputs[control_node]
                    [output_idx as usize]
                    .clone()
            }
            Value::DataInstOutput(inst) => {
                self.call_stack.last().unwrap().data_inst_outputs[inst].clone()
            }
        }
    }
    fn lazy_init_global_var(&mut self, gv: GlobalVar) {
        let cx = self.cx();

        let entry = self.global_vars.entry(gv);
        if entry.is_some() {
            return;
        }

        let gv_decl = &self.module.global_vars[gv];

        // FIXME(eddyb) use the actual type for this (or force qptr?).
        if gv_decl.addr_space == AddrSpace::SpvStorageClass(self.wk.PushConstant) {
            *entry = Some(DynVal::Aggregate(
                [DynVal::Aggregate(self.push_constants.iter().cloned().collect())]
                    .into_iter()
                    .collect(),
            ));
            return;
        }

        let builtin = if gv_decl.addr_space == AddrSpace::SpvStorageClass(self.wk.Input) {
            cx[gv_decl.attrs].attrs.iter().find_map(|attr| match attr {
                Attr::SpvAnnotation(spv_inst) if spv_inst.opcode == self.wk.OpDecorate => {
                    match spv_inst
                        .imms
                        .strip_prefix(&[spv::Imm::Short(self.wk.Decoration, self.wk.BuiltIn)])?
                    {
                        &[spv::Imm::Short(builtin_kind, builtin)] => Some((builtin_kind, builtin)),
                        _ => None,
                    }
                }
                _ => None,
            })
        } else {
            None
        };

        if let Some((builtin_kind, builtin)) = builtin {
            let print_builtin = || {
                spv::print::operand_from_imms([spv::Imm::Short(builtin_kind, builtin)])
                    .concat_to_plain_text()
            };
            let init = if builtin == self.wk.FragCoord {
                match self.launch {
                    Launch::FragRect { width, height } => DynVal::Vector(
                        [
                            DynScalar::F32(DynLeaf::PerInvocation(Rc::new(
                                (0..height)
                                    .flat_map(|_| 0..width)
                                    .map(|x| (x as f32) + 0.5)
                                    .collect(),
                            ))),
                            DynScalar::F32(DynLeaf::PerInvocation(Rc::new(
                                (0..height)
                                    .map(|y| (y as f32) + 0.5)
                                    .flat_map(|y| (0..width).map(move |_| y))
                                    .collect(),
                            ))),
                            DynScalar::F32(DynLeaf::Uniform(0.0)),
                            DynScalar::F32(DynLeaf::Uniform(1.0)),
                        ]
                        .into(),
                    ),
                    _ => unreachable!("{} used outside Fragment shader", print_builtin()),
                }
            } else {
                todo!("unknown {}", print_builtin());
            };
            *entry = Some(init);
        }
    }
}
