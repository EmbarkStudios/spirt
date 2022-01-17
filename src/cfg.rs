//! Control-flow graph (CFG) abstractions and utilities.

use crate::{spv, AttrSet, EntityKeyedDenseMap, FxIndexMap, Region, Value};
use smallvec::SmallVec;
use std::rc::Rc;

/// The control-flow graph of a function, represented as per-region
/// control-flow instructions that execute "after" the region itself.
#[derive(Default)]
pub struct ControlFlowGraph {
    pub terminators: EntityKeyedDenseMap<Region, ControlInst>,
}

impl ControlFlowGraph {
    /// Iterate over all `Region`s reachable through the CFG, starting at `entry`,
    /// in RPO ("reverse post-order").
    ///
    /// RPO ("reverse post-order") over a CFG provides certain guarantees, most
    /// importantly that SSA definitions are visited before any of their uses.
    pub fn rev_post_order(&self, entry: Region) -> impl DoubleEndedIterator<Item = Region> + Clone {
        self.post_order(entry).rev()
    }

    /// Iterate over all `Region`s reachable through the CFG, starting at `entry`,
    /// in post-order.
    pub fn post_order(&self, entry: Region) -> impl DoubleEndedIterator<Item = Region> + Clone {
        let mut post_order = SmallVec::<[Region; 4]>::new();
        {
            let mut visited = EntityKeyedDenseMap::new();
            self.post_order_step(entry, &mut visited, &mut post_order);
        }

        // HACK(eddyb) this gets a cheaply-clonable iterator by `Rc`-ing the `Vec`.
        // FIXME(eddyb) change the callsites instead to do something like this themselves.
        let post_order = Rc::new(post_order);
        (0..post_order.len()).map(move |i| post_order[i])
    }

    fn post_order_step(
        &self,
        region: Region,
        // FIXME(eddyb) use a dense entity-keyed bitset here instead.
        visited: &mut EntityKeyedDenseMap<Region, ()>,
        post_order: &mut SmallVec<[Region; 4]>,
    ) {
        let already_visited = visited.insert(region, ()).is_some();
        if already_visited {
            return;
        }

        for &target in &self.terminators[region].targets {
            self.post_order_step(target, visited, post_order);
        }
        post_order.push(region);
    }
}

pub struct ControlInst {
    pub attrs: AttrSet,

    pub kind: ControlInstKind,

    pub inputs: SmallVec<[Value; 2]>,

    // FIXME(eddyb) change the inline size of this to fit most instructions.
    pub targets: SmallVec<[Region; 4]>,

    // FIXME(eddyb) this is clunky because it models φ nodes (`OpPhi` in SPIR-V),
    // replace the CFG setup with stricter structural regions.
    pub target_inputs: FxIndexMap<Region, SmallVec<[Value; 2]>>,
}

pub enum ControlInstKind {
    /// Reaching this point in the control-flow is undefined behavior, e.g.:
    /// * a `SelectBranch` case that's known to be impossible
    /// * after a function call, where the function never returns
    ///
    /// Optimizations can take advantage of this information, to assume that any
    /// necessary preconditions for reaching this point, are never met.
    Unreachable,

    /// Leave the current function, optionally returning a value.
    Return,

    /// Leave the current invocation, similar to returning from every function
    /// call in the stack (up to and including the entry-point), but potentially
    /// indicating a fatal error as well.
    ExitInvocation(ExitInvocationKind),

    /// Unconditional branch to a single target.
    Branch,

    /// Branch to one of several targets, chosen by a single value input.
    SelectBranch(SelectionKind),
}

pub enum ExitInvocationKind {
    SpvInst(spv::Inst),
}

pub enum SelectionKind {
    /// Conditional branch on boolean condition, i.e. `if`-`else`.
    BoolCond,

    SpvInst(spv::Inst),
}
