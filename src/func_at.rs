//! Traversal helpers for intra-function entities.
//!
//! `FuncAt<P>`/`FuncAtMut<P>` are like `(&FuncDefBody, P)`/`(&mut FuncDefBody, P`)
//! (where `P` is some type describing a "position" in the function), except:
//! * they only borrow the `EntityDefs` fields of `FuncDefBody`
//!   * this can prevent borrow conflicts, especially when mutating other fields
//!   * it also avoids accidentally accessing parts of the function definition
//!     without going through `P` (as `EntityDefs` requires keys for any access)
//! * they're dedicated types with inherent methods and trait `impl`s

use crate::{
    ControlNode, ControlNodeDef, ControlRegion, ControlRegionDef, DataInst, DataInstDef,
    EntityDefs, EntityList, EntityListIter, FuncDefBody,
};

/// Immutable traversal (i.e. visiting) helper for intra-function entities.
///
/// The point/position type `P` should be an entity or a shallow entity wrapper
/// (e.g. `EntityList<ControlNode>` or `cfg::ControlPoint`).
#[derive(Copy, Clone)]
pub struct FuncAt<'a, P: Copy> {
    pub control_regions: &'a EntityDefs<ControlRegion>,
    pub control_nodes: &'a EntityDefs<ControlNode>,
    pub data_insts: &'a EntityDefs<DataInst>,

    pub position: P,
}

impl<'a, P: Copy> FuncAt<'a, P> {
    /// Reposition to `new_position`.
    pub fn at<P2: Copy>(self, new_position: P2) -> FuncAt<'a, P2> {
        FuncAt {
            control_regions: self.control_regions,
            control_nodes: self.control_nodes,
            data_insts: self.data_insts,
            position: new_position,
        }
    }
}

impl<'a> FuncAt<'a, ControlRegion> {
    pub fn def(self) -> &'a ControlRegionDef {
        &self.control_regions[self.position]
    }

    pub fn at_children(self) -> FuncAt<'a, EntityList<ControlNode>> {
        self.at(self.def().children)
    }
}

impl<'a> IntoIterator for FuncAt<'a, EntityList<ControlNode>> {
    type IntoIter = FuncAt<'a, Option<EntityListIter<ControlNode>>>;
    type Item = FuncAt<'a, ControlNode>;
    fn into_iter(self) -> Self::IntoIter {
        self.at(Some(self.position.iter()))
    }
}

impl<'a> Iterator for FuncAt<'a, Option<EntityListIter<ControlNode>>> {
    type Item = FuncAt<'a, ControlNode>;
    fn next(&mut self) -> Option<Self::Item> {
        let (next, rest) = self.position?.split_first(&self.control_nodes);
        self.position = rest;
        Some(self.at(next))
    }
}

impl<'a> FuncAt<'a, ControlNode> {
    pub fn def(self) -> &'a ControlNodeDef {
        &self.control_nodes[self.position]
    }
}

impl<'a> IntoIterator for FuncAt<'a, Option<EntityList<DataInst>>> {
    type IntoIter = FuncAt<'a, Option<EntityListIter<DataInst>>>;
    type Item = FuncAt<'a, DataInst>;
    fn into_iter(self) -> Self::IntoIter {
        self.at(self.position.map(|list| list.iter()))
    }
}

impl<'a> Iterator for FuncAt<'a, Option<EntityListIter<DataInst>>> {
    type Item = FuncAt<'a, DataInst>;
    fn next(&mut self) -> Option<Self::Item> {
        let (next, rest) = self.position?.split_first(&self.data_insts);
        self.position = rest;
        Some(self.at(next))
    }
}

impl<'a> FuncAt<'a, DataInst> {
    pub fn def(self) -> &'a DataInstDef {
        &self.data_insts[self.position]
    }
}

/// Mutable traversal (i.e. transforming) helper for intra-function entities.
///
/// The point/position type `P` should be an entity or a shallow entity wrapper
/// (e.g. `EntityList<ControlNode>` or `cfg::ControlPoint`).
pub struct FuncAtMut<'a, P: Copy> {
    pub control_regions: &'a mut EntityDefs<ControlRegion>,
    pub control_nodes: &'a mut EntityDefs<ControlNode>,
    pub data_insts: &'a mut EntityDefs<DataInst>,

    pub position: P,
}

impl<'a, P: Copy> FuncAtMut<'a, P> {
    /// Emulate a "reborrow", which is automatic only for `&mut` types.
    pub fn reborrow(&mut self) -> FuncAtMut<'_, P> {
        FuncAtMut {
            control_regions: self.control_regions,
            control_nodes: self.control_nodes,
            data_insts: self.data_insts,
            position: self.position,
        }
    }

    /// Reposition to `new_position`.
    pub fn at<P2: Copy>(self, new_position: P2) -> FuncAtMut<'a, P2> {
        FuncAtMut {
            control_regions: self.control_regions,
            control_nodes: self.control_nodes,
            data_insts: self.data_insts,
            position: new_position,
        }
    }
}

impl<'a> FuncAtMut<'a, ControlRegion> {
    pub fn def(self) -> &'a mut ControlRegionDef {
        &mut self.control_regions[self.position]
    }

    pub fn at_children(mut self) -> FuncAtMut<'a, EntityList<ControlNode>> {
        let children = self.reborrow().def().children;
        self.at(children)
    }
}

// HACK(eddyb) can't implement `IntoIterator` because `next` borrows `self`.
impl<'a> FuncAtMut<'a, EntityList<ControlNode>> {
    pub fn into_iter(self) -> FuncAtMut<'a, Option<EntityListIter<ControlNode>>> {
        let iter = Some(self.position.iter());
        self.at(iter)
    }
}

// HACK(eddyb) can't implement `Iterator` because `next` borrows `self`.
impl FuncAtMut<'_, Option<EntityListIter<ControlNode>>> {
    pub fn next(&mut self) -> Option<FuncAtMut<'_, ControlNode>> {
        let (next, rest) = self.position?.split_first(&self.control_nodes);
        self.position = rest;
        Some(self.reborrow().at(next))
    }
}

impl<'a> FuncAtMut<'a, ControlNode> {
    pub fn def(self) -> &'a mut ControlNodeDef {
        &mut self.control_nodes[self.position]
    }
}

// HACK(eddyb) can't implement `IntoIterator` because `next` borrows `self`.
impl<'a> FuncAtMut<'a, Option<EntityList<DataInst>>> {
    pub fn into_iter(self) -> FuncAtMut<'a, Option<EntityListIter<DataInst>>> {
        let iter = self.position.map(|list| list.iter());
        self.at(iter)
    }
}

// HACK(eddyb) can't implement `Iterator` because `next` borrows `self`.
impl FuncAtMut<'_, Option<EntityListIter<DataInst>>> {
    pub fn next(&mut self) -> Option<FuncAtMut<'_, DataInst>> {
        let (next, rest) = self.position?.split_first(&self.data_insts);
        self.position = rest;
        Some(self.reborrow().at(next))
    }
}

impl<'a> FuncAtMut<'a, DataInst> {
    pub fn def(self) -> &'a mut DataInstDef {
        &mut self.data_insts[self.position]
    }
}

impl FuncDefBody {
    /// Start immutably traversing the function at `position`.
    pub fn at<'a, P: Copy>(&'a self, position: P) -> FuncAt<'a, P> {
        FuncAt {
            control_regions: &self.control_regions,
            control_nodes: &self.control_nodes,
            data_insts: &self.data_insts,
            position,
        }
    }

    /// Start mutably traversing the function at `position`.
    pub fn at_mut<'a, P: Copy>(&'a mut self, position: P) -> FuncAtMut<'a, P> {
        FuncAtMut {
            control_regions: &mut self.control_regions,
            control_nodes: &mut self.control_nodes,
            data_insts: &mut self.data_insts,
            position,
        }
    }

    /// Shorthand for `func_def_body.at(func_def_body.body)`.
    pub fn at_body<'a>(&'a self) -> FuncAt<'a, ControlRegion> {
        self.at(self.body)
    }

    /// Shorthand for `func_def_body.at_mut(func_def_body.body)`.
    pub fn at_mut_body<'a>(&'a mut self) -> FuncAtMut<'a, ControlRegion> {
        self.at_mut(self.body)
    }
}