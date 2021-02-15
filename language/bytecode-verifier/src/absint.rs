// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

use crate::{
    binary_views::FunctionView,
    control_flow_graph::{BlockId, ControlFlowGraph},
};
use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    fmt::Debug,
    ops::{Deref, DerefMut},
};
use vm::file_format::{Bytecode, CodeOffset};

/// Trait for finite-height abstract domains. Infinite height domains would require a more complex
/// trait with widening and a partial order.
pub trait AbstractDomain: Clone + Sized + Eq + PartialOrd + PartialEq + Debug {
    fn join(&mut self, other: &Self) -> JoinResult;
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct SetDomain<Elem: Clone + Ord + Sized>(pub BTreeSet<Elem>);

impl<E: Clone + Ord + Sized> Default for SetDomain<E> {
    fn default() -> Self {
        Self(BTreeSet::new())
    }
}

impl<E: Clone + Ord + Sized> Deref for SetDomain<E> {
    type Target = BTreeSet<E>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<E: Clone + Ord + Sized> DerefMut for SetDomain<E> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<E: Clone + Ord + Sized + Debug> AbstractDomain for SetDomain<E> {
    fn join(&mut self, other: &Self) -> JoinResult {
        if self == other {
            JoinResult::Unchanged
        } else {
            for e in other.iter() {
                self.insert(e.clone());
            }
            JoinResult::Changed
        }
    }
}

impl<E: Clone + Ord + Sized> SetDomain<E> {
    pub fn singleton(e: E) -> Self {
        let mut s = SetDomain::default();
        s.insert(e);
        s
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct MapDomain<K: Ord, V: AbstractDomain>(pub BTreeMap<K, V>);

impl<K: Ord, V: AbstractDomain> MapDomain<K, V> {
    /// join `v` with self[k] if `k` is bound, insert `v` otherwise
    pub fn insert_join(&mut self, k: K, v: V) {
        self.0
            .entry(k)
            .and_modify(|old_v| {
                old_v.join(&v);
            })
            .or_insert(v);
    }
}

impl<K: Ord, V: AbstractDomain> Default for MapDomain<K, V> {
    fn default() -> Self {
        Self(BTreeMap::new())
    }
}

impl<K: Clone + Sized + Eq + Ord + Debug, V: AbstractDomain> AbstractDomain for MapDomain<K, V> {
    fn join(&mut self, other: &Self) -> JoinResult {
        if self == other {
            JoinResult::Unchanged
        } else {
            for (k, v1) in other.iter() {
                self.entry(k.clone())
                    .and_modify(|v2| {
                        v2.join(&v1);
                    })
                    .or_insert_with(|| v1.clone());
            }
            JoinResult::Changed
        }
    }
}

impl<K: Clone + Sized + Eq + Ord, V: AbstractDomain> Deref for MapDomain<K, V> {
    type Target = BTreeMap<K, V>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<K: Clone + Sized + Eq + Ord, V: AbstractDomain> DerefMut for MapDomain<K, V> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

#[derive(Debug, Eq, PartialEq)]
pub(crate) enum JoinResult {
    Changed,
    Unchanged,
}

#[derive(Clone)]
pub(crate) enum BlockPostcondition<AnalysisError> {
    /// Block not yet analyzed
    Unprocessed,
    /// Analyzing block was successful
    /// TODO might carry post state at some point
    Success,
    /// Analyzing block resulted in an error
    Error(AnalysisError),
}

#[allow(dead_code)]
#[derive(Clone)]
pub(crate) struct BlockInvariant<State, AnalysisError> {
    /// Precondition of the block
    pub(crate) pre: State,
    /// Postcondition of the block
    pub(crate) post: BlockPostcondition<AnalysisError>,
}

/// A map from block id's to the pre/post of each block after a fixed point is reached.
#[allow(dead_code)]
pub(crate) type InvariantMap<State, AnalysisError> =
    HashMap<BlockId, BlockInvariant<State, AnalysisError>>;

/// Take a pre-state + instruction and mutate it to produce a post-state
/// Auxiliary data can be stored in self.
pub(crate) trait TransferFunctions {
    type State: AbstractDomain;
    type AnalysisError: Clone;

    /// Execute local@instr found at index local@index in the current basic block from pre-state
    /// local@pre.
    /// Should return an AnalysisError if executing the instruction is unsuccessful, and () if
    /// the effects of successfully executing local@instr have been reflected by mutatating
    /// local@pre.
    /// Auxilary data from the analysis that is not part of the abstract state can be collected by
    /// mutating local@self.
    /// The last instruction index in the current block is local@last_index. Knowing this
    /// information allows clients to detect the end of a basic block and special-case appropriately
    /// (e.g., normalizing the abstract state before a join).
    fn execute(
        &mut self,
        pre: &mut Self::State,
        instr: &Bytecode,
        index: CodeOffset,
        last_index: CodeOffset,
    ) -> Result<(), Self::AnalysisError>;
}

pub(crate) trait AbstractInterpreter: TransferFunctions {
    /// Analyze procedure local@function_view starting from pre-state local@initial_state.
    fn analyze_function(
        &mut self,
        initial_state: Self::State,
        function_view: &FunctionView,
    ) -> InvariantMap<Self::State, Self::AnalysisError> {
        let mut inv_map: InvariantMap<Self::State, Self::AnalysisError> = InvariantMap::new();
        let entry_block_id = function_view.cfg().entry_block_id();
        let mut work_list = vec![entry_block_id];
        inv_map.insert(
            entry_block_id,
            BlockInvariant {
                pre: initial_state,
                post: BlockPostcondition::Unprocessed,
            },
        );

        while let Some(block_id) = work_list.pop() {
            let block_invariant = match inv_map.get_mut(&block_id) {
                Some(invariant) => invariant,
                None => unreachable!("Missing invariant for block {}", block_id),
            };

            let pre_state = &block_invariant.pre;
            let post_state = match self.execute_block(block_id, pre_state, function_view) {
                Err(e) => {
                    block_invariant.post = BlockPostcondition::Error(e);
                    continue;
                }
                Ok(s) => {
                    block_invariant.post = BlockPostcondition::Success;
                    s
                }
            };

            // propagate postcondition of this block to successor blocks
            for next_block_id in function_view.cfg().successors(block_id) {
                match inv_map.get_mut(next_block_id) {
                    Some(next_block_invariant) => {
                        let join_result = {
                            let old_pre = &mut next_block_invariant.pre;
                            old_pre.join(&post_state)
                        };
                        match join_result {
                            JoinResult::Unchanged => {
                                // Pre is the same after join. Reanalyzing this block would produce
                                // the same post. Don't schedule it.
                                continue;
                            }
                            JoinResult::Changed => {
                                // The pre changed. Schedule the next block.
                                work_list.push(*next_block_id);
                            }
                        }
                    }
                    None => {
                        // Haven't visited the next block yet. Use the post of the current block as
                        // its pre and schedule it.
                        inv_map.insert(
                            *next_block_id,
                            BlockInvariant {
                                pre: post_state.clone(),
                                post: BlockPostcondition::Success,
                            },
                        );
                        work_list.push(*next_block_id);
                    }
                }
            }
        }
        inv_map
    }

    fn execute_block(
        &mut self,
        block_id: BlockId,
        pre_state: &Self::State,
        function_view: &FunctionView,
    ) -> Result<Self::State, Self::AnalysisError> {
        let mut state_acc = pre_state.clone();
        let block_end = function_view.cfg().block_end(block_id);
        for offset in function_view.cfg().instr_indexes(block_id) {
            let instr = &function_view.code().code[offset as usize];
            self.execute(&mut state_acc, instr, offset, block_end)?
        }
        Ok(state_acc)
    }
}
