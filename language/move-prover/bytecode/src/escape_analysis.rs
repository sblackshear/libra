// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

//! The read/write set analysis is a compositional analysis that starts from the leaves of the
//! call graph and analyzes each procedure once. The result is a summary of the abstract paths
//! read/written by each procedure and the value(s) returned by the procedure.
//!
//! When the analysis encounters a call, it fetches the summary for the callee and applies it to the
//! current state. This logic (implemented in `apply_summary`) is by far the most complex part of the
//! analysis.

use crate::{
    dataflow_analysis::{
        AbstractDomain, DataflowAnalysis, JoinResult, MapDomain, TransferFunctions,
    },
    function_target::FunctionData,
    function_target_pipeline::{FunctionTargetProcessor, FunctionTargetsHolder},
    stackless_bytecode::{Bytecode, Operation},
    stackless_control_flow_graph::StacklessControlFlowGraph,
};
use move_binary_format::file_format::CodeOffset;
use move_model::{ast::TempIndex, model::FunctionEnv};
use std::cmp::Ordering;

// =================================================================================================
// Data Model

/// An access to local or global state
#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum AbsValue {
    NonRef,
    OkRef,
    InternalRef,
}

impl AbsValue {
    pub fn is_internal_ref(&self) -> bool {
        matches!(self, Self::InternalRef)
    }
}

type EscapeAnalysisState = MapDomain<TempIndex, AbsValue>;

impl EscapeAnalysisState {
    fn get_local_index(&self, i: &TempIndex) -> &AbsValue {
        self.get(i)
            .unwrap_or_else(|| panic!("Unbound local index {} in state {:?}", i, self))
    }

    fn assign(&mut self, lhs: TempIndex, rhs: &TempIndex) {
        let rhs_value = *self.get_local_index(rhs);
        self.insert(lhs, rhs_value);
    }
}

// =================================================================================================
// Abstract Domain Operations

// =================================================================================================
// Joins

impl PartialOrd for AbsValue {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self == other {
            return Some(Ordering::Equal);
        }
        match (self, other) {
            (_, AbsValue::InternalRef) => Some(Ordering::Less),
            _ => None,
        }
    }
}

impl AbstractDomain for AbsValue {
    fn join(&mut self, other: &Self) -> JoinResult {
        if self == other {
            return JoinResult::Unchanged;
        }
        // unequal; use top value
        *self = AbsValue::InternalRef;
        JoinResult::Changed
    }
}

// =================================================================================================
// Transfer functions

struct EscapeAnalysis<'a> {
    func_env: &'a FunctionEnv<'a>,
}

impl<'a> TransferFunctions for EscapeAnalysis<'a> {
    type State = EscapeAnalysisState;
    const BACKWARD: bool = false;

    fn execute(&self, state: &mut Self::State, instr: &Bytecode, _offset: CodeOffset) {
        use Bytecode::*;
        use Operation::*;

        match instr {
            Call(_, rets, oper, args, _abort_action) => match oper {
                BorrowField(..) => {
                    let to_propagate = match state.get_local_index(&args[0]) {
                        AbsValue::OkRef | AbsValue::InternalRef => AbsValue::InternalRef,
                        AbsValue::NonRef => panic!("Invariant violation: expected reference"),
                    };
                    state.insert(rets[0], to_propagate);
                }
                BorrowGlobal(_mid, _sid, _types) => {
                    state.insert(rets[0], AbsValue::InternalRef);
                }
                ReadRef | MoveFrom(..) | Exists(..) | Pack(..) | Eq | Neq | CastU8 | CastU64
                | CastU128 | Not | Add | Sub | Mul | Div | Mod | BitOr | BitAnd | Xor | Shl
                | Shr | Lt | Gt | Le | Ge | Or | And => {
                    // These operations all produce a non-reference value
                    state.insert(rets[0], AbsValue::NonRef);
                }
                BorrowLoc => {
                    state.insert(rets[0], AbsValue::OkRef);
                }
                Function(mid, fid, _) => {
                    let has_internal_ref_input = args
                        .iter()
                        .any(|arg_index| state.get(&arg_index).unwrap().is_internal_ref());
                    for (ret_index, ret_type) in self
                        .func_env
                        .module_env
                        .env
                        .get_module(*mid)
                        .into_function(*fid)
                        .get_return_types()
                        .iter()
                        .enumerate()
                    {
                        let ret_value = if ret_type.is_reference() {
                            if has_internal_ref_input {
                                AbsValue::InternalRef
                            } else {
                                AbsValue::OkRef
                            }
                        } else {
                            AbsValue::NonRef
                        };
                        state.insert(rets[ret_index], ret_value);
                    }
                }
                Unpack(..) => {
                    for ret_index in rets {
                        state.insert(*ret_index, AbsValue::NonRef);
                    }
                }
                FreezeRef => state.assign(rets[0], &args[0]),
                WriteRef | MoveTo(..) => {
                    // these operations do not assign any locals
                }
                Destroy => {
                    state.remove(&args[0]);
                }
                oper => panic!("unsupported oper {:?}", oper),
            },
            Load(_, lhs, _) => {
                state.insert(*lhs, AbsValue::NonRef);
            }
            Assign(_, lhs, rhs, _) => state.assign(*lhs, rhs),
            Ret(_, rets) => {
                for ret in rets {
                    if state.get_local_index(ret).is_internal_ref() {
                        println!(
                            "Found internal ref leak in {}",
                            self.func_env.get_full_name_str()
                        )
                    }
                }
            }
            Abort(..) | SaveMem(..) | Prop(..) | SaveSpecVar(..) | Branch(..) | Jump(..)
            | Label(..) | SpecBlock(..) | Nop(..) => {
                // these operations do not assign any locals
            }
        }
    }
}

impl<'a> DataflowAnalysis for EscapeAnalysis<'a> {}
pub struct EscapeAnalysisProcessor();
impl EscapeAnalysisProcessor {
    pub fn new() -> Box<Self> {
        Box::new(EscapeAnalysisProcessor())
    }
}

impl FunctionTargetProcessor for EscapeAnalysisProcessor {
    fn process(
        &self,
        _targets: &mut FunctionTargetsHolder,
        func_env: &FunctionEnv<'_>,
        data: FunctionData,
    ) -> FunctionData {
        if func_env.is_native() {
            return data;
        }
        let mut initial_state = EscapeAnalysisState::default();
        // initialize_formals
        for (param_index, param_type) in func_env.get_parameter_types().iter().enumerate() {
            let param_val = if param_type.is_reference() {
                AbsValue::OkRef
            } else {
                AbsValue::NonRef
            };
            initial_state.insert(param_index, param_val);
        }
        /*println!(
            "Analyzing {} from initial state {:?}",
            func_env.get_full_name_str(),
            initial_state
        );*/
        let cfg = StacklessControlFlowGraph::new_forward(&data.code);
        let analysis = EscapeAnalysis { func_env };
        analysis.analyze_function(initial_state, &data.code, &cfg);
        data
    }

    fn name(&self) -> String {
        "escape_analysis".to_string()
    }
}
