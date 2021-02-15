// Copyright (c) The Diem Core Contributors
// SPDX-License-Identifier: Apache-2.0

//! This module defines the transfer functions for verifying reference safety of a procedure body.
//! The checks include (but are not limited to)
//! - verifying that there are no dangaling references,
//! - accesses to mutable references are safe
//! - accesses to global storage references are safe

use crate::{
    absint::{
        AbstractDomain, AbstractInterpreter, JoinResult, MapDomain, SetDomain, TransferFunctions,
    },
    binary_views::{BinaryIndexedView, FunctionView},
};

use mirai_annotations::*;
use std::{collections::HashMap, fmt::Debug};
use vm::{
    errors::{PartialVMError, PartialVMResult},
    file_format::{
        Bytecode, CodeOffset, FieldHandleIndex, FunctionDefinitionIndex, IdentifierIndex,
        LocalIndex, SignatureToken, StructDefinition, StructDefinitionIndex,
        StructFieldInformation,
    },
};

// ========= domains

#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
enum RefQualifier {
    Mut,
    Immut,
}

#[derive(Debug, Clone, Eq, PartialEq, PartialOrd, Ord)]
struct AbstractPath {
    paths: SetDomain<Path>,
    qualifier: RefQualifier,
}

/// Offset of an access path: either a field, vector index, or global key
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Offset {
    /// Index into contents of a struct by field offset
    Field(FieldHandleIndex),
    /// Unknown index into a vector
    VectorIndex,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Path {
    root: Root,
    offsets: Vec<Offset>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Root {
    Local(LocalIndex),
    Global(StructDefinitionIndex),
}

type AbstractState = MapDomain<LocalIndex, AbstractPath>;

// ========= joins

impl AbstractDomain for RefQualifier {
    fn join(&mut self, q: &RefQualifier) -> JoinResult {
        match self {
            RefQualifier::Mut => JoinResult::Unchanged,
            RefQualifier::Immut => {
                if *q == RefQualifier::Immut {
                    JoinResult::Unchanged
                } else {
                    *self = RefQualifier::Mut;
                    JoinResult::Changed
                }
            }
        }
    }
}

impl AbstractDomain for AbstractPath {
    fn join(&mut self, a: &AbstractPath) -> JoinResult {
        if self.paths.join(&a.paths) == JoinResult::Changed
            || self.qualifier.join(&a.qualifier) == JoinResult::Changed
        {
            JoinResult::Changed
        } else {
            JoinResult::Unchanged
        }
    }
}

// ========= impls

impl Path {
    /// Return true if `self` is a prefix of `p` (proper or improper)
    pub fn is_prefix(&self, p: &Path) -> bool {
        if self.root != p.root || self.offsets.len() > p.offsets.len() {
            return false;
        }
        for (i, offset) in self.offsets.iter().enumerate() {
            if p.offsets[i] != *offset {
                return false;
            }
        }
        true
    }
}

impl Path {
    pub fn add_offset(&mut self, offset: Offset) {
        self.offsets.push(offset)
    }
}

impl AbstractPath {
    pub fn non_ref() -> Self {
        AbstractPath {
            paths: SetDomain::default(),
            qualifier: RefQualifier::Immut,
        }
    }

    /// Return true if `self` contains a path `p <= p_in`
    pub fn contains_path_prefix(&self, p_in: &Path) -> bool {
        self.paths.iter().any(|p| p.is_prefix(p_in))
    }

    /// Return true if `self` contains any path `p` that is a prefix of some path in other
    pub fn contains_prefix(&self, other: &AbstractPath) -> bool {
        self.paths
            .iter()
            .any(|p| other.paths.iter().any(|other_p| p.is_prefix(other_p)))
    }

    pub fn add_offset(&mut self, offset: Offset) {
        let mut acc = SetDomain::default();
        for p in self.paths.iter() {
            let new_p = p.clone();
            new_p.add_offset(offset);
            acc.insert(new_p);
        }
        self.paths = acc
    }
}

// ========= analysis

struct ReferenceSafetyAnalysis<'a> {
    resolver: &'a BinaryIndexedView<'a>,
    function_view: &'a FunctionView<'a>,
    name_def_map: &'a HashMap<IdentifierIndex, FunctionDefinitionIndex>,
    stack: Vec<AbstractPath>,
}

impl<'a> ReferenceSafetyAnalysis<'a> {
    fn new(
        resolver: &'a BinaryIndexedView<'a>,
        function_view: &'a FunctionView<'a>,
        name_def_map: &'a HashMap<IdentifierIndex, FunctionDefinitionIndex>,
    ) -> Self {
        Self {
            resolver,
            function_view,
            name_def_map,
            stack: vec![],
        }
    }
}

pub(crate) fn verify<'a>(
    resolver: &'a BinaryIndexedView<'a>,
    function_view: &FunctionView,
    name_def_map: &'a HashMap<IdentifierIndex, FunctionDefinitionIndex>,
) -> PartialVMResult<()> {
    let initial_state = AbstractState::default();

    let mut verifier = ReferenceSafetyAnalysis::new(resolver, function_view, name_def_map);
    let inv_map = verifier.analyze_function(initial_state, function_view);
    /*// Report all the join failures
    for (_block_id, BlockInvariant { post, .. }) in inv_map {
        match post {
            BlockPostcondition::Error(err) => return Err(err),
            // Block might be unprocessed if all predecessors had an error
            BlockPostcondition::Unprocessed | BlockPostcondition::Success => (),
        }
    }*/
    Ok(())
}

/*fn call(
    verifier: &mut ReferenceSafetyAnalysis,
    state: &mut AbstractState,
    offset: CodeOffset,
    function_handle: &FunctionHandle,
) -> PartialVMResult<()> {
    let parameters = verifier.resolver.signature_at(function_handle.parameters);
    let arguments = parameters
        .0
        .iter()
        .map(|_| verifier.stack.pop().unwrap())
        .rev()
        .collect();

    let acquired_resources = match verifier.name_def_map.get(&function_handle.name) {
        Some(idx) => {
            let func_def = verifier.resolver.function_def_at(*idx)?;
            let fh = verifier.resolver.function_handle_at(func_def.function);
            if function_handle == fh {
                func_def.acquires_global_resources.iter().cloned().collect()
            } else {
                BTreeSet::new()
            }
        }
        None => BTreeSet::new(),
    };
    let return_ = verifier.resolver.signature_at(function_handle.return_);
    let values = state.call(offset, arguments, &acquired_resources, return_)?;
    for value in values {
        verifier.stack.push(value)
    }
    Ok(())
}*/

fn num_fields(struct_def: &StructDefinition) -> usize {
    match &struct_def.field_information {
        StructFieldInformation::Native => 0,
        StructFieldInformation::Declared(fields) => fields.len(),
    }
}

/// Error if state or stack contain a path p such that path <= p
fn check_prefix(path: &AbstractPath, state: &AbstractState, stack: &Vec<AbstractState>) {
    for p in state.values() {
        if p.contains_prefix(p) {
            unimplemented!("raise error here")
        }
    }
    for p in stack.iter() {
        if p.contains_prefix(p) {
            unimplemented!("raise error here")
        }
    }
}

fn execute_inner(
    verifier: &mut ReferenceSafetyAnalysis,
    state: &mut AbstractState,
    bytecode: &Bytecode,
    offset: CodeOffset,
) -> PartialVMResult<()> {
    match bytecode {
        Bytecode::Pop => verifier.stack.pop(),

        Bytecode::CopyLoc(local) => verifier.stack.push(state.get(local)),
        Bytecode::MoveLoc(local) => {
            let v = state.remove(local).unwrap();
            check_prefix(v, state, &verifier.stack);

            verifier.stack.push(v)
        }
        Bytecode::StLoc(local) => {
            let v = verifier.stack.pop();
        }

        Bytecode::FreezeRef => {
            let id = verifier.stack.pop().unwrap().ref_id().unwrap();
            let frozen = state.freeze_ref(offset, id)?;
            verifier.stack.push(frozen)
        }
        Bytecode::Eq | Bytecode::Neq => {
            let v1 = verifier.stack.pop().unwrap();
            let v2 = verifier.stack.pop().unwrap();
            let value = state.comparison(offset, v1, v2)?;
            verifier.stack.push(value)
        }
        Bytecode::ReadRef => {
            let id = verifier.stack.pop().unwrap().ref_id().unwrap();
            let value = state.read_ref(offset, id)?;
            verifier.stack.push(value)
        }
        Bytecode::WriteRef => {
            let id = verifier.stack.pop().unwrap().ref_id().unwrap();
            let val_operand = verifier.stack.pop().unwrap();
            checked_verify!(val_operand.is_value());
            state.write_ref(offset, id)?
        }

        Bytecode::MutBorrowLoc(local) => {
            let value = state.borrow_loc(offset, true, *local)?;
            verifier.stack.push(value)
        }
        Bytecode::ImmBorrowLoc(local) => {
            let value = state.borrow_loc(offset, false, *local)?;
            verifier.stack.push(value)
        }
        Bytecode::MutBorrowField(field_handle_index) => {
            let id = verifier.stack.pop().unwrap().ref_id().unwrap();
            let value = state.borrow_field(offset, true, id, *field_handle_index)?;
            verifier.stack.push(value)
        }
        Bytecode::MutBorrowFieldGeneric(field_inst_index) => {
            let field_inst = verifier
                .resolver
                .field_instantiation_at(*field_inst_index)?;
            let id = verifier.stack.pop().unwrap().ref_id().unwrap();
            let value = state.borrow_field(offset, true, id, field_inst.handle)?;
            verifier.stack.push(value)
        }
        Bytecode::ImmBorrowField(field_handle_index) => {
            let id = verifier.stack.pop().unwrap().ref_id().unwrap();
            let value = state.borrow_field(offset, false, id, *field_handle_index)?;
            verifier.stack.push(value)
        }
        Bytecode::ImmBorrowFieldGeneric(field_inst_index) => {
            let field_inst = verifier
                .resolver
                .field_instantiation_at(*field_inst_index)?;
            let id = verifier.stack.pop().unwrap().ref_id().unwrap();
            let value = state.borrow_field(offset, false, id, field_inst.handle)?;
            verifier.stack.push(value)
        }

        Bytecode::MutBorrowGlobal(idx) => {
            checked_verify!(verifier.stack.pop().unwrap().is_value());
            let value = state.borrow_global(offset, true, *idx)?;
            verifier.stack.push(value)
        }
        Bytecode::MutBorrowGlobalGeneric(idx) => {
            checked_verify!(verifier.stack.pop().unwrap().is_value());
            let struct_inst = verifier.resolver.struct_instantiation_at(*idx)?;
            let value = state.borrow_global(offset, true, struct_inst.def)?;
            verifier.stack.push(value)
        }
        Bytecode::ImmBorrowGlobal(idx) => {
            checked_verify!(verifier.stack.pop().unwrap().is_value());
            let value = state.borrow_global(offset, false, *idx)?;
            verifier.stack.push(value)
        }
        Bytecode::ImmBorrowGlobalGeneric(idx) => {
            checked_verify!(verifier.stack.pop().unwrap().is_value());
            let struct_inst = verifier.resolver.struct_instantiation_at(*idx)?;
            let value = state.borrow_global(offset, false, struct_inst.def)?;
            verifier.stack.push(value)
        }
        Bytecode::MoveFrom(idx) => {
            checked_verify!(verifier.stack.pop().unwrap().is_value());
            let value = state.move_from(offset, *idx)?;
            verifier.stack.push(value)
        }
        Bytecode::MoveFromGeneric(idx) => {
            checked_verify!(verifier.stack.pop().unwrap().is_value());
            let struct_inst = verifier.resolver.struct_instantiation_at(*idx)?;
            let value = state.move_from(offset, struct_inst.def)?;
            verifier.stack.push(value)
        }

        Bytecode::Call(idx) => {
            let function_handle = verifier.resolver.function_handle_at(*idx);
            //call(verifier, state, offset, function_handle)?
        }
        Bytecode::CallGeneric(idx) => {
            let func_inst = verifier.resolver.function_instantiation_at(*idx);
            let function_handle = verifier.resolver.function_handle_at(func_inst.handle);
            //call(verifier, state, offset, function_handle)?
        }

        Bytecode::Ret => {
            let mut return_values = vec![];
            for _ in 0..verifier.function_view.return_().len() {
                return_values.push(verifier.stack.pop().unwrap());
            }
            return_values.reverse();

            state.ret(offset, return_values)?
        }

        Bytecode::Branch(_)
        | Bytecode::Nop
        | Bytecode::CastU8
        | Bytecode::CastU64
        | Bytecode::CastU128
        | Bytecode::Not
        | Bytecode::Exists(_)
        | Bytecode::ExistsGeneric(_) => (),

        Bytecode::BrTrue(_) | Bytecode::BrFalse(_) | Bytecode::Abort => {
            checked_verify!(verifier.stack.pop().unwrap().is_value());
        }
        Bytecode::MoveTo(_) | Bytecode::MoveToGeneric(_) => {
            // resource value
            checked_verify!(verifier.stack.pop().unwrap().is_value());
            // signer reference
            state.release_value(verifier.stack.pop().unwrap());
        }

        Bytecode::LdTrue | Bytecode::LdFalse => {
            verifier.stack.push(state.value_for(&SignatureToken::Bool))
        }
        Bytecode::LdU8(_) => verifier.stack.push(state.value_for(&SignatureToken::U8)),
        Bytecode::LdU64(_) => verifier.stack.push(state.value_for(&SignatureToken::U64)),
        Bytecode::LdU128(_) => verifier.stack.push(state.value_for(&SignatureToken::U128)),
        Bytecode::LdConst(idx) => {
            let signature = &verifier.resolver.constant_at(*idx).type_;
            verifier.stack.push(state.value_for(signature))
        }

        Bytecode::Add
        | Bytecode::Sub
        | Bytecode::Mul
        | Bytecode::Mod
        | Bytecode::Div
        | Bytecode::BitOr
        | Bytecode::BitAnd
        | Bytecode::Xor
        | Bytecode::Shl
        | Bytecode::Shr
        | Bytecode::Or
        | Bytecode::And
        | Bytecode::Lt
        | Bytecode::Gt
        | Bytecode::Le
        | Bytecode::Ge => {
            checked_verify!(verifier.stack.pop().unwrap().is_value());
            checked_verify!(verifier.stack.pop().unwrap().is_value());
            // TODO maybe call state.value_for
            //            verifier.stack.push(AbstractValue::NonReference)
        }

        Bytecode::Pack(idx) => {
            let struct_def = verifier.resolver.struct_def_at(*idx)?;
            //          pack(verifier, struct_def)
        }
        Bytecode::PackGeneric(idx) => {
            let struct_inst = verifier.resolver.struct_instantiation_at(*idx)?;
            let struct_def = verifier.resolver.struct_def_at(struct_inst.def)?;
            //        pack(verifier, struct_def)
        }
        Bytecode::Unpack(idx) => {
            let struct_def = verifier.resolver.struct_def_at(*idx)?;
            //      unpack(verifier, struct_def)
        }
        Bytecode::UnpackGeneric(idx) => {
            let struct_inst = verifier.resolver.struct_instantiation_at(*idx)?;
            let struct_def = verifier.resolver.struct_def_at(struct_inst.def)?;
            //    unpack(verifier, struct_def)
        }
    };
    Ok(())
}

impl<'a> TransferFunctions for ReferenceSafetyAnalysis<'a> {
    type State = AbstractState;
    type AnalysisError = PartialVMError;

    fn execute(
        &mut self,
        state: &mut Self::State,
        bytecode: &Bytecode,
        index: CodeOffset,
        last_index: CodeOffset,
    ) -> Result<(), Self::AnalysisError> {
        execute_inner(self, state, bytecode, index)?;
        if index == last_index {
            checked_verify!(self.stack.is_empty());
            *state = state.construct_canonical_state()
        }
        Ok(())
    }
}

impl<'a> AbstractInterpreter for ReferenceSafetyAnalysis<'a> {}
