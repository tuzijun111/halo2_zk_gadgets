use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        param::{N_BYTES_GAS, N_BYTES_U64},
        step::ExecutionState,
        util::{
            and,
            common_gadget::{CommonCallGadget, TransferGadget},
            constraint_builder::{
                ConstrainBuilderCommon, EVMConstraintBuilder, ReversionInfo, StepStateTransition,
                Transition::{Delta, To},
            },
            math_gadget::{
                ConstantDivisionGadget, IsZeroGadget, LtGadget, LtWordGadget, MinMaxGadget,
            },
            memory_gadget::{CommonMemoryAddressGadget, MemoryAddressGadget},
            not, or, select, CachedRegion, Cell, StepRws,
        },
    },
    util::word::{Word, WordCell, WordExpr},
};

use crate::{
    evm_circuit::witness::{Block, Call, ExecStep, Transaction},
    table::{AccountFieldTag, CallContextFieldTag},
    util::Expr,
};
use bus_mapping::evm::OpcodeId;
use eth_types::{evm_types::GAS_STIPEND_CALL_WITH_VALUE, Field, ToAddress, U256};
use halo2_proofs::{circuit::Value, plonk::Error};

/// Gadget for call related opcodes. It supports `OpcodeId::CALL`,
/// `OpcodeId::CALLCODE`, `OpcodeId::DELEGATECALL` and `OpcodeId::STATICCALL`.
/// both for successful and failure(insufficient balance error) cases.
#[derive(Clone, Debug)]

pub(crate) struct CallOpGadget<F> {
    opcode: Cell<F>,
    is_call: IsZeroGadget<F>,
    is_callcode: IsZeroGadget<F>,
    is_delegatecall: IsZeroGadget<F>,
    is_staticcall: IsZeroGadget<F>,
    tx_id: Cell<F>,
    reversion_info: ReversionInfo<F>,
    current_callee_address: WordCell<F>,
    current_caller_address: WordCell<F>,
    is_static: Cell<F>,
    depth: Cell<F>,
    call: CommonCallGadget<F, MemoryAddressGadget<F>, true>,
    current_value: WordCell<F>,
    is_warm: Cell<F>,
    is_warm_prev: Cell<F>,
    callee_reversion_info: ReversionInfo<F>,
    transfer: TransferGadget<F>,
    // current handling Call* opcode's caller balance
    caller_balance: WordCell<F>,
    // check if insufficient balance case
    is_insufficient_balance: LtWordGadget<F>,
    is_depth_ok: LtGadget<F, N_BYTES_U64>,
    one_64th_gas: ConstantDivisionGadget<F, N_BYTES_GAS>,
    capped_callee_gas_left: MinMaxGadget<F, N_BYTES_GAS>,
}

impl<F: Field> ExecutionGadget<F> for CallOpGadget<F> {
    const NAME: &'static str = "CALL_OP";

    const EXECUTION_STATE: ExecutionState = ExecutionState::CALL_OP;

    fn configure(cb: &mut EVMConstraintBuilder<F>) -> Self {
        let opcode = cb.query_cell();
        cb.opcode_lookup(opcode.expr(), 1.expr());
        let is_call = IsZeroGadget::construct(cb, opcode.expr() - OpcodeId::CALL.expr());
        let is_callcode = IsZeroGadget::construct(cb, opcode.expr() - OpcodeId::CALLCODE.expr());
        let is_delegatecall =
            IsZeroGadget::construct(cb, opcode.expr() - OpcodeId::DELEGATECALL.expr());
        let is_staticcall =
            IsZeroGadget::construct(cb, opcode.expr() - OpcodeId::STATICCALL.expr());

        // Use rw_counter of the step which triggers next call as its call_id.
        let callee_call_id = cb.curr.state.rw_counter.clone();

        let tx_id = cb.call_context(None, CallContextFieldTag::TxId);
        let mut reversion_info = cb.reversion_info_read(None);
        let [is_static, depth] = [CallContextFieldTag::IsStatic, CallContextFieldTag::Depth]
            .map(|field_tag| cb.call_context(None, field_tag));

        let current_callee_address =
            cb.call_context_read_as_word(None, CallContextFieldTag::CalleeAddress);
        let (current_caller_address, current_value) = cb.condition(is_delegatecall.expr(), |cb| {
            (
                cb.call_context_read_as_word(None, CallContextFieldTag::CallerAddress),
                cb.call_context_read_as_word(None, CallContextFieldTag::Value),
            )
        });

        let call_gadget: CommonCallGadget<F, MemoryAddressGadget<F>, true> =
            CommonCallGadget::construct(
                cb,
                is_call.expr(),
                is_callcode.expr(),
                is_delegatecall.expr(),
                is_staticcall.expr(),
            );
        cb.condition(not::expr(is_call.expr() + is_callcode.expr()), |cb| {
            cb.require_zero_word(
                "for non call/call code, value is zero",
                call_gadget.value.to_word(),
            );
        });

        let caller_address = Word::select(
            is_delegatecall.expr(),
            current_caller_address.to_word(),
            current_callee_address.to_word(),
        );
        let callee_address = Word::select(
            is_callcode.expr() + is_delegatecall.expr(),
            current_callee_address.to_word(),
            call_gadget.callee_address(),
        );

        // Add callee to access list
        let is_warm = cb.query_bool();
        let is_warm_prev = cb.query_bool();
        cb.account_access_list_write_unchecked(
            tx_id.expr(),
            call_gadget.callee_address(),
            is_warm.expr(),
            is_warm_prev.expr(),
            Some(&mut reversion_info),
        );

        // Propagate rw_counter_end_of_reversion and is_persistent
        let mut callee_reversion_info =
            cb.reversion_info_write_unchecked(Some(callee_call_id.expr()));
        cb.require_equal(
            "callee_is_persistent == is_persistent ⋅ is_success",
            callee_reversion_info.is_persistent(),
            reversion_info.is_persistent() * call_gadget.is_success.expr(),
        );
        cb.condition(call_gadget.is_success.expr() * (1.expr() - reversion_info.is_persistent()), |cb| {
            cb.require_equal(
                "callee_rw_counter_end_of_reversion == rw_counter_end_of_reversion - (reversible_write_counter + 1)",
                callee_reversion_info.rw_counter_end_of_reversion(),
                reversion_info.rw_counter_of_reversion(1.expr()),
            );
        });

        cb.condition(is_call.expr() * call_gadget.has_value.clone(), |cb| {
            cb.require_zero(
                "CALL with value must not be in static call stack",
                is_static.expr(),
            );
        });

        let caller_balance = cb.query_word_unchecked();
        cb.account_read(
            caller_address.to_word(),
            AccountFieldTag::Balance,
            caller_balance.to_word(),
        );
        let is_insufficient_balance =
            LtWordGadget::construct(cb, &caller_balance.to_word(), &call_gadget.value.to_word());
        // depth < 1025
        let is_depth_ok = LtGadget::construct(cb, depth.expr(), 1025.expr());

        let is_precheck_ok = and::expr([
            is_depth_ok.expr(),
            not::expr(is_insufficient_balance.expr()),
        ]);

        // stack write is zero when is_insufficient_balance is true
        cb.condition(not::expr(is_precheck_ok.expr()), |cb| {
            cb.require_zero(
                "stack write result is zero when is_insufficient_balance is true",
                call_gadget.is_success.expr(),
            );
        });

        // Verify transfer only for CALL opcode in the successful case.  If value == 0,
        // skip the transfer (this is necessary for non-existing accounts, which
        // will not be crated when value is 0 and so the callee balance lookup
        // would be invalid).
        let transfer = cb.condition(is_call.expr() * is_precheck_ok.expr(), |cb| {
            TransferGadget::construct(
                cb,
                caller_address.to_word(),
                callee_address.to_word(),
                not::expr(call_gadget.callee_not_exists.expr()),
                0.expr(),
                call_gadget.value.clone(),
                &mut callee_reversion_info,
            )
        });

        // For CALLCODE opcode, verify caller balance is greater than or equal to stack
        // `value` in successful case. that is `is_insufficient_balance` is false.
        // for call opcode, this has been checked in transfer gadget implicitly.
        cb.condition(is_callcode.expr() * call_gadget.is_success.expr(), |cb| {
            cb.require_zero(
                "transfer_value <= caller_balance for CALLCODE opcode in successful case ",
                is_insufficient_balance.expr(),
            );
        });

        // no_callee_code is true when the account exists and has empty
        // code hash, or when the account doesn't exist (which we encode with
        // code_hash = 0).
        let no_callee_code =
            call_gadget.is_empty_code_hash.expr() + call_gadget.callee_not_exists.expr();

        // Sum up and verify gas cost.
        // Only CALL opcode could invoke transfer to make empty account into non-empty.
        let gas_cost = call_gadget.gas_cost_expr(is_warm_prev.expr(), is_call.expr());
        // Apply EIP 150
        let gas_available = cb.curr.state.gas_left.expr() - gas_cost.clone();
        let one_64th_gas = ConstantDivisionGadget::construct(cb, gas_available.clone(), 64);
        let all_but_one_64th_gas = gas_available - one_64th_gas.quotient();
        let capped_callee_gas_left =
            MinMaxGadget::construct(cb, call_gadget.gas_expr(), all_but_one_64th_gas.clone());
        let callee_gas_left = select::expr(
            call_gadget.gas_is_u64.expr(),
            capped_callee_gas_left.min(),
            all_but_one_64th_gas,
        );

        // TODO: Handle precompiled

        let stack_pointer_delta =
            select::expr(is_call.expr() + is_callcode.expr(), 6.expr(), 5.expr());
        let memory_expansion = call_gadget.memory_expansion.clone();

        // handle calls to accounts with no code.
        cb.condition(
            and::expr(&[no_callee_code.expr(), is_precheck_ok.expr()]),
            |cb| {
                // Save caller's call state
                cb.call_context_lookup_write(
                    None,
                    CallContextFieldTag::LastCalleeId,
                    Word::from_lo_unchecked(callee_call_id.expr()),
                );
                for field_tag in [
                    CallContextFieldTag::LastCalleeReturnDataOffset,
                    CallContextFieldTag::LastCalleeReturnDataLength,
                ] {
                    cb.call_context_lookup_write(None, field_tag, Word::zero());
                }

                // For CALL opcode, it has an extra stack pop `value` (+1) and if the value is
                // not zero, two account write for `transfer` call (+2).
                //
                // For CALLCODE opcode, it has an extra stack pop `value` and one account read
                // for caller balance (+2).
                //
                // For DELEGATECALL opcode, it has two extra call context lookups for current
                // caller address and value (+2).
                //
                // No extra lookups for STATICCALL opcode.
                let transfer_rwc_delta = is_call.expr() * transfer.reversible_w_delta();
                let rw_counter_delta = 21.expr()
                    + is_call.expr() * 1.expr()
                    + transfer_rwc_delta.clone()
                    + is_callcode.expr()
                    + is_delegatecall.expr() * 2.expr();
                cb.require_step_state_transition(StepStateTransition {
                    rw_counter: Delta(rw_counter_delta),
                    program_counter: Delta(1.expr()),
                    stack_pointer: Delta(stack_pointer_delta.expr()),
                    gas_left: Delta(
                        call_gadget.has_value.clone() * GAS_STIPEND_CALL_WITH_VALUE.expr()
                            - gas_cost.clone(),
                    ),
                    memory_word_size: To(memory_expansion.next_memory_word_size()),
                    // For CALL opcode, `transfer` invocation has two account write if value is not
                    // zero.
                    reversible_write_counter: Delta(1.expr() + transfer_rwc_delta),
                    ..StepStateTransition::default()
                });
            },
        );

        // handle is_insufficient_balance or !is_depth_ok step transition
        cb.condition(not::expr(is_precheck_ok.expr()), |cb| {
            // Save caller's call state
            cb.call_context_lookup_write(
                None,
                CallContextFieldTag::LastCalleeId,
                Word::from_lo_unchecked(callee_call_id.expr()),
            );
            for field_tag in [
                CallContextFieldTag::LastCalleeReturnDataOffset,
                CallContextFieldTag::LastCalleeReturnDataLength,
            ] {
                cb.call_context_lookup_write(None, field_tag, Word::zero());
            }

            cb.require_step_state_transition(StepStateTransition {
                rw_counter: Delta(22.expr()),
                program_counter: Delta(1.expr()),
                stack_pointer: Delta(stack_pointer_delta.expr()),
                gas_left: Delta(
                    call_gadget.has_value.clone() * GAS_STIPEND_CALL_WITH_VALUE.expr()
                        - gas_cost.clone(),
                ),
                memory_word_size: To(memory_expansion.next_memory_word_size()),
                reversible_write_counter: Delta(1.expr()),
                ..StepStateTransition::default()
            });
        });

        cb.condition(
            and::expr(&[not::expr(no_callee_code), is_precheck_ok.expr()]),
            |cb| {
                // Save caller's call state
                for (field_tag, value) in [
                    (
                        CallContextFieldTag::ProgramCounter,
                        cb.curr.state.program_counter.expr() + 1.expr(),
                    ),
                    (
                        CallContextFieldTag::StackPointer,
                        cb.curr.state.stack_pointer.expr() + stack_pointer_delta,
                    ),
                    (
                        CallContextFieldTag::GasLeft,
                        cb.curr.state.gas_left.expr() - gas_cost - callee_gas_left.clone(),
                    ),
                    (
                        CallContextFieldTag::MemorySize,
                        memory_expansion.next_memory_word_size(),
                    ),
                    (
                        CallContextFieldTag::ReversibleWriteCounter,
                        cb.curr.state.reversible_write_counter.expr() + 1.expr(),
                    ),
                ] {
                    cb.call_context_lookup_write(None, field_tag, Word::from_lo_unchecked(value));
                }

                // Setup next call's context.
                let cd_address = call_gadget.cd_address.clone();
                let rd_address = call_gadget.rd_address.clone();
                for (field_tag, value) in [
                    (
                        CallContextFieldTag::CallerId,
                        Word::from_lo_unchecked(cb.curr.state.call_id.expr()),
                    ),
                    (
                        CallContextFieldTag::TxId,
                        Word::from_lo_unchecked(tx_id.expr()),
                    ),
                    (
                        CallContextFieldTag::Depth,
                        Word::from_lo_unchecked(depth.expr() + 1.expr()),
                    ),
                    (CallContextFieldTag::CallerAddress, caller_address),
                    (CallContextFieldTag::CalleeAddress, callee_address),
                    (
                        CallContextFieldTag::CallDataOffset,
                        Word::from_lo_unchecked(cd_address.offset()),
                    ),
                    (
                        CallContextFieldTag::CallDataLength,
                        Word::from_lo_unchecked(cd_address.length()),
                    ),
                    (
                        CallContextFieldTag::ReturnDataOffset,
                        Word::from_lo_unchecked(rd_address.offset()),
                    ),
                    (
                        CallContextFieldTag::ReturnDataLength,
                        Word::from_lo_unchecked(rd_address.length()),
                    ),
                    (
                        CallContextFieldTag::Value,
                        Word::select(
                            is_delegatecall.expr(),
                            current_value.to_word(),
                            call_gadget.value.to_word(),
                        ),
                    ),
                    (
                        CallContextFieldTag::IsSuccess,
                        Word::from_lo_unchecked(call_gadget.is_success.expr()),
                    ),
                    (
                        CallContextFieldTag::IsStatic,
                        Word::from_lo_unchecked(or::expr([is_static.expr(), is_staticcall.expr()])),
                    ),
                    (CallContextFieldTag::LastCalleeId, Word::zero()),
                    (
                        CallContextFieldTag::LastCalleeReturnDataOffset,
                        Word::zero(),
                    ),
                    (
                        CallContextFieldTag::LastCalleeReturnDataLength,
                        Word::zero(),
                    ),
                    (CallContextFieldTag::IsRoot, Word::zero()),
                    (CallContextFieldTag::IsCreate, Word::zero()),
                    (
                        CallContextFieldTag::CodeHash,
                        call_gadget.callee_code_hash.to_word(),
                    ),
                ] {
                    cb.call_context_lookup_write(Some(callee_call_id.expr()), field_tag, value);
                }

                // Give gas stipend if value is not zero
                let callee_gas_left = callee_gas_left
                    + call_gadget.has_value.clone() * GAS_STIPEND_CALL_WITH_VALUE.expr();

                // For CALL opcode, it has an extra stack pop `value` (+1) and if the value is
                // not zero, two account write for `transfer` call (+2).
                //
                // For CALLCODE opcode, it has an extra stack pop `value` and one account read
                // for caller balance (+2).
                //
                // For DELEGATECALL opcode, it has two extra call context lookups for current
                // caller address and value (+2).
                //
                // No extra lookups for STATICCALL opcode.
                let transfer_rwc_delta =
                    is_call.expr() * not::expr(transfer.value_is_zero.expr()) * 2.expr();
                let rw_counter_delta = 41.expr()
                    + is_call.expr() * 1.expr()
                    + transfer_rwc_delta.clone()
                    + is_callcode.expr()
                    + is_delegatecall.expr() * 2.expr();
                cb.require_step_state_transition(StepStateTransition {
                    rw_counter: Delta(rw_counter_delta),
                    call_id: To(callee_call_id.expr()),
                    is_root: To(false.expr()),
                    is_create: To(false.expr()),
                    code_hash: To(call_gadget.callee_code_hash.to_word()),
                    gas_left: To(callee_gas_left),
                    // For CALL opcode, `transfer` invocation has two account write if value is not
                    // zero.
                    reversible_write_counter: To(transfer_rwc_delta),
                    ..StepStateTransition::new_context()
                });
            },
        );

        Self {
            opcode,
            is_call,
            is_callcode,
            is_delegatecall,
            is_staticcall,
            tx_id,
            reversion_info,
            current_callee_address,
            current_caller_address,
            current_value,
            is_static,
            depth,
            call: call_gadget,
            is_warm,
            is_warm_prev,
            callee_reversion_info,
            transfer,
            caller_balance,
            is_insufficient_balance,
            is_depth_ok,
            one_64th_gas,
            capped_callee_gas_left,
        }
    }

    fn assign_exec_step(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        block: &Block<F>,
        _: &Transaction,
        call: &Call,
        step: &ExecStep,
    ) -> Result<(), Error> {
        let opcode = step.opcode().unwrap();
        let is_call = opcode == OpcodeId::CALL;
        let is_callcode = opcode == OpcodeId::CALLCODE;
        let is_delegatecall = opcode == OpcodeId::DELEGATECALL;
        let mut rws = StepRws::new(block, step);
        let tx_id = rws.next().call_context_value();
        rws.next(); // RwCounterEndOfReversion
        rws.next(); // IsPersistent

        let is_static = rws.next().call_context_value();
        let depth = rws.next().call_context_value();
        let current_callee_address = rws.next().call_context_value();

        let is_valid_depth = depth.low_u64() < 1025;
        self.is_depth_ok
            .assign(region, offset, F::from(depth.low_u64()), F::from(1025))?;
        // This offset is used to change the index offset of `step.rw_indices`.
        // Since both CALL and CALLCODE have an extra stack pop `value`, and
        // opcode DELEGATECALL has two extra call context lookups - current
        // caller address and current value.
        let [current_caller_address, current_value] = if is_delegatecall {
            [
                rws.next().call_context_value(),
                rws.next().call_context_value(),
            ]
        } else {
            [U256::zero(), U256::zero()]
        };
        let gas = rws.next().stack_value();
        let callee_address = rws.next().stack_value();

        let value = if is_call || is_callcode {
            rws.next().stack_value()
        } else {
            U256::zero()
        };
        let cd_offset = rws.next().stack_value();
        let cd_length = rws.next().stack_value();
        let rd_offset = rws.next().stack_value();
        let rd_length = rws.next().stack_value();
        let is_success = rws.next().stack_value();

        let callee_code_hash = rws.next().account_codehash_pair().0;
        let callee_exists = !callee_code_hash.is_zero();

        let (is_warm, is_warm_prev) = rws.next().tx_access_list_value_pair();

        let callee_rw_counter_end_of_reversion = rws.next().call_context_value();
        let callee_is_persistent = rws.next().call_context_value();

        // check if it is insufficient balance case.
        // get caller balance
        let caller_balance = rws.next().account_balance_pair().0;
        self.caller_balance
            .assign_u256(region, offset, caller_balance)?;
        self.is_insufficient_balance
            .assign(region, offset, caller_balance, value)?;

        self.opcode
            .assign(region, offset, Value::known(F::from(opcode.as_u64())))?;
        self.is_call.assign(
            region,
            offset,
            F::from(opcode.as_u64()) - F::from(OpcodeId::CALL.as_u64()),
        )?;
        self.is_callcode.assign(
            region,
            offset,
            F::from(opcode.as_u64()) - F::from(OpcodeId::CALLCODE.as_u64()),
        )?;
        self.is_delegatecall.assign(
            region,
            offset,
            F::from(opcode.as_u64()) - F::from(OpcodeId::DELEGATECALL.as_u64()),
        )?;
        self.is_staticcall.assign(
            region,
            offset,
            F::from(opcode.as_u64()) - F::from(OpcodeId::STATICCALL.as_u64()),
        )?;
        self.tx_id
            .assign(region, offset, Value::known(F::from(tx_id.low_u64())))?;
        self.reversion_info.assign(
            region,
            offset,
            call.rw_counter_end_of_reversion,
            call.is_persistent,
        )?;
        self.current_callee_address.assign_h160(
            region,
            offset,
            current_callee_address.to_address(),
        )?;
        self.current_caller_address.assign_h160(
            region,
            offset,
            current_caller_address.to_address(),
        )?;
        self.current_value
            .assign_u256(region, offset, current_value)?;
        self.is_static
            .assign(region, offset, Value::known(F::from(is_static.low_u64())))?;
        self.depth
            .assign(region, offset, Value::known(F::from(depth.low_u64())))?;

        let memory_expansion_gas_cost = self.call.assign(
            region,
            offset,
            gas,
            callee_address,
            value,
            is_success,
            cd_offset,
            cd_length,
            rd_offset,
            rd_length,
            step.memory_word_size(),
            callee_code_hash,
        )?;
        self.is_warm
            .assign(region, offset, Value::known(F::from(is_warm as u64)))?;
        self.is_warm_prev
            .assign(region, offset, Value::known(F::from(is_warm_prev as u64)))?;
        self.callee_reversion_info.assign(
            region,
            offset,
            callee_rw_counter_end_of_reversion.low_u64() as usize,
            callee_is_persistent.low_u64() != 0,
        )?;

        let is_call_or_callcode = is_call || is_callcode;
        let is_sufficient = caller_balance >= value;
        let is_precheck_ok = is_valid_depth && (is_sufficient || !is_call_or_callcode);

        // conditionally assign
        if is_call && is_precheck_ok && !value.is_zero() {
            if !callee_exists {
                rws.next().account_codehash_pair(); // callee hash
            }

            let caller_balance_pair = rws.next().account_balance_pair();
            let callee_balance_pair = rws.next().account_balance_pair();
            self.transfer.assign(
                region,
                offset,
                caller_balance_pair,
                callee_balance_pair,
                value,
            )?;
        }

        let has_value = !value.is_zero() && !is_delegatecall;
        let gas_cost = self.call.cal_gas_cost_for_assignment(
            memory_expansion_gas_cost,
            is_warm_prev,
            is_call,
            has_value,
            !callee_exists,
        )?;
        let gas_available: u64 = step.gas_left - gas_cost;

        self.one_64th_gas
            .assign(region, offset, gas_available.into())?;
        self.capped_callee_gas_left.assign(
            region,
            offset,
            F::from(gas.low_u64()),
            F::from(gas_available - gas_available / 64),
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::test_util::CircuitTestBuilder;
    use bus_mapping::circuit_input_builder::FixedCParams;
    use eth_types::{
        address, bytecode, evm_types::OpcodeId, geth_types::Account, word, Address, ToWord, Word,
    };

    use itertools::Itertools;
    use mock::{test_ctx::helpers::account_0_code_account_1_no_code, TestContext};

    use std::default::Default;

    const TEST_CALL_OPCODES: &[OpcodeId] = &[
        OpcodeId::CALL,
        OpcodeId::CALLCODE,
        OpcodeId::DELEGATECALL,
        OpcodeId::STATICCALL,
    ];

    #[test]
    fn callop_insufficient_balance() {
        let stacks = [Stack {
            // this value is bigger than caller's balance
            value: Word::from(11).pow(18.into()),
            ..Default::default()
        }];

        let callees = [callee(bytecode! {}), callee(bytecode! { STOP })];
        // only call, callcode will encounter insufficient balance error.
        let test_opcodes: &[OpcodeId] = &[OpcodeId::CALL, OpcodeId::CALLCODE];

        for ((opcode, stack), callee) in test_opcodes
            .iter()
            .cartesian_product(stacks.into_iter())
            .cartesian_product(callees.into_iter())
        {
            test_ok(caller_for_insufficient_balance(opcode, stack), callee);
        }
    }

    #[test]
    fn callop_nested() {
        for opcode in TEST_CALL_OPCODES {
            test_nested(opcode);
        }
    }

    #[test]
    fn callop_recursive() {
        for opcode in TEST_CALL_OPCODES {
            test_recursive(opcode);
        }
    }

    #[test]
    fn callop_simple() {
        let stacks = [
            // With nothing
            Stack::default(),
            // With value
            Stack {
                value: Word::from(10).pow(18.into()),
                ..Default::default()
            },
            // With gas
            Stack {
                gas: 100,
                ..Default::default()
            },
            Stack {
                gas: 100000,
                ..Default::default()
            },
            // With memory expansion
            Stack {
                cd_offset: 64.into(),
                cd_length: 320,
                rd_offset: Word::zero(),
                rd_length: 32,
                ..Default::default()
            },
            Stack {
                cd_offset: Word::zero(),
                cd_length: 32,
                rd_offset: 64.into(),
                rd_length: 320,
                ..Default::default()
            },
            Stack {
                cd_offset: 0xFFFFFF.into(),
                cd_length: 0,
                rd_offset: 0xFFFFFF.into(),
                rd_length: 0,
                ..Default::default()
            },
            // With memory expansion and value
            Stack {
                cd_offset: 64.into(),
                cd_length: 320,
                rd_offset: 0.into(),
                rd_length: 32,
                value: Word::from(10).pow(18.into()),
                ..Default::default()
            },
        ];
        let callees = [callee(bytecode! {}), callee(bytecode! { STOP })];

        for ((opcode, stack), callee) in TEST_CALL_OPCODES
            .iter()
            .cartesian_product(stacks.into_iter())
            .cartesian_product(callees.into_iter())
        {
            test_ok(caller(opcode, stack, true), callee);
        }
    }

    #[test]
    fn callop_overflow_offset_and_zero_length() {
        let stack = Stack {
            cd_offset: Word::MAX,
            cd_length: 0,
            rd_offset: Word::MAX,
            rd_length: 0,
            ..Default::default()
        };

        TEST_CALL_OPCODES
            .iter()
            .for_each(|opcode| test_ok(caller(opcode, stack, true), callee(bytecode! {})));
    }

    #[derive(Clone, Copy, Debug, Default)]
    struct Stack {
        gas: u64,
        value: Word,
        cd_offset: Word,
        cd_length: u64,
        rd_offset: Word,
        rd_length: u64,
    }

    fn callee(code: bytecode::Bytecode) -> Account {
        Account::mock_code_balance(code)
    }

    fn caller(opcode: &OpcodeId, stack: Stack, caller_is_success: bool) -> Account {
        let is_call_or_callcode = opcode == &OpcodeId::CALL || opcode == &OpcodeId::CALLCODE;
        let terminator = if caller_is_success {
            OpcodeId::RETURN
        } else {
            OpcodeId::REVERT
        };

        // Call twice for testing both cold and warm access
        let mut bytecode = bytecode! {
            PUSH32(Word::from(stack.rd_length))
            PUSH32(stack.rd_offset)
            PUSH32(Word::from(stack.cd_length))
            PUSH32(stack.cd_offset)
        };
        if is_call_or_callcode {
            bytecode.push(32, stack.value);
        }
        bytecode.append(&bytecode! {
            PUSH32(Address::repeat_byte(0xff).to_word())
            PUSH32(Word::from(stack.gas))
            .write_op(*opcode)
            PUSH32(Word::from(stack.rd_length))
            PUSH32(stack.rd_offset)
            PUSH32(Word::from(stack.cd_length))
            PUSH32(stack.cd_offset)
        });
        if is_call_or_callcode {
            bytecode.push(32, stack.value);
        }
        bytecode.append(&bytecode! {
            PUSH32(Address::repeat_byte(0xff).to_word())
            PUSH32(Word::from(stack.gas))
            .write_op(*opcode)
            PUSH1(0)
            PUSH1(0)
            .write_op(terminator)
        });

        Account::mock_100_ether(bytecode)
    }

    fn caller_for_insufficient_balance(opcode: &OpcodeId, stack: Stack) -> Account {
        let is_call_or_callcode = opcode == &OpcodeId::CALL || opcode == &OpcodeId::CALLCODE;
        let terminator = OpcodeId::STOP;

        let mut bytecode = bytecode! {
            PUSH32(Word::from(stack.rd_length))
            PUSH32(stack.rd_offset)
            PUSH32(Word::from(stack.cd_length))
            PUSH32(stack.cd_offset)
        };
        if is_call_or_callcode {
            bytecode.push(32, stack.value);
        }
        bytecode.append(&bytecode! {
            PUSH32(Address::repeat_byte(0xff).to_word())
            PUSH32(Word::from(stack.gas))
            .write_op(*opcode)
            .write_op(terminator)
        });

        Account {
            address: Address::repeat_byte(0xfe),
            balance: Word::from(10).pow(18.into()), // 1 Ether
            code: bytecode.into(),
            ..Default::default()
        }
    }

    fn test_nested(opcode: &OpcodeId) {
        let callers = [
            caller(
                opcode,
                Stack {
                    gas: 100000,
                    ..Default::default()
                },
                true,
            ),
            caller(
                opcode,
                Stack {
                    gas: 100000,
                    ..Default::default()
                },
                false,
            ),
        ];
        let callees = [
            // Success
            callee(bytecode! { PUSH1(0) PUSH1(0) RETURN }),
            // Failure
            callee(bytecode! { PUSH1(0) PUSH1(0) REVERT }),
        ];

        for (caller, callee) in callers.into_iter().cartesian_product(callees.into_iter()) {
            test_ok(caller, callee);
        }
    }

    #[test]
    fn callop_base() {
        test_ok(
            caller(&OpcodeId::CALL, Stack::default(), true),
            callee(bytecode! {}),
        );
    }

    fn test_ok(caller: Account, callee: Account) {
        let ctx = TestContext::<3, 1>::new(
            None,
            |accs| {
                accs[0]
                    .address(address!("0x000000000000000000000000000000000000cafe"))
                    .balance(Word::from(10u64.pow(19)));
                accs[1].account(&caller);
                accs[2].account(&callee);
            },
            |mut txs, accs| {
                txs[0]
                    .from(accs[0].address)
                    .to(accs[1].address)
                    .gas(100000.into())
                    // Set a non-zero value could test if DELEGATECALL use value of current call.
                    .value(1000.into());
            },
            |block, _tx| block.number(0xcafeu64),
        )
        .unwrap();

        CircuitTestBuilder::new_from_test_ctx(ctx)
            .params(FixedCParams {
                max_rws: 500,
                ..Default::default()
            })
            .run();
    }

    fn test_recursive(opcode: &OpcodeId) {
        let is_call_or_callcode = opcode == &OpcodeId::CALL || opcode == &OpcodeId::CALLCODE;
        let mut caller_bytecode = bytecode! {
            PUSH1(0)
            PUSH1(0)
            PUSH1(0)
            PUSH1(0)
        };
        if is_call_or_callcode {
            caller_bytecode.push(1, U256::zero());
        }
        caller_bytecode.append(&bytecode! {
            PUSH32(Address::repeat_byte(0xff).to_word())
            PUSH2(if is_call_or_callcode {10000} else {10032})
            .write_op(*opcode)
            STOP
        });
        // The following bytecode calls itself recursively if gas_left is greater than
        // 100, and halts with REVERT if gas_left is odd, otherwise just halts
        // with STOP.
        let mut callee_bytecode = bytecode! {
            GAS
            PUSH1(100)
            GT
            PUSH1(if is_call_or_callcode {43} else {41}) // jump dest
            JUMPI

            PUSH1(0)
            PUSH1(0)
            PUSH1(0)
            PUSH1(0)
        };

        if is_call_or_callcode {
            callee_bytecode.push(1, U256::zero());
        }

        callee_bytecode.append(&bytecode! {
            PUSH20(Address::repeat_byte(0xff).to_word())
            PUSH1(if is_call_or_callcode {132} else {129}) // gas
            GAS
            SUB
            .write_op(*opcode)

            JUMPDEST // 41 for static_call, 43 for call
            GAS
            PUSH1(1)
            AND
            PUSH1(if is_call_or_callcode {56} else {54})
            JUMPI

            PUSH1(0)
            PUSH1(0)
            REVERT

            // 56 or 54 for call or static_call
            JUMPDEST
            STOP
        });
        test_ok(
            Account::mock_100_ether(caller_bytecode),
            callee(callee_bytecode),
        );
    }

    #[test]
    fn test_depth() {
        let callee_code = bytecode! {
            PUSH1(0x00)
            PUSH1(0x00)
            PUSH1(0x00)
            PUSH1(0x00)
            PUSH1(0x00)
            ADDRESS
            PUSH2(0xffff)
            GAS
            SUB
            CALL
            PUSH1(0x01)
            SUB
        };

        let ctx = TestContext::<2, 1>::new(
            None,
            account_0_code_account_1_no_code(callee_code),
            |mut txs, accs| {
                txs[0]
                    .to(accs[0].address)
                    .from(accs[1].address)
                    .gas(word!("0x2386F26FC10000"));
            },
            |block, _tx| block.number(0xcafeu64),
        )
        .unwrap();

        CircuitTestBuilder::new_from_test_ctx(ctx)
            .params(FixedCParams {
                max_rws: 300000,
                ..Default::default()
            })
            .run();
    }
}
