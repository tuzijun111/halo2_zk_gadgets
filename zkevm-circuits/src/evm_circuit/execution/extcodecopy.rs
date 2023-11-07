use crate::{
    evm_circuit::{
        param::{N_BYTES_ACCOUNT_ADDRESS, N_BYTES_MEMORY_WORD_SIZE, N_BYTES_U64},
        step::ExecutionState,
        util::{
            common_gadget::{SameContextGadget, WordByteCapGadget},
            constraint_builder::{
                ConstrainBuilderCommon, EVMConstraintBuilder, ReversionInfo, StepStateTransition,
                Transition,
            },
            math_gadget::IsZeroWordGadget,
            memory_gadget::{
                CommonMemoryAddressGadget, MemoryAddressGadget, MemoryCopierGasGadget,
                MemoryExpansionGadget,
            },
            not, select, AccountAddress, CachedRegion, Cell,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    table::{AccountFieldTag, CallContextFieldTag},
    util::word::{Word, Word32Cell, WordExpr},
};
use bus_mapping::circuit_input_builder::CopyDataType;
use eth_types::{evm_types::GasCost, Field, ToScalar};
use gadgets::util::Expr;
use halo2_proofs::{
    circuit::Value,
    plonk::{Error, Expression},
};

use super::ExecutionGadget;

#[derive(Clone, Debug)]
pub(crate) struct ExtcodecopyGadget<F> {
    same_context: SameContextGadget<F>,
    external_address_word: Word32Cell<F>,
    memory_address: MemoryAddressGadget<F>,
    code_offset: WordByteCapGadget<F, N_BYTES_U64>,
    tx_id: Cell<F>,
    reversion_info: ReversionInfo<F>,
    is_warm: Cell<F>,
    code_hash: Word32Cell<F>,
    not_exists: IsZeroWordGadget<F, Word<Expression<F>>>,
    code_size: Cell<F>,
    copy_rwc_inc: Cell<F>,
    memory_expansion: MemoryExpansionGadget<F, 1, N_BYTES_MEMORY_WORD_SIZE>,
    memory_copier_gas: MemoryCopierGasGadget<F, { GasCost::COPY }>,
}

impl<F: Field> ExecutionGadget<F> for ExtcodecopyGadget<F> {
    const NAME: &'static str = "EXTCODECOPY";

    const EXECUTION_STATE: ExecutionState = ExecutionState::EXTCODECOPY;

    fn configure(cb: &mut EVMConstraintBuilder<F>) -> Self {
        let opcode = cb.query_cell();

        let external_address_word = cb.query_word32();
        let external_address = AccountAddress::new(
            external_address_word.limbs[..N_BYTES_ACCOUNT_ADDRESS]
                .to_vec()
                .try_into()
                .unwrap(),
        );

        let code_size = cb.query_cell();

        let memory_length = cb.query_memory_address();
        let memory_offset = cb.query_word_unchecked();
        let code_offset = WordByteCapGadget::construct(cb, code_size.expr());

        cb.stack_pop(external_address_word.to_word());
        cb.stack_pop(memory_offset.to_word());
        cb.stack_pop(code_offset.original_word().to_word());
        cb.stack_pop(memory_length.to_word());

        let tx_id = cb.call_context(None, CallContextFieldTag::TxId);
        let mut reversion_info = cb.reversion_info_read(None);
        let is_warm = cb.query_bool();
        cb.account_access_list_write_unchecked(
            tx_id.expr(),
            external_address.to_word(),
            1.expr(),
            is_warm.expr(),
            Some(&mut reversion_info),
        );

        let code_hash = cb.query_word32();
        cb.account_read(
            external_address.to_word(),
            AccountFieldTag::CodeHash,
            code_hash.to_word(),
        );
        let not_exists = IsZeroWordGadget::construct(cb, &code_hash.to_word());
        let exists = not::expr(not_exists.expr());
        cb.condition(exists.expr(), |cb| {
            cb.bytecode_length(code_hash.to_word(), code_size.expr());
        });
        cb.condition(not_exists.expr(), |cb| {
            cb.require_zero("code_size is zero when non_exists", code_size.expr());
        });

        let memory_address = MemoryAddressGadget::construct(cb, memory_offset, memory_length);
        let memory_expansion = MemoryExpansionGadget::construct(cb, [memory_address.address()]);
        let memory_copier_gas = MemoryCopierGasGadget::construct(
            cb,
            memory_address.length(),
            memory_expansion.gas_cost(),
        );
        let gas_cost = memory_copier_gas.gas_cost()
            + select::expr(
                is_warm.expr(),
                GasCost::WARM_ACCESS.expr(),
                GasCost::COLD_ACCOUNT_ACCESS.expr(),
            );

        let copy_rwc_inc = cb.query_cell();
        cb.condition(memory_address.has_length(), |cb| {
            // Set source start to the minimun value of code offset and code size.
            let src_addr = select::expr(
                code_offset.lt_cap(),
                code_offset.valid_value(),
                code_size.expr(),
            );

            cb.copy_table_lookup(
                code_hash.to_word(),
                CopyDataType::Bytecode.expr(),
                Word::from_lo_unchecked(cb.curr.state.call_id.expr()),
                CopyDataType::Memory.expr(),
                src_addr,
                code_size.expr(),
                memory_address.offset(),
                memory_address.length(),
                0.expr(),
                copy_rwc_inc.expr(),
            );
        });
        cb.condition(not::expr(memory_address.has_length()), |cb| {
            cb.require_zero(
                "if no bytes to copy, copy table rwc inc == 0",
                copy_rwc_inc.expr(),
            );
        });

        let step_state_transition = StepStateTransition {
            rw_counter: Transition::Delta(cb.rw_counter_offset()),
            program_counter: Transition::Delta(1.expr()),
            stack_pointer: Transition::Delta(4.expr()),
            memory_word_size: Transition::To(memory_expansion.next_memory_word_size()),
            gas_left: Transition::Delta(-gas_cost),
            reversible_write_counter: Transition::Delta(1.expr()),
            ..Default::default()
        };
        let same_context = SameContextGadget::construct(cb, opcode, step_state_transition);

        Self {
            same_context,
            external_address_word,
            memory_address,
            code_offset,
            tx_id,
            is_warm,
            reversion_info,
            code_hash,
            not_exists,
            code_size,
            copy_rwc_inc,
            memory_expansion,
            memory_copier_gas,
        }
    }

    fn assign_exec_step(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        block: &Block<F>,
        transaction: &Transaction,
        call: &Call,
        step: &ExecStep,
    ) -> Result<(), Error> {
        self.same_context.assign_exec_step(region, offset, step)?;

        let [external_address, memory_offset, code_offset, memory_length] =
            [0, 1, 2, 3].map(|idx| block.get_rws(step, idx).stack_value());
        self.external_address_word
            .assign_u256(region, offset, external_address)?;
        let memory_address =
            self.memory_address
                .assign(region, offset, memory_offset, memory_length)?;

        self.tx_id
            .assign(region, offset, Value::known(F::from(transaction.id)))?;
        self.reversion_info.assign(
            region,
            offset,
            call.rw_counter_end_of_reversion,
            call.is_persistent,
        )?;

        let (_, is_warm) = block.get_rws(step, 7).tx_access_list_value_pair();
        self.is_warm
            .assign(region, offset, Value::known(F::from(is_warm as u64)))?;

        let code_hash = block.get_rws(step, 8).account_codehash_pair().0;
        self.code_hash.assign_u256(region, offset, code_hash)?;
        self.not_exists.assign_u256(region, offset, code_hash)?;

        let code_size = if code_hash.is_zero() {
            0
        } else {
            block
                .bytecodes
                .get_from_u256(&code_hash)
                .expect("could not find external bytecode")
                .codesize() as u64
        };
        self.code_size
            .assign(region, offset, Value::known(F::from(code_size)))?;

        self.code_offset
            .assign(region, offset, code_offset, F::from(code_size))?;

        self.copy_rwc_inc.assign(
            region,
            offset,
            Value::known(
                memory_length
                    .to_scalar()
                    .expect("unexpected U256 -> Scalar conversion failure"),
            ),
        )?;

        let (_, memory_expansion_gas_cost) = self.memory_expansion.assign(
            region,
            offset,
            step.memory_word_size(),
            [memory_address],
        )?;

        self.memory_copier_gas.assign(
            region,
            offset,
            memory_length.as_u64(),
            memory_expansion_gas_cost,
        )?;

        Ok(())
    }
}

#[cfg(test)]
mod test {
    use crate::{evm_circuit::test::rand_bytes_array, test_util::CircuitTestBuilder};
    use eth_types::{
        address, bytecode, geth_types::Account, Address, Bytecode, Bytes, ToWord, Word,
    };
    use lazy_static::lazy_static;
    use mock::TestContext;

    lazy_static! {
        static ref EXTERNAL_ADDRESS: Address =
            address!("0xaabbccddee000000000000000000000000000000");
    }

    fn test_ok(
        external_account: Option<Account>,
        code_offset: Word,
        memory_offset: Word,
        length: usize,
        is_warm: bool,
    ) {
        let external_address = external_account
            .as_ref()
            .map(|a| a.address)
            .unwrap_or(*EXTERNAL_ADDRESS);

        let mut code = Bytecode::default();

        if is_warm {
            code.append(&bytecode! {
                PUSH20(external_address.to_word())
                EXTCODEHASH
                POP
            });
        }
        code.append(&bytecode! {
            PUSH32(length)
            PUSH32(code_offset)
            PUSH32(memory_offset)
            PUSH20(external_address.to_word())
            #[start]
            EXTCODECOPY
            STOP
        });

        let ctx = TestContext::<3, 1>::new(
            None,
            |accs| {
                accs[0]
                    .address(address!("0x000000000000000000000000000000000000cafe"))
                    .code(code);
                accs[1]
                    .address(address!("0x0000000000000000000000000000000000000010"))
                    .balance(Word::from(1u64 << 20));
                accs[2].address(external_address);
                if let Some(external_account) = external_account {
                    accs[2].account(&external_account);
                }
            },
            |mut txs, accs| {
                txs[0]
                    .to(accs[0].address)
                    .from(accs[1].address)
                    .gas(1_000_000.into());
            },
            |block, _tx| block.number(0x1111111),
        )
        .unwrap();

        CircuitTestBuilder::new_from_test_ctx(ctx).run();
    }

    #[test]
    fn extcodecopy_empty_account() {
        test_ok(None, Word::zero(), Word::zero(), 0x36, true); // warm account
        test_ok(None, Word::zero(), Word::zero(), 0x36, false); // cold account
    }

    #[test]
    fn extcodecopy_nonempty_account() {
        test_ok(
            Some(Account {
                address: *EXTERNAL_ADDRESS,
                code: Bytes::from([10, 40]),
                ..Default::default()
            }),
            Word::zero(),
            Word::zero(),
            0x36,
            true,
        ); // warm account

        test_ok(
            Some(Account {
                address: *EXTERNAL_ADDRESS,
                code: Bytes::from([10, 40]),
                ..Default::default()
            }),
            Word::zero(),
            Word::zero(),
            0x36,
            false,
        ); // cold account
    }

    #[test]
    fn extcodecopy_largerthan256() {
        test_ok(
            Some(Account {
                address: *EXTERNAL_ADDRESS,
                code: Bytes::from(rand_bytes_array::<256>()),
                ..Default::default()
            }),
            Word::zero(),
            Word::zero(),
            0x36,
            true,
        );
        test_ok(
            Some(Account {
                address: *EXTERNAL_ADDRESS,
                code: Bytes::from(rand_bytes_array::<256>()),
                ..Default::default()
            }),
            Word::zero(),
            Word::zero(),
            0x36,
            false,
        );
    }

    #[test]
    fn extcodecopy_outofbound() {
        test_ok(
            Some(Account {
                address: *EXTERNAL_ADDRESS,
                code: Bytes::from(rand_bytes_array::<64>()),
                ..Default::default()
            }),
            0x20.into(),
            Word::zero(),
            0x104,
            true,
        );
        test_ok(
            Some(Account {
                address: *EXTERNAL_ADDRESS,
                code: Bytes::from(rand_bytes_array::<64>()),
                ..Default::default()
            }),
            0x20.into(),
            Word::zero(),
            0x104,
            false,
        );
    }

    #[test]
    fn extcodecopy_code_offset_overflow() {
        test_ok(
            Some(Account {
                address: *EXTERNAL_ADDRESS,
                code: Bytes::from(rand_bytes_array::<256>()),
                ..Default::default()
            }),
            Word::MAX,
            Word::zero(),
            0x36,
            true,
        );
        test_ok(
            Some(Account {
                address: *EXTERNAL_ADDRESS,
                code: Bytes::from(rand_bytes_array::<256>()),
                ..Default::default()
            }),
            Word::MAX,
            Word::zero(),
            0x36,
            false,
        );
    }

    #[test]
    fn extcodecopy_overflow_memory_offset_and_zero_length() {
        test_ok(
            Some(Account {
                address: *EXTERNAL_ADDRESS,
                code: Bytes::from(rand_bytes_array::<256>()),
                ..Default::default()
            }),
            0x20.into(),
            Word::MAX,
            0,
            true,
        );
        test_ok(
            Some(Account {
                address: *EXTERNAL_ADDRESS,
                code: Bytes::from(rand_bytes_array::<256>()),
                ..Default::default()
            }),
            0x20.into(),
            Word::MAX,
            0,
            true,
        );
    }
}
