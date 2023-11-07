use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        param::{N_BYTES_GAS, N_BYTES_U64},
        step::ExecutionState,
        util::{
            common_gadget::CommonErrorGadget,
            constraint_builder::{ConstrainBuilderCommon, EVMConstraintBuilder},
            math_gadget::LtGadget,
            memory_gadget::{CommonMemoryAddressGadget, MemoryAddressGadget},
            CachedRegion, Cell,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    table::CallContextFieldTag,
    util::{word::WordExpr, Expr},
};

use eth_types::{
    evm_types::{GasCost, OpcodeId},
    Field,
};

use halo2_proofs::{circuit::Value, plonk::Error};

const MAXCODESIZE: u64 = 0x6000u64;

/// Gadget for code store oog and max code size exceed
#[derive(Clone, Debug)]
pub(crate) struct ErrorCodeStoreGadget<F> {
    opcode: Cell<F>,
    memory_address: MemoryAddressGadget<F>,
    // check not static call
    is_static: Cell<F>,
    // check for CodeStoreOutOfGas error
    code_store_gas_insufficient: LtGadget<F, N_BYTES_GAS>,
    // check for MaxCodeSizeExceeded error
    max_code_size_exceed: LtGadget<F, N_BYTES_U64>,
    common_error_gadget: CommonErrorGadget<F>,
}

impl<F: Field> ExecutionGadget<F> for ErrorCodeStoreGadget<F> {
    const NAME: &'static str = "ErrorCodeStore";

    const EXECUTION_STATE: ExecutionState = ExecutionState::ErrorCodeStore;

    fn configure(cb: &mut EVMConstraintBuilder<F>) -> Self {
        let opcode = cb.query_cell();
        cb.require_equal(
            "ErrorCodeStore checking at RETURN in create context ",
            opcode.expr(),
            OpcodeId::RETURN.expr(),
        );

        let offset = cb.query_word_unchecked();
        let length = cb.query_memory_address();
        cb.stack_pop(offset.to_word());
        cb.stack_pop(length.to_word());
        let memory_address = MemoryAddressGadget::construct(cb, offset, length);
        // constrain not in static call
        let is_static = cb.call_context(None, CallContextFieldTag::IsStatic);
        cb.require_zero("is_static is false in ErrorCodeStore", is_static.expr());

        cb.require_true("is_create is true", cb.curr.state.is_create.expr());

        // constrain code store gas > gas left, that is GasCost::CODE_DEPOSIT_BYTE_COST
        // * length > gas left
        let code_store_gas_insufficient = LtGadget::construct(
            cb,
            cb.curr.state.gas_left.expr(),
            GasCost::CODE_DEPOSIT_BYTE_COST.expr() * memory_address.length(),
        );

        // constrain code size > MAXCODESIZE
        let max_code_size_exceed =
            LtGadget::construct(cb, MAXCODESIZE.expr(), memory_address.length());

        // check must be one of CodeStoreOutOfGas or MaxCodeSizeExceeded
        cb.require_in_set(
            "CodeStoreOutOfGas or MaxCodeSizeExceeded",
            code_store_gas_insufficient.expr() + max_code_size_exceed.expr(),
            vec![1.expr(), 2.expr()],
        );

        let common_error_gadget =
            CommonErrorGadget::construct(cb, opcode.expr(), cb.rw_counter_offset());

        Self {
            opcode,
            memory_address,
            is_static,
            code_store_gas_insufficient,
            max_code_size_exceed,
            common_error_gadget,
        }
    }

    fn assign_exec_step(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        block: &Block<F>,
        _tx: &Transaction,
        call: &Call,
        step: &ExecStep,
    ) -> Result<(), Error> {
        let opcode = step.opcode().unwrap();
        self.opcode
            .assign(region, offset, Value::known(F::from(opcode.as_u64())))?;
        let [memory_offset, length] = [0, 1].map(|i| block.get_rws(step, i).stack_value());
        self.memory_address
            .assign(region, offset, memory_offset, length)?;

        self.is_static
            .assign(region, offset, Value::known(F::from(call.is_static as u64)))?;
        self.code_store_gas_insufficient.assign(
            region,
            offset,
            F::from(step.gas_left),
            F::from(GasCost::CODE_DEPOSIT_BYTE_COST * length.as_u64()),
        )?;

        self.max_code_size_exceed.assign(
            region,
            offset,
            F::from(MAXCODESIZE),
            F::from(length.as_u64()),
        )?;

        self.common_error_gadget
            .assign(region, offset, block, call, step, 5)?;
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use bus_mapping::circuit_input_builder::FixedCParams;
    use eth_types::{
        address, bytecode, evm_types::OpcodeId, geth_types::Account, Address, Bytecode, Word,
    };

    use lazy_static::lazy_static;
    use mock::{eth, TestContext, MOCK_ACCOUNTS};

    use crate::test_util::CircuitTestBuilder;

    lazy_static! {
        static ref CALLER_ADDRESS: Address = address!("0x00bbccddee000000000000000000000000002400");
    }

    const MAXCODESIZE: u64 = 0x6000u64;

    fn run_test_circuits(ctx: TestContext<2, 1>) {
        CircuitTestBuilder::new_from_test_ctx(ctx)
            .params(FixedCParams {
                max_rws: 4500,
                ..FixedCParams::default()
            })
            .run();
    }

    fn initialization_bytecode(is_oog: bool) -> Bytecode {
        let memory_bytes = [0x60; 10];
        let memory_value = Word::from_big_endian(&memory_bytes);
        let code_len = if is_oog { 5 } else { MAXCODESIZE + 1 };

        let mut code = bytecode! {
            PUSH10(memory_value)
            PUSH32(code_len)
            MSTORE
            PUSH2(code_len) // length to copy
            PUSH2(32u64 - u64::try_from(memory_bytes.len()).unwrap()) // offset
        };
        code.write_op(OpcodeId::RETURN);

        code
    }

    fn creator_bytecode(initialization_bytecode: Bytecode, is_create2: bool) -> Bytecode {
        let initialization_bytes = initialization_bytecode.code();
        let mut code = Bytecode::default();

        // construct maxcodesize + 1 memory bytes
        let code_creator: Vec<u8> = initialization_bytes
            .to_vec()
            .iter()
            .cloned()
            .chain(0u8..((32 - initialization_bytes.len() % 32) as u8))
            .collect();
        for (index, word) in code_creator.chunks(32).enumerate() {
            code.push(32, Word::from_big_endian(word));
            code.push(32, Word::from(index * 32));
            code.write_op(OpcodeId::MSTORE);
        }

        if is_create2 {
            code.append(&bytecode! {PUSH1(45)}); // salt;
        }
        code.append(&bytecode! {
            PUSH32(initialization_bytes.len()) // size
            PUSH2(0x00) // offset
            PUSH2(23414) // value
        });
        code.write_op(if is_create2 {
            OpcodeId::CREATE2
        } else {
            OpcodeId::CREATE
        });
        code.append(&bytecode! {
            PUSH1(0)
            PUSH1(0)
            RETURN
        });

        code
    }

    fn test_context(caller: Account, is_oog: bool) -> TestContext<2, 1> {
        TestContext::new(
            None,
            |accs| {
                accs[0]
                    .address(address!("0x000000000000000000000000000000000000cafe"))
                    .balance(eth(10));
                accs[1].account(&caller);
            },
            |mut txs, accs| {
                txs[0]
                    .from(accs[0].address)
                    .to(accs[1].address)
                    .gas(if is_oog {
                        53800u64.into()
                    } else {
                        103800u64.into()
                    });
            },
            |block, _| block,
        )
        .unwrap()
    }

    #[test]
    fn test_create_codestore_oog() {
        for is_create2 in [false, true] {
            let initialization_code = initialization_bytecode(true);
            let root_code = creator_bytecode(initialization_code, is_create2);
            let caller = Account {
                address: *CALLER_ADDRESS,
                code: root_code.into(),
                nonce: 1u64.into(),
                balance: eth(10),
                ..Default::default()
            };
            run_test_circuits(test_context(caller, true));
        }
    }

    #[test]
    fn test_create_max_code_size_exceed() {
        for is_create2 in [false, true] {
            let initialization_code = initialization_bytecode(false);
            let root_code = creator_bytecode(initialization_code, is_create2);
            let caller = Account {
                address: *CALLER_ADDRESS,
                code: root_code.into(),
                nonce: 1u64.into(),
                balance: eth(10),
                ..Default::default()
            };
            run_test_circuits(test_context(caller, false));
        }
    }

    #[test]
    fn tx_deploy_code_store_oog() {
        let code = initialization_bytecode(true);

        let ctx = TestContext::<1, 1>::new(
            None,
            |accs| {
                accs[0].address(MOCK_ACCOUNTS[0]).balance(eth(20));
            },
            |mut txs, _accs| {
                txs[0]
                    .from(MOCK_ACCOUNTS[0])
                    .gas(538006u64.into())
                    .value(eth(2))
                    .input(code.into());
            },
            |block, _tx| block.number(0xcafeu64),
        )
        .unwrap();

        CircuitTestBuilder::new_from_test_ctx(ctx).run();
    }

    #[test]
    fn tx_deploy_max_code_size_exceed() {
        let code = initialization_bytecode(false);

        let ctx = TestContext::<1, 1>::new(
            None,
            |accs| {
                accs[0].address(MOCK_ACCOUNTS[0]).balance(eth(20));
            },
            |mut txs, _accs| {
                txs[0]
                    .from(MOCK_ACCOUNTS[0])
                    .gas(58000u64.into())
                    .value(eth(2))
                    .input(code.into());
            },
            |block, _tx| block.number(0xcafeu64),
        )
        .unwrap();

        CircuitTestBuilder::new_from_test_ctx(ctx).run();
    }
}
