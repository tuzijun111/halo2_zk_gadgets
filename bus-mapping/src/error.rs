//! Error module for the bus-mapping crate

use core::fmt::{Display, Formatter, Result as FmtResult};
use eth_types::{evm_types::OpcodeId, Address, GethExecStep, Word, H256};
use ethers_providers::ProviderError;
use std::error::Error as StdError;

use crate::geth_errors::{
    GETH_ERR_GAS_UINT_OVERFLOW, GETH_ERR_OUT_OF_GAS, GETH_ERR_STACK_OVERFLOW,
    GETH_ERR_STACK_UNDERFLOW,
};

/// Error type for any BusMapping related failure.
#[derive(Debug)]
pub enum Error {
    /// Serde de/serialization error.
    SerdeError(serde_json::error::Error),
    /// JSON-RPC related error.
    JSONRpcError(ProviderError),
    /// OpcodeId is not a call type.
    OpcodeIdNotCallType,
    /// Account not found in the StateDB
    AccountNotFound(Address),
    /// Storage key not found in the StateDB
    StorageKeyNotFound(Address, Word),
    /// Address not found in the CodeDB,
    AddressNotFound(Address),
    /// Code not found in the CodeDB
    CodeNotFound(H256),
    /// Unable to figure out error at a [`GethExecStep`]
    UnexpectedExecStepError(&'static str, Box<GethExecStep>),
    /// Invalid [`eth_types::GethExecTrace`] due to an invalid/unexpected value
    /// in it.
    InvalidGethExecTrace(&'static str),
    /// Invalid [`GethExecStep`] due to an invalid/unexpected value in it.
    InvalidGethExecStep(&'static str, Box<GethExecStep>),
    /// Eth type related error.
    EthTypeError(eth_types::Error),
    /// EVM Execution error
    ExecutionError(ExecError),
    /// Internal Code error
    InternalError(&'static str),
    /// Rw number overflow
    RwsNotEnough(usize, usize),
}

impl From<eth_types::Error> for Error {
    fn from(err: eth_types::Error) -> Self {
        Error::EthTypeError(err)
    }
}

impl From<ProviderError> for Error {
    fn from(err: ProviderError) -> Self {
        Error::JSONRpcError(err)
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "{:?}", self)
    }
}

impl StdError for Error {}

/// Out of Gas errors by opcode
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum OogError {
    /// Out of Gas for opcodes which have non-zero constant gas cost
    Constant,
    /// Out of Gas for MLOAD, MSTORE, MSTORE8, which have static memory
    /// expansion gas cost
    StaticMemoryExpansion,
    /// Out of Gas for CREATE, RETURN, REVERT, which have dynamic memory
    /// expansion gas cost
    DynamicMemoryExpansion,
    /// Out of Gas for CALLDATACOPY, CODECOPY, EXTCODECOPY, RETURNDATACOPY,
    /// which copy a specified chunk of memory
    MemoryCopy,
    /// Out of Gas for BALANCE, EXTCODESIZE, EXTCODEHASH, which possibly touch
    /// an extra account
    AccountAccess,
    /// Out of Gas for RETURN which has code storing gas cost when it's is
    /// creation
    CodeStore,
    /// Out of Gas for LOG0, LOG1, LOG2, LOG3, LOG4
    Log,
    /// Out of Gas for EXP
    Exp,
    /// Out of Gas for SHA3
    Sha3,
    /// Out of Gas for SLOAD and SSTORE
    SloadSstore,
    /// Out of Gas for CALL, CALLCODE, DELEGATECALL and STATICCALL
    Call,
    /// Out of Gas for CREATE and CREATE2
    Create,
    /// Out of Gas for SELFDESTRUCT
    SelfDestruct,
}

// Given OpCodeId, returns correponding OogError.
impl From<&OpcodeId> for OogError {
    fn from(op: &OpcodeId) -> Self {
        match op {
            OpcodeId::MLOAD | OpcodeId::MSTORE | OpcodeId::MSTORE8 => {
                OogError::StaticMemoryExpansion
            }
            OpcodeId::RETURN | OpcodeId::REVERT => OogError::DynamicMemoryExpansion,
            OpcodeId::CALLDATACOPY
            | OpcodeId::CODECOPY
            | OpcodeId::EXTCODECOPY
            | OpcodeId::RETURNDATACOPY => OogError::MemoryCopy,
            OpcodeId::BALANCE | OpcodeId::EXTCODESIZE | OpcodeId::EXTCODEHASH => {
                OogError::AccountAccess
            }
            OpcodeId::LOG0 | OpcodeId::LOG1 | OpcodeId::LOG2 | OpcodeId::LOG3 | OpcodeId::LOG4 => {
                OogError::Log
            }
            OpcodeId::EXP => OogError::Exp,
            OpcodeId::SHA3 => OogError::Sha3,
            OpcodeId::CALL | OpcodeId::CALLCODE | OpcodeId::DELEGATECALL | OpcodeId::STATICCALL => {
                OogError::Call
            }
            OpcodeId::SLOAD | OpcodeId::SSTORE => OogError::SloadSstore,
            OpcodeId::CREATE | OpcodeId::CREATE2 => OogError::Create,
            OpcodeId::SELFDESTRUCT => OogError::SelfDestruct,
            _ => OogError::Constant,
        }
    }
}

/// Insufficient balance errors by opcode/state.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InsufficientBalanceError {
    /// Insufficient balance during CALL/CALLCODE opcode.
    Call,
    /// Insufficient balance during CREATE opcode.
    Create,
    /// Insufficient balance during CREATE2 opcode.
    Create2,
}

/// Nonce uint overflow errors by opcode/state.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NonceUintOverflowError {
    /// Nonce uint overflow during CREATE opcode.
    Create,
    /// Nonce uint overflow during CREATE2 opcode.
    Create2,
}

/// Call depth errors by opcode/state.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DepthError {
    /// Call depth errors in CALL/CALLCODE opcode.
    Call,
    /// Call depth errors in CREATE opcode.
    Create,
    /// Call depth errors in CREATE2 opcode.
    Create2,
}

/// EVM Execution Error
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExecError {
    /// Invalid Opcode
    InvalidOpcode,
    /// For opcodes who push more than pop
    StackOverflow,
    /// For opcodes which pop, DUP and SWAP, which peek deeper element directly
    StackUnderflow,
    /// Out of Gas
    OutOfGas(OogError),
    /// For SSTORE, LOG0, LOG1, LOG2, LOG3, LOG4, CREATE, CALL, CREATE2,
    /// SELFDESTRUCT
    WriteProtection,
    /// For CALL, CALLCODE, DELEGATECALL, STATICCALL, CREATE, CREATE2
    Depth(DepthError),
    /// For CALL, CALLCODE, CREATE, CREATE2
    InsufficientBalance(InsufficientBalanceError),
    /// For CREATE2
    ContractAddressCollision,
    /// contract must not begin with 0xef due to EIP #3541 EVM Object Format
    /// (EOF)
    InvalidCreationCode,
    /// For JUMP, JUMPI
    InvalidJump,
    /// For RETURNDATACOPY
    ReturnDataOutOfBounds,
    /// For RETURN in a CREATE, CREATE2
    CodeStoreOutOfGas,
    /// For RETURN in a CREATE, CREATE2
    MaxCodeSizeExceeded,
    /// For CREATE, CREATE2
    NonceUintOverflow(NonceUintOverflowError),
}

// Returns a GethExecStep's error if present, else return the empty error.
impl TryFrom<&GethExecStep> for ExecError {
    type Error = ();

    fn try_from(step: &GethExecStep) -> Result<Self, Self::Error> {
        Ok(match step.error.as_ref().ok_or(())?.as_str() {
            GETH_ERR_OUT_OF_GAS | GETH_ERR_GAS_UINT_OVERFLOW => {
                // NOTE: We report a GasUintOverflow error as an OutOfGas error
                let oog_err = OogError::from(&step.op);
                ExecError::OutOfGas(oog_err)
            }
            error => {
                if error.starts_with(GETH_ERR_STACK_OVERFLOW) {
                    ExecError::StackOverflow
                } else if error.starts_with(GETH_ERR_STACK_UNDERFLOW) {
                    ExecError::StackUnderflow
                } else {
                    panic!("Unknown GethExecStep.error: {}", error);
                }
            }
        })
    }
}
