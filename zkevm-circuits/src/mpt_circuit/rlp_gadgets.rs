use crate::{
    _cb, circuit,
    circuit_tools::{
        cached_region::CachedRegion,
        cell_manager::Cell,
        constraint_builder::{ConstraintBuilder, RLCable, RLCableValue},
    },
    evm_circuit::util::from_bytes,
    matchw,
    mpt_circuit::{
        helpers::FIXED,
        param::{RLP_LIST_LONG, RLP_LIST_SHORT, RLP_SHORT},
        FixedTableTag,
    },
    util::{word, Expr},
};
use eth_types::Field;
use gadgets::util::{not, pow, Scalar};
use halo2_proofs::plonk::{Error, Expression, VirtualCells};

use super::{
    helpers::MPTConstraintBuilder,
    param::{KEY_PREFIX_ODD, KEY_TERMINAL_PREFIX_ODD, RLP_LONG},
};

// Decodes the first byte of an RLP data stream to return (is_list, is_short, is_long, is_very_long)
pub(crate) fn decode_rlp(byte: u8) -> (bool, bool, bool, bool) {
    if byte < RLP_LIST_SHORT {
        const RLP_SHORT_INCLUSIVE: u8 = RLP_SHORT - 1;
        const RLP_LONG_EXCLUSIVE: u8 = RLP_LONG + 1;
        const RLP_VALUE_MAX: u8 = RLP_LIST_SHORT - 1;

        let mut is_short = false;
        let mut is_long = false;
        let mut is_very_long = false;
        match byte {
            0..=RLP_SHORT_INCLUSIVE => is_short = true,
            RLP_SHORT..=RLP_LONG => is_long = true,
            RLP_LONG_EXCLUSIVE..=RLP_VALUE_MAX => is_very_long = true,
            _ => unreachable!(),
        }
        (false, is_short, is_long, is_very_long)
    } else {
        const RLP_LIST_LONG_1: u8 = RLP_LIST_LONG + 1;
        const RLP_LIST_LONG_2: u8 = RLP_LIST_LONG + 2;

        let mut is_short = false;
        let mut is_long = false;
        let mut is_very_long = false;
        match byte {
            RLP_LIST_SHORT..=RLP_LIST_LONG => is_short = true,
            RLP_LIST_LONG_1 => is_long = true,
            RLP_LIST_LONG_2 => is_very_long = true,
            _ => (),
        }
        (true, is_short, is_long, is_very_long)
    }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct RLPListGadget<F> {
    pub(crate) is_short: Cell<F>,
    pub(crate) is_long: Cell<F>,
    pub(crate) is_very_long: Cell<F>,
    pub(crate) is_string: Cell<F>,
    pub(crate) bytes: Vec<Expression<F>>,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct RLPListWitness {
    pub(crate) is_short: bool,
    pub(crate) is_long: bool,
    pub(crate) is_very_long: bool,
    pub(crate) is_string: bool,
    pub(crate) bytes: Vec<u8>,
}

impl<F: Field> RLPListGadget<F> {
    pub(crate) fn construct(cb: &mut MPTConstraintBuilder<F>, bytes: &[Expression<F>]) -> Self {
        circuit!([meta, cb], {
            let is_short = cb.query_cell();
            let is_long = cb.query_cell();
            let is_very_long = cb.query_cell();
            let is_string = cb.query_cell();

            require!(
                (
                    FixedTableTag::RLP.expr(),
                    bytes[0].expr(),
                    not!(is_string),
                    is_short.expr(),
                    is_long.expr(),
                    is_very_long.expr()
                ) =>> @FIXED
            );

            RLPListGadget {
                is_short,
                is_long,
                is_very_long,
                is_string,
                bytes: bytes.to_vec(),
            }
        })
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        bytes: &[u8],
    ) -> Result<RLPListWitness, Error> {
        let (is_list, is_short, is_long, is_very_long) = decode_rlp(bytes[0]);
        let is_string = !is_list;

        self.is_short.assign(region, offset, is_short.scalar())?;
        self.is_long.assign(region, offset, is_long.scalar())?;
        self.is_very_long
            .assign(region, offset, is_very_long.scalar())?;
        self.is_string.assign(region, offset, is_string.scalar())?;

        Ok(RLPListWitness {
            is_short,
            is_long,
            is_very_long,
            is_string,
            bytes: bytes.to_vec(),
        })
    }

    pub(crate) fn is_list(&self) -> Expression<F> {
        not::expr(self.is_string.expr())
    }

    pub(crate) fn is_list_at(&self, meta: &mut VirtualCells<F>, rot: usize) -> Expression<F> {
        not::expr(self.is_string.rot(meta, rot))
    }

    // Single RLP byte, length at most 55 bytes
    pub(crate) fn is_short(&self) -> Expression<F> {
        self.is_short.expr()
    }

    // RLP byte followed by the length in 1 byte, followed by the length
    pub(crate) fn is_long(&self) -> Expression<F> {
        self.is_long.expr()
    }

    pub(crate) fn is_long_at(&self, meta: &mut VirtualCells<F>, rot: usize) -> Expression<F> {
        self.is_long.rot(meta, rot)
    }

    // RLP byte followed by the length in 1 byte, followed by the length
    pub(crate) fn is_very_long(&self) -> Expression<F> {
        self.is_very_long.expr()
    }

    /// Number of RLP bytes
    pub(crate) fn num_rlp_bytes(&self) -> Expression<F> {
        circuit!([meta, _cb!()], {
            matchx! {(
                self.is_short() => 1.expr(),
                self.is_long() => 2.expr(),
                self.is_very_long() => 3.expr(),
            )}
        })
    }

    /// Returns the total length of the list (including RLP bytes)
    pub(crate) fn num_bytes(&self) -> Expression<F> {
        self.num_rlp_bytes() + self.len()
    }

    /// Returns the length of the list (excluding RLP bytes)
    pub(crate) fn len(&self) -> Expression<F> {
        circuit!([meta, _cb!()], {
            matchx! {(
                self.is_short() => get_len_list_short::expr(self.bytes[0].expr()),
                self.is_long() => self.bytes[1].expr(),
                self.is_very_long() => self.bytes[1].expr() * 256.expr() + self.bytes[2].expr(),
            )}
        })
    }

    /// Returns the rlc of all the list data provided
    pub(crate) fn rlc_rlp(&self, r: &Expression<F>) -> Expression<F> {
        self.bytes.rlc(r)
    }

    /// Returns the rlc of all the list data provided
    pub(crate) fn rlc_rlp_rev(&self, r: &Expression<F>) -> Expression<F> {
        self.bytes.rlc_rev(r)
    }

    /// Returns the rlc of only the RLP bytes
    pub(crate) fn rlc_rlp_only(&self, r: &Expression<F>) -> (Expression<F>, Expression<F>) {
        circuit!([meta, _cb!()], {
            matchx! {(
                self.is_short() => (self.bytes[..1].rlc(r), pow::expr(r.expr(), 1)),
                self.is_long() => (self.bytes[..2].rlc(r), pow::expr(r.expr(), 2)),
                self.is_very_long() => (self.bytes[..3].rlc(r), pow::expr(r.expr(), 3)),
            )}
        })
    }

    pub(crate) fn rlc_rlp_only_rev(&self, r: &Expression<F>) -> (Expression<F>, Expression<F>) {
        circuit!([meta, _cb!()], {
            matchx! {(
                self.is_short() => (self.bytes[..1].rlc_rev(r), pow::expr(r.expr(), 1)),
                self.is_long() => (self.bytes[..2].rlc_rev(r), pow::expr(r.expr(), 2)),
                self.is_very_long() => (self.bytes[..3].rlc_rev(r), pow::expr(r.expr(), 3)),
            )}
        })
    }
}

impl RLPListWitness {
    pub(crate) fn is_list(&self) -> bool {
        !self.is_string
    }

    // Single RLP byte, length at most 55 bytes
    pub(crate) fn is_short(&self) -> bool {
        self.is_short
    }

    // RLP byte followed by the number of bytes in length, followed by the length
    pub(crate) fn is_long(&self) -> bool {
        self.is_long
    }

    // RLP byte followed by the number of bytes in length, followed by the length
    pub(crate) fn is_very_long(&self) -> bool {
        self.is_very_long
    }

    /// Number of RLP bytes
    pub(crate) fn num_rlp_bytes(&self) -> usize {
        matchw! {
            self.is_short() => 1,
            self.is_long() => 2,
            self.is_very_long() => 3,
        }
    }

    /// Returns the total length of the list (including RLP bytes)
    pub(crate) fn num_bytes(&self) -> usize {
        matchw! {
            self.is_short => get_num_bytes_list_short::value(self.bytes[0]),
            self.is_long => 2 + (self.bytes[1] as usize),
            self.is_very_long => 3 + (self.bytes[1] as usize) * 256 + (self.bytes[2] as usize),
        }
    }

    /// Returns the length of the list (excluding RLP bytes)
    pub(crate) fn len(&self) -> usize {
        matchw! {
            self.is_short() => get_len_list_short::value(self.bytes[0]),
            self.is_long() => self.bytes[1] as usize,
        }
    }

    /// Returns the rlc of the complete list value and the complete list
    /// (including RLP bytes)
    pub(crate) fn rlc_rlp<F: Field>(&self, r: F) -> F {
        self.bytes.rlc_value(r)
    }

    /// Returns the rlc of the complete list value and the complete list
    /// (including RLP bytes)
    pub(crate) fn rlc_rlp_rev<F: Field>(&self, r: F) -> F {
        self.bytes.rlc_value_rev(r)
    }

    /// Returns the rlc of the RLP bytes
    pub(crate) fn rlc_rlp_only<F: Field>(&self, r: F) -> (F, F) {
        matchw! {
            self.is_short() => (self.bytes[..1].rlc_value(r), r),
            self.is_long() => (self.bytes[..2].rlc_value(r), r*r),
            self.is_very_long() => (self.bytes[..3].rlc_value(r), r*r*r),
        }
    }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct RLPListDataGadget<F> {
    pub(crate) rlp_list_bytes: [Cell<F>; 3],
    pub(crate) rlp_list: RLPListGadget<F>,
}

impl<F: Field> RLPListDataGadget<F> {
    pub(crate) fn construct(cb: &mut MPTConstraintBuilder<F>) -> Self {
        let rlp_list_bytes = cb.query_bytes();
        let rlp_list_bytes_expr = rlp_list_bytes.iter().map(|c| c.expr()).collect::<Vec<_>>();
        RLPListDataGadget {
            rlp_list: RLPListGadget::construct(cb, &rlp_list_bytes_expr),
            rlp_list_bytes,
        }
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        list_bytes: &[u8],
    ) -> Result<RLPListWitness, Error> {
        for (cell, byte) in self.rlp_list_bytes.iter().zip(list_bytes.iter()) {
            cell.assign(region, offset, byte.scalar())?;
        }
        self.rlp_list.assign(region, offset, list_bytes)
    }

    pub(crate) fn rlc_rlp(&self, r: &Expression<F>) -> (Expression<F>, Expression<F>) {
        self.rlp_list.rlc_rlp_only(r)
    }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct RLPValueGadget<F> {
    pub(crate) is_short: Cell<F>,
    pub(crate) is_long: Cell<F>,
    pub(crate) is_very_long: Cell<F>,
    pub(crate) is_list: Cell<F>,
    pub(crate) bytes: Vec<Expression<F>>,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct RLPValueWitness {
    pub(crate) is_short: bool,
    pub(crate) is_long: bool,
    pub(crate) is_very_long: bool,
    pub(crate) is_list: bool,
    pub(crate) bytes: Vec<u8>,
}

impl<F: Field> RLPValueGadget<F> {
    pub(crate) fn construct(cb: &mut MPTConstraintBuilder<F>, bytes: &[Expression<F>]) -> Self {
        circuit!([meta, cb], {
            let is_short = cb.query_cell();
            let is_long = cb.query_cell();
            let is_very_long = cb.query_cell();
            let is_list = cb.query_cell();

            require!(
                (
                    FixedTableTag::RLP.expr(),
                    bytes[0].expr(),
                    is_list.expr(),
                    is_short.expr(),
                    is_long.expr(),
                    is_very_long.expr()
                ) =>> @FIXED
            );

            RLPValueGadget {
                is_short,
                is_long,
                is_very_long,
                is_list,
                bytes: bytes.to_vec(),
            }
        })
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        bytes: &[u8],
    ) -> Result<RLPValueWitness, Error> {
        let (is_list, is_short, is_long, is_very_long) = decode_rlp(bytes[0]);

        self.is_short.assign(region, offset, is_short.scalar())?;
        self.is_long.assign(region, offset, is_long.scalar())?;
        self.is_very_long
            .assign(region, offset, is_very_long.scalar())?;
        self.is_list.assign(region, offset, is_list.scalar())?;

        Ok(RLPValueWitness {
            is_short,
            is_long,
            is_very_long,
            is_list,
            bytes: bytes.to_vec(),
        })
    }

    // Returns true if this is indeed a string RLP
    pub(crate) fn is_string(&self) -> Expression<F> {
        not::expr(self.is_list.expr())
    }

    pub(crate) fn is_string_at(&self, meta: &mut VirtualCells<F>, rot: usize) -> Expression<F> {
        not::expr(self.is_list.rot(meta, rot))
    }

    // Single RLP byte containing the byte value
    pub(crate) fn is_short(&self) -> Expression<F> {
        self.is_short.expr()
    }

    // Single RLP byte containing the length of the value
    pub(crate) fn is_long(&self) -> Expression<F> {
        self.is_long.expr()
    }

    pub(crate) fn is_long_at(&self, meta: &mut VirtualCells<F>, rot: usize) -> Expression<F> {
        self.is_long.rot(meta, rot)
    }

    // RLP byte containing the lenght of the length,
    // followed by the length, followed by the actual data
    pub(crate) fn is_very_long(&self) -> Expression<F> {
        self.is_very_long.expr()
    }

    /// Number of RLP bytes
    pub(crate) fn num_rlp_bytes(&self) -> Expression<F> {
        circuit!([meta, _cb!()], {
            matchx! {(
                self.is_short() => 0.expr(),
                self.is_long() => 1.expr(),
                self.is_very_long() => 2.expr(),
            )}
        })
    }

    /// Number of bytes in total (including RLP bytes)
    pub(crate) fn num_bytes(&self) -> Expression<F> {
        circuit!([meta, _cb!()], {
            matchx! {(
                self.is_short() => 1.expr(),
                self.is_long() => get_num_bytes_short::expr(self.bytes[0].expr()),
                self.is_very_long() => {
                    unreachablex!();
                    0.expr()
                },
            )}
        })
    }

    /// Length of the value (excluding RLP bytes)
    pub(crate) fn len(&self) -> Expression<F> {
        circuit!([meta, _cb!()], {
            matchx! {(
                self.is_short() => 1.expr(),
                self.is_long() => get_len_short::expr(self.bytes[0].expr()),
                self.is_very_long() => {
                    unreachablex!();
                    0.expr()
                },
            )}
        })
    }

    pub(crate) fn rlc_rlp(&self, r: &Expression<F>) -> Expression<F> {
        self.bytes.rlc(r)
    }

    pub(crate) fn rlc_rlp_rev(&self, r: &Expression<F>) -> Expression<F> {
        self.bytes.rlc_rev(r)
    }

    pub(crate) fn rlc_rlp_only_rev(&self, r: &Expression<F>) -> (Expression<F>, Expression<F>) {
        circuit!([meta, _cb!()], {
            matchx! {(
                self.is_short() => (self.bytes[..1].rlc_rev(r), pow::expr(r.expr(), 1)),
                self.is_long() => (self.bytes[..1].rlc_rev(r), pow::expr(r.expr(), 1)),
                self.is_very_long() => {
                    unreachablex!();
                    (0.expr(), 0.expr())
                },
            )}
        })
    }

    pub(crate) fn rlc_value(&self, r: &Expression<F>) -> Expression<F> {
        circuit!([meta, _cb!()], {
            matchx! {(
                self.is_short() => {
                    self.bytes[0].expr()
                },
                self.is_long() => {
                    self.bytes[1..].rlc(r)
                },
                self.is_very_long() => {
                    unreachablex!();
                    0.expr()
                },
            )}
        })
    }
}

impl RLPValueWitness {
    pub(crate) fn is_string(&self) -> bool {
        !self.is_list
    }

    // Single RLP byte containing the byte value
    pub(crate) fn is_short(&self) -> bool {
        self.is_short
    }

    // Single RLP byte containing the length of the value
    pub(crate) fn is_long(&self) -> bool {
        self.is_long
    }

    // RLP byte containing the lenght of the length,
    // followed by the length, followed by the actual data
    pub(crate) fn is_very_long(&self) -> bool {
        self.is_very_long
    }

    /// Number of RLP bytes
    pub(crate) fn num_rlp_bytes(&self) -> usize {
        matchw! {
            self.is_short() => 0,
            self.is_long() => 1,
            self.is_very_long() => 2,
        }
    }

    /// Number of bytes in total (including RLP bytes)
    pub(crate) fn num_bytes(&self) -> usize {
        matchw! {
            self.is_short() => 1,
            self.is_long() => get_num_bytes_short::value(self.bytes[0]),
            self.is_very_long() => unreachable!(),
        }
    }

    /// Length of the value (excluding RLP bytes)
    pub(crate) fn len(&self) -> usize {
        matchw! {
            self.is_short() => 1,
            self.is_long() => get_len_short::value(self.bytes[0]),
            self.is_very_long() => unreachable!(),
        }
    }

    pub(crate) fn rlc_rlp_rev<F: Field>(&self, r: F) -> F {
        self.bytes.rlc_value_rev(r)
    }

    pub(crate) fn rlc_value<F: Field>(&self, r: F) -> F {
        matchw! {
            self.is_short() => {
                self.bytes[0].scalar()
            },
            self.is_long() => {
                self.bytes[1..].rlc_value(r)
            },
            self.is_very_long() => {
                unreachable!();
            },
        }
    }
}

pub(crate) fn get_terminal_odd_nibble<F: Field>(byte: Expression<F>) -> Expression<F> {
    // The odd nible is stored in the same byte as the prefix
    byte - KEY_TERMINAL_PREFIX_ODD.expr()
}

pub(crate) fn get_ext_odd_nibble<F: Field>(byte: Expression<F>) -> Expression<F> {
    // The odd nible is stored in the same byte as the prefix
    byte - KEY_PREFIX_ODD.expr()
}

pub(crate) fn get_ext_odd_nibble_value<F: Field>(byte: F) -> F {
    // The odd nible is stored in the same byte as the prefix
    byte - F::from(KEY_PREFIX_ODD as u64)
}

// A single RLP byte
pub(crate) mod get_len_short {
    use crate::mpt_circuit::param::RLP_SHORT;
    use eth_types::Field;
    use gadgets::util::Expr;
    use halo2_proofs::plonk::Expression;

    pub(crate) fn expr<F: Field>(byte: Expression<F>) -> Expression<F> {
        byte - RLP_SHORT.expr()
    }
    pub(crate) fn value(byte: u8) -> usize {
        (byte - RLP_SHORT) as usize
    }
}

// A single RLP byte + the encoded length
pub(crate) mod get_num_bytes_short {
    use super::get_len_short;
    use eth_types::Field;
    use gadgets::util::Expr;
    use halo2_proofs::plonk::Expression;

    pub(crate) fn expr<F: Field>(byte: Expression<F>) -> Expression<F> {
        1.expr() + get_len_short::expr(byte)
    }
    pub(crate) fn value(byte: u8) -> usize {
        1 + get_len_short::value(byte)
    }
}

pub(crate) mod get_len_list_short {
    use crate::mpt_circuit::param::RLP_LIST_SHORT;
    use eth_types::Field;
    use gadgets::util::Expr;
    use halo2_proofs::plonk::Expression;

    pub(crate) fn expr<F: Field>(byte: Expression<F>) -> Expression<F> {
        byte - RLP_LIST_SHORT.expr()
    }
    pub(crate) fn value(byte: u8) -> usize {
        (byte - RLP_LIST_SHORT) as usize
    }
}

// A single RLP byte + the encoded length
pub(crate) mod get_num_bytes_list_short {
    use super::get_len_list_short;
    use eth_types::Field;
    use gadgets::util::Expr;
    use halo2_proofs::plonk::Expression;

    pub(crate) fn expr<F: Field>(byte: Expression<F>) -> Expression<F> {
        1.expr() + get_len_list_short::expr(byte)
    }
    pub(crate) fn value(byte: u8) -> usize {
        1 + get_len_list_short::value(byte)
    }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct RLPItemGadget<F> {
    pub(crate) value: RLPValueGadget<F>,
    pub(crate) list: RLPListGadget<F>,
}

#[derive(Clone, Debug, Default)]
pub(crate) struct RLPItemWitness {
    pub(crate) value: RLPValueWitness,
    pub(crate) list: RLPListWitness,
    pub(crate) bytes: Vec<u8>,
}

impl<F: Field> RLPItemGadget<F> {
    pub(crate) fn construct(cb: &mut MPTConstraintBuilder<F>, bytes: &[Expression<F>]) -> Self {
        RLPItemGadget {
            value: RLPValueGadget::construct(cb, bytes),
            list: RLPListGadget::construct(cb, bytes),
        }
    }

    pub(crate) fn assign(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        bytes: &[u8],
    ) -> Result<RLPItemWitness, Error> {
        let value_witness = self.value.assign(region, offset, bytes)?;
        let list_witness = self.list.assign(region, offset, bytes)?;
        assert!(!(value_witness.is_string() && list_witness.is_list()));
        Ok(RLPItemWitness {
            value: value_witness,
            list: list_witness,
            bytes: bytes.to_vec(),
        })
    }

    pub(crate) fn is_string(&self) -> Expression<F> {
        self.value.is_string()
    }

    pub(crate) fn is_string_at(&self, meta: &mut VirtualCells<F>, rot: usize) -> Expression<F> {
        self.value.is_string_at(meta, rot)
    }

    pub(crate) fn is_list(&self) -> Expression<F> {
        self.list.is_list()
    }

    pub(crate) fn is_list_at(&self, meta: &mut VirtualCells<F>, rot: usize) -> Expression<F> {
        self.list.is_list_at(meta, rot)
    }

    // Single RLP byte containing the byte value
    pub(crate) fn is_short(&self) -> Expression<F> {
        circuit!([meta, _cb!()], {
            matchx! {(
                self.value.is_string() => self.value.is_short(),
                self.list.is_list() => self.list.is_short(),
            )}
        })
    }

    // Single RLP byte containing the length of the value
    pub(crate) fn is_long(&self) -> Expression<F> {
        circuit!([meta, _cb!()], {
            matchx! {(
                self.value.is_string() => self.value.is_long(),
                self.list.is_list() => self.list.is_long(),
            )}
        })
    }

    // Single RLP byte containing the length of the value
    pub(crate) fn is_long_at(&self, meta: &mut VirtualCells<F>, rot: usize) -> Expression<F> {
        circuit!([meta, _cb!()], {
            matchx! {(
                self.value.is_string() => self.value.is_long_at(meta, rot),
                self.list.is_list() => self.list.is_long_at(meta, rot),
            )}
        })
    }

    // RLP byte containing the lenght of the length,
    // followed by the length, followed by the actual data
    pub(crate) fn is_very_long(&self) -> Expression<F> {
        circuit!([meta, _cb!()], {
            matchx! {(
                self.value.is_string() => self.value.is_very_long(),
                self.list.is_list() => self.list.is_very_long(),
            )}
        })
    }

    /// Number of RLP bytes
    pub(crate) fn num_rlp_bytes(&self) -> Expression<F> {
        circuit!([meta, _cb!()], {
            matchx! {(
                self.value.is_string() => self.value.num_rlp_bytes(),
                self.list.is_list() => self.list.num_rlp_bytes(),
            )}
        })
    }

    /// Number of bytes in total (including RLP bytes)
    pub(crate) fn num_bytes(&self) -> Expression<F> {
        circuit!([meta, _cb!()], {
            matchx! {(
                self.value.is_string() => self.value.num_bytes(),
                self.list.is_list() => self.list.num_bytes(),
            )}
        })
    }

    /// Length of the value (excluding RLP bytes)
    pub(crate) fn len(&self) -> Expression<F> {
        circuit!([meta, _cb!()], {
            matchx! {(
                self.value.is_string() => self.value.len(),
                self.list.is_list() => self.list.len(),
            )}
        })
    }

    // returns the RLC of the full string if the RLP is a list.
    pub(crate) fn rlc_content(&self, r: &Expression<F>) -> Expression<F> {
        circuit!([meta, _cb!()], {
            matchx! {(
                self.value.is_string() => self.value.rlc_value(r),
                self.list.is_list() => self.list.rlc_rlp(r),
            )}
        })
    }
}

impl RLPItemWitness {
    /// Number of bytes in total (including RLP bytes)
    pub(crate) fn num_bytes(&self) -> usize {
        matchw! {
            self.value.is_string() => self.value.num_bytes(),
            self.list.is_list() => self.list.num_bytes(),
        }
    }

    /// Number of bytes in total (including RLP bytes)
    pub(crate) fn num_rlp_bytes(&self) -> usize {
        matchw! {
            self.value.is_string() => self.value.num_rlp_bytes(),
            self.list.is_list() => self.list.num_rlp_bytes(),
        }
    }

    /// Length of the value (excluding RLP bytes)
    pub(crate) fn len(&self) -> usize {
        matchw! {
            self.value.is_string() => self.value.len(),
            self.list.is_list() => self.list.len(),
        }
    }

    pub(crate) fn is_string(&self) -> bool {
        self.value.is_string()
    }

    pub(crate) fn is_list(&self) -> bool {
        self.list.is_list()
    }

    pub(crate) fn is_short(&self) -> bool {
        matchw! {
            self.value.is_string() => self.value.is_short(),
            self.list.is_list() => self.list.is_short(),
        }
    }

    pub(crate) fn is_long(&self) -> bool {
        matchw! {
            self.value.is_string() => self.value.is_long(),
            self.list.is_list() => self.list.is_long(),
        }
    }

    pub(crate) fn rlc_content<F: Field>(&self, r: F) -> F {
        matchw! {
            self.value.is_string() => self.value.rlc_value(r),
            self.list.is_list() => self.list.rlc_rlp(r),
        }
    }

    pub(crate) fn rlc_rlp_rev<F: Field>(&self, r: F) -> F {
        // Compute the denominator needed for BE
        let mult_inv = pow::value(r, 34 - self.num_bytes())
            .invert()
            .unwrap_or(F::ZERO);
        matchw! {
            self.value.is_string() => self.value.rlc_rlp_rev(r) * mult_inv,
            self.list.is_list() => self.list.rlc_rlp_rev(r) * mult_inv,
        }
    }

    pub(crate) fn word<F: Field>(&self) -> word::Word<F> {
        // word::Word::from(Word::from_big_endian(&self.bytes[1..33]))
        let (lo, hi) = if self.is_string() {
            if self.is_short() {
                let lo: F = self.bytes[0].scalar();
                let hi: F = 0.scalar();
                (lo, hi)
            } else {
                let mut bytes = self.bytes[1..].to_vec();
                let mut len = self.len();
                while len < 33 {
                    bytes.insert(0, 0);
                    len += 1;
                }
                let lo = from_bytes::value(
                    bytes[17..33]
                        .iter()
                        .cloned()
                        .rev()
                        .collect::<Vec<u8>>()
                        .as_slice(),
                );
                let hi = from_bytes::value(
                    bytes[1..17]
                        .iter()
                        .cloned()
                        .rev()
                        .collect::<Vec<u8>>()
                        .as_slice(),
                );
                (lo, hi)
            }
        } else {
            let mut bytes = self.bytes[1..].to_vec();
            let mut len = self.len();
            while len < 33 {
                bytes.insert(0, 0);
                len += 1;
            }
            let lo = from_bytes::value(
                bytes[17..33]
                    .iter()
                    .cloned()
                    .rev()
                    .collect::<Vec<u8>>()
                    .as_slice(),
            );
            let hi = from_bytes::value(
                bytes[1..17]
                    .iter()
                    .cloned()
                    .rev()
                    .collect::<Vec<u8>>()
                    .as_slice(),
            );
            (lo, hi)
        };
        word::Word::new([lo, hi])
    }
}
