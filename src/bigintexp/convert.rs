use core::{ops::Mul, str::FromStr};
use std::string::String;

use num::Num;
use num_traits::ToPrimitive;

use crate::biguint::convert::{fls, high_bits_to_u64};
use crate::{BigInt, BigIntExp, ParseBigIntError};

use super::Base;

impl<const BASE: Base> FromStr for BigIntExp<BASE> {
    type Err = ParseBigIntError;
    /// Parses string `s` that should consist of an optional sign, followed by decimal digits
    /// that may contain a decimal dot.
    /// In case `BASE` is not 10, the returned value will round
    /// to the decimals provided in `s`.
    #[inline]
    fn from_str(s: &str) -> Result<BigIntExp<BASE>, ParseBigIntError> {
        if BASE == 10 {
            BigIntExp::from_str_radix(s, 10)
        } else {
            match BigIntExp::<10>::from_str_radix(s, 10) {
                Err(e) => Err(e),
                Ok(bie_10) => {
                    let digits = s.chars().filter(|c| c.is_ascii_digit()).count();
                    let min_digits_base = digits as f64 * f64::ln(10f64) / f64::ln(BASE as f64);
                    Ok(bie_10.to_base::<BASE>(min_digits_base.ceil().max(1f64) as u32))
                }
            }
        }
    }
}

impl<const BASE: Base> Num for BigIntExp<BASE> {
    type FromStrRadixErr = ParseBigIntError;
    fn from_str_radix(s: &str, radix: u32) -> Result<Self, ParseBigIntError> {
        assert!(radix >= 2);
        let (exp, bi) = if let Some(dot_pos) = s.find('.') {
            let mut whole_num_str = String::new();
            whole_num_str.push_str(&s[..dot_pos]);
            whole_num_str.push_str(&s[(dot_pos + 1)..]);
            assert!(BASE as u32 == radix); // FIXME: divide by radix ** (len() - (dot_pos + 1))
            match BigInt::from_str_radix(&whole_num_str, radix) {
                Err(e) => return Err(e),
                Ok(big_int) => (((dot_pos + 1) as i32) - (s.len() as i32), big_int),
            }
        } else {
            match BigInt::from_str_radix(s, radix) {
                Err(e) => return Err(e),
                Ok(big_int) => (0, big_int),
            }
        };
        Ok(Self::new(exp, bi))
    }
}

impl ToPrimitive for BigIntExp<2> {
    #[inline]
    fn to_i64(&self) -> Option<i64> {
        todo!();
    }

    fn to_u64(&self) -> Option<u64> {
        use crate::Sign::*;
        match self.data.sign() {
            Minus => None,
            NoSign => Some(0),
            Plus => {
                let mantissa = crate::biguint::convert::high_bits_to_u64(self.data.magnitude());
                let exponent = self.exp + self.data.bits() as i32
                    - i32::from(crate::biguint::convert::fls(mantissa));
                if exponent >= 0 {
                    if exponent < u64::BITS as i32 {
                        Some(mantissa << exponent)
                    } else {
                        None
                    }
                } else if exponent > -(u64::BITS as i32) {
                    Some(mantissa >> -exponent)
                } else {
                    None
                }
            }
        }
    }

    fn to_f64(&self) -> Option<f64> {
        let sign = self.data.sign();
        if sign == crate::Sign::NoSign {
            return Some(0f64);
        }
        let mantissa: u64 = high_bits_to_u64(self.data.magnitude());
        let exponent: i32 = self.exp + self.data.bits() as i32 - i32::from(fls(mantissa));
        Some(if exponent > core::f64::MAX_EXP {
            if sign == crate::Sign::Plus {
                core::f64::INFINITY
            } else {
                core::f64::NEG_INFINITY
            }
        } else {
            if sign == crate::Sign::Plus {
                mantissa as f64
            } else {
                -(mantissa as f64)
            }
            .mul(2.0f64.powi(exponent as i32))
        })
    }
}
