use core::str::FromStr;

use num::Num;
use num_traits::ToPrimitive;

use crate::{BigIntExp, ParseBigIntError};

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

impl ToPrimitive for BigIntExp<2> {
    #[inline]
    fn to_i64(&self) -> Option<i64> {
        todo!();
        // self.to_u64().as_ref().and_then(u64::to_i64)
    }

    #[inline]
    fn to_i128(&self) -> Option<i128> {
        todo!();
        // self.to_u128().as_ref().and_then(u128::to_i128)
    }

    #[allow(clippy::useless_conversion)]
    #[inline]
    fn to_u64(&self) -> Option<u64> {
        todo!();
        // let mut ret: u64 = 0;
        // let mut bits = 0;

        // for i in self.data.iter() {
        //     if bits >= 64 {
        //         return None;
        //     }

        //     // XXX Conversion is useless if already 64-bit.
        //     ret += u64::from(*i) << bits;
        //     bits += big_digit::BITS;
        // }

        // Some(ret)
    }

    #[inline]
    fn to_u128(&self) -> Option<u128> {
        todo!();
        // let mut ret: u128 = 0;
        // let mut bits = 0;

        // for i in self.data.iter() {
        //     if bits >= 128 {
        //         return None;
        //     }

        //     ret |= u128::from(*i) << bits;
        //     bits += big_digit::BITS;
        // }

        // Some(ret)
    }

    #[inline]
    fn to_f32(&self) -> Option<f32> {
        todo!();
        // let mantissa = high_bits_to_u64(self);
        // let exponent = self.bits() - u64::from(fls(mantissa));

        // if exponent > core::f32::MAX_EXP as u64 {
        //     Some(core::f32::INFINITY)
        // } else {
        //     Some((mantissa as f32) * 2.0f32.powi(exponent as i32))
        // }
    }

    #[inline]
    fn to_f64(&self) -> Option<f64> {
        todo!();
        // let mantissa = high_bits_to_u64(self);
        // let exponent = self.bits() - u64::from(fls(mantissa));

        // if exponent > core::f64::MAX_EXP as u64 {
        //     Some(core::f64::INFINITY)
        // } else {
        //     Some((mantissa as f64) * 2.0f64.powi(exponent as i32))
        // }
    }
}
