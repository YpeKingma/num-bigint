// `Add`/`Sub` ops may flip from `BigInt` to its `BigUint` magnitude
#![allow(clippy::suspicious_arithmetic_impl)]

use crate::std_alloc::{String, Vec};
use crate::{ParseBigIntError, Sign};
use core::cmp::Ordering::{self};
// use core::default::Default;
use core::fmt;
use core::hash;
use core::ops::{Add, Div, Mul, Neg, Rem, Sub};
use core::str;

// use alloc::string::ToString;
use num_integer::{Integer, Roots};
use num_traits::{Num, One, Pow, Signed, Zero};

use crate::bigint::BigInt;

type Base = u16; // should be at least 2

/// A big signed integer type times BASE to the power of an integer exponent.
pub struct BigIntExp<const BASE: Base> {
    exp: u32,
    data: BigInt,
}

// Note: derived `Clone` doesn't specialize `clone_from`,
// but we want to keep the allocation in `data`.
impl<const BASE: Base> Clone for BigIntExp<BASE> {
    #[inline]
    fn clone(&self) -> Self {
        BigIntExp::<BASE> {
            exp: self.exp,
            data: self.data.clone(),
        }
    }

    #[inline]
    fn clone_from(&mut self, other: &Self) {
        self.exp = other.exp;
        self.data.clone_from(&other.data);
    }
}

impl<const BASE: Base> hash::Hash for BigIntExp<BASE> {
    #[inline]
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.exp.hash(state);
        self.data.hash(state);
    }
}

impl<const BASE: Base> PartialEq for BigIntExp<BASE> {
    #[inline]
    fn eq(&self, other: &BigIntExp<BASE>) -> bool {
        self.exp == other.exp && self.data == other.data
    }
}

impl<const BASE: Base> Eq for BigIntExp<BASE> {}

impl<const BASE: Base> PartialOrd for BigIntExp<BASE> {
    #[inline]
    fn partial_cmp(&self, other: &BigIntExp<BASE>) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<const BASE: Base> Ord for BigIntExp<BASE> {
    #[inline]
    fn cmp(&self, _other: &BigIntExp<BASE>) -> Ordering {
        todo!();
    }
}

impl<const BASE: Base> Default for BigIntExp<BASE> {
    #[inline]
    fn default() -> BigIntExp<BASE> {
        Zero::zero()
    }
}

impl<const BASE: Base> fmt::Debug for BigIntExp<BASE> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl<const BASE: Base> fmt::Display for BigIntExp<BASE> {
    /// Formats as a string with digits in `BASE`.
    /// `BASE` must be in the range `2...36`.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_bigint::BigIntExp;
    ///
    /// let i = BigIntExp::<16>::parse_bytes(b"ff").unwrap();
    /// assert_eq!(i.to_sting(), "ff");
    /// ```
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!();
        // f.pad_integral(!self.is_negative(), "", &self.data.to_str_radix(BASE as u32))
    }
}

// CHECKME: impl fmt::{Binary,Octal,LowerHex,UpperHex}, Not, Not&

impl<const BASE: Base> Add for BigIntExp<BASE> {
    type Output = Self;
    fn add(self, _rhs: Self) -> Self::Output {
        todo!()
        // match self.pow_ten.cmp(&rhs.pow_ten) {
        //     Ordering::Equal => BigIntPowTen::new(&self.big_int + &rhs.big_int, self.pow_ten),
        //     Ordering::Less => {
        //         let dp = (rhs.pow_ten - self.pow_ten) as u32;
        //         BigIntPowTen::new(&self.big_int + &rhs.big_int * tenpow(dp), self.pow_ten)
        //     },
        //     Ordering::Greater => {
        //         let dp = (self.pow_ten - rhs.pow_ten) as u32;
        //         BigIntPowTen::new(&self.big_int * tenpow(dp) + &rhs.big_int, rhs.pow_ten)
        //     },
        // }
    }
}

impl<const BASE: Base> Add for &BigIntExp<BASE> {
    type Output = BigIntExp<BASE>;
    fn add(self, _rhs: &BigIntExp<BASE>) -> Self::Output {
        todo!()
    }
}

impl<const BASE: Base> Zero for BigIntExp<BASE> {
    #[inline]
    fn zero() -> BigIntExp<BASE> {
        BigIntExp::<BASE> {
            exp: 0,
            data: BigInt::zero(),
        }
    }

    #[inline]
    fn set_zero(&mut self) {
        self.exp = 0;
        self.data = Zero::zero();
    }

    #[inline]
    fn is_zero(&self) -> bool {
        self.data.is_zero()
    }
}

impl<const BASE: Base> Mul for BigIntExp<BASE> {
    type Output = Self;
    fn mul(self, _rhs: BigIntExp<BASE>) -> Self::Output {
        todo!()
    }
}

impl<const BASE: Base> One for BigIntExp<BASE> {
    #[inline]
    fn one() -> BigIntExp<BASE> {
        BigIntExp::<BASE> {
            exp: 0,
            data: One::one(),
        }
    }

    #[inline]
    fn set_one(&mut self) {
        self.exp = 0;
        self.data = One::one();
    }

    #[inline]
    fn is_one(&self) -> bool {
        self.exp == 0 && self.data.is_one()
    }
}

impl<const BASE: Base> Num for BigIntExp<BASE> {
    type FromStrRadixErr = ParseBigIntError;
    fn from_str_radix(
        _s: &str,
        _radix: u32,
    ) -> Result<Self, <Self as num_traits::Num>::FromStrRadixErr> {
        // also convert from radix to BASE.
        todo!()
    }
}

impl<const BASE: Base> Div for BigIntExp<BASE> {
    type Output = Self;
    fn div(self, _: BigIntExp<BASE>) -> <Self as Div<BigIntExp<BASE>>>::Output {
        todo!()
    }
}

impl<const BASE: Base> Sub for BigIntExp<BASE> {
    type Output = Self;
    fn sub(self, _: BigIntExp<BASE>) -> <Self as Sub<BigIntExp<BASE>>>::Output {
        todo!()
    }
}

impl<const BASE: Base> Sub for &BigIntExp<BASE> {
    type Output = BigIntExp<BASE>;
    fn sub(self, _rhs: Self) -> Self::Output {
        todo!()
    }
}

impl<const BASE: Base> Signed for BigIntExp<BASE> {
    #[inline]
    fn abs(&self) -> BigIntExp<BASE> {
        BigIntExp::<BASE> {
            exp: self.exp,
            data: self.data.abs(),
        }
    }

    #[inline]
    fn abs_sub(&self, _other: &Self) -> Self {
        todo!();
        // if *self <= *other {
        //     Zero::zero()
        // } else {
        //     self - other
        // }
    }

    #[inline]
    fn signum(&self) -> Self {
        todo!();
        // match self.sign {
        //     Plus => One::one(),
        //     Minus => -One::one(),
        //     NoSign => Zero::zero(),
        // }
    }

    #[inline]
    fn is_positive(&self) -> bool {
        self.data.is_positive()
    }

    #[inline]
    fn is_negative(&self) -> bool {
        self.data.is_negative()
    }
}

// todo impl: UnsignedAbs

impl<const BASE: Base> Neg for BigIntExp<BASE> {
    type Output = BigIntExp<BASE>;

    #[inline]
    fn neg(mut self) -> BigIntExp<BASE> {
        self.data = -self.data;
        self
    }
}

impl<const BASE: Base> Neg for &BigIntExp<BASE> {
    type Output = BigIntExp<BASE>;

    #[inline]
    fn neg(self) -> BigIntExp<BASE> {
        -self.clone()
    }
}

impl<const BASE: Base> Integer for BigIntExp<BASE> {
    #[inline]
    fn div_rem(&self, _other: &Self) -> (Self, Self) {
        todo!();
        // // r.sign == self.sign
        // let (d_ui, r_ui) = self.data.div_rem(&other.data);
        // let d = BigInt::from_biguint(self.sign, d_ui);
        // let r = BigInt::from_biguint(self.sign, r_ui);
        // if other.is_negative() {
        //     (-d, r)
        // } else {
        //     (d, r)
        // }
    }

    #[inline]
    fn div_floor(&self, _other: &Self) -> Self {
        todo!();
        // let (d_ui, m) = self.data.div_mod_floor(&other.data);
        // let d = BigInt::from(d_ui);
        // match (self.sign, other.sign) {
        //     (Plus, Plus) | (NoSign, Plus) | (Minus, Minus) => d,
        //     (Plus, Minus) | (NoSign, Minus) | (Minus, Plus) => {
        //         if m.is_zero() {
        //             -d
        //         } else {
        //             -d - 1u32
        //         }
        //     }
        //     (_, NoSign) => unreachable!(),
    }

    #[inline]
    fn mod_floor(&self, _other: &Self) -> Self {
        todo!();
        // // m.sign == other.sign
        // let m_ui = self.data.mod_floor(&other.data);
        // let m = BigInt::from_biguint(other.sign, m_ui);
        // match (self.sign, other.sign) {
        //     (Plus, Plus) | (NoSign, Plus) | (Minus, Minus) => m,
        //     (Plus, Minus) | (NoSign, Minus) | (Minus, Plus) => {
        //         if m.is_zero() {
        //             m
        //         } else {
        //             other - m
        //         }
        //     }
        //     (_, NoSign) => unreachable!(),
        // }
    }

    fn div_mod_floor(&self, _other: &Self) -> (Self, Self) {
        todo!();
        // // m.sign == other.sign
        // let (d_ui, m_ui) = self.data.div_mod_floor(&other.data);
        // let d = BigInt::from(d_ui);
        // let m = BigInt::from_biguint(other.sign, m_ui);
        // match (self.sign, other.sign) {
        //     (Plus, Plus) | (NoSign, Plus) | (Minus, Minus) => (d, m),
        //     (Plus, Minus) | (NoSign, Minus) | (Minus, Plus) => {
        //         if m.is_zero() {
        //             (-d, m)
        //         } else {
        //             (-d - 1u32, other - m)
        //         }
        //     }
        //     (_, NoSign) => unreachable!(),
        // }
    }

    #[inline]
    fn div_ceil(&self, _other: &Self) -> Self {
        todo!();
        // let (d_ui, m) = self.data.div_mod_floor(&other.data);
        // let d = BigInt::from(d_ui);
        // match (self.sign, other.sign) {
        //     (Plus, Minus) | (NoSign, Minus) | (Minus, Plus) => -d,
        //     (Plus, Plus) | (NoSign, Plus) | (Minus, Minus) => {
        //         if m.is_zero() {
        //             d
        //         } else {
        //             d + 1u32
        //         }
        //     }
        //     (_, NoSign) => unreachable!(),
        // }
    }

    /// Calculates the Greatest Common Divisor (GCD) of the number and `other`.
    ///
    /// The result is always positive.
    #[inline]
    fn gcd(&self, _other: &Self) -> Self {
        todo!();
        // BigInt::from(self.data.gcd(&other.data))
    }

    /// Calculates the Lowest Common Multiple (LCM) of the number and `other`.
    #[inline]
    fn lcm(&self, _other: &Self) -> Self {
        todo!();
        // BigInt::from(self.data.lcm(&other.data))
    }

    /// Calculates the Greatest Common Divisor (GCD) and
    /// Lowest Common Multiple (LCM) together.
    #[inline]
    fn gcd_lcm(&self, _other: &Self) -> (Self, Self) {
        todo!();
        // let (gcd, lcm) = self.data.gcd_lcm(&other.data);
        // (BigInt::from(gcd), BigInt::from(lcm))
    }

    /// Greatest common divisor, least common multiple, and Bézout coefficients.
    #[inline]
    fn extended_gcd_lcm(&self, _other: &Self) -> (num_integer::ExtendedGcd<Self>, Self) {
        todo!();
        // let egcd = self.extended_gcd(other);
        // let lcm = if egcd.gcd.is_zero() {
        //     BigInt::zero()
        // } else {
        //     BigInt::from(&self.data / &egcd.gcd.data * &other.data)
        // };
        // (egcd, lcm)
    }

    /// Deprecated, use `is_multiple_of` instead.
    #[inline]
    fn divides(&self, other: &Self) -> bool {
        self.is_multiple_of(other)
    }

    /// Returns `true` if the number is a multiple of `other`.
    #[inline]
    fn is_multiple_of(&self, _other: &Self) -> bool {
        todo!();
        // self.data.is_multiple_of(&other.data)
    }

    /// Returns `true` if the number is divisible by `2`.
    #[inline]
    fn is_even(&self) -> bool {
        self.data.is_even()
    }

    /// Returns `true` if the number is not divisible by `2`.
    #[inline]
    fn is_odd(&self) -> bool {
        self.data.is_odd()
    }

    /// Rounds up to nearest multiple of argument.
    #[inline]
    fn next_multiple_of(&self, other: &Self) -> Self {
        let m = self.mod_floor(other);
        if m.is_zero() {
            self.clone()
        } else {
            self + &(other - &m)
        }
    }
    /// Rounds down to nearest multiple of argument.
    #[inline]
    fn prev_multiple_of(&self, other: &Self) -> Self {
        self - &self.mod_floor(other)
    }
}

impl<const BASE: Base> Rem for BigIntExp<BASE> {
    type Output = Self;
    fn rem(self, _rhs: BigIntExp<BASE>) -> <Self as Rem<BigIntExp<BASE>>>::Output {
        todo!()
    }
}

impl<const BASE: Base> Roots for BigIntExp<BASE> {
    fn nth_root(&self, n: u32) -> Self {
        assert!(
            !(self.is_negative() && n.is_even()),
            "root of degree {} is imaginary",
            n
        );
        todo!();
        // BigInt::from_biguint(self.sign, self.data.nth_root(n))
    }

    fn sqrt(&self) -> Self {
        assert!(!self.is_negative(), "square root is imaginary");
        todo!();
        // BigInt::from_biguint(self.sign, self.data.sqrt())
    }

    fn cbrt(&self) -> Self {
        todo!();
        // BigInt::from_biguint(self.sign, self.data.cbrt())
    }
}

impl<const BASE: Base> BigIntExp<BASE> {
    pub fn new(exp: u32, data: BigInt) -> Self {
        let mut res = BigIntExp::<BASE> { exp, data };
        res.normalize();
        res
    }

    #[inline]
    fn normalize(&mut self) {
        if self.data.is_zero() {
            self.exp = 0;
        } else {
            let base_bi: BigInt = BigInt::from(BASE);
            loop {
                let (quot, rem) = self.data.div_rem(&base_bi);
                if !rem.is_zero() {
                    return;
                }
                self.data = quot;
                self.exp += 1;
            }
        }
    }
}

/// A generic trait for converting a value to a [`BigIntExp`].
/// This should always succeed
/// when converting from any integer or numeric primitive.
pub trait ToBigIntExp<const BASE: Base> {
    /// Converts the value of `self` to a [`BigIntExp`].
    fn to_bigintexp(&self) -> Option<BigIntExp<BASE>>;
}

impl<const BASE: Base> From<BigInt> for BigIntExp<BASE> {
    fn from(data: BigInt) -> Self {
        Self::new(0, data)
    }
}

impl<const BASE: Base> BigIntExp<BASE> {
    /// Creates a [`BigIntExp`] from digit bytes in using `BASE`.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_bigint::{BigIntExp, ToBigInt};
    ///
    /// assert_eq!(BigIntExp<10>::parse_bytes(b"1234"), ToBigIntExp::to_bigintexp(&1234));
    /// assert_eq!(BigIntExp<16>::parse_bytes(b"ABCD"), ToBigIntExp::to_bigintexp(&0xABCD));
    /// assert_eq!(BigIntExp<16>::parse_bytes(b"G"), None);
    /// ```
    #[inline]
    pub fn parse_bytes(buf: &[u8]) -> Option<Self> {
        let s = str::from_utf8(buf).ok()?;
        Self::from_str_radix(s, BASE as u32).ok()
    }

    /// Creates a [`BigInt`]. Each `u8` of the input slice is
    /// interpreted as one digit of the number
    /// and must therefore be less than `BASE`.
    ///
    /// The bytes are in big-endian byte order.
    /// `BASE` must be in the range `2...256`.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_bigint::{BigInt, Sign};
    ///
    /// let inbase190 = vec![15, 33, 125, 12, 14];
    /// let a = BigIntExp::from_radix_be<190>(Sign::Minus, &inbase190).unwrap();
    /// assert_eq!(a.to_radix_be(), (Sign:: Minus, inbase190));
    /// ```
    pub fn from_radix_be(sign: Sign, buf: &[u8]) -> Option<Self> {
        let u = BigInt::from_radix_be(sign, buf, BASE as u32)?;
        Some(BigIntExp::new(0, u))
    }

    /// Creates and initializes a [`BigInt`]. Each `u8` of the input slice is
    /// interpreted as one digit of the number
    /// and must therefore be less than `radix`.
    ///
    /// The bytes are in little-endian byte order.
    /// `BASE` must be in the range `2...256`.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_bigint::{BigInt, Sign};
    ///
    /// let inbase190 = vec![14, 12, 125, 33, 15];
    /// let a = BigIntExp::from_radix_be<190>(Sign::Minus, &inbase190).unwrap();
    /// assert_eq!(a.to_radix_be(), (Sign::Minus, inbase190));
    /// ```
    pub fn from_radix_le(sign: Sign, buf: &[u8]) -> Option<Self> {
        let i = BigInt::from_radix_le(sign, buf, BASE as u32)?;
        Some(BigIntExp::new(0, i))
    }

    /// Returns the sign and the byte representation of the [`BigInt`] in big-endian byte order.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_bigint::{ToBigInt, Sign};
    ///
    /// let i = -1125.to_bigint().unwrap();
    /// assert_eq!(i.to_bytes_be(), (Sign::Minus, vec![4, 101]));
    /// ```
    #[inline]
    pub fn to_bytes_be(&self) -> (Sign, Vec<u8>) {
        self.data.to_bytes_be()
    }

    /// Returns the sign and the byte representation of the [`BigIntExp`] in little-endian byte order.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_bigint::{ToBigInt, Sign};
    ///
    /// let i = -1125.to_bigint().unwrap();
    /// assert_eq!(i.to_bytes_le(), (Sign::Minus, vec![101, 4]));
    /// ```
    #[inline]
    pub fn to_bytes_le(&self) -> (Sign, Vec<u8>) {
        todo!();
        // (self.sign, self.data.to_bytes_le())
    }

    /// Returns the exponent and the BigInt forming the [`BigIntExp`].
    #[inline]
    pub fn into(self) -> (u32, BigInt) {
        (self.exp, self.data)
    }


    #[inline]
    pub fn checked_add(&self, v: &Self) -> Option<Self> {
        Some(self + v)
    }

    #[inline]
    pub fn checked_sub(&self, v: &Self) -> Option<Self> {
        Some(self - v)
    }

    #[inline]
    pub fn checked_mul(&self, v: &Self) -> Option<Self> {
        Some(self.clone() * v.clone())
    }

    #[inline]
    pub fn checked_div(&self, v: &Self) -> Option<Self> {
        if v.is_zero() {
            return None;
        }
        Some(self.clone() / v.clone())
    }

    /// Returns `self ^ exponent`.
    pub fn pow(&self, exponent: u32) -> Self {
        // (data * BASE ** exp) ** exponent = data ** exponent * BASE ** (exp*exponent)
        if exponent == 0 {
            One::one()
        } else {
            BigIntExp::<BASE> {
                exp: self.exp * exponent, // CHECKME: overflow
                data: self.data.clone().pow(exponent),
            }
        }
    }

    /// Returns `(self ^ exponent) mod modulus`
    ///
    /// Note that this rounds like `mod_floor`, not like the `%` operator,
    /// which makes a difference when given a negative `self` or `modulus`.
    /// The result will be in the interval `[0, modulus)` for `modulus > 0`,
    /// or in the interval `(modulus, 0]` for `modulus < 0`
    ///
    /// Panics if the exponent is negative or the modulus is zero.
    pub fn modpow(&self, _exponent: &Self, _modulus: &Self) -> Self {
        // ((data * BASE ** exp) ** exponent) % modulus = (data ** exponent * BASE ** (exp*exponent)) % modulus
        todo!();
    }

    /// Returns the truncated principal square root of `self` --
    /// see [`num_integer::Roots::sqrt()`].
    pub fn sqrt(&self) -> Self {
        Roots::sqrt(self)
    }

    /// Returns the truncated principal cube root of `self` --
    /// see [`num_integer::Roots::cbrt()`].
    pub fn cbrt(&self) -> Self {
        Roots::cbrt(self)
    }

    /// Returns the truncated principal `n`th root of `self` --
    /// See [`num_integer::Roots::nth_root()`].
    pub fn nth_root(&self, n: u32) -> Self {
        Roots::nth_root(self, n)
    }
}

