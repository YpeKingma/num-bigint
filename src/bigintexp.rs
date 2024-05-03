// `Add`/`Sub` ops may flip from `BigInt` to its `BigUint` magnitude
#![allow(clippy::suspicious_arithmetic_impl)]

use crate::ParseBigIntError;
use core::cmp::Ordering::{self};
// use core::default::Default;
use core::fmt;
use core::hash;
use core::ops::{Add, Div, Mul, Neg, Rem, Sub};
use core::str;
// use static_assertions;
use std::string::String;

// use alloc::string::ToString;
use num_integer::{Integer, Roots};
use num_traits::{Num, One, Pow, Signed, Zero};

use crate::bigint::BigInt;

type Base = u16; // should be at least 2

/// A big signed integer type times BASE to the power of an integer exponent.
pub struct BigIntExp<const BASE: Base> {
    exp: i32,
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
    /// let bie = BigIntExp::<16>::parse_bytes(b"ff").unwrap();
    /// assert_eq!(bie.to_string(), "ff");
    /// ```
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut tmp = self.data.abs().to_str_radix(BASE as u32);
        if self.exp > 0 {
            for _ in 0..self.exp {
                tmp.push('0');
            }
        } else {
            // insert or prepend a decimal dot.
            let insert_dot_pos = tmp.len() as i32 + self.exp;
            if insert_dot_pos > 0 {
                if insert_dot_pos < tmp.len() as i32 {
                    tmp.insert(insert_dot_pos as usize, '.');
                }
            } else {
                let mut prfx = String::from("0.");
                for _ in 0..-insert_dot_pos {
                    prfx.push('0');
                }
                prfx.push_str(&tmp);
                tmp = prfx;
            }
        }
        f.pad_integral(!self.is_negative(), "", &tmp)
    }
}

// CHECKME: impl fmt::{Binary,Octal,LowerHex,UpperHex}, Not, Not&

impl<const BASE: Base> Add for BigIntExp<BASE> {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        &self + &rhs
    }
}

impl<const BASE: Base> Add for &BigIntExp<BASE> {
    type Output = BigIntExp<BASE>;
    fn add(self, rhs: Self) -> Self::Output {
        match self.exp.cmp(&rhs.exp) {
            Ordering::Equal => BigIntExp::new(self.exp, &self.data + &rhs.data),
            Ordering::Less => {
                let de = (rhs.exp - self.exp) as u32;
                let base_pow_de: BigInt = BigInt::from(BASE).pow(de);
                BigIntExp::new(self.exp, &self.data + &rhs.data * base_pow_de)
            }
            Ordering::Greater => {
                let de = (self.exp - rhs.exp) as u32;
                let base_pow_de: BigInt = BigInt::from(BASE).pow(de);
                BigIntExp::new(rhs.exp, &self.data * base_pow_de + &rhs.data)
            }
        }
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
    #[inline]
    fn mul(self, rhs: Self) -> Self::Output {
        &self * &rhs
    }
}

impl<const BASE: Base> Mul for &BigIntExp<BASE> {
    type Output = BigIntExp<BASE>;
    fn mul(self, rhs: Self) -> Self::Output {
        BigIntExp::<BASE>::new(self.exp + rhs.exp, &self.data * &rhs.data)
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
    fn from_str_radix(s: &str, radix: u32) -> Result<Self, ParseBigIntError> {
        // FIXME: allow a dot.
        BigInt::from_str_radix(s, radix).map(Self::from)
    }
}

impl<const BASE: Base> Div for BigIntExp<BASE> {
    type Output = Self;
    fn div(self, rhs: Self) -> Self {
        BigIntExp::<BASE>::new(self.exp - rhs.exp, self.data.div(rhs.data))
    }
}

impl<const BASE: Base> Sub for BigIntExp<BASE> {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: BigIntExp<BASE>) -> <Self as Sub<BigIntExp<BASE>>>::Output {
        &self - &rhs
    }
}

impl<const BASE: Base> Sub for &BigIntExp<BASE> {
    type Output = BigIntExp<BASE>;
    fn sub(self, rhs: Self) -> Self::Output {
        match self.exp.cmp(&rhs.exp) {
            Ordering::Equal => BigIntExp::new(self.exp, &self.data - &rhs.data),
            Ordering::Less => {
                let de = (rhs.exp - self.exp) as u32;
                let base_pow_de: BigInt = BigInt::from(BASE).pow(de);
                BigIntExp::new(self.exp, &self.data - &rhs.data * base_pow_de)
            }
            Ordering::Greater => {
                let de = (self.exp - rhs.exp) as u32;
                let base_pow_de: BigInt = BigInt::from(BASE).pow(de);
                BigIntExp::new(rhs.exp, &self.data * base_pow_de - &rhs.data)
            }
        }
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
    fn abs_sub(&self, other: &Self) -> Self {
        if *self <= *other {
            Zero::zero()
        } else {
            self - other
        }
    }

    #[inline]
    fn signum(&self) -> Self {
        BigIntExp::<BASE> {
            exp: 0,
            data: self.data.signum(),
        }
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
    fn div_rem(&self, other: &Self) -> (Self, Self) {
        let (quot, rem) = self.data.div_mod_floor(&other.data);
        let de = self.exp - other.exp;
        (Self::new(de, quot), Self::new(de, rem))
    }

    #[inline]
    fn div_floor(&self, other: &Self) -> Self {
        let (quot, _rem) = self.data.div_mod_floor(&other.data);
        let de = self.exp - other.exp;
        Self::new(de, quot)
    }

    #[inline]
    fn mod_floor(&self, other: &Self) -> Self {
        let (_quot, rem) = self.data.div_mod_floor(&other.data);
        let de = self.exp - other.exp;
        Self::new(de, rem)
    }

    fn div_mod_floor(&self, other: &Self) -> (Self, Self) {
        self.div_rem(other)
    }

    #[inline]
    fn div_ceil(&self, other: &Self) -> Self {
        use crate::Sign::*;
        let (d, m) = self.data.div_mod_floor(&other.data);
        match (self.data.sign(), other.data.sign()) {
            (Plus, Minus) | (NoSign, Minus) | (Minus, Plus) => -d,
            (Plus, Plus) | (NoSign, Plus) | (Minus, Minus) => {
                if m.is_zero() {
                    d
                } else {
                    d + 1u32
                }
            }
            (_, NoSign) => unreachable!(),
        }
        .into()
    }

    /// Calculates the Greatest Common Divisor (GCD) of the number and `other`.
    ///
    /// The result is always positive.
    fn gcd(&self, other: &Self) -> Self {
        // CHECKME:
        let gcd_bi = self.data.gcd(&other.data);
        let min_exp = self.exp.min(other.exp);
        Self::new(min_exp, gcd_bi)
    }

    /// Calculates the Lowest Common Multiple (LCM) of the number and `other`.
    fn lcm(&self, other: &Self) -> Self {
        // CHECKME:
        let lcm_bi = self.data.lcm(&other.data);
        let max_exp = self.exp.max(other.exp);
        Self::new(max_exp, lcm_bi)
    }

    /// Calculates the Greatest Common Divisor (GCD) and
    /// Lowest Common Multiple (LCM) together.
    #[inline]
    fn gcd_lcm(&self, other: &Self) -> (Self, Self) {
        // CHECKME:
        let (gcd_bi, lcm_bi) = self.data.gcd_lcm(&other.data);
        let min_exp = self.exp.min(other.exp);
        let max_exp = self.exp.max(other.exp);
        (Self::new(min_exp, gcd_bi), Self::new(max_exp, lcm_bi))
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
    fn is_multiple_of(&self, other: &Self) -> bool {
        // CHECKME:
        self.data.is_multiple_of(&other.data)
    }

    /// Returns `true` if the number is divisible by `2`.
    fn is_even(&self) -> bool {
        // CHECKME:
        if self.exp < 0 {
            false
        } else if BASE.is_even() {
            !self.data.is_zero()
        } else {
            self.data.is_even()
        }
    }

    /// Returns `true` if the number is not divisible by `2`.
    #[inline]
    fn is_odd(&self) -> bool {
        // CHECKME:
        if self.exp < 0 {
            false
        } else {
            self.data.is_odd()
        }
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
    fn rem(self, other: Self) -> Self {
        let (_quot, rem) = self.data.div_mod_floor(&other.data);
        let de = self.exp - other.exp;
        Self::new(de, rem)
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

impl<const BASE: Base> From<BigInt> for BigIntExp<BASE> {
    fn from(data: BigInt) -> Self {
        Self::new(0, data)
    }
}



impl<const BASE: Base> BigIntExp<BASE> {

    pub fn new(exp: i32, data: BigInt) -> Self {
        static_assertions::const_assert!(BASE >= 2);
        assert!(BASE >= 2);
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

    /// Returns the exponent and the BigInt forming the [`BigIntExp`].
    #[inline]
    pub fn into(self) -> (i32, BigInt) {
        (self.exp, self.data)
    }

    /// Creates a [`BigIntExp`] from digit bytes using `BASE`.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_bigint::{BigIntExp, BigInt};
    ///
    /// assert_eq!(BigIntExp::<10>::parse_bytes(b"1234"), Some(BigIntExp::from(BigInt::from(1234))));
    /// assert_eq!(BigIntExp::<16>::parse_bytes(b"ABCD"), Some(BigIntExp::from(BigInt::from(0xABCD))));
    /// assert_eq!(BigIntExp::<16>::parse_bytes(b"G"), None);
    /// ```
    #[inline]
    pub fn parse_bytes(buf: &[u8]) -> Option<Self> {
        let s = str::from_utf8(buf).ok()?;
        Self::from_str_radix(s, BASE as u32).ok()
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
        Some(self * v)
    }

    #[inline]
    pub fn checked_div(&self, v: &Self) -> Option<Self> {
        if v.is_zero() {
            return None;
        }
        Some(self.clone() / v.clone())
    }

    /// Returns `self ^ exponent`.
    pub fn pow(&self, exponent: i32) -> Self {
        // (data * BASE ** exp) ** exponent = data ** exponent * BASE ** (exp*exponent)
        match exponent.signum() {
            0 => One::one(),
            1 => {
                BigIntExp::<BASE> {
                    exp: self.exp * exponent, // CHECKME: overflow
                    data: self.data.clone().pow(exponent as u32),
                }
            }
            -1 => {
                BigIntExp::<BASE> {
                    exp: -self.exp * exponent,                       // CHECKME: overflow
                    data: self.data.clone().pow((-exponent) as u32), // CHECKME: overflow
                }
            }
            _ => unreachable!(),
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
