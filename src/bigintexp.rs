// `Add`/`Sub` ops may flip from `BigInt` to its `BigUint` magnitude
#![allow(clippy::suspicious_arithmetic_impl)]

use crate::std_alloc::{String, Vec};
use crate::{ParseBigIntError, Sign};
use core::cmp::Ordering::{self, Equal};
use core::default::Default;
use core::fmt;
use core::hash;
use core::ops::{Add, Div, Mul, Neg, Not, Rem, Sub};
use core::str;
use core::{i128, u128};
use core::{i64, u64};

use num_integer::{Integer, Roots};
use num_traits::{Num, One, Pow, Signed, Zero};

use crate::big_digit::BigDigit;
use crate::bigint::BigInt;
use crate::biguint::to_str_radix_reversed;
use crate::biguint::{BigUint, IntDigits, U32Digits, U64Digits};

#[cfg(any(feature = "quickcheck", feature = "arbitrary"))]
mod arbitrary;

#[cfg(feature = "serde")]
mod serde;

type Base = u16; // should be at least 2

/// A big signed integer type times a base to the power of an integer exponent.
pub struct BigIntExp<const base: Base> {
    exp: u32,
    data: BigInt,
}

type BigIntPowTen = BigIntExp<10>;

// Note: derived `Clone` doesn't specialize `clone_from`,
// but we want to keep the allocation in `data`.
impl<const base: Base> Clone for BigIntExp<base> {
    #[inline]
    fn clone(&self) -> Self {
        BigIntExp::<base> {
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

impl<const base: Base> hash::Hash for BigIntExp<base> {
    #[inline]
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.exp.hash(state);
        self.data.hash(state);
    }
}

impl<const base: Base> PartialEq for BigIntExp<base> {
    #[inline]
    fn eq(&self, other: &BigIntExp<base>) -> bool {
        self.exp == other.exp && self.data == other.data
    }
}

impl<const base: Base> Eq for BigIntExp<base> {}

impl<const base: Base> PartialOrd for BigIntExp<base> {
    #[inline]
    fn partial_cmp(&self, other: &BigIntExp<base>) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<const base: Base> Ord for BigIntExp<base> {
    #[inline]
    fn cmp(&self, other: &BigIntExp<base>) -> Ordering {
        todo!();
    }
}

impl<const base: Base> Default for BigIntExp<base> {
    #[inline]
    fn default() -> BigIntExp<base> {
        Zero::zero()
    }
}

impl<const base: Base> fmt::Debug for BigIntExp<base> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl<const base: Base> fmt::Display for BigIntExp<base> {
    /// Only for base allowed in to_str_radix.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!();
        // f.pad_integral(!self.is_negative(), "", &self.data.to_str_radix(base as u32))
    }
}

// CHECKME: impl fmt::{Binary,Octal,LowerHex,UpperHex}, Not, Not&

impl<const base: Base> Add for BigIntExp<base> {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
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

impl<const base: Base> Add for &BigIntExp<base> {}


impl<const base: Base> Zero for BigIntExp<base> {
    #[inline]
    fn zero() -> BigIntExp<base> {
        BigIntExp::<base> {
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

impl<const base: Base> Mul for BigIntExp<base> {
    type Output = Self;
    fn mul(self, rhs: BigIntExp<base>) -> Self::Output {
        todo!()
    }
}

impl<const base: Base> One for BigIntExp<base> {
    #[inline]
    fn one() -> BigIntExp<base> {
        BigIntExp::<base> {
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

impl<const base: Base> Num for BigIntExp<base> {
    type FromStrRadixErr = ParseBigIntError;
    fn from_str_radix(_: &str, _: u32) -> Result<Self, <Self as num_traits::Num>::FromStrRadixErr> {
        todo!()
    }
}

impl<const base: Base> Div for BigIntExp<base> {
    type Output = Self;
    fn div(self, _: BigIntExp<base>) -> <Self as Div<BigIntExp<base>>>::Output {
        todo!()
    }
}

impl<const base: Base> Sub for BigIntExp<base> {
    type Output = Self;
    fn sub(self, _: BigIntExp<base>) -> <Self as Sub<BigIntExp<base>>>::Output {
        todo!()
    }
}

impl<const base: Base> Sub for &BigIntExp<base> {
    type Output = BigIntExp<base>;
    fn sub(self, rsh: Self) -> Self::Output {
        todo!()
    }
}

impl<const base: Base> Signed for BigIntExp<base> {
    #[inline]
    fn abs(&self) -> BigIntExp<base> {
        BigIntExp::<base> {
            exp: self.exp,
            data: self.data.abs(),
        }
    }

    #[inline]
    fn abs_sub(&self, other: &Self) -> Self {
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

impl<const base: Base> Neg for BigIntExp<base> {
    type Output = BigIntExp<base>;

    #[inline]
    fn neg(mut self) -> BigIntExp<base> {
        self.data = -self.data;
        self
    }
}

impl<const base: Base> Neg for &BigIntExp<base> {
    type Output = BigIntExp<base>;

    #[inline]
    fn neg(self) -> BigIntExp<base> {
        -self.clone()
    }
}

impl<const base: Base> Integer for BigIntExp<base> {
    #[inline]
    fn div_rem(&self, other: &Self) -> (Self, Self) {
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
    fn div_floor(&self, other: &Self) -> Self {
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
    fn mod_floor(&self, other: &Self) -> Self {
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

    fn div_mod_floor(&self, other: &Self) -> (Self, Self) {
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
    fn div_ceil(&self, other: &Self) -> Self {
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
    fn gcd(&self, other: &Self) -> Self {
        todo!();
        // BigInt::from(self.data.gcd(&other.data))
    }

    /// Calculates the Lowest Common Multiple (LCM) of the number and `other`.
    #[inline]
    fn lcm(&self, other: &Self) -> Self {
        todo!();
        // BigInt::from(self.data.lcm(&other.data))
    }

    /// Calculates the Greatest Common Divisor (GCD) and
    /// Lowest Common Multiple (LCM) together.
    #[inline]
    fn gcd_lcm(&self, other: &Self) -> (Self, Self) {
        todo!();
        // let (gcd, lcm) = self.data.gcd_lcm(&other.data);
        // (BigInt::from(gcd), BigInt::from(lcm))
    }

    /// Greatest common divisor, least common multiple, and Bézout coefficients.
    #[inline]
    fn extended_gcd_lcm(&self, other: &Self) -> (num_integer::ExtendedGcd<Self>, Self) {
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
            self + (other - &m)
        }
    }
    /// Rounds down to nearest multiple of argument.
    #[inline]
    fn prev_multiple_of(&self, other: &Self) -> Self {
        self - &self.mod_floor(other)
    }
}

impl<const base: Base> Rem for BigIntExp<base> {
    type Output = Self;
    fn rem(self, rhs: BigIntExp<base>) -> <Self as Rem<BigIntExp<base>>>::Output {
        todo!()
    }
}

impl<const base: Base> Roots for BigIntExp<base> {
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

impl<const base: Base> BigIntExp<base> {
    const BASE_BI: BigInt = BigInt::from(base);

    pub fn new(exp: u32, bi: BigInt) -> Self {
        let mut res = BigIntExp::<base> { exp, data: bi };
        res.normalize();
        res
    }

    #[inline]
    fn normalize(&mut self) {
        if self.data.is_zero() {
            self.exp = 0;
        } else {
            loop {
                let (quot, rem) = self.data.div_rem(&Self::BASE_BI);
                if !rem.is_zero() {
                    return;
                }
                self.data = quot;
                self.exp += 1;
            }
        }
    }
}

/// A generic trait for converting a value to a [`BigInt`]. This may return
/// `None` when converting from `f32` or `f64`, and will always succeed
/// when converting from any integer or unsigned primitive, or [`BigUint`].
pub trait ToBigIntExp<const base: Base> {
    /// Converts the value of `self` to a [`BigIntExp`].
    fn to_bigintexp(&self) -> Option<BigIntExp<base>>;
}

impl<const base: Base> From<BigInt> for BigIntExp<base> {
    fn from(bi: BigInt) -> Self {
        let mut res = BigIntExp::<base> { exp: 0, data: bi };
        res.normalize();
        res
    }
}

impl<const base: Base> BigIntExp<base> {
    /// Creates and initializes a [`BigIntExp`].
    ///
    /// # Examples
    ///
    /// ```
    /// use num_bigint::{BigIntExp, ToBigInt};
    ///
    /// assert_eq!(BigIntExp<10>::parse_bytes(b"1234"), ToBigInt::to_bigint(&1234));
    /// assert_eq!(BigIntExp<16>::parse_bytes(b"ABCD"), ToBigInt::to_bigint(&0xABCD));
    /// assert_eq!(BigIntExp<16>::parse_bytes(b"G"), None);
    /// ```
    #[inline]
    pub fn parse_bytes(buf: &[u8]) -> Option<Self> {
        let s = str::from_utf8(buf).ok()?;
        Self::from_str_radix(s, base as u32).ok()
    }

    /// Creates and initializes a [`BigInt`]. Each `u8` of the input slice is
    /// interpreted as one digit of the number
    /// and must therefore be less than `radix`.
    ///
    /// The bytes are in big-endian byte order.
    /// `radix` must be in the range `2...256`.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_bigint::{BigInt, Sign};
    ///
    /// let inbase190 = vec![15, 33, 125, 12, 14];
    /// let a = BigInt::from_radix_be(Sign::Minus, &inbase190, 190).unwrap();
    /// assert_eq!(a.to_radix_be(190), (Sign:: Minus, inbase190));
    /// ```
    pub fn from_radix_be(sign: Sign, buf: &[u8]) -> Option<Self> {
        let u = BigInt::from_radix_be(sign, buf, base as u32)?;
        Some(BigIntExp::new(0, u))
    }

    /// Creates and initializes a [`BigInt`]. Each `u8` of the input slice is
    /// interpreted as one digit of the number
    /// and must therefore be less than `radix`.
    ///
    /// The bytes are in little-endian byte order.
    /// `base` must be in the range `2...256`.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_bigint::{BigInt, Sign};
    ///
    /// let inbase190 = vec![14, 12, 125, 33, 15];
    /// let a = BigIntExp::from_radix_be<190>(Sign::Minus, &inbase190).unwrap();
    /// assert_eq!(a.to_radix_be(190), (Sign::Minus, inbase190));
    /// ```
    pub fn from_radix_le(sign: Sign, buf: &[u8]) -> Option<Self> {
        let i = BigInt::from_radix_le(sign, buf, base as u32)?;
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

    /// Returns the sign and the `u32` digits representation of the [`BigInt`] ordered least
    /// significant digit first.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_bigint::{BigInt, Sign};
    ///
    /// assert_eq!(BigInt::from(-1125).to_u32_digits(), (Sign::Minus, vec![1125]));
    /// assert_eq!(BigInt::from(4294967295u32).to_u32_digits(), (Sign::Plus, vec![4294967295]));
    /// assert_eq!(BigInt::from(4294967296u64).to_u32_digits(), (Sign::Plus, vec![0, 1]));
    /// assert_eq!(BigInt::from(-112500000000i64).to_u32_digits(), (Sign::Minus, vec![830850304, 26]));
    /// assert_eq!(BigInt::from(112500000000i64).to_u32_digits(), (Sign::Plus, vec![830850304, 26]));
    /// ```
    #[inline]
    pub fn to_u32_digits(&self) -> (Sign, Vec<u32>) {
        (self.sign, self.data.to_u32_digits())
    }

    /// Returns the sign and the `u64` digits representation of the [`BigInt`] ordered least
    /// significant digit first.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_bigint::{BigInt, Sign};
    ///
    /// assert_eq!(BigInt::from(-1125).to_u64_digits(), (Sign::Minus, vec![1125]));
    /// assert_eq!(BigInt::from(4294967295u32).to_u64_digits(), (Sign::Plus, vec![4294967295]));
    /// assert_eq!(BigInt::from(4294967296u64).to_u64_digits(), (Sign::Plus, vec![4294967296]));
    /// assert_eq!(BigInt::from(-112500000000i64).to_u64_digits(), (Sign::Minus, vec![112500000000]));
    /// assert_eq!(BigInt::from(112500000000i64).to_u64_digits(), (Sign::Plus, vec![112500000000]));
    /// assert_eq!(BigInt::from(1u128 << 64).to_u64_digits(), (Sign::Plus, vec![0, 1]));
    /// ```
    #[inline]
    pub fn to_u64_digits(&self) -> (Sign, Vec<u64>) {
        (self.sign, self.data.to_u64_digits())
    }

    /// Returns an iterator of `u32` digits representation of the [`BigInt`] ordered least
    /// significant digit first.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_bigint::BigInt;
    ///
    /// assert_eq!(BigInt::from(-1125).iter_u32_digits().collect::<Vec<u32>>(), vec![1125]);
    /// assert_eq!(BigInt::from(4294967295u32).iter_u32_digits().collect::<Vec<u32>>(), vec![4294967295]);
    /// assert_eq!(BigInt::from(4294967296u64).iter_u32_digits().collect::<Vec<u32>>(), vec![0, 1]);
    /// assert_eq!(BigInt::from(-112500000000i64).iter_u32_digits().collect::<Vec<u32>>(), vec![830850304, 26]);
    /// assert_eq!(BigInt::from(112500000000i64).iter_u32_digits().collect::<Vec<u32>>(), vec![830850304, 26]);
    /// ```
    #[inline]
    pub fn iter_u32_digits(&self) -> U32Digits<'_> {
        self.data.iter_u32_digits()
    }

    /// Returns an iterator of `u64` digits representation of the [`BigInt`] ordered least
    /// significant digit first.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_bigint::BigInt;
    ///
    /// assert_eq!(BigInt::from(-1125).iter_u64_digits().collect::<Vec<u64>>(), vec![1125u64]);
    /// assert_eq!(BigInt::from(4294967295u32).iter_u64_digits().collect::<Vec<u64>>(), vec![4294967295u64]);
    /// assert_eq!(BigInt::from(4294967296u64).iter_u64_digits().collect::<Vec<u64>>(), vec![4294967296u64]);
    /// assert_eq!(BigInt::from(-112500000000i64).iter_u64_digits().collect::<Vec<u64>>(), vec![112500000000u64]);
    /// assert_eq!(BigInt::from(112500000000i64).iter_u64_digits().collect::<Vec<u64>>(), vec![112500000000u64]);
    /// assert_eq!(BigInt::from(1u128 << 64).iter_u64_digits().collect::<Vec<u64>>(), vec![0, 1]);
    /// ```
    #[inline]
    pub fn iter_u64_digits(&self) -> U64Digits<'_> {
        self.data.iter_u64_digits()
    }

    /// Returns the two's-complement byte representation of the [`BigInt`] in big-endian byte order.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_bigint::ToBigInt;
    ///
    /// let i = -1125.to_bigint().unwrap();
    /// assert_eq!(i.to_signed_bytes_be(), vec![251, 155]);
    /// ```
    #[inline]
    pub fn to_signed_bytes_be(&self) -> Vec<u8> {
        convert::to_signed_bytes_be(self)
    }

    /// Returns the two's-complement byte representation of the [`BigInt`] in little-endian byte order.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_bigint::ToBigInt;
    ///
    /// let i = -1125.to_bigint().unwrap();
    /// assert_eq!(i.to_signed_bytes_le(), vec![155, 251]);
    /// ```
    #[inline]
    pub fn to_signed_bytes_le(&self) -> Vec<u8> {
        convert::to_signed_bytes_le(self)
    }

    /// Returns the integer formatted as a string in the given radix.
    /// `radix` must be in the range `2...36`.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_bigint::BigInt;
    ///
    /// let i = BigInt::parse_bytes(b"ff", 16).unwrap();
    /// assert_eq!(i.to_str_radix(16), "ff");
    /// ```
    #[inline]
    pub fn to_str_radix(&self, radix: u32) -> String {
        let mut v = to_str_radix_reversed(&self.data, radix);

        if self.is_negative() {
            v.push(b'-');
        }

        v.reverse();
        unsafe { String::from_utf8_unchecked(v) }
    }

    /// Returns the integer in the requested base in big-endian digit order.
    /// The output is not given in a human readable alphabet but as a zero
    /// based `u8` number.
    /// `radix` must be in the range `2...256`.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_bigint::{BigInt, Sign};
    ///
    /// assert_eq!(BigInt::from(-0xFFFFi64).to_radix_be(159),
    ///            (Sign::Minus, vec![2, 94, 27]));
    /// // 0xFFFF = 65535 = 2*(159^2) + 94*159 + 27
    /// ```
    #[inline]
    pub fn to_radix_be(&self, radix: u32) -> (Sign, Vec<u8>) {
        (self.sign, self.data.to_radix_be(radix))
    }

    /// Returns the integer in the requested base in little-endian digit order.
    /// The output is not given in a human readable alphabet but as a zero
    /// based `u8` number.
    /// `radix` must be in the range `2...256`.
    ///
    /// # Examples
    ///
    /// ```
    /// use num_bigint::{BigInt, Sign};
    ///
    /// assert_eq!(BigInt::from(-0xFFFFi64).to_radix_le(159),
    ///            (Sign::Minus, vec![27, 94, 2]));
    /// // 0xFFFF = 65535 = 27 + 94*159 + 2*(159^2)
    /// ```
    #[inline]
    pub fn to_radix_le(&self, radix: u32) -> (Sign, Vec<u8>) {
        (self.sign, self.data.to_radix_le(radix))
    }

    /// Returns the sign of the [`BigInt`] as a [`Sign`].
    ///
    /// # Examples
    ///
    /// ```
    /// use num_bigint::{BigInt, Sign};
    /// use num_traits::Zero;
    ///
    /// assert_eq!(BigInt::from(1234).sign(), Sign::Plus);
    /// assert_eq!(BigInt::from(-4321).sign(), Sign::Minus);
    /// assert_eq!(BigInt::zero().sign(), Sign::NoSign);
    /// ```
    #[inline]
    pub fn sign(&self) -> Sign {
        self.sign
    }

    /// Returns the magnitude of the [`BigInt`] as a [`BigUint`].
    ///
    /// # Examples
    ///
    /// ```
    /// use num_bigint::{BigInt, BigUint};
    /// use num_traits::Zero;
    ///
    /// assert_eq!(BigInt::from(1234).magnitude(), &BigUint::from(1234u32));
    /// assert_eq!(BigInt::from(-4321).magnitude(), &BigUint::from(4321u32));
    /// assert!(BigInt::zero().magnitude().is_zero());
    /// ```
    #[inline]
    pub fn magnitude(&self) -> &BigUint {
        &self.data
    }

    /// Convert this [`BigInt`] into its [`Sign`] and [`BigUint`] magnitude,
    /// the reverse of [`BigInt::from_biguint()`].
    ///
    /// # Examples
    ///
    /// ```
    /// use num_bigint::{BigInt, BigUint, Sign};
    /// use num_traits::Zero;
    ///
    /// assert_eq!(BigInt::from(1234).into_parts(), (Sign::Plus, BigUint::from(1234u32)));
    /// assert_eq!(BigInt::from(-4321).into_parts(), (Sign::Minus, BigUint::from(4321u32)));
    /// assert_eq!(BigInt::zero().into_parts(), (Sign::NoSign, BigUint::zero()));
    /// ```
    #[inline]
    pub fn into_parts(self) -> (Sign, BigUint) {
        (self.sign, self.data)
    }

    /// Determines the fewest bits necessary to express the [`BigInt`],
    /// not including the sign.
    #[inline]
    pub fn bits(&self) -> u64 {
        self.data.bits()
    }

    /// Converts this [`BigInt`] into a [`BigUint`], if it's not negative.
    #[inline]
    pub fn to_biguint(&self) -> Option<BigUint> {
        match self.sign {
            Plus => Some(self.data.clone()),
            NoSign => Some(Zero::zero()),
            Minus => None,
        }
    }

    #[inline]
    pub fn checked_add(&self, v: &BigInt) -> Option<BigInt> {
        Some(self + v)
    }

    #[inline]
    pub fn checked_sub(&self, v: &BigInt) -> Option<BigInt> {
        Some(self - v)
    }

    #[inline]
    pub fn checked_mul(&self, v: &BigInt) -> Option<BigInt> {
        Some(self * v)
    }

    #[inline]
    pub fn checked_div(&self, v: &BigInt) -> Option<BigInt> {
        if v.is_zero() {
            return None;
        }
        Some(self / v)
    }

    /// Returns `self ^ exponent`.
    pub fn pow(&self, exponent: u32) -> Self {
        Pow::pow(self, exponent)
    }

    /// Returns `(self ^ exponent) mod modulus`
    ///
    /// Note that this rounds like `mod_floor`, not like the `%` operator,
    /// which makes a difference when given a negative `self` or `modulus`.
    /// The result will be in the interval `[0, modulus)` for `modulus > 0`,
    /// or in the interval `(modulus, 0]` for `modulus < 0`
    ///
    /// Panics if the exponent is negative or the modulus is zero.
    pub fn modpow(&self, exponent: &Self, modulus: &Self) -> Self {
        power::modpow(self, exponent, modulus)
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

    /// Returns the number of least-significant bits that are zero,
    /// or `None` if the entire number is zero.
    pub fn trailing_zeros(&self) -> Option<u64> {
        self.data.trailing_zeros()
    }

    /// Returns whether the bit in position `bit` is set,
    /// using the two's complement for negative numbers
    pub fn bit(&self, bit: u64) -> bool {
        if self.is_negative() {
            // Let the binary representation of a number be
            //   ... 0  x 1 0 ... 0
            // Then the two's complement is
            //   ... 1 !x 1 0 ... 0
            // where !x is obtained from x by flipping each bit
            if bit >= u64::from(crate::big_digit::BITS) * self.len() as u64 {
                true
            } else {
                let trailing_zeros = self.data.trailing_zeros().unwrap();
                match Ord::cmp(&bit, &trailing_zeros) {
                    Ordering::Less => false,
                    Ordering::Equal => true,
                    Ordering::Greater => !self.data.bit(bit),
                }
            }
        } else {
            self.data.bit(bit)
        }
    }

    /// Sets or clears the bit in the given position,
    /// using the two's complement for negative numbers
    ///
    /// Note that setting/clearing a bit (for positive/negative numbers,
    /// respectively) greater than the current bit length, a reallocation
    /// may be needed to store the new digits
    pub fn set_bit(&mut self, bit: u64, value: bool) {
        match self.sign {
            Sign::Plus => self.data.set_bit(bit, value),
            Sign::Minus => bits::set_negative_bit(self, bit, value),
            Sign::NoSign => {
                if value {
                    self.data.set_bit(bit, true);
                    self.sign = Sign::Plus;
                } else {
                    // Clearing a bit for zero is a no-op
                }
            }
        }
        // The top bit may have been cleared, so normalize
        self.normalize();
    }
}

#[test]
fn test_from_biguint() {
    fn check(inp_s: Sign, inp_n: usize, ans_s: Sign, ans_n: usize) {
        let inp = BigInt::from_biguint(inp_s, BigUint::from(inp_n));
        let ans = BigInt {
            sign: ans_s,
            data: BigUint::from(ans_n),
        };
        assert_eq!(inp, ans);
    }
    check(Plus, 1, Plus, 1);
    check(Plus, 0, NoSign, 0);
    check(Minus, 1, Minus, 1);
    check(NoSign, 1, NoSign, 0);
}

#[test]
fn test_from_slice() {
    fn check(inp_s: Sign, inp_n: u32, ans_s: Sign, ans_n: u32) {
        let inp = BigInt::from_slice(inp_s, &[inp_n]);
        let ans = BigInt {
            sign: ans_s,
            data: BigUint::from(ans_n),
        };
        assert_eq!(inp, ans);
    }
    check(Plus, 1, Plus, 1);
    check(Plus, 0, NoSign, 0);
    check(Minus, 1, Minus, 1);
    check(NoSign, 1, NoSign, 0);
}

#[test]
fn test_assign_from_slice() {
    fn check(inp_s: Sign, inp_n: u32, ans_s: Sign, ans_n: u32) {
        let mut inp = BigInt::from_slice(Minus, &[2627_u32, 0_u32, 9182_u32, 42_u32]);
        inp.assign_from_slice(inp_s, &[inp_n]);
        let ans = BigInt {
            sign: ans_s,
            data: BigUint::from(ans_n),
        };
        assert_eq!(inp, ans);
    }
    check(Plus, 1, Plus, 1);
    check(Plus, 0, NoSign, 0);
    check(Minus, 1, Minus, 1);
    check(NoSign, 1, NoSign, 0);
}
