
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
