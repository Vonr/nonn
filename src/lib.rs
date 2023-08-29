#![doc = include_str!("../README.md")]
#![no_std]

use core::fmt;
use core::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div, DivAssign,
    Mul, MulAssign, Not, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
};
use core::str::FromStr;

use core::num::ParseIntError;

macro_rules! impl_nonn_fmt {
    ( ( $( $Trait: ident ),+ ) for $Ty: ident<$Int: ident>($NonZero: ident) ) => {
        $(
            impl<const N: $Int> fmt::$Trait for $Ty<N> {
                #[inline]
                fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                    self.get().fmt(f)
                }
            }
        )+
    }
}

// A bunch of methods for unsigned nonn types only.
macro_rules! nonn_unsigned_operations {
    ( $Ty: ident<$Int: ident>($NonZero: ident) ) => {
        /// Adds an unsigned integer to a non-N value.
        /// Checks for overflow and returns [`None`] on overflow.
        ///
        /// # Examples
        ///
        /// ```
        #[doc = concat!("# use nonn::", stringify!($Ty), ";")]
        /// # fn main() { test().unwrap(); }
        /// # fn test() -> Option<()> {
        #[doc = concat!("let one = ", stringify!($Ty), "::<42>::new(1)?;")]
        #[doc = concat!("let two = ", stringify!($Ty), "::<42>::new(2)?;")]
        #[doc = concat!("let max = ", stringify!($Ty), "::<42>::new(",
                                                                    stringify!($Int), "::MAX)?;")]
        ///
        /// assert_eq!(Some(two), one.checked_add(1));
        /// assert_eq!(None, max.checked_add(1));
        /// # Some(())
        /// # }
        /// ```
        #[must_use = "this returns the result of the operation, \
        without modifying the original"]
        #[inline]
        pub const fn checked_add(self, other: $Int) -> Option<Self> {
            if let Some(result) = self.get().checked_add(other) {
                match $Ty::<N>::new(result) {
                    out @ Some(..) => out,
                    None => panic!("Result of checked addition was N"),
                }
            } else {
                None
            }
        }

        /// Adds an unsigned integer to a non-N value.
        #[doc = concat!("Return [`", stringify!($Ty), "::MAX`] on overflow.")]
        ///
        /// # Examples
        ///
        /// ```
        #[doc = concat!("# use nonn::", stringify!($Ty), ";")]
        /// # fn main() { test().unwrap(); }
        /// # fn test() -> Option<()> {
        #[doc = concat!("let one = ", stringify!($Ty), "::<42>::new(1)?;")]
        #[doc = concat!("let two = ", stringify!($Ty), "::<42>::new(2)?;")]
        #[doc = concat!("let max = ", stringify!($Ty), "::<42>::new(",
                                                                    stringify!($Int), "::MAX)?;")]
        ///
        /// assert_eq!(two, one.saturating_add(1));
        /// assert_eq!(max, max.saturating_add(1));
        /// # Some(())
        /// # }
        /// ```
        #[must_use = "this returns the result of the operation, \
            without modifying the original"]
        #[inline]
        pub const fn saturating_add(self, other: $Int) -> Self {
            match $Ty::<N>::new(self.get().saturating_add(other)) {
                Some(out) => out,
                None => panic!("Result of saturating addition was N"),
            }
        }

        /// Returns the smallest power of two greater than or equal to n.
        /// Checks for overflow and returns [`None`]
        /// if the next power of two is greater than the type’s maximum value.
        ///
        /// # Examples
        ///
        /// ```
        #[doc = concat!("# use nonn::", stringify!($Ty), ";")]
        /// # fn main() { test().unwrap(); }
        /// # fn test() -> Option<()> {
        #[doc = concat!("let two = ", stringify!($Ty), "::<42>::new(2)?;")]
        #[doc = concat!("let three = ", stringify!($Ty), "::<42>::new(3)?;")]
        #[doc = concat!("let four = ", stringify!($Ty), "::<42>::new(4)?;")]
        #[doc = concat!("let max = ", stringify!($Ty), "::<42>::new(",
                                                                    stringify!($Int), "::MAX)?;")]
        ///
        /// assert_eq!(Some(two), two.checked_next_power_of_two() );
        /// assert_eq!(Some(four), three.checked_next_power_of_two() );
        /// assert_eq!(None, max.checked_next_power_of_two() );
        /// # Some(())
        /// # }
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        pub const fn checked_next_power_of_two(self) -> Option<Self> {
            if let Some(nn) = self.get().checked_next_power_of_two() {
                match Self::new(nn) {
                    out @ Some(..) => out,
                    None => panic!("Result of checked next power of two was N"),
                }
            } else {
                None
            }
        }

        /// Returns the base 2 logarithm of the number, rounded down.
        #[doc = concat!("[`", stringify!($Int), "::ilog2`],")]
        ///
        /// # Examples
        ///
        /// ```
        #[doc = concat!("# use nonn::", stringify!($Ty), ";")]
        #[doc = concat!("assert_eq!(", stringify!($Ty), "::<42>::new(7).unwrap().ilog2(), 2);")]
        #[doc = concat!("assert_eq!(", stringify!($Ty), "::<42>::new(8).unwrap().ilog2(), 3);")]
        #[doc = concat!("assert_eq!(", stringify!($Ty), "::<42>::new(9).unwrap().ilog2(), 3);")]
        /// ```
        #[must_use = "this returns the result of the operation, \
        without modifying the original"]
        #[cfg(ilog)]
        #[inline]
        pub const fn ilog2(self) -> u32 {
            self.get().ilog2()
        }

        /// Returns the base 10 logarithm of the number, rounded down.
        #[doc = concat!("[`", stringify!($Int), "::ilog10`],")]
        ///
        /// # Examples
        ///
        /// ```
        #[doc = concat!("# use nonn::", stringify!($Ty), ";")]
        #[doc = concat!("assert_eq!(", stringify!($Ty), "::<42>::new(99).unwrap().ilog10(), 1);")]
        #[doc = concat!("assert_eq!(", stringify!($Ty), "::<42>::new(100).unwrap().ilog10(), 2);")]
        #[doc = concat!("assert_eq!(", stringify!($Ty), "::<42>::new(101).unwrap().ilog10(), 2);")]
        /// ```
        #[must_use = "this returns the result of the operation, \
        without modifying the original"]
        #[cfg(ilog)]
        #[inline]
        pub const fn ilog10(self) -> u32 {
            self.get().ilog10()
        }
    };
}

// A bunch of methods for signed nonn types only.
macro_rules! nonn_signed_operations {
    ( $Ty: ident<$Int: ident>($NonZero: ident) ) => {
        /// Computes the absolute value of self.
        #[doc = concat!("See [`", stringify!($Int), "::abs`]")]
        /// for documentation on overflow behaviour.
        ///
        /// # Example
        ///
        /// ```
        #[doc = concat!("# use nonn::", stringify!($Ty), ";")]
        /// # fn main() { test().unwrap(); }
        /// # fn test() -> Option<()> {
        #[doc = concat!("let pos = ", stringify!($Ty), "::<42>::new(1)?;")]
        #[doc = concat!("let neg = ", stringify!($Ty), "::<42>::new(-1)?;")]
        ///
        /// assert_eq!(pos, pos.abs());
        /// assert_eq!(pos, neg.abs());
        /// # Some(())
        /// # }
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        pub const fn abs(self) -> Self {
            match Self::new(self.get().abs()) {
                Some(out) => out,
                None => panic!("Result of absolute was N"),
            }
        }

        /// Checked absolute value.
        /// Checks for overflow and returns [`None`] if
        #[doc = concat!("`self == ", stringify!($Ty), "::MIN`.")]
        /// The result cannot be N.
        ///
        /// # Example
        ///
        /// ```
        #[doc = concat!("# use nonn::", stringify!($Ty), ";")]
        /// # fn main() { test().unwrap(); }
        /// # fn test() -> Option<()> {
        #[doc = concat!("let pos = ", stringify!($Ty), "::<42>::new(1)?;")]
        #[doc = concat!("let neg = ", stringify!($Ty), "::<42>::new(-1)?;")]
        #[doc = concat!("let min = ", stringify!($Ty), "::<42>::new(",
                                                                stringify!($Int), "::MIN)?;")]
        ///
        /// assert_eq!(Some(pos), neg.checked_abs());
        /// assert_eq!(None, min.checked_abs());
        /// # Some(())
        /// # }
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        pub const fn checked_abs(self) -> Option<Self> {
            if let Some(nn) = self.get().checked_abs() {
                match Self::new(nn) {
                    out @ Some(..) => out,
                    None => panic!("Result of checked absolute was N"),
                }
            } else {
                None
            }
        }

        /// Computes the absolute value of self,
        /// with overflow information, see
        #[doc = concat!("[`", stringify!($Int), "::overflowing_abs`].")]
        ///
        /// # Example
        ///
        /// ```
        #[doc = concat!("# use nonn::", stringify!($Ty), ";")]
        /// # fn main() { test().unwrap(); }
        /// # fn test() -> Option<()> {
        #[doc = concat!("let pos = ", stringify!($Ty), "::<42>::new(1)?;")]
        #[doc = concat!("let neg = ", stringify!($Ty), "::<42>::new(-1)?;")]
        #[doc = concat!("let min = ", stringify!($Ty), "::<42>::new(",
                                                                stringify!($Int), "::MIN)?;")]
        ///
        /// assert_eq!((pos, false), pos.overflowing_abs());
        /// assert_eq!((pos, false), neg.overflowing_abs());
        /// assert_eq!((min, true), min.overflowing_abs());
        /// # Some(())
        /// # }
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        pub const fn overflowing_abs(self) -> (Self, bool) {
            let (nn, flag) = self.get().overflowing_abs();
            (
                match Self::new(nn) {
                    Some(out) => out,
                    None => panic!("Result of overflowing absolute was N"),
                },
                flag,
            )
        }

        /// Saturating absolute value, see
        #[doc = concat!("[`", stringify!($Int), "::saturating_abs`].")]
        ///
        /// # Example
        ///
        /// ```
        #[doc = concat!("# use nonn::", stringify!($Ty), ";")]
        /// # fn main() { test().unwrap(); }
        /// # fn test() -> Option<()> {
        #[doc = concat!("let pos = ", stringify!($Ty), "::<42>::new(1)?;")]
        #[doc = concat!("let neg = ", stringify!($Ty), "::<42>::new(-1)?;")]
        #[doc = concat!("let min = ", stringify!($Ty), "::<42>::new(",
                                                                stringify!($Int), "::MIN)?;")]
        #[doc = concat!("let min_plus = ", stringify!($Ty), "::<42>::new(",
                                                                stringify!($Int), "::MIN + 1)?;")]
        #[doc = concat!("let max = ", stringify!($Ty), "::<42>::new(",
                                                                stringify!($Int), "::MAX)?;")]
        ///
        /// assert_eq!(pos, pos.saturating_abs());
        /// assert_eq!(pos, neg.saturating_abs());
        /// assert_eq!(max, min.saturating_abs());
        /// assert_eq!(max, min_plus.saturating_abs());
        /// # Some(())
        /// # }
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        pub const fn saturating_abs(self) -> Self {
            match Self::new(self.get().saturating_abs()) {
                Some(out) => out,
                None => panic!("Result of saturating absolute was N"),
            }
        }

        /// Wrapping absolute value, see
        #[doc = concat!("[`", stringify!($Int), "::wrapping_abs`].")]
        ///
        /// # Example
        ///
        /// ```
        #[doc = concat!("# use nonn::", stringify!($Ty), ";")]
        /// # fn main() { test().unwrap(); }
        /// # fn test() -> Option<()> {
        #[doc = concat!("let pos = ", stringify!($Ty), "::<42>::new(1)?;")]
        #[doc = concat!("let neg = ", stringify!($Ty), "::<42>::new(-1)?;")]
        #[doc = concat!("let min = ", stringify!($Ty), "::<42>::new(",
                                                                stringify!($Int), "::MIN)?;")]
        #[doc = concat!("# let max = ", stringify!($Ty), "::<42>::new(",
                                                                stringify!($Int), "::MAX)?;")]
        ///
        /// assert_eq!(pos, pos.wrapping_abs());
        /// assert_eq!(pos, neg.wrapping_abs());
        /// assert_eq!(min, min.wrapping_abs());
        /// # Some(())
        /// # }
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        pub const fn wrapping_abs(self) -> Self {
            match Self::new(self.get().wrapping_abs()) {
                Some(out) => out,
                None => panic!("Result of wrapping absolute was N"),
            }
        }

        /// Returns `true` if `self` is positive and `false` if the
        /// number is negative.
        ///
        /// # Example
        ///
        /// ```
        #[doc = concat!("# use nonn::", stringify!($Ty), ";")]
        #[doc = concat!("let pos_five = ", stringify!($Ty), "::<42>::new(5).unwrap();")]
        #[doc = concat!("let neg_five = ", stringify!($Ty), "::<42>::new(-5).unwrap();")]
        ///
        /// assert!(pos_five.is_positive());
        /// assert!(!neg_five.is_positive());
        /// ```
        #[must_use]
        #[inline]
        pub const fn is_positive(self) -> bool {
            self.get().is_positive()
        }

        /// Returns `true` if `self` is negative and `false` if the
        /// number is positive.
        ///
        /// # Example
        ///
        /// ```
        #[doc = concat!("# use nonn::", stringify!($Ty), ";")]
        /// # fn main() { test().unwrap(); }
        /// # fn test() -> Option<()> {
        #[doc = concat!("let pos_five = ", stringify!($Ty), "::<42>::new(5)?;")]
        #[doc = concat!("let neg_five = ", stringify!($Ty), "::<42>::new(-5)?;")]
        ///
        /// assert!(neg_five.is_negative());
        /// assert!(!pos_five.is_negative());
        /// # Some(())
        /// # }
        /// ```
        #[must_use]
        #[inline]
        pub const fn is_negative(self) -> bool {
            self.get().is_negative()
        }

        /// Checked negation. Computes `-self`,
        #[doc = concat!("returning `None` if `self == ", stringify!($Ty), "::MIN`.")]
        ///
        /// # Example
        ///
        /// ```
        #[doc = concat!("# use nonn::", stringify!($Ty), ";")]
        /// # fn main() { test().unwrap(); }
        /// # fn test() -> Option<()> {
        #[doc = concat!("let pos_five = ", stringify!($Ty), "::<42>::new(5)?;")]
        #[doc = concat!("let neg_five = ", stringify!($Ty), "::<42>::new(-5)?;")]
        #[doc = concat!("let min = ", stringify!($Ty), "::<42>::new(",
                                                                stringify!($Int), "::MIN)?;")]
        ///
        /// assert_eq!(pos_five.checked_neg(), Some(neg_five));
        /// assert_eq!(min.checked_neg(), None);
        /// # Some(())
        /// # }
        /// ```
        #[inline]
        pub const fn checked_neg(self) -> Option<Self> {
            if let Some(result) = self.get().checked_neg() {
                return match Self::new(result) {
                    out @ Some(..) => out,
                    None => panic!("Result of checked negation was N"),
                };
            }
            None
        }

        /// Negates self, overflowing if this is equal to the minimum value.
        ///
        #[doc = concat!("See [`", stringify!($Int), "::overflowing_neg`]")]
        /// for documentation on overflow behaviour.
        ///
        /// # Example
        ///
        /// ```
        #[doc = concat!("# use nonn::", stringify!($Ty), ";")]
        /// # fn main() { test().unwrap(); }
        /// # fn test() -> Option<()> {
        #[doc = concat!("let pos_five = ", stringify!($Ty), "::<42>::new(5)?;")]
        #[doc = concat!("let neg_five = ", stringify!($Ty), "::<42>::new(-5)?;")]
        #[doc = concat!("let min = ", stringify!($Ty), "::<42>::new(",
                                                                stringify!($Int), "::MIN)?;")]
        ///
        /// assert_eq!(pos_five.overflowing_neg(), (neg_five, false));
        /// assert_eq!(min.overflowing_neg(), (min, true));
        /// # Some(())
        /// # }
        /// ```
        #[inline]
        pub const fn overflowing_neg(self) -> (Self, bool) {
            let (result, overflow) = self.get().overflowing_neg();

            match Self::new(result) {
                Some(out) => (out, overflow),
                None => panic!("Result of overflowing negation was N"),
            }
        }

        /// Saturating negation. Computes `-self`,
        #[doc = concat!("returning [`", stringify!($Ty), "::<42>::MAX`]")]
        #[doc = concat!("if `self == ", stringify!($Ty), "::<42>::MIN`")]
        /// instead of overflowing.
        ///
        /// # Example
        ///
        /// ```
        #[doc = concat!("# use nonn::", stringify!($Ty), ";")]
        /// # fn main() { test().unwrap(); }
        /// # fn test() -> Option<()> {
        #[doc = concat!("let pos_five = ", stringify!($Ty), "::<42>::new(5)?;")]
        #[doc = concat!("let neg_five = ", stringify!($Ty), "::<42>::new(-5)?;")]
        #[doc = concat!("let min = ", stringify!($Ty), "::<42>::new(",
                                                                stringify!($Int), "::MIN)?;")]
        #[doc = concat!("let min_plus_one = ", stringify!($Ty), "::<42>::new(",
                                                                stringify!($Int), "::MIN + 1)?;")]
        #[doc = concat!("let max = ", stringify!($Ty), "::<42>::new(",
                                                                stringify!($Int), "::MAX)?;")]
        ///
        /// assert_eq!(pos_five.saturating_neg(), neg_five);
        /// assert_eq!(min.saturating_neg(), max);
        /// assert_eq!(max.saturating_neg(), min_plus_one);
        /// # Some(())
        /// # }
        /// ```
        #[inline]
        pub const fn saturating_neg(self) -> Self {
            if let Some(result) = self.checked_neg() {
                return result;
            }
            Self::MAX
        }

        /// Wrapping (modular) negation. Computes `-self`, wrapping around at the boundary
        /// of the type.
        ///
        #[doc = concat!("See [`", stringify!($Int), "::wrapping_neg`]")]
        /// for documentation on overflow behaviour.
        ///
        /// # Example
        ///
        /// ```
        #[doc = concat!("# use nonn::", stringify!($Ty), ";")]
        /// # fn main() { test().unwrap(); }
        /// # fn test() -> Option<()> {
        #[doc = concat!("let pos_five = ", stringify!($Ty), "::<42>::new(5)?;")]
        #[doc = concat!("let neg_five = ", stringify!($Ty), "::<42>::new(-5)?;")]
        #[doc = concat!("let min = ", stringify!($Ty), "::<42>::new(",
                                                                stringify!($Int), "::MIN)?;")]
        ///
        /// assert_eq!(pos_five.wrapping_neg(), neg_five);
        /// assert_eq!(min.wrapping_neg(), min);
        /// # Some(())
        /// # }
        /// ```
        #[inline]
        pub const fn wrapping_neg(self) -> Self {
            let result = self.get().wrapping_neg();
            match Self::new(result) {
                Some(out) => out,
                None => panic!("Result of wrapping negation was N"),
            }
        }
    };
}

// A bunch of methods for both signed and unsigned nonn types.
macro_rules! nonn_unsigned_signed_operations {
    ( $signedness:ident $Ty: ident<$Int: ident>($NonZero: ident) ) => {
        /// Multiplies two non-N integers together.
        /// Checks for overflow and returns [`None`] on overflow.
        ///
        /// # Examples
        ///
        /// ```
        #[doc = concat!("# use nonn::", stringify!($Ty), ";")]
        #[doc = concat!("let two = ", stringify!($Ty), "::<42>::new(2).unwrap();")]
        #[doc = concat!("let four = ", stringify!($Ty), "::<42>::new(4).unwrap();")]
        #[doc = concat!("let max = ", stringify!($Ty), "::<42>::new(",
                                        stringify!($Int), "::MAX).unwrap();")]
        ///
        /// assert_eq!(Some(four), two.checked_mul(two));
        /// assert_eq!(None, max.checked_mul(two));
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        pub const fn checked_mul(self, other: Self) -> Option<Self> {
            if let Some(result) = self.get().checked_mul(other.get()) {
                match Self::new(result) {
                    out @ Some(..) => out,
                    None => panic!("Result of checked multiplication was N"),
                }
            } else {
                None
            }
        }

        /// Multiplies two non-N integers together.
        #[doc = concat!("Return [`", stringify!($Ty), "::<42>::MAX`] on overflow.")]
        ///
        /// # Examples
        ///
        /// ```
        #[doc = concat!("# use nonn::", stringify!($Ty), ";")]
        /// # fn main() { test().unwrap(); }
        /// # fn test() -> Option<()> {
        #[doc = concat!("let two = ", stringify!($Ty), "::<42>::new(2)?;")]
        #[doc = concat!("let four = ", stringify!($Ty), "::<42>::new(4)?;")]
        #[doc = concat!("let max = ", stringify!($Ty), "::<42>::new(",
                                        stringify!($Int), "::MAX)?;")]
        ///
        /// assert_eq!(four, two.saturating_mul(two));
        /// assert_eq!(max, four.saturating_mul(max));
        /// # Some(())
        /// # }
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        pub const fn saturating_mul(self, other: Self) -> Self {
            match Self::new(self.get().saturating_mul(other.get())) {
                Some(out) => out,
                None => panic!("Result of saturating multiplication was N"),
            }
        }

        /// Multiplies two non-N integers together,
        /// assuming overflow cannot occur.
        /// Overflow is unchecked, and it is undefined behaviour to overflow
        /// *even if the result would wrap to a non-N value*.
        /// The behaviour is undefined as soon as
        #[doc = sign_dependent_expr!{
                            $signedness ?
                            if signed {
                                concat!("`self * rhs > ", stringify!($Int), "::MAX`, ",
                                        "or `self * rhs < ", stringify!($Int), "::MIN`.")
                            } else {
                                concat!("`self * rhs > ", stringify!($Int), "::MAX`.")
                            }
                        }]

        /// Raises non-N value to an integer power.
        /// Checks for overflow and returns [`None`] on overflow.
        ///
        /// # Examples
        ///
        /// ```
        #[doc = concat!("# use nonn::", stringify!($Ty), ";")]
        /// # fn main() { test().unwrap(); }
        /// # fn test() -> Option<()> {
        #[doc = concat!("let three = ", stringify!($Ty), "::<42>::new(3)?;")]
        #[doc = concat!("let twenty_seven = ", stringify!($Ty), "::<42>::new(27)?;")]
        #[doc = concat!("let half_max = ", stringify!($Ty), "::<42>::new(",
                                        stringify!($Int), "::MAX / 2)?;")]
        ///
        /// assert_eq!(Some(twenty_seven), three.checked_pow(3));
        /// assert_eq!(None, half_max.checked_pow(3));
        /// # Some(())
        /// # }
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        pub const fn checked_pow(self, other: u32) -> Option<Self> {
            if let Some(result) = self.get().checked_pow(other) {
                match Self::new(result) {
                    out @ Some(..) => out,
                    None => panic!("Result of checked power was N"),
                }
            } else {
                None
            }
        }

        /// Raise non-N value to an integer power.
        #[doc = sign_dependent_expr!{
                            $signedness ?
                            if signed {
                                concat!("Return [`", stringify!($Ty), "::<42>::MIN`] ",
                                            "or [`", stringify!($Ty), "::<42>::MAX`] on overflow.")
                            } else {
                                concat!("Return [`", stringify!($Ty), "::<42>::MAX`] on overflow.")
                            }
                        }]
        ///
        /// # Examples
        ///
        /// ```
        #[doc = concat!("# use nonn::", stringify!($Ty), ";")]
        /// # fn main() { test().unwrap(); }
        /// # fn test() -> Option<()> {
        #[doc = concat!("let three = ", stringify!($Ty), "::<42>::new(3)?;")]
        #[doc = concat!("let twenty_seven = ", stringify!($Ty), "::<42>::new(27)?;")]
        #[doc = concat!("let max = ", stringify!($Ty), "::<42>::new(",
                                        stringify!($Int), "::MAX)?;")]
        ///
        /// assert_eq!(twenty_seven, three.saturating_pow(3));
        /// assert_eq!(max, max.saturating_pow(3));
        /// # Some(())
        /// # }
        /// ```
        #[must_use = "this returns the result of the operation, \
                      without modifying the original"]
        #[inline]
        pub const fn saturating_pow(self, other: u32) -> Self {
            match Self::new(self.get().saturating_pow(other)) {
                Some(out) => out,
                None => panic!("Result of saturating power was N"),
            }
        }
    };
}

macro_rules! sign_dependent_expr {
    (signed ? if signed { $signed_case:expr } $(else { $unsigned_case:expr })? ) => {
        $signed_case
    };
    (unsigned ? if signed { $signed_case:expr } $(else { $unsigned_case:expr })? ) => {
        $($unsigned_case)?
    };
    (signed ? if unsigned { $unsigned_case:expr } $(else { $signed_case:expr })? ) => {
        $($signed_case)?
    };
    (unsigned ? if unsigned { $unsigned_case:expr } $(else { $signed_case:expr })? ) => {
        $unsigned_case
    };
}

macro_rules! sign_dependent_items {
    (signed ? if signed { $($signed_case:item)* } $(else { $($unsigned_case:item)* })? ) => {
        $($signed_case)*
    };
    (unsigned ? if signed { $($signed_case:item)* } $(else { $($unsigned_case:item)* })? ) => {
        $($($unsigned_case)*)?
    };
    (signed ? if unsigned { $($unsigned_case:item)* } $(else { $($signed_case:item)* })? ) => {
        $($($signed_case)*)?
    };
    (unsigned ? if unsigned { $($unsigned_case:item)* } $(else { $($signed_case:item)* })? ) => {
        $($unsigned_case)*
    };
}

macro_rules! nonn_impl {
    [$($signedness: ident $Ty: ident<$Int: ident: $Size: literal>($NonZero: ident)),*$(,)?] => {$(
        #[doc = concat!($Size, " ", stringify!($signedness), " integer type that is known not to equal to any single value N.")]
        ///
        /// This enables some memory layout optimization.
        #[doc = concat!("For example, `Option<", stringify!($Ty), "<N>>` is the same size as `", stringify!($Int), "`:")]
        ///
        /// ```rust
        #[doc = concat!("# use nonn::", stringify!($Ty), ";")]
        /// use std::mem::size_of;
        #[doc = concat!("assert_eq!(size_of::<Option<", stringify!($Ty), "<42>>>(), size_of::<", stringify!($Int), ">());")]
        /// ```
        ///
        /// # Layout
        ///
        #[doc = concat!("`", stringify!($Ty), "\\<N>` is guaranteed to have the same layout and bit validity as `", stringify!($Int), "`")]
        /// with the exception that N is not a valid instance.
        #[doc = concat!("`Option<", stringify!($Ty), ">` is guaranteed to be compatible with `", stringify!($Int), "`,")]
        /// including in FFI.
        ///
        #[doc = concat!("Note that this does not mean you can transmute this type to get a `", stringify!($Int), "` of the same value.")]
        #[doc = concat!("If you need an `", stringify!($Int), "` of the same value, use [`", stringify!($Ty), "::get`] instead.")]
        #[derive(Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Hash)]
        #[repr(transparent)]
        pub struct $Ty<const N: $Int>(::core::num::$NonZero);

        impl<const N: $Int> $Ty<N> {
            /// The smallest value that can be represented by this non-N
            /// integer type.
            pub const MIN: Self = if N == <$Int>::MIN {
                unsafe { Self::new_unchecked(<$Int>::MIN + 1) }
            } else {
                unsafe { Self::new_unchecked(<$Int>::MIN) }
            };

            /// The largest value that can be represented by this non-N
            /// integer type.
            pub const MAX: Self = if N == <$Int>::MAX {
                unsafe { Self::new_unchecked(<$Int>::MAX - 1) }
            } else {
                unsafe { Self::new_unchecked(<$Int>::MAX) }
            };

            /// The size of this non-N integer type in bits.
            ///
            #[doc = concat!("This value is equal to [`", stringify!($Int), "::BITS`].")]
            ///
            /// # Examples
            ///
            /// ```
            #[doc = concat!("# use nonn::", stringify!($Ty), ";")]
            ///
            #[doc = concat!("assert_eq!(", stringify!($Ty), "::<42>::BITS, ", stringify!($Int), "::BITS);")]
            /// ```
            pub const BITS: u32 = <$Int>::BITS;

            /// Creates a non-N if the given value is not N.
            #[must_use]
            #[inline]
            pub const fn new(n: $Int) -> Option<Self> {
                match <::core::num::$NonZero>::new(n ^ N) {
                    Some(inner) => Some(Self(inner)),
                    None => None,
                }
            }

            #[doc = concat!("Creates a ", stringify!($Ty), "\\<N> without checking whether the value is non-N.")]
            /// This results in undefined behaviour if the value is N.
            ///
            /// # Safety
            ///
            /// The value must not be N.
            #[must_use]
            #[inline]
            pub const unsafe fn new_unchecked(n: $Int) -> Self {
                Self(::core::num::$NonZero::new_unchecked(n ^ N))
            }

            /// Returns the value as a primitive type.
            #[inline]
            pub const fn get(self) -> $Int {
                self.0.get() ^ N
            }

            #[doc = concat!("Returns a new ", stringify!($Ty), "\\<M> with the current value if it is not M.")]
            #[must_use]
            #[inline]
            pub const fn cast<const M: $Int>(self) -> Option<$Ty<M>> {
                $Ty::<M>::new(self.get())
            }

            #[doc = concat!("Returns a new ", stringify!($Ty), "\\<M> with the current value without checking whether it is not M.")]
            /// This results in undefined behaviour if the current value is M.
            ///
            /// # Safety
            ///
            /// The current value must not be M.
            #[must_use]
            #[inline]
            pub const unsafe fn cast_unchecked<const M: $Int>(self) -> $Ty<M> {
                $Ty::<M>::new_unchecked(self.get())
            }

            /// Returns the number of leading zeros in the binary representation of `self`.
            ///
            /// # Examples
            ///
            /// Basic usage:
            ///
            /// ```
            #[doc = concat!("# use nonn::", stringify!($Ty), ";")]
            #[doc = concat!("let n = ", stringify!($Ty), "::<42>::new(", sign_dependent_expr!($signedness ?
                if signed {
                    concat!("-1", stringify!($Int))
                } else {
                    concat!(stringify!($Int), "::MAX")
                }),
                ").unwrap();")]
            ///
            /// assert_eq!(n.leading_zeros(), 0);
            /// ```
            #[must_use = "this returns the result of the operation, \
            without modifying the original"]
            #[inline]
            pub const fn leading_zeros(self) -> u32 {
                self.get().leading_zeros()
            }

            /// Returns the number of trailing zeros in the binary representation
            /// of `self`.
            ///
            /// # Examples
            ///
            /// Basic usage:
            ///
            /// ```
            #[doc = concat!("# use nonn::", stringify!($Ty), ";")]
            #[doc = concat!("let n = ", stringify!($Ty), "::<42>::new(0b0101000).unwrap();")]
            ///
            /// assert_eq!(n.trailing_zeros(), 3);
            /// ```
            #[must_use = "this returns the result of the operation, \
            without modifying the original"]
            #[inline]
            pub const fn trailing_zeros(self) -> u32 {
                self.get().trailing_zeros()
            }

            nonn_unsigned_signed_operations!($signedness $Ty<$Int>($NonZero));

            sign_dependent_items!($signedness ? if signed {
                nonn_signed_operations!($Ty<$Int>($NonZero));
            } else {
                /// Returns `true` if and only if `self == (1 << k)` for some `k`.
                ///
                /// # Examples
                ///
                /// Basic usage:
                ///
                /// ```
                #[doc = concat!("# use nonn::", stringify!($Ty), ";")]
                #[doc = concat!("let eight = ", stringify!($Ty), "::<42>::new(8).unwrap();")]
                /// assert!(eight.is_power_of_two());
                #[doc = concat!("let ten = ", stringify!($Ty), "::<42>::new(10).unwrap();")]
                /// assert!(!ten.is_power_of_two());
                /// ```
                #[must_use]
                #[inline]
                pub const fn is_power_of_two(self) -> bool {
                    self.get().is_power_of_two()
                }

                nonn_unsigned_operations!($Ty<$Int>($NonZero));
            });
        }

        impl<const N: $Int> From<$Ty<N>> for $Int {
            #[doc = concat!("Converts a `", stringify!($Ty), "` into an `", stringify!($Int), "`")]
            #[inline]
            fn from(nonn: $Ty<N>) -> Self {
                nonn.0.get()
            }
        }

        impl<const N: $Int, const M: $Int> BitOr<$Ty<M>> for $Ty<N> {
            type Output = Self;

            #[inline]
            fn bitor(self, rhs: $Ty<M>) -> Self::Output {
                match Self::new(self.get() | rhs.get()) {
                    Some(out) => out,
                    None => panic!("Result of bitwise or was N"),
                }
            }
        }

        impl<const N: $Int> BitOr<$Int> for $Ty<N> {
            type Output = Self;

            #[inline]
            fn bitor(self, rhs: $Int) -> Self::Output {
                match Self::Output::new(self.get() | rhs) {
                    Some(out) => out,
                    None => panic!("Result of bitwise or was N"),
                }
            }
        }

        impl<const N: $Int, const M: $Int> BitOrAssign<$Ty<M>> for $Ty<N> {
            #[inline]
            fn bitor_assign(&mut self, rhs: $Ty<M>) {
                *self = *self | rhs;
            }
        }

        impl<const N: $Int> BitOrAssign<$Int> for $Ty<N> {
            #[inline]
            fn bitor_assign(&mut self, rhs: $Int) {
                *self = *self | rhs;
            }
        }

        impl<const N: $Int, const M: $Int> BitAnd<$Ty<M>> for $Ty<N> {
            type Output = Self;

            #[inline]
            fn bitand(self, rhs: $Ty<M>) -> Self::Output {
                match Self::new(self.get() & rhs.get()) {
                    Some(out) => out,
                    None => panic!("Result of bitwise and was N"),
                }
            }
        }

        impl<const N: $Int> BitAnd<$Int> for $Ty<N> {
            type Output = Self;

            #[inline]
            fn bitand(self, rhs: $Int) -> Self::Output {
                match Self::Output::new(self.get() & rhs) {
                    Some(out) => out,
                    None => panic!("Result of bitwise and was N"),
                }
            }
        }

        impl<const N: $Int, const M: $Int> BitAndAssign<$Ty<M>> for $Ty<N> {
            #[inline]
            fn bitand_assign(&mut self, rhs: $Ty<M>) {
                *self = *self & rhs;
            }
        }

        impl<const N: $Int> BitAndAssign<$Int> for $Ty<N> {
            #[inline]
            fn bitand_assign(&mut self, rhs: $Int) {
                *self = *self & rhs;
            }
        }

        impl<const N: $Int, const M: $Int> BitXor<$Ty<M>> for $Ty<N> {
            type Output = Self;

            #[inline]
            fn bitxor(self, rhs: $Ty<M>) -> Self::Output {
                match Self::new(self.get() ^ rhs.get()) {
                    Some(out) => out,
                    None => panic!("Result of bitwise xor was N"),
                }
            }
        }

        impl<const N: $Int> BitXor<$Int> for $Ty<N> {
            type Output = Self;

            #[inline]
            fn bitxor(self, rhs: $Int) -> Self::Output {
                match Self::Output::new(self.get() ^ rhs) {
                    Some(out) => out,
                    None => panic!("Result of bitwise xor was N"),
                }
            }
        }

        impl<const N: $Int, const M: $Int> BitXorAssign<$Ty<M>> for $Ty<N> {
            #[inline]
            fn bitxor_assign(&mut self, rhs: $Ty<M>) {
                *self = *self ^ rhs;
            }
        }

        impl<const N: $Int> BitXorAssign<$Int> for $Ty<N> {
            #[inline]
            fn bitxor_assign(&mut self, rhs: $Int) {
                *self = *self ^ rhs;
            }
        }

        impl<const N: $Int, const M: $Int> Add<$Ty<M>> for $Ty<N> {
            type Output = Self;

            #[inline]
            fn add(self, rhs: $Ty<M>) -> Self::Output {
                match Self::new(self.get() + rhs.get()) {
                    Some(out) => out,
                    None => panic!("Result of addition was N"),
                }
            }
        }

        impl<const N: $Int> Add<$Int> for $Ty<N> {
            type Output = Self;

            #[inline]
            fn add(self, rhs: $Int) -> Self::Output {
                match Self::Output::new(self.get() + rhs) {
                    Some(out) => out,
                    None => panic!("Result of addition was N"),
                }
            }
        }

        impl<const N: $Int, const M: $Int> AddAssign<$Ty<M>> for $Ty<N> {
            #[inline]
            fn add_assign(&mut self, rhs: $Ty<M>) {
                *self = *self + rhs;
            }
        }

        impl<const N: $Int> AddAssign<$Int> for $Ty<N> {
            #[inline]
            fn add_assign(&mut self, rhs: $Int) {
                *self = *self + rhs;
            }
        }

        impl<const N: $Int, const M: $Int> Sub<$Ty<M>> for $Ty<N> {
            type Output = Self;

            #[inline]
            fn sub(self, rhs: $Ty<M>) -> Self::Output {
                match Self::new(self.get() - rhs.get()) {
                    Some(out) => out,
                    None => panic!("Result of subtraction was N"),
                }
            }
        }

        impl<const N: $Int> Sub<$Int> for $Ty<N> {
            type Output = Self;

            #[inline]
            fn sub(self, rhs: $Int) -> Self::Output {
                match Self::Output::new(self.get() - rhs) {
                    Some(out) => out,
                    None => panic!("Result of subtraction was N"),
                }
            }
        }

        impl<const N: $Int, const M: $Int> SubAssign<$Ty<M>> for $Ty<N> {
            #[inline]
            fn sub_assign(&mut self, rhs: $Ty<M>) {
                *self = *self - rhs;
            }
        }

        impl<const N: $Int> SubAssign<$Int> for $Ty<N> {
            #[inline]
            fn sub_assign(&mut self, rhs: $Int) {
                *self = *self - rhs;
            }
        }

        impl<const N: $Int, const M: $Int> Mul<$Ty<M>> for $Ty<N> {
            type Output = Self;

            #[inline]
            fn mul(self, rhs: $Ty<M>) -> Self::Output {
                match Self::new(self.get() * rhs.get()) {
                    Some(out) => out,
                    None => panic!("Result of multiplication was N"),
                }
            }
        }

        impl<const N: $Int> Mul<$Int> for $Ty<N> {
            type Output = Self;

            #[inline]
            fn mul(self, rhs: $Int) -> Self::Output {
                match Self::Output::new(self.get() * rhs) {
                    Some(out) => out,
                    None => panic!("Result of multiplication was N"),
                }
            }
        }

        impl<const N: $Int, const M: $Int> MulAssign<$Ty<M>> for $Ty<N> {
            #[inline]
            fn mul_assign(&mut self, rhs: $Ty<M>) {
                *self = *self * rhs;
            }
        }

        impl<const N: $Int> MulAssign<$Int> for $Ty<N> {
            #[inline]
            fn mul_assign(&mut self, rhs: $Int) {
                *self = *self * rhs;
            }
        }

        impl<const N: $Int, const M: $Int> Div<$Ty<M>> for $Ty<N> {
            type Output = Self;

            #[inline]
            fn div(self, rhs: $Ty<M>) -> Self::Output {
                match Self::new(self.get() / rhs.get()) {
                    Some(out) => out,
                    None => panic!("Result of division was N"),
                }
            }
        }

        impl<const N: $Int> Div<$Int> for $Ty<N> {
            type Output = Self;

            #[inline]
            fn div(self, rhs: $Int) -> Self::Output {
                match Self::Output::new(self.get() / rhs) {
                    Some(out) => out,
                    None => panic!("Result of division was N"),
                }
            }
        }

        impl<const N: $Int, const M: $Int> DivAssign<$Ty<M>> for $Ty<N> {
            #[inline]
            fn div_assign(&mut self, rhs: $Ty<M>) {
                *self = *self / rhs;
            }
        }

        impl<const N: $Int> DivAssign<$Int> for $Ty<N> {
            #[inline]
            fn div_assign(&mut self, rhs: $Int) {
                *self = *self / rhs;
            }
        }

        impl<const N: $Int, const M: $Int> Rem<$Ty<M>> for $Ty<N> {
            type Output = Self;

            #[inline]
            fn rem(self, rhs: $Ty<M>) -> Self::Output {
                match Self::new(self.get() % rhs.get()) {
                    Some(out) => out,
                    None => panic!("Result of remainder was N"),
                }
            }
        }

        impl<const N: $Int> Rem<$Int> for $Ty<N> {
            type Output = Self;

            #[inline]
            fn rem(self, rhs: $Int) -> Self::Output {
                match Self::Output::new(self.get() % rhs) {
                    Some(out) => out,
                    None => panic!("Result of remainder was N"),
                }
            }
        }

        impl<const N: $Int, const M: $Int> RemAssign<$Ty<M>> for $Ty<N> {
            #[inline]
            fn rem_assign(&mut self, rhs: $Ty<M>) {
                *self = *self % rhs;
            }
        }

        impl<const N: $Int> RemAssign<$Int> for $Ty<N> {
            #[inline]
            fn rem_assign(&mut self, rhs: $Int) {
                *self = *self % rhs;
            }
        }

        impl<const N: $Int> Not for $Ty<N> {
            type Output = Self;

            #[inline]
            fn not(self) -> Self::Output {
                match Self::Output::new(!self.get()) {
                    Some(out) => out,
                    None => panic!("Result of not was N"),
                }
            }
        }

        impl<const N: $Int, const M: $Int> Shl<$Ty<M>> for $Ty<N> {
            type Output = Self;

            #[inline]
            fn shl(self, rhs: $Ty<M>) -> Self::Output {
                match Self::new(self.get() << rhs.get()) {
                    Some(out) => out,
                    None => panic!("Result of shlition was N"),
                }
            }
        }

        impl<const N: $Int> Shl<$Int> for $Ty<N> {
            type Output = Self;

            #[inline]
            fn shl(self, rhs: $Int) -> Self::Output {
                match Self::Output::new(self.get() << rhs) {
                    Some(out) => out,
                    None => panic!("Result of shlition was N"),
                }
            }
        }

        impl<const N: $Int, const M: $Int> ShlAssign<$Ty<M>> for $Ty<N> {
            #[inline]
            fn shl_assign(&mut self, rhs: $Ty<M>) {
                *self = *self << rhs;
            }
        }

        impl<const N: $Int> ShlAssign<$Int> for $Ty<N> {
            #[inline]
            fn shl_assign(&mut self, rhs: $Int) {
                *self = *self << rhs;
            }
        }

        impl<const N: $Int, const M: $Int> Shr<$Ty<M>> for $Ty<N> {
            type Output = Self;

            #[inline]
            fn shr(self, rhs: $Ty<M>) -> Self::Output {
                match Self::new(self.get() >> rhs.get()) {
                    Some(out) => out,
                    None => panic!("Result of shrition was N"),
                }
            }
        }

        impl<const N: $Int> Shr<$Int> for $Ty<N> {
            type Output = Self;

            #[inline]
            fn shr(self, rhs: $Int) -> Self::Output {
                match Self::Output::new(self.get() >> rhs) {
                    Some(out) => out,
                    None => panic!("Result of shrition was N"),
                }
            }
        }

        impl<const N: $Int, const M: $Int> ShrAssign<$Ty<M>> for $Ty<N> {
            #[inline]
            fn shr_assign(&mut self, rhs: $Ty<M>) {
                *self = *self >> rhs;
            }
        }

        impl<const N: $Int> ShrAssign<$Int> for $Ty<N> {
            #[inline]
            fn shr_assign(&mut self, rhs: $Int) {
                *self = *self >> rhs;
            }
        }

        impl<const N: $Int> FromStr for $Ty<N> {
            type Err = ParseIntError;

            fn from_str(src: &str) -> Result<Self, Self::Err> {
                ::core::num::$NonZero::from_str(src).map(|non_zero| Self(non_zero))
            }
        }

        impl_nonn_fmt! {
            (Debug, Display, Binary, Octal, LowerHex, UpperHex) for $Ty<$Int>($NonZero)
        }
    )*};
}

nonn_impl![
    unsigned NonNU8<u8: "8-bit">(NonZeroU8),
    unsigned NonNU16<u16: "16-bit">(NonZeroU16),
    unsigned NonNU32<u32: "32-bit">(NonZeroU32),
    unsigned NonNU64<u64: "64-bit">(NonZeroU64),
    unsigned NonNU128<u128: "128-bit">(NonZeroU128),
    unsigned NonNUsize<usize: "Pointer-sized">(NonZeroUsize),
    signed NonNI8<i8: "8-bit">(NonZeroI8),
    signed NonNI16<i16: "16-bit">(NonZeroI16),
    signed NonNI32<i32: "32-bit">(NonZeroI32),
    signed NonNI64<i64: "64-bit">(NonZeroI64),
    signed NonNI128<i128: "128-bit">(NonZeroI128),
    signed NonNIsize<isize: "Pointer-sized">(NonZeroIsize),
];
