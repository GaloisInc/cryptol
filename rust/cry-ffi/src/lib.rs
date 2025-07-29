//! Utilities to streamline the process of writing Rust functions that adhere to
//! Cryptol's `abstract` calling convention.
//!
//! # Basic usage
//!
//! Any Rust function intended to be used with the `abstract` calling convention
//! should have the following type signature:
//!
//! ```
//! # use cry_ffi::*;
//! #
//! #[no_mangle]
//! pub extern "C" fn example(args: &CryValExporter, res: &CryValImporter) {
//!     // ...
//! }
//! ```
//!
//! Let's explain this part by part:
//!
//! * `#[no_mangle]`: This ensures that when the code is compiled to a shared
//!   library, the original name of the Rust function will be preserved. This is
//!   important to ensure that Cryptol can look up the function.
//!
//! * `pub extern "C"`: This ensures that the function is exported as an
//!   external function using the C ABI.
//!
//! * The name `example` isn't particularly important, and you can use whatever
//!   name you'd like here. The only requirement is that the corresponding
//!   Cryptol foreign function also have the same name.
//!
//! * The type signature will always contain the argument types
//!   `(args: &CryValExporter, res: &CryValImporter)` and the return type `()`.
//!   This is a requirement imposed by Cryptol's `abstract` calling convention.
//!
//! Note that nothing in the type signature of the Rust function indicates what
//! the type of the corresponding Cryptol `foreign` function is. That
//! information can only be determined by looking at the implementation of the
//! Rust function. Let's look at a fully implemented example to illustrate this
//! point:
//!
//! ```
//! # use cry_ffi::*;
//! #
//! // For a Cryptol function `foreign abstract example : [64] -> [64] -> [64]`
//!
//! #[no_mangle]
//! pub extern "C" fn example(args: &CryValExporter, res: &CryValImporter) {
//!     let x = u64::recv(args);
//!     let y = u64::recv(args);
//!     let z = x + y;
//!     z.send(res);
//! }
//! ```
//!
//! This leverages the [`Exportable`] trait to export the function's first and
//! second arguments (both of type `u64`) from Cryptol to Rust and bind them to the
//! variables `x` and `y`, respectively. It then performs some additional
//! computation on the Rust side (`x + y`) and imports the result (also of type
//! `u64`) back from Rust to Cryptol using the [`Importable`] trait. The calls
//! to `recv` and `send` effectively determine the type of the Cryptol `foreign`
//! function.
//!
//! Refer to the documentation for the [`Exportable`] and [`Importable`] traits
//! for more information, and refer to the implementations of these traits for
//! a list of types that can be marshalled across the FFI boundary.
//!
//! # Compiling for FFI usage
//!
//! Once you have a Rust program that defines functions compatible with the
//! `abstract` calling convention, you should compile the program as a `cdylib`
//! (i.e., as a C-compatible shared library). For `cargo`-based projects, you
//! should add the following line to the target in your `Cargo.toml` that you
//! want to compile to a shared library:
//!
//! ```toml,no_run
//! crate-type = ["cdylib"]
//! ```
//!
//! If you are compiling a Rust file directly with `rustc`, then invoke the
//! compiler like so:
//!
//! ```text,no_run
//! $ rustc --crate-type=cdylib ...
//! ```
//!
//! # Safety
//!
//! All of the functions in this crate encapsulate any unsafe Rust code in safe
//! functions, so most callers will not need to use the `unsafe` keyword. There
//! is still an inherent amount of unsafety in that callers need to adhere to
//! the conventions expected by the Cryptol `abstract` calling convention for a
//! particular `extern` function. There are a number of ways that a user could
//! break these conventions (e.g., defining a function with a type
//! signature that is different from above, exporting a different number of
//! arguments, or exporting/importing different types), all of which could lead
//! to undefined behavior.

#![cfg_attr(not(test), no_std)]
extern crate alloc;

use alloc::boxed::Box;
use alloc::slice::from_raw_parts_mut;
use alloc::vec;
use alloc::vec::Vec;
use core::ffi::*;
use core::mem::{self, MaybeUninit};
use num::{BigInt, BigRational, BigUint, ToPrimitive};
use num::bigint::{Sign, ToBigInt};

/// A macro that is useful for simplifying calls to fields of [`CryValImporter`]
/// or [`CryValExporter`].
///
/// # Examples
///
/// ```rust
/// # use cry_ffi::*;
/// #
/// # #[no_mangle]
/// # pub extern "C" fn example(args: &CryValExporter, res: &CryValImporter) {
///     let mut val: u64 = 0;
///     cry_ffi!(args, recv_u64, &mut val);
///     cry_ffi!(res, send_small_uint, val);
/// # }
/// ```
#[macro_export]
macro_rules! cry_ffi {
    ($object:ident, $method:ident, $arg:expr) => {
        ($object.$method)($object.self_ref, $arg)
    };
}

/// Imports foreign values into Cryptol. This can be used when a foreign
/// function needs to return a result to the Cryptol interpreter.
///
/// Most users will not need to use the fields of this struct directly and can
/// instead use the higher-level [`Importable`] trait.
#[repr(C)]
pub struct CryValImporter<'a> {
    /// This should be passed to all the function pointers. It captures the
    /// current state of the importing process.
    pub self_ref: &'a c_void,

    /// Make a boolean value (`0: false`, `> 0: true`).
    pub send_bool: extern "C" fn(&c_void, u8),

    /// Make an unsigned integer, which fits in a `u64`.
    pub send_small_uint: extern "C" fn(&c_void, u64),

    /// Make an signed integer, which fits in a `i64`.
    pub send_small_sint: extern "C" fn(&c_void, i64),

    /// Make a floating-point value.
    pub send_double: extern "C" fn(&c_void, c_double),

    /// Start building a sum type. The `usize` argument is the number of the
    /// constructor.
    pub send_tag: extern "C" fn(&c_void, usize),

    /// Start building a large integer, which does not fit in a `u64` value. The
    /// `usize` argument is the number of `u64` digits that we need. The result
    /// is a buffer where the digits should be placed, least significant first.
    ///
    /// Note that while most fields in this struct use reference types to more
    /// closely resemble idiomatic Rust code, this field is an exception, as it
    /// returns a raw pointer. An idiomatic Rust function would return a slice
    /// or `Vec` here, but these are not supported in the Rust FFI. As a result,
    /// callers must turn the returned raw pointer into a slice/`Vec` themselves
    /// by combining it with the `usize` argument (e.g., by using the
    /// [`from_raw_parts_mut`] method on slices).
    pub send_new_large_int: extern "C" fn(&c_void, usize) -> *mut u64,

    /// Finish bulding a large integer, which does not fit in a `u64` value. The
    /// `u8` argument is `1` for negative integers and `0` for non-negative
    /// integers.
    pub send_sign: extern "C" fn(&c_void, u8),
}

/// A trait for classifying types that can be imported as foreign values into
/// Cryptol. This should be used when a foreign function needs to return a
/// result to the Cryptol interpreter.
pub trait Importable {
    /// Import a foreign value into Cryptol.
    fn send(&self, res: &CryValImporter);
}

impl Importable for bool {
    fn send(&self, res: &CryValImporter) {
        cry_ffi!(res, send_bool, if *self { 1 } else { 0 });
    }
}

impl Importable for u8 {
    fn send(&self, res: &CryValImporter) {
        cry_ffi!(res, send_small_uint, *self as u64);
    }
}

impl Importable for u16 {
    fn send(&self, res: &CryValImporter) {
        cry_ffi!(res, send_small_uint, *self as u64);
    }
}

impl Importable for u32 {
    fn send(&self, res: &CryValImporter) {
        cry_ffi!(res, send_small_uint, *self as u64);
    }
}

impl Importable for u64 {
    fn send(&self, res: &CryValImporter) {
        cry_ffi!(res, send_small_uint, *self);
    }
}

impl Importable for u128 {
    fn send(&self, res: &CryValImporter) {
        BigInt::from(*self).send(res);
    }
}

impl Importable for i8 {
    fn send(&self, res: &CryValImporter) {
        cry_ffi!(res, send_small_sint, *self as i64);
    }
}

impl Importable for i16 {
    fn send(&self, res: &CryValImporter) {
        cry_ffi!(res, send_small_sint, *self as i64);
    }
}

impl Importable for i32 {
    fn send(&self, res: &CryValImporter) {
        cry_ffi!(res, send_small_sint, *self as i64);
    }
}

impl Importable for i64 {
    fn send(&self, res: &CryValImporter) {
        cry_ffi!(res, send_small_sint, *self);
    }
}

impl Importable for i128 {
    fn send(&self, res: &CryValImporter) {
        BigInt::from(*self).send(res);
    }
}

impl Importable for f32 {
    fn send(&self, res: &CryValImporter) {
        cry_ffi!(res, send_double, *self as f64);
    }
}

impl Importable for f64 {
    fn send(&self, res: &CryValImporter) {
        cry_ffi!(res, send_double, *self);
    }
}

impl Importable for BigInt {
    fn send(&self, res: &CryValImporter) {
        let (sign, send_digits) = self.to_u64_digits();
        let sign_u8: u8 =
            match sign {
                Sign::Minus => 1,
                Sign::NoSign => 0,
                Sign::Plus => 0,
            };
        let size: usize = send_digits.len();
        let recv_digits_ptr: *mut u64 = cry_ffi!(res, send_new_large_int, size);
        let recv_digits: &mut [u64] = unsafe {
            from_raw_parts_mut(recv_digits_ptr, size)
        };
        recv_digits.copy_from_slice(send_digits.as_slice());
        cry_ffi!(res, send_sign, sign_u8);
    }
}

impl Importable for BigUint {
    fn send(&self, res: &CryValImporter) {
        self
          .to_bigint()
          .expect("BigUint cannot be represented as a BigInt value")
          .send(res)
    }
}

impl Importable for BigRational {
    fn send(&self, res: &CryValImporter) {
        self.numer().send(res);
        self.denom().send(res);
    }
}

impl<T: Importable, const N: usize> Importable for [T; N] {
    fn send(&self, res: &CryValImporter) {
        for t in self.iter() {
            t.send(res);
        }
    }
}

impl<T: Importable> Importable for [T] {
    fn send(&self, res: &CryValImporter) {
        for t in self.iter() {
            t.send(res);
        }
    }
}

impl<T: Importable> Importable for Vec<T> {
    fn send(&self, res: &CryValImporter) {
        for t in self.iter() {
            t.send(res);
        }
    }
}

impl<T: Importable> Importable for Option<T> {
    fn send(&self, res: &CryValImporter) {
        match self {
            None => cry_ffi!(res, send_tag, 0),
            Some(t) => {
                cry_ffi!(res, send_tag, 1);
                t.send(res);
            },
        };
    }
}

impl<T: Importable, E: Importable> Importable for Result<T, E> {
    fn send(&self, res: &CryValImporter) {
        match self {
            Ok(t) => {
                cry_ffi!(res, send_tag, 0);
                t.send(res);
            }
            Err(e) => {
                cry_ffi!(res, send_tag, 1);
                e.send(res);
            },
        };
    }
}

/// A macro to automate defining `Importable` instances for tuples. To import a
/// tuple, we import all of its fields from left to right.
macro_rules! importable_tuple {
    ($($idx:tt $t:ident),*) => {
        impl<$($t: Importable),*> Importable for ($($t,)*)
        {
            fn send(&self, _res: &CryValImporter) {
                $(self.$idx.send(_res);)*
            }
        }
    };
}

/*  0 */ importable_tuple!();
/*  1 */ importable_tuple!(0 A);
/*  2 */ importable_tuple!(0 A, 1 B);
/*  3 */ importable_tuple!(0 A, 1 B, 2 C);
/*  4 */ importable_tuple!(0 A, 1 B, 2 C, 3 D);
/*  5 */ importable_tuple!(0 A, 1 B, 2 C, 3 D, 4 E);
/*  6 */ importable_tuple!(0 A, 1 B, 2 C, 3 D, 4 E, 5 F);
/*  7 */ importable_tuple!(0 A, 1 B, 2 C, 3 D, 4 E, 5 F, 6 G);
/*  8 */ importable_tuple!(0 A, 1 B, 2 C, 3 D, 4 E, 5 F, 6 G, 7 H);
/*  9 */ importable_tuple!(0 A, 1 B, 2 C, 3 D, 4 E, 5 F, 6 G, 7 H, 8 I);
/* 10 */ importable_tuple!(0 A, 1 B, 2 C, 3 D, 4 E, 5 F, 6 G, 7 H, 8 I, 9 J);
/* 11 */ importable_tuple!(0 A, 1 B, 2 C, 3 D, 4 E, 5 F, 6 G, 7 H, 8 I, 9 J, 10 K);
/* 12 */ importable_tuple!(0 A, 1 B, 2 C, 3 D, 4 E, 5 F, 6 G, 7 H, 8 I, 9 J, 10 K, 11 L);
/* 13 */ importable_tuple!(0 A, 1 B, 2 C, 3 D, 4 E, 5 F, 6 G, 7 H, 8 I, 9 J, 10 K, 11 L, 12 M);
/* 14 */ importable_tuple!(0 A, 1 B, 2 C, 3 D, 4 E, 5 F, 6 G, 7 H, 8 I, 9 J, 10 K, 11 L, 12 M, 13 N);
/* 15 */ importable_tuple!(0 A, 1 B, 2 C, 3 D, 4 E, 5 F, 6 G, 7 H, 8 I, 9 J, 10 K, 11 L, 12 M, 13 N, 14 O);
/* 16 */ importable_tuple!(0 A, 1 B, 2 C, 3 D, 4 E, 5 F, 6 G, 7 H, 8 I, 9 J, 10 K, 11 L, 12 M, 13 N, 14 O, 15 P);

/// Exports foreign values from Cryptol. This can be used to get a foreign
/// function's arguments from the Cryptol interpreter.
///
/// Most users will not need to use the fields of this struct directly and can
/// instead use the higher-level [`Exportable`] trait.
#[repr(C)]
pub struct CryValExporter<'a> {
    /// This should be passed to all the function pointers. It captures the
    /// current state of the exporting process.
    pub self_ref: &'a c_void,

    /// Export a `u8` value. This is used to represent `Bit`, `[n]` (`n <= 8`),
    /// and `Integer` signs. Returns `0` on success.
    pub recv_u8: extern "C" fn(&c_void, &mut u8) -> u32,

    /// Export a double. Returns `0` on success.
    pub recv_double: extern "C" fn(&c_void, &mut c_double) -> u32,

    /// Export a `u64` value. This is used for getting the size of an `Integer`
    /// or word, `[n]` (`8 < n /\ n <= 64`), and also for the tag of a sum type.
    /// Returns `0` on success.
    pub recv_u64: extern "C" fn(&c_void, &mut u64) -> u32,

    /// Receive the `u64` digits of an `Integer` or a word. These are placed in
    /// the provided `*mut u64` buffer, starting with the least significant one.
    /// The buffer should be big enough to fit the digits. Returns `0` on
    /// success.
    pub recv_u64_digits: extern "C" fn(&c_void, *mut u64) -> u32,
}

/// A trait for classifying types that can be exported as foreign values from
/// Cryptol. This should be used to get a foreign function's arguments from the
/// Cryptol interpreter.
///
/// See also the [`recv_type_param`] function, which exports a numeric type
/// parameter in a polymorphic foreign function.
pub trait Exportable: Sized {
    /// This allows users to constrain the shape of values that are exported.
    /// Many [`Exportable`] impls do not require any additional parameters, so
    /// it is acceptable for these impls to simply define `Parameters = ()`.
    /// (See also `recv`, which exports a value with [`default()`] parameters.)
    /// Other types cannot feasibly be exported with additional information.
    /// For instance, a [`Vec`] value cannot be exported without knowing its
    /// length, so the [`Exportable`] impl for [`Vec`] defines
    /// `Parameters = Len`.
    ///
    /// [`default()`]:
    ///     https://doc.rust-lang.org/nightly/std/default/trait.Default.html
    type Parameters: Clone;

    /// Export a foreign value from Cryptol. Calling `T::recv(args)` is
    /// equivalent to calling `T::recv_with(Default::default(), args)`.
    ///
    /// This method is defined in the trait for optimizing [`default()`]
    /// parameters if you want to do that. It is a logic error to not preserve
    /// the semantics when overriding.
    ///
    /// [`default()`]:
    ///     https://doc.rust-lang.org/nightly/std/default/trait.Default.html
    fn recv(args: &CryValExporter) -> Self
    where
        Self::Parameters: Default,
    {
        Self::recv_with(Default::default(), args)
    }

    /// Export a foreign value from Cryptol using the supplied `Parameters`. If
    /// you wish to use the [`default()`] parameters, use `recv` instead.
    ///
    /// [`default()`]:
    ///     https://doc.rust-lang.org/nightly/std/default/trait.Default.html
    fn recv_with(params: Self::Parameters, args: &CryValExporter) -> Self;
}

/// A newtype around [`usize`] that denotes the length of a collection such as a
/// [`Vec`] or a slice. Unlike [`usize`], [`Len`] intentionally does not
/// implement [`Default`]. This is because [`Len`] is used as a choice of
/// `Parameters` for some [`Exportable`] impls, and the lack of a [`Default`]
/// impl pushes users to think carefully about what length to use when
/// exporting.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Len(pub usize);

/// A newtype around [`usize`] that denotes the number of bits in a numeric
/// type (e.g., the `n` in Cryptol's `[n]` word type). Unlike [`usize`],
/// [`Bits`] intentionally does not implement [`Default`]. This is because
/// [`Bits`] is used as a choice of `Parameters` for some [`Exportable`] impls,
/// and the lack of a [`Default`] impl pushes users to think carefully about
/// what number of bits to use when exporting.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Bits(pub usize);

/// A newtype around [`BigUint`] that denotes the `modulus` of a Cryptol `Z`
/// value. Unlike [`BigUint`], [`Modulus`] intentionally does not implement
/// [`Default`]. This is because [`BigUint`] is used as the choice of
/// `Parameters` for some [`Exportable`] impls, and the lack of a [`Default`]
/// impl pushes users to think carefully about what modulus to use when
/// exporting.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Modulus(pub BigUint);

impl Exportable for bool {
    type Parameters = ();
    fn recv_with(_params: Self::Parameters, args: &CryValExporter) -> Self {
        let mut v: u8 = 0;
        assert!(cry_ffi!(args, recv_u8, &mut v) == 0);
        v != 0
    }
}

impl Exportable for u8 {
    type Parameters = ();
    fn recv_with(_params: Self::Parameters, args: &CryValExporter) -> Self {
        let mut v: u8 = 0;
        assert!(cry_ffi!(args, recv_u8, &mut v) == 0);
        v
    }
}

impl Exportable for u16 {
    type Parameters = ();
    fn recv_with(_params: Self::Parameters, args: &CryValExporter) -> Self {
        let mut v: u64 = 0;
        assert!(cry_ffi!(args, recv_u64, &mut v) == 0);
        v as u16
    }
}

impl Exportable for u32 {
    type Parameters = ();
    fn recv_with(_params: Self::Parameters, args: &CryValExporter) -> Self {
        let mut v: u64 = 0;
        assert!(cry_ffi!(args, recv_u64, &mut v) == 0);
        v as u32
    }
}

impl Exportable for u64 {
    type Parameters = ();
    fn recv_with(_params: Self::Parameters, args: &CryValExporter) -> Self {
        let mut v: u64 = 0;
        assert!(cry_ffi!(args, recv_u64, &mut v) == 0);
        v
    }
}

impl Exportable for u128 {
    type Parameters = ();
    fn recv_with(_params: Self::Parameters, args: &CryValExporter) -> Self {
        let digits: Vec<u32> = recv_integer_size_and_digits(args);
        BigUint::new(digits)
          .to_u128()
          .expect("BigUint cannot be represented as a u128 value")
    }
}

impl Exportable for i8 {
    type Parameters = ();
    fn recv_with(_params: Self::Parameters, args: &CryValExporter) -> Self {
        u8::recv(args) as i8
    }
}

impl Exportable for i16 {
    type Parameters = ();
    fn recv_with(_params: Self::Parameters, args: &CryValExporter) -> Self {
        u16::recv(args) as i16
    }
}

impl Exportable for i32 {
    type Parameters = ();
    fn recv_with(_params: Self::Parameters, args: &CryValExporter) -> Self {
        u32::recv(args) as i32
    }
}

impl Exportable for i64 {
    type Parameters = ();
    fn recv_with(_params: Self::Parameters, args: &CryValExporter) -> Self {
        u64::recv(args) as i64
    }
}

impl Exportable for i128 {
    type Parameters = ();
    fn recv_with(_params: Self::Parameters, args: &CryValExporter) -> Self {
        u128::recv(args) as i128
    }
}

impl Exportable for f32 {
    type Parameters = ();
    fn recv_with(_params: Self::Parameters, args: &CryValExporter) -> Self {
        let mut v: f64 = 0.0;
        assert!(cry_ffi!(args, recv_double, &mut v) == 0);
        v as f32
    }
}

impl Exportable for f64 {
    type Parameters = ();
    fn recv_with(_params: Self::Parameters, args: &CryValExporter) -> Self {
        let mut v: f64 = 0.0;
        assert!(cry_ffi!(args, recv_double, &mut v) == 0);
        v
    }
}

// Taken from num-bigint's unexposed internals

/// An iterator of `u32` digits representation of a `BigUint` or `BigInt`,
/// ordered least significant digit first.
struct U32Digits<'a> {
    data: &'a [u64],
    next_is_lo: bool,
    last_hi_is_zero: bool,
}

impl<'a> U32Digits<'a> {
    #[inline]
    fn new(data: &'a [u64]) -> Self {
        let last_hi_is_zero = data
            .last()
            .map(|&last| {
                let last_hi = (last >> 32) as u32;
                last_hi == 0
            })
            .unwrap_or(false);
        U32Digits {
            data,
            next_is_lo: true,
            last_hi_is_zero,
        }
    }
}

impl Iterator for U32Digits<'_> {
    type Item = u32;
    #[inline]
    fn next(&mut self) -> Option<u32> {
        match self.data.split_first() {
            Some((&first, data)) => {
                let next_is_lo = self.next_is_lo;
                self.next_is_lo = !next_is_lo;
                if next_is_lo {
                    Some(first as u32)
                } else {
                    self.data = data;
                    if data.is_empty() && self.last_hi_is_zero {
                        self.last_hi_is_zero = false;
                        None
                    } else {
                        Some((first >> 32) as u32)
                    }
                }
            }
            None => None,
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.len();
        (len, Some(len))
    }

    #[inline]
    fn last(self) -> Option<u32> {
        self.data.last().map(|&last| {
            if self.last_hi_is_zero {
                last as u32
            } else {
                (last >> 32) as u32
            }
        })
    }

    #[inline]
    fn count(self) -> usize {
        self.len()
    }
}

impl ExactSizeIterator for U32Digits<'_> {
    #[inline]
    fn len(&self) -> usize {
        self.data.len() * 2
            - usize::from(self.last_hi_is_zero)
            - usize::from(!self.next_is_lo)
    }
}

fn recv_integer_size_and_digits(args: &CryValExporter) -> Vec<u32> {
    let mut size: u64 = 0;
    assert!(cry_ffi!(args, recv_u64, &mut size) == 0);

    let mut digits_vec: Vec<u64> = vec![0; size as usize];
    let digits_slice: &mut [u64] = digits_vec.as_mut_slice();
    let digits_ptr: *mut u64 = digits_slice.as_mut_ptr();
    assert!(cry_ffi!(args, recv_u64_digits, digits_ptr) == 0);

    U32Digits::new(digits_slice).collect::<Vec<u32>>()
}

impl Exportable for BigInt {
    type Parameters = ();
    fn recv_with(_params: Self::Parameters, args: &CryValExporter) -> Self {
        let mut sign_u8: u8 = 0;
        assert!(cry_ffi!(args, recv_u8, &mut sign_u8) == 0);
        let sign: Sign =
            if sign_u8 == 1 {
                Sign::Minus
            } else {
                Sign::Plus
            };

        let digits: Vec<u32> = recv_integer_size_and_digits(args);
        BigInt::new(sign, digits)
    }
}

impl Exportable for BigUint {
    type Parameters = ();
    fn recv_with(_params: Self::Parameters, args: &CryValExporter) -> Self {
        BigInt::recv(args).to_biguint().expect("negative BigInt")
    }
}

impl Exportable for BigRational {
    type Parameters = ();
    fn recv_with(_params: Self::Parameters, args: &CryValExporter) -> Self {
        let numer = BigInt::recv(args);
        let denom = BigInt::recv(args);
        BigRational::new(numer, denom)
    }
}

impl <T: Exportable, const N: usize> Exportable for [T; N] {
    type Parameters = T::Parameters;
    fn recv_with(params: Self::Parameters, args: &CryValExporter) -> Self {
        let mut arr: [MaybeUninit<T>; N] = [const { MaybeUninit::uninit() }; N];

        for elem in arr.iter_mut() {
            elem.write(T::recv_with(params.clone(), args));
        }

        unsafe { mem::transmute_copy::<_, [T; N]>(&arr) }
    }
}

impl <T: Exportable> Exportable for Vec<T> {
    type Parameters = (Len, T::Parameters);
    fn recv_with(params: Self::Parameters, args: &CryValExporter) -> Self {
        let (Len(len), t_params) = params;
        let mut vec: Vec<T> = Vec::with_capacity(len);

        for _ in 0..len {
            vec.push(T::recv_with(t_params.clone(), args));
        }

        vec
    }
}

impl <T: Exportable> Exportable for Box<[T]> {
    type Parameters = (Len, T::Parameters);
    fn recv_with(params: Self::Parameters, args: &CryValExporter) -> Self {
        let vec = Vec::<T>::recv_with(params, args);
        vec.into_boxed_slice()
    }
}

impl<T: Exportable> Exportable for Option<T> {
    type Parameters = T::Parameters;
    fn recv_with(params: Self::Parameters, args: &CryValExporter) -> Self {
        let mut tag: u64 = 0;
        assert!(cry_ffi!(args, recv_u64, &mut tag) == 0);
        match tag {
            0 => None,
            1 => {
                let v = T::recv_with(params, args);
                Some(v)
            },
            _ => panic!("Unexpected tag for Option: {:?}", tag),
        }
    }
}

impl<T: Exportable, E: Exportable> Exportable for Result<T, E> {
    type Parameters = (T::Parameters, E::Parameters);
    fn recv_with(params: Self::Parameters, args: &CryValExporter) -> Self {
        let (t_params, e_params) = params;
        let mut tag: u64 = 0;
        assert!(cry_ffi!(args, recv_u64, &mut tag) == 0);
        match tag {
            0 => {
                let t = T::recv_with(t_params, args);
                Ok(t)
            },
            1 => {
                let e = E::recv_with(e_params, args);
                Err(e)
            },
            _ => panic!("Unexpected tag for Result: {:?}", tag),
        }
    }
}

/// A macro to automate defining `Exportable` instances for tuples. To export a
/// tuple, we export all of its fields from left to right.
macro_rules! exportable_tuple {
    ($($idx:tt $t:ident),*) => {
        impl<$($t: Exportable),*> Exportable for ($($t,)*)
        {
            type Parameters = ($($t::Parameters,)*);
            fn recv_with(_params: Self::Parameters, _args: &CryValExporter) -> Self {
                ($($t::recv_with(_params.$idx, _args),)*)
            }
        }
    };
}

/*  0 */ exportable_tuple!();
/*  1 */ exportable_tuple!(0 A);
/*  2 */ exportable_tuple!(0 A, 1 B);
/*  3 */ exportable_tuple!(0 A, 1 B, 2 C);
/*  4 */ exportable_tuple!(0 A, 1 B, 2 C, 3 D);
/*  5 */ exportable_tuple!(0 A, 1 B, 2 C, 3 D, 4 E);
/*  6 */ exportable_tuple!(0 A, 1 B, 2 C, 3 D, 4 E, 5 F);
/*  7 */ exportable_tuple!(0 A, 1 B, 2 C, 3 D, 4 E, 5 F, 6 G);
/*  8 */ exportable_tuple!(0 A, 1 B, 2 C, 3 D, 4 E, 5 F, 6 G, 7 H);
/*  9 */ exportable_tuple!(0 A, 1 B, 2 C, 3 D, 4 E, 5 F, 6 G, 7 H, 8 I);
/* 10 */ exportable_tuple!(0 A, 1 B, 2 C, 3 D, 4 E, 5 F, 6 G, 7 H, 8 I, 9 J);
/* 11 */ exportable_tuple!(0 A, 1 B, 2 C, 3 D, 4 E, 5 F, 6 G, 7 H, 8 I, 9 J, 10 K);
/* 12 */ exportable_tuple!(0 A, 1 B, 2 C, 3 D, 4 E, 5 F, 6 G, 7 H, 8 I, 9 J, 10 K, 11 L);
/* 13 */ exportable_tuple!(0 A, 1 B, 2 C, 3 D, 4 E, 5 F, 6 G, 7 H, 8 I, 9 J, 10 K, 11 L, 12 M);
/* 14 */ exportable_tuple!(0 A, 1 B, 2 C, 3 D, 4 E, 5 F, 6 G, 7 H, 8 I, 9 J, 10 K, 11 L, 12 M, 13 N);
/* 15 */ exportable_tuple!(0 A, 1 B, 2 C, 3 D, 4 E, 5 F, 6 G, 7 H, 8 I, 9 J, 10 K, 11 L, 12 M, 13 N, 14 O);
/* 16 */ exportable_tuple!(0 A, 1 B, 2 C, 3 D, 4 E, 5 F, 6 G, 7 H, 8 I, 9 J, 10 K, 11 L, 12 M, 13 N, 14 O, 15 P);

/// Export a numeric type parameter in a polymorphic foreign function.
pub fn recv_type_param(args: &CryValExporter) -> BigUint {
    let param_u64 = u64::recv(args);
    let param_is_large: bool = param_u64 == u64::MAX;
    if param_is_large {
        BigUint::recv(args)
    } else {
        BigUint::from(param_u64)
    }
}
