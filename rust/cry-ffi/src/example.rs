//! A simple example to demonstrate how to marshall various Rust types using
//! `cry-ffi`. If you compile this example to a shared library (using the
//! top-level `Makefile` in this repo), the resulting shared library can be used
//! in tandem with the `Example.cry` file's `foreign` functions.

use cry_ffi::*;
use num::{BigInt, BigRational, BigUint};

macro_rules! test_fn {
    ($name:ident, $t:ty) => {
        #[no_mangle]
        pub extern "C" fn $name(args: &CryValExporter, res: &CryValImporter) {
            let arg = <$t>::recv(args);
            arg.send(res);
        }
    };
}

struct N { un_n: u8 }

impl Exportable for N {
    fn recv(args: &CryValExporter) -> Self {
        N { un_n: u8::recv(args) }
    }
}

impl Importable for N {
    fn send(&self, res: &CryValImporter) {
        self.un_n.send(res);
    }
}

test_fn!(test_bool, bool);
test_fn!(test_u8, u8);
test_fn!(test_u16, u16);
test_fn!(test_u32, u32);
test_fn!(test_u64, u64);
test_fn!(test_u128, u128);
test_fn!(test_i8, i8);
test_fn!(test_i16, i16);
test_fn!(test_i32, i32);
test_fn!(test_i64, i64);
test_fn!(test_i128, i128);
test_fn!(test_integer, BigInt);
test_fn!(test_rational, BigRational);
test_fn!(test_float, f32);
test_fn!(test_double, f64);
test_fn!(test_array_16_u8, [u8; 16]);
test_fn!(test_record0, ());
test_fn!(test_record1_u8, (u8,));
test_fn!(test_record2_u8_u16, (u8, u16));
test_fn!(test_tuple0, ());
test_fn!(test_tuple2_u8_u16, (u8, u16));
test_fn!(test_newtype_u8, N);
test_fn!(test_option_u8, Option<u8>);
test_fn!(test_result_u16_u32, Result<u16, u32>);

#[no_mangle]
pub extern "C" fn test_two_u8_args(args: &CryValExporter, res: &CryValImporter) {
    let arg0 = u8::recv(args);
    let arg1 = u8::recv(args);
    let r: u8 = arg0 - arg1;
    r.send(res);
}

#[no_mangle]
pub extern "C" fn test_two_u128_res(args: &CryValExporter, res: &CryValImporter) {
    let arg = u128::recv(args);
    (arg, arg).send(res);
}

#[no_mangle]
pub extern "C" fn test_param(args: &CryValExporter, res: &CryValImporter) {
    let param: BigUint = recv_type_param(args);
    param.send(res);
}
