# `SuiteB_FFI`

`SuiteB_FFI` is a drop-in replacement for the builtin `SuiteB` module, using the
FFI to implement AES operations with hardware AES-NI instructions when
available, and falling back to the `SuiteB` software implementation in Cryptol
and Haskell otherwise.

When AES-NI is available, it is several times faster than `SuiteB`; on a Linux
machine with an Intel i7-10510U it is about 5.5x faster. Note that AES-NI is
only available on modern x86-64 processors, but you could modify this to support
similar instructions for other architectures or bind to a portable C library
instead.

The actual AES implementation is written with x86-64 intrinsics in C and based
on Intel's [AES-NI
whitepaper](https://www.intel.com/content/dam/doc/white-paper/advanced-encryption-standard-new-instructions-set-paper.pdf)
but with modifications to support how the `SuiteB` module's API is structured.
In particular, the representation of round keys as `[4][32]` in `SuiteB` means
that we need to do a byte swap every time we access memory to correct for
endianness.

Maintaining compatibility with `SuiteB` actually severely limits the speedup
that we can achieve: right now about 96% of the time spent calling the encrypt
function in Cryptol is spent doing the Cryptol evaluation surrounding the FFI
call and the actual AES computation only takes up less than 4% of the total
time. This is because the encrypt function in `SuiteB` only encrypts one block,
so if you were to create a foreign function that encrypted many blocks at once,
the overhead would be much smaller relative to the work done in the foreign
function and you would achieve a much greater speedup.

The implementation passes the AES tests from the Cryptol SuiteB test suite
(`aes-mct-ecb` and `aes-vectors`) but has not been verified beyond that.

## Usage

Run `make` to build the C code. The code checks for hardware AES-NI support at
runtime with `cpuid` when any AES function is first used. On non-x86-64
platforms, running `make` will build a dummy implementation that always falls
back to software `SuiteB`. On x86-64, `make` uses `-march=native` to build an
optimized version for running on the current machine. To build a (somewhat)
portable version that will run on any x86-64 machine with AES-NI and SSSE3, use
`make PORTABLE=1`. Once it is built, loading the `SuiteB_FFI` Cryptol module
will automatically load the shared library.

Run `make test` to test correctness. This runs the tests in the `tests/`
directory which are copied from Cryptol's `/tests/suiteb/` but using the
`SuiteB_FFI` module instead of `SuiteB`.

Run `make perf-test` to test performance on the `aes-mct-ecb` test. This prints
out the time it takes to run the test with the FFI version and the Cryptol
version.

Run `make perf-bench` to test the performance of the individual AES-128
functions with Cryptol's `:time` benchmarking command. This prints out the
benchmarked time for the key expansion and encryption functions for both
implementations, and the speedup in both cases.
