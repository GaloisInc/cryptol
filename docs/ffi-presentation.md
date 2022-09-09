---
title: Cryptol FFI
author: Bretton
date: 2022-09-02
---

# Cryptol FFI

- Call functions written in C

---

# Why?

- Performance
- Use existing code in C
- Do things that Cryptol can't do?

---

# What does it look like?

```cry
foreign add : [32] -> [32] -> [32]
```

```c
uint32_t add(uint32_t x, uint32_t y) {
  return x + y;
}
```

```
Main> add 1 2
0x00000003
```

---

# How do you use it?

```
+-------------+
| Example.cry | ------------------------+       +---------------Cryptol---------------+
+-------------+                         |       | Cryptol> :l Example.cry             |
                                        |       | Loading module Cryptol              |
+-----------+        +---------------+  +------>| Loading module Example              |
| Example.c | =====> | Example.so    | -------->| Loading dynamic library Example.so  |
+-----------+   cc   | Example.dylib |  dlopen  | Example> add 1 2                    |
                     +---------------+          | 0x00000003                          |
                                                +-------------------------------------+
```

- Find shared library with same name as Cryptol file
- Dynamically load with `dlopen`
- Bind each `foreign` function with `dlsym`
- Windows not supported yet
- Compile it yourself (for now...)
  - `cc -fPIC -shared Example.c -o Example.so`
  - `cc -dynamiclib Example.c -o Example.dylib`

---

# How does it work?

- Since Cryptol is interpreted, number/types of arguments to foreign functions are not known statically
- `libffi` calls functions with the right calling conventions given interface at runtime
  - Rant about `libffi` in Haskell

---

# Supported types

## Basic types

Cryptol | C
--- | ---
Bit | uint8_t
[K]Bit, 0 <= K <= 8 | uint8_t
[K]Bit, 8 < K <= 16 | uint16_t
[K]Bit, 16 < K <= 32 | uint32_t
[K]Bit, 32 < K <= 64 | uint64_t
Float32 | float
Float64 | double

---

# Supported types

## Multiple arguments?

Cryptol | C
--- | ---
A -> B -> ... -> Z | Z' (A', B', ...)

---

# Supported types

## More complex types

- So far it has been pretty simple
- How about sequences? I guess we need arrays
  - Who allocates the memory?
  - Who owns the memory?
  - How are they passed vs returned?

---

# Supported types

## Sequences

Cryptol | C
--- | ---
[n1][n2]...[nk]T | U*

where

T | U
--- | ---
[K]Bit, 0 <= K <= 8 | uint8_t
[K]Bit, 8 < K <= 16 | uint16_t
[K]Bit, 16 < K <= 32 | uint32_t
[K]Bit, 32 < K <= 64 | uint64_t
Float32 | float
Float64 | double

- Cryptol allocates and owns all memory
- Sequence as Cryptol parameter: `const U*` C parameter
- Sequence as Cryptol return type: `U*` C output parameter
  - Passed after Cryptol parameters
  - Return type of C function is `void`
- Multidimensional sequences: flatten (except the [K]Bit part)
- How about n1, n2, ..., nk?
  - Must be `fin`

---

# Supported ~~types~~ kinds?

## Numeric type arguments

Cryptol | C
--- | ---
\# | size_t

- Must be `fin`
- Type arguments are passed before any value arguments

---

# Supported types

## Tuples and records as parameters

- Passed as separate arguments

Cryptol | C (multiple!)
--- | ---
(T1, T2, ..., Tn) | U1, U2, ..., Un
{s1: T1, s2: T2, ..., sn: Tn} | U1, U2, ..., Un

where

Cryptol | C
--- | ---
Ti | Ui

Note:
- Order of record fields is however it's written in the type in the source code
- Uncurried and curried Cryptol functions correspond to the same C function
- () corresponds to no arguments at all
- Can be nested

---

# Supported types

## Tuples and records as return types

- Returned as separate output parameters
- This means the component types need to become pointers
  - Except for sequences which are already pointers

Cryptol | C (multiple!)
--- | ---
(T1, T2, ..., Tn) | V1, V2, ..., Vn
{s1: T1, s2: T2, ..., sn: Tn} | V1, V2, ..., Vn

where

Cryptol parameter | C
--- | ---
Ti | Ui

and Vi = if Ui is a pointer type then Ui else Ui*

Note:
- Return type of C function is `void`
- () corresponds to no return value and no output arguments
- Can be nested

---

# Supported types

## Type synonyms

- Type synonyms are expanded before applying the previous rules

---

# Examples

```cry
foreign f : {n} (fin n) => [n][10] -> {a : Bit, b : [64]} -> (Float64, [n + 1][20])
```

```c
void f(size_t n, uint16_t *in0, uint8_t in1, uint64_t in2,
       double *out0, uint32_t *out1);
```

- More examples in FFI tests

---

# Evaluation

- All arguments are fully evaluated
- Result will be fully evaluated too (of course)

---

# Questionable uses of FFI

```cry
foreign print : {n} (fin n) => [n][8] -> ()
```

```c
void print(size_t n, char *s) {
  printf("%.*s\n", (int) n, s);
}
```

```
Main> print "Hello world!"
Hello world!
()
```

```cry
foreign launchMissiles : ()
```

etc

- Cryptol functions should be pure
- Beware of laziness

---

# AES example

- Replacement for `SuiteB` module using AES-NI for AES functions
- ~5.5x faster
  - But could actually be much faster, if not limited to 1 block

---

# Somewhat interesting(?) implementation details

- `ForeignPtr` for `dlclose`
- Interesting types in FFI marshalling
```hs
getMarshalBasicArg :: FFIBasicType ->
    (forall a. FFIArg a => (GenValue Concrete -> Eval a) -> b) -> b
data GetRet = GetRet
    { getRetAsValue   :: forall a. FFIRet a => IO a
    , getRetAsOutArgs :: [SomeFFIArg] -> IO () }
```

---

# Future work

- Automatically generate header files from `foreign` declarations
- Support Windows
- Support Integer/Z
- Cryptol implementation of `foreign` functions + SAW integration

---

# Other stuff (not FFI)

- `:time` command for benchmarking evaluation of Cryptol expressions
  - Evaluates it a bunch of times and reports the average time
- Import specific operators
  - `import M ((<+>))`
- Fixed fixity (fixedity?) of prefix operators
  - `-x**2` parses as `-(x**2)` not `(-x)**2`

---

# Thank you!

- Iavor, Eddy, Ryan

# Questions?

- Why is the Cryptol logo a water drop
