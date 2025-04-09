#pragma once

#include <stdlib.h>
#include <stdint.h>

// A convenince macro to call a method on an object.
#define CRY_FFI(obj, f, args...) ((obj)->f((obj)->self, args))

/** Imports foreign values into Cryptol.
This should be used when a foreign function needs to return a result
to the Cryptol interpreter.
*/
struct CryValImporter {
  /** This should be passed to all the function pointers.
      It captures the current state of the importing process. */
  void*     self;

  /** Make a boolean value: 0: false, > 0: true */
  void      (*send_bool)(void*, uint8_t);

  /** Make an unsigned Integer, which fits in uint64_t */
  void      (*send_small_uint)(void*, uint64_t);

  /** Make a signed Integer, which fits in int64_t */
  void      (*send_small_sint)(void*, int64_t);

  /** Make a floating point value */
  void      (*send_double)(void*, double);

  /** Start building a sum type,
      the argument is the number of the constructor */
  void      (*send_tag)(void*, size_t);

  /** Start building an Integer, which does not fit in int64_t.
      The argument is the number of uint64_t digits we need.
      The result is a buffer where the digits should be placed,
      least significant first.
   */
  uint64_t* (*send_new_large_int)(void*, size_t);

  /** Finish bulding an Integer, which does not fit in uint64_t.
      The argument is 1 for negative, and 0 for non-negative.
   */
  void      (*send_sign)(void*, uint8_t);
};


/** Exports Cryptol values into a foreign environment.
This should be used to get a foreign function's arguments from the
Cryptol interpreter.  Cryptol values are exported as follows:

  Bit:
    recv_u8(&value)

  Float32, Float64:
    recv_double(&value)

  Integer:
    recv_u8(&sign); recv_u64(&size); recv_u64_digits(value);
    // uint64_t value[size]

  numeric type parameter:
    recv_u64(&value);
    if (value == (maxBound :: uint64_t)) then receve an integer (as above).

  [n]
    | n <= 8            recv_u8(&value)
    | 8 < n && n <= 64  recv_u64(&value)
    | otherwise         receive Integer (as above)

  [n] a
    receive `n` values of type `a`

  Rational:
    receive 2 integers (as above): 1st is numerator, 2nd denominator.
  
  Tagged sum:
    recv_u64(&tag); receive fields based on the tag;
    The constructor number correspond to the order of declaration.

  Tuple, record, newtype:
     Receive the elements one after the other.
     The fields of records and newtypes are sent in alphabetical order.
*/
struct CryValExporter {
  /** This should be passed to all function pointers.
      It captures the current state of the exporting process.
  */
  void *self;

  /** Get a uint8_t.
      This is used to represent Bit, [n] (n <= 8), and integer signs. */
  uint32_t (*recv_u8)(void*, uint8_t*);

  /** Get a double */
  uint32_t (*recv_double)(void*, double*);

  /* Get a uint64_t.  This is used for to get the size of an integer or word,
     [n] (8 < n && n <= 64), and also for the tag of a sum type.
     Returns 0 on success.
  */
  uint32_t (*recv_u64)(void*, uint64_t*);

  /** Receive the uint64_t digits of an integer or a word.
      These are placed in the provided buffer, starting with the least
      significant one.  The buffer should be big enough to fit the digits.
      Returns 0 on success.
   */
  uint32_t (*recv_u64_digits)(void*, uint64_t*);
};

