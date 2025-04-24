#pragma once

#include <stdlib.h>
#include <stdint.h>

// A convenince macro to call a method on an object.
#define CRY_FFI(obj, f, args...) ((obj)->f((obj)->self, args))

/** Imports foreign values into Cryptol.
This should be used when a foreign function needs to return a result
to the Cryptol interpreter. Cryptol values are imported as follows:

  Bit:
    send_bool(value);

  Float32, Float64:
    send_double(value);

  Integer, Z:
    uint64_t* digits = send_new_large_int(size);
    // write value into `digits`
    send_sign(sign);

  [n]
    | n <= 64           send_small_uint(value) or
                        send_small_sint(value)
    | otherwise         send Integer (as above)
                        (like receiving an Integer, but without a sign)

  [n] a
    send `n` values of type `a`

  Rational:
    send 2 Integers (as above): 1st is numerator, 2nd denominator.

  Tagged sum:
    send_tag(&tag); send fields based on the tag;
    The constructor number corresponds to the order of the declaration.

  Tuple, record, newtype:
     send the elements one after the other.
     The fields of records and newtypes are sent in alphabetical order.
*/
struct CryValImporter {
  /** This should be passed to all the function pointers.
      It captures the current state of the importing process.
  */
  void*     self;

  /** Make a boolean value: 0: false, > 0: true.
      This is used to send Bit values.
  */
  void      (*send_bool)(void*, uint8_t);

  /** Make a small unsigned integer, which fits in an uint64_t.
      This is used to send words [n] (n <= 64).
  */
  void      (*send_small_uint)(void*, uint64_t);

  /** Make a small signed integer, which fits in an int64_t.
      This is used to send words [n] (n <= 64).
  */
  void      (*send_small_sint)(void*, int64_t);

  /** Make a floating point value.
      This is used to send Float32 and Float64 values.
  */
  void      (*send_double)(void*, double);

  /** Start building a sum type.
      The size_t argument is the number of the constructor.
  */
  void      (*send_tag)(void*, size_t);

  /** Start building an Integer, a Z value, or a large word [n] (n > 64).
      The size argument is the number of uint64_t digits we need.
      The result is a buffer where the digits should be placed,
      least significant first.
   */
  uint64_t* (*send_new_large_int)(void*, size_t);

  /** Finish bulding an Integer, a Z value, or a large word [n] (n > 64).
      The sign argument is 1 for negative, and 0 for non-negative.
   */
  void      (*send_sign)(void*, uint8_t);
};


/** Exports Cryptol values into a foreign environment.
This should be used to get a foreign function's arguments from the
Cryptol interpreter. Cryptol values are exported as follows:

  Bit:
    recv_u8(&value);

  Float32, Float64:
    recv_double(&value);

  Integer, Z:
    recv_u8(&sign); recv_u64(&size); recv_u64_digits(value);

  numeric type parameter:
    recv_u64(&value);
    if (value == (maxBound :: uint64_t)) then receive an Integer (as above).

  [n]
    | n <= 8            recv_u8(&value)
    | 8 < n && n <= 64  recv_u64(&value)
    | otherwise         recv_u64(&size); recv_u64_digits(value);
                        (like receiving an Integer, but without a sign)

  [n] a
    receive `n` values of type `a`

  Rational:
    receive 2 Integers (as above): 1st is numerator, 2nd denominator.

  Tagged sum:
    recv_u64(&tag); receive fields based on the tag;
    The constructor number corresponds to the order of the declaration.

  Tuple, record, newtype:
     Receive the elements one after the other.
     The fields of records and newtypes are received in alphabetical order.
*/
struct CryValExporter {
  /** This should be passed to all function pointers.
      It captures the current state of the exporting process.
  */
  void *self;

  /** Get a uint8_t. This is used to receive:

      * The value of a Bit
      * The value of a small words [n] (n <= 8)
      * The sign of an Integer or Z value

     Returns 0 on success.
  */
  uint32_t (*recv_u8)(void*, uint8_t*);

  /** Get a double. This is used to receive the value of a Float32 or Float64.

      Returns 0 on success.
  */
  uint32_t (*recv_double)(void*, double*);

  /* Get a uint64_t. This is used to receive:

     * The value of a small numeric type parameter
     * The value of a word [n] (8 < n && n <= 64)
     * The size of an Integer or Z value
     * The size of a large numeric type parameter
     * The tag of a sum type

     Returns 0 on success.
  */
  uint32_t (*recv_u64)(void*, uint64_t*);

  /** Receive the uint64_t digits of an Integer, a Z value, a large numeric type
      parameter, or a large word [n] (n > 64). These are placed in the provided
      buffer, starting with the least significant one. The buffer should be big
      enough to fit the digits.

      Returns 0 on success.
   */
  uint32_t (*recv_u64_digits)(void*, uint64_t*);
};

