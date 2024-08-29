#pragma once

#include <stdlib.h>
#include <stdint.h>

struct CryValueBuilder {
  /** This should be passed to all the function pointers.  */
  void*     self;

  /** Make a boolean value: 0: false, > 0: true */
  void      (*send_bool)(void*, uint8_t);

  /** Make an unsigned Integer, which fits in uint64_t */
  void      (*send_small_uint)(void*, uint64_t);

  /** Make an signed Integer, which fits in int64_t */
  void      (*send_small_sint)(void*, int64_t);

  /** Start building a sum type,
      the argument is the number of the constructor */
  void      (*send_tag)(void*, size_t);

  /** Start building an Integer, which does not fit in int64_t.
      The argument is the number of uint64_t digits we need.
      The result is a buffer where the digits should be placed,
      least significant first.
   */
  uint64_t* (*new_large_int)(void*, size_t);

  /** Finish bulding an Integer, which does not fit in uint64_t.
      The argument is 1 for negative, and 0 for non-negative.
   */
  void      (*send_sign)(void*, uint8_t);
};