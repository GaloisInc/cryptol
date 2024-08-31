#pragma once

#include <stdlib.h>
#include <stdint.h>


// Imports foreign values into Cryptol.
struct CryValImporter {
  /** This should be passed to all the function pointers.
      It captures the current state of the importing process. */
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
  uint64_t* (*send_new_large_int)(void*, size_t);

  /** Finish bulding an Integer, which does not fit in uint64_t.
      The argument is 1 for negative, and 0 for non-negative.
   */
  void      (*send_sign)(void*, uint8_t);
};


/** Exports Cryptol values into a foreign environment. */
struct CryValExporter {
  /** This should be passed to all function pointers.
      It captures the current state of the exporting process.
  */
  void *self;

  /** Get a uint8_t. This is used to represent Bit, and integer signs. */
  uint32_t (*recv_u8)(void*, uint8_t*);

  /* Get a uint64_t.  This is used to get the size of an integer or word,
     and also for the tag of a sum type.
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