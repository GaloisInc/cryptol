#include <assert.h>
#include <math.h>
#include <stdint.h>
#include <stddef.h>

#include "test-ffi.h"

uint8_t add8(uint8_t x, uint8_t y) {
  return x + y;
}

uint16_t sub16(uint16_t x, uint16_t y) {
  return x - y;
}

uint32_t mul32(uint32_t x, uint32_t y) {
  return x * y;
}

uint64_t div64(uint64_t x, uint64_t y) {
  return x / y;
}

uint8_t extendInput(uint8_t x) {
  return x;
}

uint8_t maskOutput(uint8_t x) {
  return x;
}

uint8_t noBits(uint8_t zero) {
  assert(zero == 0);
  return 1;
}

uint8_t not(uint8_t x) {
  return !x;
}

float addFloat32(float x, float y) {
  return x + y;
}

double subFloat64(double x, double y) {
  return x - y;
}

float specialFloats(uint8_t select) {
  switch (select) {
    case 0:
      return INFINITY;
    case 1:
      return -INFINITY;
    case 2:
      return NAN;
    case 3:
      return -0.0f;
  }
  return 0;
}

uint8_t usesTypeSynonym(uint32_t x, float y) {
  return x == y;
}

uint32_t sum10(uint32_t *xs) {
  uint32_t sum = 0;
  for (unsigned i = 0; i < 10; ++i) {
    sum += xs[i];
  }
  return sum;
}

void reverse5(double *in, double *out) {
  for (unsigned i = 0; i < 5; ++i) {
    out[i] = in[4 - i];
  }
}

void compoundTypes(uint32_t n, uint16_t x, uint32_t *y, uint32_t *z,
    uint16_t *a_0, uint16_t *a_1, uint32_t *c, uint8_t *d, uint8_t *e) {
  *a_0 = n >> 16;
  *a_1 = n;
  for (unsigned i = 0; i < 3; ++i) {
    c[i] = y[i];
  }
  for (unsigned i = 0; i < 5; ++i) {
    c[i + 3] = z[i];
  }
  *d = x >> 5;
  *e = x;
}

uint64_t typeToValue(size_t n) {
  return n;
}

uint32_t sumPoly(size_t n, uint32_t *xs) {
  uint32_t sum = 0;
  for (size_t i = 0; i < n; ++i) {
    sum += xs[i];
  }
  return sum;
}

void inits(size_t n, uint8_t *in, uint8_t *out) {
  for (unsigned i = 1; i <= n; ++i) {
    for (unsigned j = 0; j < i; ++j) {
      *out++ = in[j];
    }
  }
}

void zipMul3(size_t n, size_t m, size_t p, float *xs, float *ys, float *zs,
    float *out) {
  for (size_t i = 0; i < n && i < m && i < p; ++i) {
    out[i] = xs[i] * ys[i] * zs[i];
  }
}

void nestedSeq(size_t n, size_t m, size_t p, uint8_t *in, uint8_t *out) {
  for (unsigned i = 0; i < n * m * p; ++i) {
    out[i] = in[i];
  }
}

void i2Q(mpz_t in, mpq_t out) {
  mpq_set_num(out, in);
}

void i2Z5(mpz_t in, mpz_t out) {
  mpz_set(out, in);
}

void i2Z(size_t s, mpz_t in, mpz_t out) {
  mpz_set_ui(out, s+1);
}

void i2Qs(mpz_t in, mpq_t *out) {
  mpq_set_num(out[0], in);
  mpq_inv(out[1], out[0]);
}

void iQ2Qi(mpz_t in_0, mpq_t in_1, mpq_t out_0, mpz_t out_1) {
  mpz_set(out_1, in_0);
  mpq_set(out_0, in_1);
}

uint8_t nested() { return 72; }
