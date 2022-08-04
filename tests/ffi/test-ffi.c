#include <math.h>
#include <stdint.h>

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
