#include <stddef.h>
#include <stdint.h>
uint8_t add8(uint8_t in0, uint8_t in1);
uint16_t sub16(uint16_t in0, uint16_t in1);
uint32_t mul32(uint32_t in0, uint32_t in1);
uint64_t div64(uint64_t in0, uint64_t in1);
uint8_t extendInput(uint8_t in);
uint8_t maskOutput(uint8_t in);
uint8_t noBits(uint8_t in);
uint8_t not(uint8_t in);
float addFloat32(float in0, float in1);
double subFloat64(double in0, double in1);
float specialFloats(uint8_t in);
uint8_t usesTypeSynonym(uint32_t in0, float in1);
uint32_t sum10(uint32_t * in);
void reverse5(double * in, double * out);
void compoundTypes(uint32_t in0_0, uint16_t in0_1_x, uint32_t * in0_1_y, uint32_t * in1_z, uint16_t * out_a_0, uint16_t * out_a_1, uint32_t * out_b_c, uint8_t * out_b_d, uint8_t * out_b_e);
uint64_t typeToValue(size_t n);
uint32_t sumPoly(size_t n, uint32_t * in);
void inits(size_t n, uint8_t * in, uint8_t * out);
void zipMul3(size_t n, size_t m, size_t p, float * in0, float * in1, float * in2, float * out);
void nestedSeq(size_t n, size_t m, size_t p, uint8_t * in, uint8_t * out);
