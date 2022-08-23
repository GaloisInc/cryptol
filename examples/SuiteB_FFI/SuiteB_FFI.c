// Based on sample code from the Intel AES-NI whitepaper
// https://www.intel.com/content/dam/doc/white-paper/advanced-encryption-standard-new-instructions-set-paper.pdf

#include <stdint.h>
#include <stddef.h>

#ifdef __x86_64__

#include <cpuid.h>
#include <immintrin.h>

// Since Cryptol represents the round keys using [4][32], we need to do a byte
// swap every time we write/read the keys to/from memory to correct for
// endianness.
#define BSWAP32_128 _mm_set_epi64x(0x0c0d0e0f08090a0b, 0x0405060700010203)

uint8_t checkAESNISupported() {
  unsigned int eax, ebx, ecx, edx;
  if (!__get_cpuid(1, &eax, &ebx, &ecx, &edx)) {
    return 0;
  }
  return (ecx & bit_AES) != 0;
}

static inline __m128i prepare_roundkey_128(__m128i tmp1, __m128i tmp2) {
  __m128i tmp3;
  tmp2 = _mm_shuffle_epi32(tmp2, 0xff);
  tmp3 = _mm_slli_si128(tmp1, 0x4);
  tmp1 = _mm_xor_si128(tmp1, tmp3);
  tmp3 = _mm_slli_si128(tmp3, 0x4);
  tmp1 = _mm_xor_si128(tmp1, tmp3);
  tmp3 = _mm_slli_si128(tmp3, 0x4);
  tmp1 = _mm_xor_si128(tmp1, tmp3);
  tmp1 = _mm_xor_si128(tmp1, tmp2);
  return tmp1;
}

void aesniExpandEncrypt128(const uint8_t *key, uint32_t *initialKey,
uint32_t *roundKeys, uint32_t *finalKey) {
  __m128i tmp1, tmp2, tmp3;
  __m128i bswap32 = BSWAP32_128;
  __m128i *roundKeys128 = (__m128i *) roundKeys;
  tmp1 = _mm_loadu_si128((__m128i *) key);
  tmp3 = _mm_shuffle_epi8(tmp1, bswap32);
  _mm_storeu_si128((__m128i *) initialKey, tmp3);
  tmp2 = _mm_aeskeygenassist_si128(tmp1, 0x1);
  tmp1 = prepare_roundkey_128(tmp1, tmp2);
  tmp3 = _mm_shuffle_epi8(tmp1, bswap32);
  _mm_storeu_si128(roundKeys128, tmp3);
  tmp2 = _mm_aeskeygenassist_si128(tmp1, 0x2);
  tmp1 = prepare_roundkey_128(tmp1, tmp2);
  tmp3 = _mm_shuffle_epi8(tmp1, bswap32);
  _mm_storeu_si128(roundKeys128 + 1, tmp3);
  tmp2 = _mm_aeskeygenassist_si128(tmp1, 0x4);
  tmp1 = prepare_roundkey_128(tmp1, tmp2);
  tmp3 = _mm_shuffle_epi8(tmp1, bswap32);
  _mm_storeu_si128(roundKeys128 + 2, tmp3);
  tmp2 = _mm_aeskeygenassist_si128(tmp1, 0x8);
  tmp1 = prepare_roundkey_128(tmp1, tmp2);
  tmp3 = _mm_shuffle_epi8(tmp1, bswap32);
  _mm_storeu_si128(roundKeys128 + 3, tmp3);
  tmp2 = _mm_aeskeygenassist_si128(tmp1, 0x10);
  tmp1 = prepare_roundkey_128(tmp1, tmp2);
  tmp3 = _mm_shuffle_epi8(tmp1, bswap32);
  _mm_storeu_si128(roundKeys128 + 4, tmp3);
  tmp2 = _mm_aeskeygenassist_si128(tmp1, 0x20);
  tmp1 = prepare_roundkey_128(tmp1, tmp2);
  tmp3 = _mm_shuffle_epi8(tmp1, bswap32);
  _mm_storeu_si128(roundKeys128 + 5, tmp3);
  tmp2 = _mm_aeskeygenassist_si128(tmp1, 0x40);
  tmp1 = prepare_roundkey_128(tmp1, tmp2);
  tmp3 = _mm_shuffle_epi8(tmp1, bswap32);
  _mm_storeu_si128(roundKeys128 + 6, tmp3);
  tmp2 = _mm_aeskeygenassist_si128(tmp1, 0x80);
  tmp1 = prepare_roundkey_128(tmp1, tmp2);
  tmp3 = _mm_shuffle_epi8(tmp1, bswap32);
  _mm_storeu_si128(roundKeys128 + 7, tmp3);
  tmp2 = _mm_aeskeygenassist_si128(tmp1, 0x1b);
  tmp1 = prepare_roundkey_128(tmp1, tmp2);
  tmp3 = _mm_shuffle_epi8(tmp1, bswap32);
  _mm_storeu_si128(roundKeys128 + 8, tmp3);
  tmp2 = _mm_aeskeygenassist_si128(tmp1, 0x36);
  tmp1 = prepare_roundkey_128(tmp1, tmp2);
  tmp3 = _mm_shuffle_epi8(tmp1, bswap32);
  _mm_storeu_si128((__m128i *) finalKey, tmp3);
}

static inline void prepare_roundkey_192(__m128i *tmp1, __m128i *tmp2,
__m128i *tmp3) {
  __m128i tmp4;
  *tmp2 = _mm_shuffle_epi32(*tmp2, 0x55);
  tmp4 = _mm_slli_si128(*tmp1, 0x4);
  *tmp1 = _mm_xor_si128(*tmp1, tmp4);
  tmp4 = _mm_slli_si128(tmp4, 0x4);
  *tmp1 = _mm_xor_si128(*tmp1, tmp4);
  tmp4 = _mm_slli_si128(tmp4, 0x4);
  *tmp1 = _mm_xor_si128(*tmp1, tmp4);
  *tmp1 = _mm_xor_si128(*tmp1, *tmp2);
  *tmp2 = _mm_shuffle_epi32(*tmp1, 0xff);
  tmp4 = _mm_slli_si128(*tmp3, 0x4);
  *tmp3 = _mm_xor_si128(*tmp3, tmp4);
  *tmp3 = _mm_xor_si128(*tmp3, *tmp2);
}

void aesniExpandEncrypt192(const uint8_t *key, uint32_t *initialKey,
uint32_t *roundKeys, uint32_t *finalKey) {
  __m128i tmp1, tmp2, tmp3, tmp4;
  __m128i bswap32 = BSWAP32_128;
  __m128i *key128 = (__m128i *) key;
  __m128i *roundKeys128 = (__m128i *) roundKeys;
  tmp1 = _mm_loadu_si128(key128);
  tmp3 = _mm_loadu_si128(key128 + 1);
  tmp4 = _mm_shuffle_epi8(tmp1, bswap32);
  _mm_storeu_si128((__m128i *) initialKey, tmp4);
  tmp4 = tmp3;
  tmp2 = _mm_aeskeygenassist_si128(tmp3, 0x1);
  prepare_roundkey_192(&tmp1, &tmp2, &tmp3);
  tmp4 = (__m128i) _mm_shuffle_pd((__m128d) tmp4, (__m128d) tmp1, 0);
  tmp4 = _mm_shuffle_epi8(tmp4, bswap32);
  _mm_storeu_si128(roundKeys128, tmp4);
  tmp4 = (__m128i) _mm_shuffle_pd((__m128d) tmp1, (__m128d) tmp3, 1);
  tmp4 = _mm_shuffle_epi8(tmp4, bswap32);
  _mm_storeu_si128(roundKeys128 + 1, tmp4);
  tmp2 = _mm_aeskeygenassist_si128(tmp3, 0x2);
  prepare_roundkey_192(&tmp1, &tmp2, &tmp3);
  tmp4 = _mm_shuffle_epi8(tmp1, bswap32);
  _mm_storeu_si128(roundKeys128 + 2, tmp4);
  tmp4 = tmp3;
  tmp2 = _mm_aeskeygenassist_si128(tmp3, 0x4);
  prepare_roundkey_192(&tmp1, &tmp2, &tmp3);
  tmp4 = (__m128i) _mm_shuffle_pd((__m128d) tmp4, (__m128d) tmp1, 0);
  tmp4 = _mm_shuffle_epi8(tmp4, bswap32);
  _mm_storeu_si128(roundKeys128 + 3, tmp4);
  tmp4 = (__m128i) _mm_shuffle_pd((__m128d) tmp1, (__m128d) tmp3, 1);
  tmp4 = _mm_shuffle_epi8(tmp4, bswap32);
  _mm_storeu_si128(roundKeys128 + 4, tmp4);
  tmp2 = _mm_aeskeygenassist_si128(tmp3, 0x8);
  prepare_roundkey_192(&tmp1, &tmp2, &tmp3);
  tmp4 = _mm_shuffle_epi8(tmp1, bswap32);
  _mm_storeu_si128(roundKeys128 + 5, tmp4);
  tmp4 = tmp3;
  tmp2 = _mm_aeskeygenassist_si128(tmp3, 0x10);
  prepare_roundkey_192(&tmp1, &tmp2, &tmp3);
  tmp4 = (__m128i) _mm_shuffle_pd((__m128d) tmp4, (__m128d) tmp1, 0);
  tmp4 = _mm_shuffle_epi8(tmp4, bswap32);
  _mm_storeu_si128(roundKeys128 + 6, tmp4);
  tmp4 = (__m128i) _mm_shuffle_pd((__m128d) tmp1, (__m128d) tmp3, 1);
  tmp4 = _mm_shuffle_epi8(tmp4, bswap32);
  _mm_storeu_si128(roundKeys128 + 7, tmp4);
  tmp2 = _mm_aeskeygenassist_si128(tmp3, 0x20);
  prepare_roundkey_192(&tmp1, &tmp2, &tmp3);
  tmp4 = _mm_shuffle_epi8(tmp1, bswap32);
  _mm_storeu_si128(roundKeys128 + 8, tmp4);
  tmp4 = tmp3;
  tmp2 = _mm_aeskeygenassist_si128(tmp3, 0x40);
  prepare_roundkey_192(&tmp1, &tmp2, &tmp3);
  tmp4 = (__m128i) _mm_shuffle_pd((__m128d) tmp4, (__m128d) tmp1, 0);
  tmp4 = _mm_shuffle_epi8(tmp4, bswap32);
  _mm_storeu_si128(roundKeys128 + 9, tmp4);
  tmp4 = (__m128i) _mm_shuffle_pd((__m128d) tmp1, (__m128d) tmp3, 1);
  tmp4 = _mm_shuffle_epi8(tmp4, bswap32);
  _mm_storeu_si128(roundKeys128 + 10, tmp4);
  tmp2 = _mm_aeskeygenassist_si128(tmp3, 0x80);
  prepare_roundkey_192(&tmp1, &tmp2, &tmp3);
  tmp4 = _mm_shuffle_epi8(tmp1, bswap32);
  _mm_storeu_si128((__m128i *) finalKey, tmp4);
}

static inline void prepare_roundkey_256_1(__m128i *tmp1, __m128i *tmp2) {
  __m128i tmp4;
  *tmp2 = _mm_shuffle_epi32(*tmp2, 0xff);
  tmp4 = _mm_slli_si128(*tmp1, 0x4);
  *tmp1 = _mm_xor_si128(*tmp1, tmp4);
  tmp4 = _mm_slli_si128(tmp4, 0x4);
  *tmp1 = _mm_xor_si128(*tmp1, tmp4);
  tmp4 = _mm_slli_si128(tmp4, 0x4);
  *tmp1 = _mm_xor_si128(*tmp1, tmp4);
  *tmp1 = _mm_xor_si128(*tmp1, *tmp2);
}

static inline void prepare_roundkey_256_2(__m128i *tmp1, __m128i *tmp3) {
  __m128i tmp2, tmp4;
  tmp4 = _mm_aeskeygenassist_si128(*tmp1, 0x0);
  tmp2 = _mm_shuffle_epi32(tmp4, 0xaa);
  tmp4 = _mm_slli_si128(*tmp3, 0x4);
  *tmp3 = _mm_xor_si128(*tmp3, tmp4);
  tmp4 = _mm_slli_si128(tmp4, 0x4);
  *tmp3 = _mm_xor_si128(*tmp3, tmp4);
  tmp4 = _mm_slli_si128(tmp4, 0x4);
  *tmp3 = _mm_xor_si128(*tmp3, tmp4);
  *tmp3 = _mm_xor_si128(*tmp3, tmp2);
}

void aesniExpandEncrypt256(const uint8_t *key, uint32_t *initialKey,
uint32_t *roundKeys, uint32_t *finalKey) {
  __m128i tmp1, tmp2, tmp3, tmp4;
  __m128i bswap32 = BSWAP32_128;
  __m128i *key128 = (__m128i *) key;
  __m128i *roundKeys128 = (__m128i *) roundKeys;
  tmp1 = _mm_loadu_si128(key128);
  tmp3 = _mm_loadu_si128(key128 + 1);
  tmp4 = _mm_shuffle_epi8(tmp1, bswap32);
  _mm_storeu_si128((__m128i *) initialKey, tmp4);
  tmp4 = _mm_shuffle_epi8(tmp3, bswap32);
  _mm_storeu_si128(roundKeys128, tmp4);
  tmp2 = _mm_aeskeygenassist_si128 (tmp3, 0x01);
  prepare_roundkey_256_1(&tmp1, &tmp2);
  tmp4 = _mm_shuffle_epi8(tmp1, bswap32);
  _mm_storeu_si128(roundKeys128 + 1, tmp4);
  prepare_roundkey_256_2(&tmp1, &tmp3);
  tmp4 = _mm_shuffle_epi8(tmp3, bswap32);
  _mm_storeu_si128(roundKeys128 + 2, tmp4);
  tmp2 = _mm_aeskeygenassist_si128(tmp3, 0x02);
  prepare_roundkey_256_1(&tmp1, &tmp2);
  tmp4 = _mm_shuffle_epi8(tmp1, bswap32);
  _mm_storeu_si128(roundKeys128 + 3, tmp4);
  prepare_roundkey_256_2(&tmp1, &tmp3);
  tmp4 = _mm_shuffle_epi8(tmp3, bswap32);
  _mm_storeu_si128(roundKeys128 + 4, tmp4);
  tmp2 = _mm_aeskeygenassist_si128(tmp3, 0x04);
  prepare_roundkey_256_1(&tmp1, &tmp2);
  tmp4 = _mm_shuffle_epi8(tmp1, bswap32);
  _mm_storeu_si128(roundKeys128 + 5, tmp4);
  prepare_roundkey_256_2(&tmp1, &tmp3);
  tmp4 = _mm_shuffle_epi8(tmp3, bswap32);
  _mm_storeu_si128(roundKeys128 + 6, tmp4);
  tmp2 = _mm_aeskeygenassist_si128(tmp3, 0x08);
  prepare_roundkey_256_1(&tmp1, &tmp2);
  tmp4 = _mm_shuffle_epi8(tmp1, bswap32);
  _mm_storeu_si128(roundKeys128 + 7, tmp4);
  prepare_roundkey_256_2(&tmp1, &tmp3);
  tmp4 = _mm_shuffle_epi8(tmp3, bswap32);
  _mm_storeu_si128(roundKeys128 + 8, tmp4);
  tmp2 = _mm_aeskeygenassist_si128(tmp3, 0x10);
  prepare_roundkey_256_1(&tmp1, &tmp2);
  tmp4 = _mm_shuffle_epi8(tmp1, bswap32);
  _mm_storeu_si128(roundKeys128 + 9, tmp4);
  prepare_roundkey_256_2(&tmp1, &tmp3);
  tmp4 = _mm_shuffle_epi8(tmp3, bswap32);
  _mm_storeu_si128(roundKeys128 + 10, tmp4);
  tmp2 = _mm_aeskeygenassist_si128(tmp3, 0x20);
  prepare_roundkey_256_1(&tmp1, &tmp2);
  tmp4 = _mm_shuffle_epi8(tmp1, bswap32);
  _mm_storeu_si128(roundKeys128 + 11, tmp4);
  prepare_roundkey_256_2(&tmp1, &tmp3);
  tmp4 = _mm_shuffle_epi8(tmp3, bswap32);
  _mm_storeu_si128(roundKeys128 + 12, tmp4);
  tmp2 = _mm_aeskeygenassist_si128(tmp3, 0x40);
  prepare_roundkey_256_1(&tmp1, &tmp2);
  tmp4 = _mm_shuffle_epi8(tmp1, bswap32);
  _mm_storeu_si128((__m128i *) finalKey, tmp4);
}

void aesniEncryptBlock(size_t k, const uint32_t *initialKey,
const uint32_t *roundKeys, const uint32_t *finalKey, const uint8_t *plaintext,
uint8_t *ciphertext) {
  __m128i tmp1, tmp2;
  __m128i bswap32 = _mm_set_epi64x(0x0c0d0e0f08090a0b, 0x0405060700010203);
  __m128i *roundKeys128 = (__m128i *) roundKeys;
  tmp1 = _mm_loadu_si128((__m128i *) plaintext);
  tmp2 = _mm_loadu_si128((__m128i *) initialKey);
  tmp2 = _mm_shuffle_epi8(tmp2, bswap32);
  tmp1 = _mm_xor_si128(tmp1, tmp2);
  for (size_t i = 0; i < k + 5; i++) {
    tmp2 = _mm_loadu_si128(roundKeys128 + i);
    tmp2 = _mm_shuffle_epi8(tmp2, bswap32);
    tmp1 = _mm_aesenc_si128(tmp1, tmp2);
  }
  tmp2 = _mm_loadu_si128((__m128i *) finalKey);
  tmp2 = _mm_shuffle_epi8(tmp2, bswap32);
  tmp1 = _mm_aesenclast_si128(tmp1, tmp2);
  _mm_storeu_si128((__m128i *) ciphertext, tmp1);
}

#else

uint8_t checkAESNISupported() {
  return 0;
}

void *aesniExpandEncrypt128 = NULL;
void *aesniExpandEncrypt192 = NULL;
void *aesniExpandEncrypt256 = NULL;
void *aesniEncryptBlock = NULL;

#endif
