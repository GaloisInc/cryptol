#include <assert.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "cry_ffi.h"

void test_bool(const struct CryValExporter* args, const struct CryValImporter* res) {
    uint8_t v;
    assert(CRY_FFI(args,recv_u8,&v) == 0);
    CRY_FFI(res,send_bool,v);
}

void test_u8(const struct CryValExporter* args, const struct CryValImporter* res) {
    uint8_t v;
    assert(CRY_FFI(args,recv_u8,&v) == 0);
    CRY_FFI(res,send_small_uint,(uint64_t)(v));
}

void test_u16(const struct CryValExporter* args, const struct CryValImporter* res) {
    uint64_t v;
    assert(CRY_FFI(args,recv_u64,&v) == 0);
    CRY_FFI(res,send_small_uint,v);
}

void test_u32(const struct CryValExporter* args, const struct CryValImporter* res) {
    test_u16(args, res);
}

void test_u64(const struct CryValExporter* args, const struct CryValImporter* res) {
    test_u16(args, res);
}

void test_i8(const struct CryValExporter* args, const struct CryValImporter* res) {
    uint8_t v;
    assert(CRY_FFI(args,recv_u8,&v) == 0);
    CRY_FFI(res,send_small_sint,(int64_t)(v));
}

void test_i16(const struct CryValExporter* args, const struct CryValImporter* res) {
    uint64_t v;
    assert(CRY_FFI(args,recv_u64,&v) == 0);
    CRY_FFI(res,send_small_sint,(int64_t)(v));
}

void test_i32(const struct CryValExporter* args, const struct CryValImporter* res) {
    test_i16(args, res);
}

void test_i64(const struct CryValExporter* args, const struct CryValImporter* res) {
    test_i16(args, res);
}

static uint64_t* recv_integer(uint8_t* sign, uint64_t* size, const struct CryValExporter* args) {
    assert(CRY_FFI(args,recv_u8,sign) == 0);
    assert(CRY_FFI(args,recv_u64,size) == 0);
    uint64_t* digits = calloc(*size, sizeof(uint64_t));
    assert(CRY_FFI(args,recv_u64_digits,digits) == 0);
    return digits;
}

static void send_integer(uint8_t sign, uint64_t size, const uint64_t* recv_digits, const struct CryValImporter* res) {
    uint64_t* send_digits = CRY_FFI(res,send_new_large_int,size);
    memcpy(send_digits, recv_digits, size);
    CRY_FFI(res,send_sign,sign);
}

void test_integer(const struct CryValExporter* args, const struct CryValImporter* res) {
    uint8_t sign;
    uint64_t size;
    uint64_t* digits = recv_integer(&sign, &size, args);
    send_integer(sign, size, digits, res);
    free(digits);
}

void test_rational(const struct CryValExporter* args, const struct CryValImporter* res) {
    uint8_t numer_sign;
    uint64_t numer_size;
    uint64_t* numer_digits = recv_integer(&numer_sign, &numer_size, args);

    uint8_t denom_sign;
    uint64_t denom_size;
    uint64_t* denom_digits = recv_integer(&denom_sign, &denom_size, args);

    send_integer(numer_sign, numer_size, numer_digits, res);
    send_integer(denom_sign, denom_size, denom_digits, res);

    free(numer_digits);
    free(denom_digits);
}

void test_float(const struct CryValExporter* args, const struct CryValImporter* res) {
    double v;
    assert(CRY_FFI(args,recv_double,&v) == 0);
    CRY_FFI(res,send_double,v);
}

void test_double(const struct CryValExporter* args, const struct CryValImporter* res) {
    test_float(args, res);
}

void test_array_16_u8(const struct CryValExporter* args, const struct CryValImporter* res) {
    uint8_t v[16];
    for (int i = 0; i < 16; i++) {
        assert(CRY_FFI(args,recv_u8,&v[i]) == 0);
    }
    for (int i = 0; i < 16; i++) {
        CRY_FFI(res,send_small_uint,(uint64_t)(v[i]));
    }
}

void test_record0(const struct CryValExporter* args, const struct CryValImporter* res) {}

void test_record1_u8(const struct CryValExporter* args, const struct CryValImporter* res) {
    test_u8(args, res);
}

void test_record2_u8_u16(const struct CryValExporter* args, const struct CryValImporter* res) {
    uint8_t v0;
    uint64_t v1;

    assert(CRY_FFI(args,recv_u8,&v0) == 0);
    assert(CRY_FFI(args,recv_u64,&v1) == 0);

    CRY_FFI(res,send_small_uint,(uint64_t)(v0));
    CRY_FFI(res,send_small_uint,v1);
}

void test_tuple0(const struct CryValExporter* args, const struct CryValImporter* res) {
    test_record0(args, res);
}

void test_tuple2_u8_u16(const struct CryValExporter* args, const struct CryValImporter* res) {
    test_record2_u8_u16(args, res);
}

void test_newtype_u8(const struct CryValExporter* args, const struct CryValImporter* res) {
    test_record1_u8(args, res);
}

static void unexpected_tag(const char* enum_name, uint64_t tag) {
    printf("Unexpected tag for %s: %" PRIu64 "\n", enum_name, tag);
    abort();
}

void test_option_u8(const struct CryValExporter* args, const struct CryValImporter* res) {
    uint64_t tag;
    uint8_t field;
    assert(CRY_FFI(args,recv_u64,&tag) == 0);
    switch (tag) {
    case 0:
        // None
        break;
    case 1:
        // Some
        assert(CRY_FFI(args,recv_u8,&field) == 0);
        break;
    default:
        unexpected_tag("Option", tag);
        break;
    }

    CRY_FFI(res,send_tag,tag);
    switch (tag) {
    case 0:
        // None
        break;
    case 1:
        // Some
        CRY_FFI(res,send_small_uint,(uint64_t)(field));
        break;
    default:
        unexpected_tag("Option", tag);
        break;
    }
}

void test_result_u16_u32(const struct CryValExporter* args, const struct CryValImporter* res) {
    uint64_t tag;
    uint64_t field;
    assert(CRY_FFI(args,recv_u64,&tag) == 0);
    switch (tag) {
    case 0:
        // Ok
        assert(CRY_FFI(args,recv_u64,&field) == 0);
        break;
    case 1:
        // Err
        assert(CRY_FFI(args,recv_u64,&field) == 0);
        break;
    default:
        unexpected_tag("Result", tag);
        break;
    }

    CRY_FFI(res,send_tag,tag);
    switch (tag) {
    case 0:
        // Ok
        CRY_FFI(res,send_small_uint,field);
        break;
    case 1:
        // Err
        CRY_FFI(res,send_small_uint,field);
        break;
    default:
        unexpected_tag("Result", tag);
        break;
    }
}

void test_two_u8_args(const struct CryValExporter* args, const struct CryValImporter* res) {
    uint8_t v0;
    uint8_t v1;

    assert(CRY_FFI(args,recv_u8,&v0) == 0);
    assert(CRY_FFI(args,recv_u8,&v1) == 0);

    CRY_FFI(res,send_small_uint,(uint64_t)(v0 - v1));
}
