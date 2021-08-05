/* MIT License
 *
 * Copyright (c) 2016-2020 INRIA, CMU and Microsoft Corporation
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */


#ifndef __Hacl_Bignum_H
#define __Hacl_Bignum_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "math/bigfix/lib_intrinsics.h"
#include "math/bigfix/types.h"
#include "math/bigfix/LowStar_Endianness.h"
#include <string.h>
#include "math/bigfix/target.h"

#include "math/bigfix/Hacl_Bignum_Base.h"

void Hacl_Bignum_Convert_bn_from_bytes_be_uint64(uint32_t len, uint8_t *b, uint64_t *res);

void Hacl_Bignum_Convert_bn_to_bytes_be_uint64(uint32_t len, uint64_t *b, uint8_t *res);

uint32_t Hacl_Bignum_Lib_bn_get_top_index_u32(uint32_t len, uint32_t *b);

uint64_t Hacl_Bignum_Lib_bn_get_top_index_u64(uint32_t len, uint64_t *b);

uint32_t
Hacl_Bignum_Addition_bn_sub_eq_len_u32(uint32_t aLen, uint32_t *a, uint32_t *b, uint32_t *res);

uint64_t
Hacl_Bignum_Addition_bn_sub_eq_len_u64(uint32_t aLen, uint64_t *a, uint64_t *b, uint64_t *res);

uint32_t
Hacl_Bignum_Addition_bn_add_eq_len_u32(uint32_t aLen, uint32_t *a, uint32_t *b, uint32_t *res);

uint64_t
Hacl_Bignum_Addition_bn_add_eq_len_u64(uint32_t aLen, uint64_t *a, uint64_t *b, uint64_t *res);

void
Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint32(
  uint32_t aLen,
  uint32_t *a,
  uint32_t *b,
  uint32_t *tmp,
  uint32_t *res
);

void
Hacl_Bignum_Karatsuba_bn_karatsuba_mul_uint64(
  uint32_t aLen,
  uint64_t *a,
  uint64_t *b,
  uint64_t *tmp,
  uint64_t *res
);

void
Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint32(
  uint32_t aLen,
  uint32_t *a,
  uint32_t *tmp,
  uint32_t *res
);

void
Hacl_Bignum_Karatsuba_bn_karatsuba_sqr_uint64(
  uint32_t aLen,
  uint64_t *a,
  uint64_t *tmp,
  uint64_t *res
);

void
Hacl_Bignum_bn_add_mod_n_u32(
  uint32_t len1,
  uint32_t *n,
  uint32_t *a,
  uint32_t *b,
  uint32_t *res
);

void
Hacl_Bignum_bn_add_mod_n_u64(
  uint32_t len1,
  uint64_t *n,
  uint64_t *a,
  uint64_t *b,
  uint64_t *res
);

uint32_t Hacl_Bignum_ModInvLimb_mod_inv_uint32(uint32_t n0);

uint64_t Hacl_Bignum_ModInvLimb_mod_inv_uint64(uint64_t n0);

uint32_t Hacl_Bignum_Montgomery_bn_check_modulus_u32(uint32_t len, uint32_t *n);

void
Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u32(
  uint32_t len,
  uint32_t nBits,
  uint32_t *n,
  uint32_t *res
);

void
Hacl_Bignum_Montgomery_bn_mont_reduction_u32(
  uint32_t len,
  uint32_t *n,
  uint32_t nInv,
  uint32_t *c,
  uint32_t *res
);

void
Hacl_Bignum_Montgomery_bn_to_mont_u32(
  uint32_t len,
  uint32_t *n,
  uint32_t nInv,
  uint32_t *r2,
  uint32_t *a,
  uint32_t *aM
);

void
Hacl_Bignum_Montgomery_bn_from_mont_u32(
  uint32_t len,
  uint32_t *n,
  uint32_t nInv_u64,
  uint32_t *aM,
  uint32_t *a
);

void
Hacl_Bignum_Montgomery_bn_mont_mul_u32(
  uint32_t len,
  uint32_t *n,
  uint32_t nInv_u64,
  uint32_t *aM,
  uint32_t *bM,
  uint32_t *resM
);

void
Hacl_Bignum_Montgomery_bn_mont_sqr_u32(
  uint32_t len,
  uint32_t *n,
  uint32_t nInv_u64,
  uint32_t *aM,
  uint32_t *resM
);

uint64_t Hacl_Bignum_Montgomery_bn_check_modulus_u64(uint32_t len, uint64_t *n);

void
Hacl_Bignum_Montgomery_bn_precomp_r2_mod_n_u64(
  uint32_t len,
  uint32_t nBits,
  uint64_t *n,
  uint64_t *res
);

void
Hacl_Bignum_Montgomery_bn_mont_reduction_u64(
  uint32_t len,
  uint64_t *n,
  uint64_t nInv,
  uint64_t *c,
  uint64_t *res
);

void
Hacl_Bignum_Montgomery_bn_to_mont_u64(
  uint32_t len,
  uint64_t *n,
  uint64_t nInv,
  uint64_t *r2,
  uint64_t *a,
  uint64_t *aM
);

void
Hacl_Bignum_Montgomery_bn_from_mont_u64(
  uint32_t len,
  uint64_t *n,
  uint64_t nInv_u64,
  uint64_t *aM,
  uint64_t *a
);

void
Hacl_Bignum_Montgomery_bn_mont_mul_u64(
  uint32_t len,
  uint64_t *n,
  uint64_t nInv_u64,
  uint64_t *aM,
  uint64_t *bM,
  uint64_t *resM
);

void
Hacl_Bignum_Montgomery_bn_mont_sqr_u64(
  uint32_t len,
  uint64_t *n,
  uint64_t nInv_u64,
  uint64_t *aM,
  uint64_t *resM
);

uint32_t
Hacl_Bignum_Exponentiation_bn_check_mod_exp_u32(
  uint32_t len,
  uint32_t *n,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b
);

void
Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_precomp_u32(
  uint32_t len,
  uint32_t *n,
  uint32_t mu,
  uint32_t *r2,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
);

void
Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_precomp_u32(
  uint32_t len,
  uint32_t *n,
  uint32_t mu,
  uint32_t *r2,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
);

void
Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_u32(
  uint32_t len,
  uint32_t nBits,
  uint32_t *n,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
);

void
Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_u32(
  uint32_t len,
  uint32_t nBits,
  uint32_t *n,
  uint32_t *a,
  uint32_t bBits,
  uint32_t *b,
  uint32_t *res
);

uint64_t
Hacl_Bignum_Exponentiation_bn_check_mod_exp_u64(
  uint32_t len,
  uint64_t *n,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b
);

void
Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_precomp_u64(
  uint32_t len,
  uint64_t *n,
  uint64_t mu,
  uint64_t *r2,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
);

void
Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_precomp_u64(
  uint32_t len,
  uint64_t *n,
  uint64_t mu,
  uint64_t *r2,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
);

void
Hacl_Bignum_Exponentiation_bn_mod_exp_vartime_u64(
  uint32_t len,
  uint32_t nBits,
  uint64_t *n,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
);

void
Hacl_Bignum_Exponentiation_bn_mod_exp_consttime_u64(
  uint32_t len,
  uint32_t nBits,
  uint64_t *n,
  uint64_t *a,
  uint32_t bBits,
  uint64_t *b,
  uint64_t *res
);

#if defined(__cplusplus)
}
#endif

#define __Hacl_Bignum_H_DEFINED
#endif
