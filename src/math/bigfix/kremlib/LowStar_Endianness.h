/*
  Copyright (c) INRIA and Microsoft Corporation. All rights reserved.
  Licensed under the Apache 2.0 License.
*/


#ifndef __LowStar_Endianness_H
#define __LowStar_Endianness_H
#include <inttypes.h>
#include <stdbool.h>
#include "math/bigfix/kremlin/lowstar_endianness.h"
#include "math/bigfix/kremlin/internal/types.h"
#include "math/bigfix/kremlin/internal/target.h"
#include "math/bigfix/kremlib/FStar_UInt128.h"

static inline void store128_le(uint8_t *x0, FStar_UInt128_uint128 x1);

static inline FStar_UInt128_uint128 load128_le(uint8_t *x0);

static inline void store128_be(uint8_t *x0, FStar_UInt128_uint128 x1);

static inline FStar_UInt128_uint128 load128_be(uint8_t *x0);


#define __LowStar_Endianness_H_DEFINED
#endif
