/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    sign.h

Abstract:

    Sign

Author:

    Nikolaj Bjorner

--*/

#pragma once

typedef enum { sign_neg = -1, sign_zero = 0, sign_pos = 1} sign;
inline sign operator-(sign s) { switch (s) { case sign_neg: return sign_pos; case sign_pos: return sign_neg; default: return sign_zero; } };
inline sign to_sign(int s) { return s == 0 ? sign_zero : (s > 0 ? sign_pos : sign_neg); }
inline sign operator*(sign a, sign b) { return to_sign((int)a * (int)b); }
inline bool is_zero(sign s) { return s == sign_zero; }
