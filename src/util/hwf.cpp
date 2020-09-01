/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    hwf.cpp

Abstract:

    Hardware Floating Point Numbers

Author:

    Christoph Wintersteiger (cwinter) 2012-07-30.

Revision History:

--*/
#include<math.h>
#include<float.h>
#include<sstream>

#ifdef _WINDOWS
#if defined(_MSC_VER)
#pragma float_control( except, on )   // exception semantics; this does _not_ mean that exceptions are enabled (we want them off!)
#pragma float_control( precise, on )  // precise semantics (no guessing!)
#pragma fp_contract(off)              // contractions off (`contraction' means x*y+z is turned into a fused-mul-add).
#pragma fenv_access(on)               // fpu environment sensitivity (needed to be allowed to make FPU mode changes).
#endif
#else
#include<fenv.h>
#endif

#if defined(__x86_64__) || defined(_M_X64) ||    \
    defined(__i386) || defined(_M_IX86)
#define USE_INTRINSICS
#endif

#include "util/hwf.h"

// Note:
// Which FPU will be used is determined by compiler settings. On x64 it's always SSE2,
// on x86 we have to chose SSE2 by enabling /arch:SSE2 (otherwise the x87 FPU will be used).
// Christoph has decided that we don't want to use the x87; this makes everything a lot easier.


// For SSE2, it is best to use compiler intrinsics because this makes it completely
// clear to the compiler what instructions should be used. E.g., for sqrt(), the Windows compiler selects
// the x87 FPU, even when /arch:SSE2 is on.
// Luckily, these are kind of standardized, at least for Windows/Linux/macOS.
#if defined(__clang__) || defined(_M_ARM) && defined(_M_ARM64)
#undef USE_INTRINSICS
#endif

#ifdef USE_INTRINSICS
#include <emmintrin.h>
#if defined(_MSC_VER) || defined(__SSE4_1__)
#include <smmintrin.h>
#endif
#endif

hwf_manager::hwf_manager() :
    m_mpz_manager(m_mpq_manager)
{
#ifdef _WINDOWS
#if defined(_WIN64)
    // Precision control is not supported on x64.
    // See: http://msdn.microsoft.com/en-us/library/e9b52ceh(VS.110).aspx
    // CMW: I think this is okay though, the compiler will chose the right instructions
    // (the x64/SSE2 FPU has separate instructions for different precisions).
#else
    // Setting the precision should only be required on the x87, but it won't hurt to do it anyways.
    // _PC_53 means double precision (53 significand bits). For extended precision use _PC_64.

#ifndef USE_INTRINSICS
    __control87_2(_PC_53, _MCW_PC, &x86_state, &sse2_state);
#endif
#endif
#else
    // macOS/Linux: Nothing.
#endif

    // We only set the precision of the FPU here in the constructor. At the moment, there are no
    // other parts of the code that could overwrite this, and Windows takes care of context switches.

    // CMW: I'm not sure what happens on CPUs with hyper-threading (since the FPU is shared).
    // I have yet to discover whether Linux and macOS save the FPU state when switching context.
    // As long as we stick to using the SSE2 FPU though, there shouldn't be any problems with respect
    // to the precision (not sure about the rounding modes though).
}

hwf_manager::~hwf_manager()
{
}

uint64_t RAW(double X) { uint64_t tmp; memcpy(&tmp, &(X), sizeof(uint64_t)); return tmp; }
double DBL(uint64_t X) { double tmp; memcpy(&tmp, &(X), sizeof(double)); return tmp; }

void hwf_manager::set(hwf & o, int value) {
    o.value = (double) value;
}

void hwf_manager::set(hwf & o, mpf_rounding_mode rm, int n, int d) {
    set_rounding_mode(rm);
    o.value = ((double) n)/((double) d);
}

void hwf_manager::set(hwf & o, double value) {
    o.value = value;
}

void hwf_manager::set(hwf & o, float value) {
    o.value = (double)value;
}

void hwf_manager::set(hwf & o, mpf_rounding_mode rm, mpq const & value) {
    set_rounding_mode(rm);
    o.value = m_mpq_manager.get_double(value);
}

void hwf_manager::set(hwf & o, mpf_rounding_mode rm, char const * value) {
    // We expect [i].[f]P[e], where P means that the exponent is interpreted as 2^e instead of 10^e.

    std::string v(value);
    size_t e_pos = v.find('p');
    if (e_pos == std::string::npos) e_pos = v.find('P');

    std::string f, e;

    f = (e_pos != std::string::npos) ? v.substr(0, e_pos) : v;
    e = (e_pos != std::string::npos) ? v.substr(e_pos+1) : "0";

    TRACE("mpf_dbg", tout << " f = " << f << " e = " << e << std::endl;);

    mpq q;
    m_mpq_manager.set(q, f.c_str());

    mpz ex;
    m_mpz_manager.set(ex, e.c_str());

    set(o, rm, q, ex);

    TRACE("mpf_dbg", tout << "set: res = " << to_string(o) << std::endl;);
}

void hwf_manager::set(hwf & o, mpf_rounding_mode rm, mpq const & significand, mpz const & exponent) {
    // Assumption: this represents significand * 2^exponent.
    set_rounding_mode(rm);

    mpq sig;
    m_mpq_manager.set(sig, significand);
    int64_t exp = m_mpz_manager.get_int64(exponent);

    if (m_mpq_manager.is_zero(significand))
        o.value = 0.0;
    else
    {
        while (m_mpq_manager.lt(sig, 1))
        {
            m_mpq_manager.mul(sig, 2, sig);
            exp--;
        }

        hwf s; s.value = m_mpq_manager.get_double(sig);
        uint64_t r = (RAW(s.value) & 0x800FFFFFFFFFFFFFull) | ((exp + 1023) << 52);
        o.value = DBL(r);
    }
}

void hwf_manager::set(hwf & o, bool sign, uint64_t significand, int exponent) {
    // Assumption: this represents (sign * -1) * (significand/2^sbits) * 2^exponent.
    SASSERT(significand <= 0x000FFFFFFFFFFFFFull);
    SASSERT(-1022 <= exponent && exponent <= 1023);
    uint64_t raw = (sign?0x8000000000000000ull:0);
    raw |= (((uint64_t)exponent) + 1023) << 52;
    raw |= significand;
    memcpy(&o.value, &raw, sizeof(double));
}

void hwf_manager::set(hwf & o, hwf const & x) {
    o.value = x.value;
}

void hwf_manager::abs(hwf & o) {
    o.value = fabs(o.value);
}

void hwf_manager::abs(hwf const & x, hwf & o) {
    o.value = fabs(x.value);
}

void hwf_manager::neg(hwf & o) {
    o.value = -o.value;
}

void hwf_manager::neg(hwf const & x, hwf & o) {
    o.value = -x.value;
}

bool hwf_manager::eq(hwf const & x, hwf const & y) {
    return (x.value == y.value);
}

bool hwf_manager::lt(hwf const & x, hwf const & y) {
    return (x.value < y.value);
}

bool hwf_manager::lte(hwf const & x, hwf const & y) {
    return (x.value <= y.value);
}

bool hwf_manager::gt(hwf const & x, hwf const & y) {
    return (x.value > y.value);
}

bool hwf_manager::gte(hwf const & x, hwf const & y) {
    return (x.value >= y.value);
}

void hwf_manager::add(mpf_rounding_mode rm, hwf const & x, hwf const & y, hwf & o) {
    set_rounding_mode(rm);
#ifdef USE_INTRINSICS
    _mm_store_sd(&o.value, _mm_add_sd(_mm_set_sd(x.value), _mm_set_sd(y.value)));
#else
    o.value = x.value + y.value;
#endif
}

void hwf_manager::sub(mpf_rounding_mode rm, hwf const & x, hwf const & y, hwf & o) {
    set_rounding_mode(rm);
#ifdef USE_INTRINSICS
    _mm_store_sd(&o.value, _mm_sub_sd(_mm_set_sd(x.value), _mm_set_sd(y.value)));
#else
    o.value = x.value - y.value;
#endif
}

#define DBL_SCALE 15360

void hwf_manager::mul(mpf_rounding_mode rm, hwf const & x, hwf const & y, hwf & o) {
    set_rounding_mode(rm);
#ifdef USE_INTRINSICS
    _mm_store_sd(&o.value, _mm_mul_sd(_mm_set_sd(x.value), _mm_set_sd(y.value)));
#else
    o.value = x.value * y.value;
#endif
}

void hwf_manager::div(mpf_rounding_mode rm, hwf const & x, hwf const & y, hwf & o) {
    set_rounding_mode(rm);
#ifdef USE_INTRINSICS
    _mm_store_sd(&o.value, _mm_div_sd(_mm_set_sd(x.value), _mm_set_sd(y.value)));
#else
    o.value = x.value / y.value;
#endif
}

void hwf_manager::fma(mpf_rounding_mode rm, hwf const & x, hwf const & y, hwf const &z, hwf & o) {
    set_rounding_mode(rm);
    o.value = ::fma(x.value, y.value, z.value);
}

void hwf_manager::sqrt(mpf_rounding_mode rm, hwf const & x, hwf & o) {
    set_rounding_mode(rm);
#ifdef USE_INTRINSICS
    _mm_store_sd(&o.value, _mm_sqrt_pd(_mm_set_sd(x.value)));
#else
    o.value = ::sqrt(x.value);
#endif
}

void hwf_manager::round_to_integral(mpf_rounding_mode rm, hwf const & x, hwf & o) {
    set_rounding_mode(rm);
    // CMW: modf is not the right function here.
    // modf(x.value, &o.value);

    // According to the Intel Architecture manual, the x87-instruction FRNDINT is the
    // same in 32-bit and 64-bit mode. The _mm_round_* intrinsics are SSE4 extensions.
#if defined(_WINDOWS) && !defined(_M_ARM) && !defined(_M_ARM64)
#if defined( __MINGW32__ ) && ( defined( __GNUG__ ) || defined( __clang__ ) )
    o.value = nearbyint(x.value);
#else
  #if defined(USE_INTRINSICS) &&                                           \
    (defined(_WINDOWS) && (defined(__AVX__) || defined(_M_X64))) || \
    (!defined(_WINDOWS) && defined(__SSE4_1__))
    switch (rm) {
    case 0: _mm_store_sd(&o.value, _mm_round_pd(_mm_set_sd(x.value), _MM_FROUND_TO_NEAREST_INT)); break;
    case 2: _mm_store_sd(&o.value, _mm_round_pd(_mm_set_sd(x.value), _MM_FROUND_TO_POS_INF)); break;
    case 3: _mm_store_sd(&o.value, _mm_round_pd(_mm_set_sd(x.value), _MM_FROUND_TO_NEG_INF)); break;
    case 4: _mm_store_sd(&o.value, _mm_round_pd(_mm_set_sd(x.value), _MM_FROUND_TO_ZERO)); break;
    case 1:
        UNREACHABLE(); // Note: MPF_ROUND_NEAREST_TAWAY is not supported by the hardware!
        break;
    default:
        UNREACHABLE(); // Unknown rounding mode.
    }
  #else
    double xv = x.value;
    double & ov = o.value;

    __asm {
        fld     xv
        frndint
        fstp    ov // Store result away.
    }
  #endif
#endif
#else
    // Linux, macOS.
    o.value = nearbyint(x.value);
#endif
}

void hwf_manager::rem(hwf const & x, hwf const & y, hwf & o) {
#if defined(_WINDOWS) && _MSC_VER <= 1700
    o.value = fmod(x.value, y.value);
    if (o.value >= (y.value/2.0))
        o.value -= y.value;
#else
    o.value = remainder(x.value, y.value);
#endif
}

void hwf_manager::maximum(hwf const & x, hwf const & y, hwf & o) {
#ifdef USE_INTRINSICS
    _mm_store_sd(&o.value, _mm_max_sd(_mm_set_sd(x.value), _mm_set_sd(y.value)));
#else
    // use __max ?
    if (is_nan(x))
        o.value = y.value;
    else if (is_nan(y))
        o.value = x.value;
    else if (lt(x, y))
        o.value = y.value;
    else
        o.value = x.value;
#endif
}

void hwf_manager::minimum(hwf const & x, hwf const & y, hwf & o) {
#ifdef USE_INTRINSICS
    _mm_store_sd(&o.value, _mm_min_sd(_mm_set_sd(x.value), _mm_set_sd(y.value)));
#else
    // use __min ?
    if (is_nan(x))
        o.value = y.value;
    else if (is_nan(y))
        o.value = x.value;
    else if (lt(x, y))
        o.value = x.value;
    else
        o.value = y.value;
#endif
}

std::string hwf_manager::to_string(hwf const & x) {
    std::stringstream ss("");
    ss << std::scientific << x.value;
    return ss.str();
}

std::string hwf_manager::to_rational_string(hwf const & a) {
    // temporary hack
    unsynch_mpq_manager qm;
    scoped_mpq q(qm);
    to_rational(a, q);
    return qm.to_string(q);
}

void hwf_manager::display_decimal(std::ostream & out, hwf const & a, unsigned k) {
    // temporary hack
    unsynch_mpq_manager qm;
    scoped_mpq q(qm);
    to_rational(a, q);
    qm.display_decimal(out, q, k);
}

void hwf_manager::display_smt2(std::ostream & out, hwf const & a, bool decimal) {
    // temporary hack
    unsynch_mpq_manager qm;
    scoped_mpq q(qm);
    to_rational(a, q);
    qm.display_smt2(out, q, decimal);
}

void hwf_manager::to_rational(hwf const & x, unsynch_mpq_manager & qm, mpq & o) {
    SASSERT(is_normal(x) || is_denormal(x) || is_zero(x));
    scoped_mpz n(qm), d(qm);

    if (is_normal(x))
        qm.set(n, (uint64_t)(sig(x) | 0x0010000000000000ull));
    else
        qm.set(n, sig(x));
    if (sgn(x))
        qm.neg(n);
    qm.set(d, (uint64_t)0x0010000000000000ull);
    int e = exp(x);
    if (e >= 0)
        qm.mul2k(n, (unsigned)e);
    else
        qm.mul2k(d, (unsigned)-e);
    qm.set(o, n, d);
}

bool hwf_manager::is_zero(hwf const & x) {
    uint64_t t = RAW(x.value) & 0x7FFFFFFFFFFFFFFFull;
    return (t == 0x0ull);
    // CMW: I tried, and these are slower:
    // return (t != 0x0ull) ? false  : true;
    // return (x.value == 0.0 || x.value == -0.0); // [uses SSE2].
}

bool hwf_manager::is_neg(hwf const & x) {
    // [Leo]: I added !is_nan(x)
    return sgn(x) && !is_nan(x);
}

bool hwf_manager::is_pos(hwf const & x) {
    return !sgn(x) && !is_nan(x);
}

bool hwf_manager::is_nzero(hwf const & x) {
    return RAW(x.value) == 0x8000000000000000ull;
}

bool hwf_manager::is_pzero(hwf const & x) {
    return RAW(x.value) == 0x0000000000000000ull;
}

bool hwf_manager::is_one(hwf const & x) {
    return RAW(x.value) == 0x3FF0000000000000ull;
}

bool hwf_manager::is_nan(hwf const & x) {
    bool r = ((RAW(x.value) & 0x7FF0000000000000ull) == 0x7FF0000000000000ull) &&
             ((RAW(x.value) & 0x000FFFFFFFFFFFFFull) != 0x0);
#ifdef _WINDOWS
    SASSERT( !r || (_fpclass(x.value) == _FPCLASS_SNAN || _fpclass(x.value) == _FPCLASS_QNAN));
#endif
    return r;
}

bool hwf_manager::is_inf(hwf const & x) {
    bool r = ((RAW(x.value) & 0x7FF0000000000000ull) == 0x7FF0000000000000ull) &&
             ((RAW(x.value) & 0x000FFFFFFFFFFFFFull) == 0x0);
#ifdef _WINDOWS
    SASSERT( !r || (_fpclass(x.value) == _FPCLASS_NINF || _fpclass(x.value) == _FPCLASS_PINF));
#endif
    return r;
}

bool hwf_manager::is_pinf(hwf const & x) {
    return !sgn(x) && is_inf(x);
}

bool hwf_manager::is_ninf(hwf const & x) {
    return sgn(x) && is_inf(x);
}

bool hwf_manager::is_normal(hwf const & x) {
    uint64_t t = RAW(x.value) & 0x7FF0000000000000ull;
    return (t != 0x0ull && t != 0x7FF0000000000000ull);
}

bool hwf_manager::is_denormal(hwf const & x) {
    uint64_t t = RAW(x.value);
    return ((t & 0x7FF0000000000000ull) == 0x0 &&
            (t & 0x000FFFFFFFFFFFFFull) != 0x0);
}

bool hwf_manager::is_regular(hwf const & x) {
    // Everything that doesn't have the top-exponent is considered regular.
    // Note that +-0.0 and denormal numbers have exponent==0; these are regular.
    // All normal numbers are also regular. What remains is +-Inf and NaN, they are
    // not regular and they are the only numbers that have exponent 7FF.
    uint64_t e = RAW(x.value) & 0x7FF0000000000000ull; // the exponent
    return (e != 0x7FF0000000000000ull);
}

bool hwf_manager::is_int(hwf const & x) {
    if (!is_normal(x))
        return false;

    const int e = exp(x);
    if (e >= 52)
        return true;
    else if (e < 0)
        return false;
    else
    {
        uint64_t t = sig(x);
        unsigned shift = 52 - ((unsigned)e);
        uint64_t mask = (0x1ull << shift) - 1;
        return (t & mask) == 0;
    }
}

void hwf_manager::mk_nzero(hwf & o) {
    uint64_t raw = 0x8000000000000000ull;
    o.value = DBL(raw);
}

void hwf_manager::mk_pzero(hwf & o) {
    o.value = 0;
}

void hwf_manager::mk_zero(bool sign, hwf & o) {
    if (sign)
        mk_nzero(o);
    else
        mk_pzero(o);
}

void hwf_manager::mk_nan(hwf & o) {
    uint64_t raw = 0x7FF0000000000001ull;
    o.value = DBL(raw);
}

void hwf_manager::mk_inf(bool sign, hwf & o) {
    uint64_t raw = (sign) ? 0xFFF0000000000000ull : 0x7FF0000000000000ull;
    o.value = DBL(raw);
}

void hwf_manager::mk_pinf(hwf & o) {
    uint64_t raw = 0x7FF0000000000000ull;
    o.value = DBL(raw);
}

void hwf_manager::mk_ninf(hwf & o) {
    uint64_t raw = 0xFFF0000000000000ull;
    o.value = DBL(raw);
}

#ifdef _WINDOWS
#if defined(_WIN64)
#ifdef USE_INTRINSICS
#define SETRM(RM) _MM_SET_ROUNDING_MODE(RM)
#else
#define SETRM(RM) _controlfp_s(&sse2_state, RM, _MCW_RC);
#endif
#else
#ifdef USE_INTRINSICS
#define SETRM(RM) _MM_SET_ROUNDING_MODE(RM)
#else
#define SETRM(RM) __control87_2(RM, _MCW_RC, &x86_state, &sse2_state)
#endif
#endif
#else
#define SETRM(RM) fesetround(RM)
#endif

unsigned hwf_manager::prev_power_of_two(hwf const & a) {
    SASSERT(!is_nan(a) && !is_pinf(a) && !is_ninf(a));
    if (!is_pos(a))
        return 0;
    if (exp(a) <= -52)
        return 0;
    return 51 + exp(a);
}

void hwf_manager::set_rounding_mode(mpf_rounding_mode rm)
{
#ifdef _WINDOWS
#ifdef USE_INTRINSICS
    switch (rm) {
    case MPF_ROUND_NEAREST_TEVEN:
        SETRM(_MM_ROUND_NEAREST);
        break;
    case MPF_ROUND_TOWARD_POSITIVE:
        SETRM(_MM_ROUND_UP);
        break;
    case MPF_ROUND_TOWARD_NEGATIVE:
        SETRM(_MM_ROUND_DOWN);
        break;
    case MPF_ROUND_TOWARD_ZERO:
        SETRM(_MM_ROUND_TOWARD_ZERO);
        break;
    case MPF_ROUND_NEAREST_TAWAY:
    default:
        UNREACHABLE(); // Note: MPF_ROUND_NEAREST_TAWAY is not supported by the hardware!
    }
#else
    switch (rm) {
    case MPF_ROUND_NEAREST_TEVEN:
        SETRM(_RC_NEAR);
        break;
    case MPF_ROUND_TOWARD_POSITIVE:
        SETRM(_RC_UP);
        break;
    case MPF_ROUND_TOWARD_NEGATIVE:
        SETRM(_RC_DOWN);
        break;
    case MPF_ROUND_TOWARD_ZERO:
        SETRM(_RC_CHOP);
        break;
    case MPF_ROUND_NEAREST_TAWAY:
    default:
        UNREACHABLE(); // Note: MPF_ROUND_NEAREST_TAWAY is not supported by the hardware!
    }
#endif
#else // macOS/Linux
    switch (rm) {
    case MPF_ROUND_NEAREST_TEVEN:
        SETRM(FE_TONEAREST);
        break;
    case MPF_ROUND_TOWARD_POSITIVE:
        SETRM(FE_UPWARD);
        break;
    case MPF_ROUND_TOWARD_NEGATIVE:
        SETRM(FE_DOWNWARD);
        break;
    case MPF_ROUND_TOWARD_ZERO:
        SETRM(FE_TOWARDZERO);
        break;
    case MPF_ROUND_NEAREST_TAWAY:
    default:
        UNREACHABLE(); // Note: MPF_ROUND_NEAREST_TAWAY is not supported by the hardware!
    }
#endif
}
