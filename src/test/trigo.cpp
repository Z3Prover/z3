/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    trigo.cpp

Abstract:

    Test trigonometric primitives in the interval class.

Author:

    Leonardo de Moura (leonardo) 2012-08-20

Revision History:

--*/
#include<cstdlib>
#include"interval_def.h"
#include"dependency.h"
#include"mpq.h"
#include"ast.h"
#include"debug.h"
#include"im_float_config.h"
#include"rlimit.h"

#define PREC 100000

static void tst_sine_core(std::ostream & out, unsynch_mpq_manager & nm, interval_manager<im_default_config> & im, mpq & a, unsigned k) {
    scoped_mpq lo(nm), hi(nm);
    im.sine(a, k, lo, hi);
    nm.display(out, lo);
    out << " <= Sin["; nm.display(out, a); out << "]\n";
    out << "Sin["; nm.display(out, a); out << "] <= ";
    nm.display(out, hi);
    out << "\n";
}

static void tst_sine(std::ostream & out, unsigned N, unsigned k) {
    unsynch_mpq_manager                 nm;
    im_default_config                   imc(nm);
    reslimit rl;
    interval_manager<im_default_config> im(rl, imc);
    scoped_mpq a(nm);
    nm.set(a, 0);
    tst_sine_core(out, nm, im, a, 1);
    for (unsigned i = 0; i < N; i++) {
        nm.set(a, 4 * (rand() % PREC), PREC);
        if (rand() % 2 == 0)
            nm.neg(a);
        tst_sine_core(out, nm, im, a, k);
   }
}


static void tst_cosine_core(std::ostream & out, unsynch_mpq_manager & nm, interval_manager<im_default_config> & im, mpq & a, unsigned k) {
    scoped_mpq lo(nm), hi(nm);
    im.cosine(a, k, lo, hi);
    nm.display(out, lo);
    out << " <= Cos["; nm.display(out, a); out << "]\n";
    out << "Cos["; nm.display(out, a); out << "] <= ";
    nm.display(out, hi);
    out << "\n";
}

static void tst_cosine(std::ostream & out, unsigned N, unsigned k) {
    reslimit rl;
    unsynch_mpq_manager                 nm;
    im_default_config                   imc(nm);
    interval_manager<im_default_config> im(rl, imc);
    scoped_mpq a(nm);
    nm.set(a, 0);
    tst_cosine_core(out, nm, im, a, 1);
    for (unsigned i = 0; i < N; i++) {
        nm.set(a, 4 * (rand() % PREC), PREC);
        if (rand() % 2 == 0)
            nm.neg(a);
        tst_cosine_core(out, nm, im, a, k);
    }
}


template<typename fmanager>
static void tst_float_sine_core(std::ostream & out,
                                fmanager & fm,
                                interval_manager<im_float_config<fmanager> > & im,
                                typename fmanager::numeral & a,
                                unsigned k) {
    _scoped_numeral<fmanager> lo(fm), hi(fm);
    im.sine(a, k, lo, hi);
    out << fm.to_rational_string(lo) << " <= Sin[" << fm.to_rational_string(a) << "]\n";
    out << "Sin[" << fm.to_rational_string(a) << "] <= " << fm.to_rational_string(hi) << "\n";
}

const unsigned EBITS = 11;
const unsigned SBITS = 53;

template<typename fmanager>
static void tst_float_sine(std::ostream & out, unsigned N, unsigned k) {
    reslimit rl;
    fmanager                                     fm;
    im_float_config<fmanager>                    ifc(fm, EBITS, SBITS);
    interval_manager<im_float_config<fmanager> > im(rl, ifc);
    _scoped_numeral<fmanager> a(fm);
    fm.set(a, EBITS, SBITS, static_cast<int>(0));
    tst_float_sine_core(out, fm, im, a, 1);

    // fm.set(a, EBITS, SBITS, MPF_ROUND_TOWARD_POSITIVE, 25336, 100000);
    // tst_float_sine_core(out, fm, im, a, k);
    // return;
    for (unsigned i = 0; i < N; i++) {
        unsigned n = 4 * (rand() % PREC);
        unsigned d = PREC;
        TRACE("sine", tout << "next-val : " << n << "/" << d << "\n";);
        fm.set(a, EBITS, SBITS, MPF_ROUND_TOWARD_POSITIVE, n, d);
        if (rand() % 2 == 0)
            fm.neg(a);
        tst_float_sine_core(out, fm, im, a, k);
   }
}

#if 0
static void tst_mpf_bug() {
    mpf_manager fm;
    scoped_mpf a(fm), b(fm), c(fm);
    fm.set(a, EBITS, SBITS, 2);
    fm.set(b, EBITS, SBITS, 3);
    std::cout << "a: " << fm.to_double(a) << "\n";
    std::cout << "b: " << fm.to_double(b) << "\n";
    fm.mul(MPF_ROUND_TOWARD_NEGATIVE, a, b, c);
    std::cout << "c: " << fm.to_double(c) << "\n";
}
#endif

static void tst_e(std::ostream & out) {
    reslimit rl;
    unsynch_mpq_manager                 nm;
    im_default_config                   imc(nm);
    interval_manager<im_default_config> im(rl, imc);
    im_default_config::interval         r;
    for (unsigned i = 0; i < 64; i++) {
        im.e(i, r);
        out << nm.to_string(im.lower(r)) << " <= E\n";
        out << "E <= " << nm.to_string(im.upper(r)) << "\n";
    }
    im.del(r);
}

static void tst_e_float(std::ostream & out) {
    std::cout << "e float...\n";
    reslimit rl;
    unsynch_mpq_manager   qm;
    mpf_manager           fm;
    im_float_config<mpf_manager>                    ifc(fm);
    interval_manager<im_float_config<mpf_manager> > im(rl, ifc);
    scoped_mpq q(qm);
    im_float_config<mpf_manager>::interval r;
    for (unsigned i = 0; i < 64; i++) {
        im.e(i, r);
        out << fm.to_rational_string(im.lower(r)) << " <= E\n";
        out << "E <= " << fm.to_rational_string(im.upper(r)) << "\n";
    }
    del_f_interval(ifc, r);
}

void tst_trigo() {
    // enable_trace("sine");
    // enable_trace("sine_bug");
    // enable_trace("mpf_mul_bug");
    std::ofstream out("trigo-lemmas.math");
    tst_e_float(out);
    tst_e(out);
    tst_float_sine<mpf_manager>(out, 100, 5);
    tst_float_sine<mpf_manager>(out, 100, 7);
    tst_sine(out, 200, 3);
    tst_sine(out, 200, 5);
    tst_sine(out, 200, 9);
    tst_cosine(out, 200, 3);
    tst_cosine(out, 200, 5);
    tst_cosine(out, 200, 9);
}
