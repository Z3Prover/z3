/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    interval.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-12-10.

Revision History:

--*/
#include"old_interval.h"

static void tst1() {
    ext_numeral inf(true);
    ext_numeral minus_inf(false);
    ext_numeral zero(0);

    SASSERT(ext_numeral(10) + ext_numeral(3) == ext_numeral(13));
    SASSERT(inf + zero == inf);
    SASSERT(minus_inf + zero == minus_inf);
    SASSERT(minus_inf + ext_numeral(3) == minus_inf);
    SASSERT(inf + inf == inf);
    SASSERT(minus_inf + minus_inf == minus_inf);
    SASSERT(minus_inf + ext_numeral(10) == minus_inf);
    SASSERT(minus_inf + ext_numeral(-10) == minus_inf);
    SASSERT(inf + ext_numeral(10) == inf);
    SASSERT(inf + ext_numeral(-10) == inf);

    SASSERT(ext_numeral(10) - ext_numeral(3) == ext_numeral(7));
    SASSERT(inf - zero == inf);
    SASSERT(minus_inf - zero == minus_inf);
    SASSERT(minus_inf - ext_numeral(3) == minus_inf);
    SASSERT(inf - minus_inf == inf);
    SASSERT(minus_inf - inf == minus_inf);
    SASSERT(zero - minus_inf == inf);
    SASSERT(zero - inf == minus_inf);
    SASSERT(ext_numeral(-10) - minus_inf == inf);
    SASSERT(ext_numeral(10) - minus_inf == inf);
    SASSERT(ext_numeral(-10) - inf == minus_inf);
    SASSERT(ext_numeral(10) - inf == minus_inf);

    SASSERT(ext_numeral(10) * inf == inf);
    SASSERT(ext_numeral(-10) * inf == minus_inf);
    SASSERT(zero * inf == zero);
    SASSERT(zero * minus_inf == zero);
    SASSERT(zero * ext_numeral(10) == zero);
    SASSERT(ext_numeral(10) * ext_numeral(-20) == ext_numeral(-200));
    SASSERT(ext_numeral(3) * ext_numeral(2) == ext_numeral(6));
    SASSERT(inf * inf == inf);
    SASSERT(inf * minus_inf == minus_inf);
    SASSERT(minus_inf * minus_inf == inf);
    SASSERT(minus_inf * inf == minus_inf);
    SASSERT(minus_inf * ext_numeral(10) == minus_inf);
    SASSERT(minus_inf * ext_numeral(-10) == inf);

    SASSERT(minus_inf < inf);
    SASSERT(!(inf < minus_inf));
    SASSERT(minus_inf < ext_numeral(10));
    SASSERT(ext_numeral(-3) < inf);
    SASSERT(ext_numeral(-10) < ext_numeral(4));
    SASSERT(ext_numeral(2) < ext_numeral(10));
    SASSERT(!(inf < ext_numeral(30)));
    SASSERT(!(ext_numeral(10) < minus_inf));
    SASSERT(!(inf < inf));
    SASSERT(!(minus_inf < minus_inf));
    SASSERT(!(zero < zero));
    SASSERT(!(ext_numeral(10) < ext_numeral(10)));
    SASSERT(inf > minus_inf);
    SASSERT(inf > zero);
    SASSERT(inf > ext_numeral(10));
    SASSERT(ext_numeral(10) > minus_inf);
    SASSERT(zero > minus_inf);
    SASSERT(!(zero > inf));
    SASSERT(!(minus_inf > inf));
    SASSERT(inf >= minus_inf);
    SASSERT(inf >= inf);
    SASSERT(minus_inf >= minus_inf);
    SASSERT(inf >= zero);
    SASSERT(zero >= minus_inf);
    SASSERT(inf <= inf);
    SASSERT(minus_inf <= minus_inf);
    SASSERT(zero <= inf);
    SASSERT(minus_inf <= zero);

    ext_numeral val(10);
    val.neg();
    SASSERT(val == ext_numeral(-10));
    val = inf;
    val.neg();
    SASSERT(val == minus_inf);
    val.neg();
    SASSERT(val == inf);

    SASSERT(minus_inf.sign());
    SASSERT(!zero.sign());
    SASSERT(!inf.sign());
    SASSERT(ext_numeral(-10).sign());
    SASSERT(!ext_numeral(10).sign());
    
    SASSERT(inf.is_infinite());
    SASSERT(minus_inf.is_infinite());
    SASSERT(!zero.is_infinite());
    SASSERT(!ext_numeral(10).is_infinite());
    SASSERT(!inf.is_zero());
    SASSERT(!minus_inf.is_zero());
    SASSERT(zero.is_zero());
    SASSERT(!ext_numeral(10).is_zero());
}

class interval_tester {
    v_dependency_manager m;
    
    interval singleton(int i) { return interval(m, rational(i)); }
    interval all() { return interval(m); }
    interval l(int i, bool o = false, int idx = 0) { return interval(m, rational(i), o, true, idx == 0 ? 0 : m.mk_leaf(reinterpret_cast<void*>(idx))); }
    interval r(int i, bool o = false, int idx = 0) { return interval(m, rational(i), o, false, idx == 0 ? 0 : m.mk_leaf(reinterpret_cast<void*>(idx))); }
    interval b(int l, int u, bool lo = false, bool uo = false, int idx_l = 0, int idx_u = 0) {
        return interval(m, rational(l), lo, idx_l == 0 ? 0 : m.mk_leaf(reinterpret_cast<void*>(idx_l)), rational(u), uo, idx_u == 0 ? 0 : m.mk_leaf(reinterpret_cast<void*>(idx_u)));
    }

    void bugs() {
        interval r1 = l(0);
        interval r2 = b(-1, 0, false, true);
        r1 *= r2;
    }

    void tst1() {
        std::cerr << singleton(10) << "\n";
        std::cerr << all() << "\n";
        std::cerr << l(-10) << "\n";
        std::cerr << r(10) << "\n";
        std::cerr << l(-10, true) << "\n";
        std::cerr << r(10, true) << "\n";
        std::cerr << b(2, 10) << "\n";
        std::cerr << wd(b(-5, 5, true, false, 1, 2) * b(-5, 5, false, true, 3, 4)) << "\n";
        std::cerr << wd(l(2, false, 1) / b(2, 6, false, false, 2, 3)) << "\n";
        std::cerr << wd(expt(b(-2, 3, true, false, 1, 2), 2)) << "\n";
        std::cerr << wd(expt(b(-4, 3, true, false, 1, 2), 2)) << "\n";
        std::cerr << wd(expt(b(2, 4, true, false, 1, 2), 2)) << "\n";
        std::cerr << wd(expt(b(0, 3, true, false, 1, 2), 2)) << "\n";
        std::cerr << wd(expt(b(-4, -2, true, false, 1, 2), 2)) << "\n";
        std::cerr << b(2, 10, false, false, 1, 2) << " * " << l(10, false, 3).inv() << " = " << wd(b(2, 10, false, false, 1, 2) / l(10, false, 3)) << "\n";
        std::cerr << b(-2, -1, false, true) << " * " << b(-3,0) << " = "; std::cerr.flush();
        std::cerr << (b(-2, -1, false, true) * b(-3,0)) << "\n";
        std::cerr << b(1, 2, true, false) << " * " << b(0,3) << " = "; std::cerr.flush();
        std::cerr << (b(1, 2, true, false) * b(0,3)) << "\n";
        std::cerr << b(1, 2, true, true) << " * " << b(-3,0) << " = "; std::cerr.flush();
        std::cerr << (b(1, 2, true, true) * b(-3,0)) << "\n";
        std::cerr << b(10,20) << " / " << b(0,1,true,false) << " = "; std::cerr.flush();
        std::cerr << (b(10,20)/b(0,1,true,false)) << "\n";
        std::cerr << (b(10,20)/b(0,2,true,false)) << "\n";
    }

public:
    void run() {
        bugs();
        tst1();
    }
};

#include"basic_interval.h"
#include"mpz.h"
#include"scoped_numeral.h"

static void tst2() {
    typedef basic_interval_manager<unsynch_mpz_manager, false> mpzi_manager;
    typedef mpzi_manager::scoped_interval scoped_mpzi;

    unsynch_mpz_manager nm;
    mpzi_manager m(nm);
    scoped_mpzi  x(m), y(m), z(m);

    m.set(x, mpz(1), mpz(2));
    m.set(y, mpz(-2), mpz(3));
    m.add(x, y, z);
    std::cout << "x: " << x << ", y: " << y << ", z: " << z << "\n";
    SASSERT(nm.eq(z.lower(), mpz(-1)));
    SASSERT(nm.eq(z.upper(), mpz(5)));
    m.mul(x, y, z);
    std::cout << "x: " << x << ", y: " << y << ", z: " << z << "\n";
    SASSERT(nm.eq(z.lower(), mpz(-4)));
    SASSERT(nm.eq(z.upper(), mpz(6)));
}

void tst_old_interval() {
    tst2();
    enable_trace("interval_bug");
    interval_tester tester;
    tester.run();
    tst1();
}

