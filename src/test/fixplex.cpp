#include "math/polysat/fixplex.h"
#include "math/polysat/fixplex_def.h"

namespace polysat {

    typedef uint64_ext::numeral numeral;

    struct solver_scope {
        reslimit lim;
    };
    struct scoped_fp : public solver_scope, public fixplex<uint64_ext> {
        scoped_fp(): fixplex<uint64_ext>(lim) {}

        void run() {
            std::cout << *this << "\n";
            std::cout << make_feasible() << "\n";
            std::cout << *this << "\n";
            statistics st;
            collect_statistics(st);
            std::cout << st << "\n";
        }
    };


    static void test1() {
        scoped_fp fp;
        var_t x = 0, y = 1, z = 2;        
        var_t ys[3] = { x, y, z };
        numeral coeffs[3] = { 2, 1, 4 };        
        fp.add_row(x, 3, ys, coeffs);
        fp.set_bounds(x, 1, 2, 0);
        fp.run();
    }

    static void test2() {
        scoped_fp fp;
        var_t x = 0, y = 1, z = 2;        
        var_t ys[3] = { x, y, z };
        numeral coeffs[3] = { 1, 2, 4 };        
        fp.add_row(x, 3, ys, coeffs);
        fp.set_bounds(x, 3, 4, 1);
        fp.run();
    }

    static void test3() {
        scoped_fp fp;
        var_t x = 0, y = 1, z = 2;        
        var_t ys[3] = { x, y, z };
        numeral coeffs[3] = { 1, 1, 1 };        
        fp.add_row(x, 3, ys, coeffs);
        fp.set_bounds(x, 3, 4, 1);
        fp.set_bounds(y, 3, 4, 2);
        fp.set_bounds(z, 3, 4, 3);
        fp.run();
    }

    static void test4() {
        scoped_fp fp;
        var_t x = 0, y = 1, z = 2;        
        var_t ys[3] = { x, y, z };
        numeral coeffs[3] = { 1, 1, 1 };        
        fp.add_row(x, 3, ys, coeffs);
        fp.set_bounds(x, 3, 4, 1);
        fp.set_bounds(y, 3, 6, 2);
        fp.run();
        fp.propagate_bounds();
        fp.reset();
        coeffs[2] = 0ull - 1;
        fp.add_row(x, 3, ys, coeffs);
        fp.set_bounds(x, 3, 4, 1);
        fp.set_bounds(y, 3, 6, 2);
        fp.run();
        fp.propagate_bounds();
        fp.reset();
        fp.add_row(x, 3, ys, coeffs);
        fp.set_bounds(x, 3, 4, 1);
        fp.set_bounds(y, 3, 6, 2);
        fp.set_bounds(z, 1, 8, 3);
        fp.run();
        fp.propagate_bounds();
        fp.reset();
    }

    static void test5() {
        std::cout << "test5\n";
        scoped_fp fp;
        var_t x = 0, y = 1, z = 2, u = 3;        
        var_t ys[3] = { x, y, z };
        numeral coeffs[3] = { 1, 1, 1 };        
        fp.add_row(x, 3, ys, coeffs);
        fp.set_bounds(x, 3, 4, 1);
        fp.set_bounds(y, 3, 6, 2);
        var_t ys2[3] = { u, y, z };
        fp.add_row(u, 3, ys2, coeffs);        
        fp.run();
        fp.del_row(x);
        std::cout << fp << "\n";
    }

    static void test_eq() {
        scoped_fp fp;
        var_t x = 0, y = 1, z = 2, u = 3;        
        var_t ys1[3] = { x, y, u };
        numeral m1 = 0ull - 1ull;
        numeral coeffs1[3] = { 1, m1, m1 };        
        var_t ys2[3] = { y, z, u };
        numeral coeffs2[3] = { 1, m1, 1 };        
        fp.add_row(x, 3, ys1, coeffs1);
        fp.add_row(z, 3, ys2, coeffs2);
        fp.set_bounds(u, 1, 2, 1);
        fp.run();
        fp.propagate_eqs();
        for (auto e : fp.var_eqs())
            std::cout << e.x << " == " << e.y << "\n";
        
    }

    static void test_gcd() {
        std::cout << "gcd\n";
        uint64_ext::manager e;
        uint64_t x = 0, y = 0, z = 0, a = 0, b = 0;
        uint64_t g = e.gcd(15, 27);
        std::cout << g << "\n";
        std::cout << 15 << " " << e.mul_inverse(15) << " " << 15*e.mul_inverse(15) << "\n";
        std::cout << 30 << " " << e.mul_inverse(30) << " " << 30*e.mul_inverse(30) << "\n";
        std::cout << 60 << " " << e.mul_inverse(60) << " " << 60*e.mul_inverse(60) << "\n";
        std::cout << 29 << " " << e.mul_inverse(29) << " " << 29*e.mul_inverse(29) << "\n";
    }
}

void tst_fixplex() {
    polysat::test1();
    polysat::test2();
    polysat::test3();
    polysat::test4();
    polysat::test5();

    polysat::test_gcd();
    polysat::test_eq();
}
