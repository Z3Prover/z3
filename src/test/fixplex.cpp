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
        fp.set_bounds(x, 1, 2);
        fp.run();
    }

    static void test2() {
        scoped_fp fp;
        var_t x = 0, y = 1, z = 2;        
        var_t ys[3] = { x, y, z };
        numeral coeffs[3] = { 1, 2, 4 };        
        fp.add_row(x, 3, ys, coeffs);
        fp.set_bounds(x, 3, 4);
        fp.run();
    }

    static void test3() {
        scoped_fp fp;
        var_t x = 0, y = 1, z = 2;        
        var_t ys[3] = { x, y, z };
        numeral coeffs[3] = { 1, 1, 1 };        
        fp.add_row(x, 3, ys, coeffs);
        fp.set_bounds(x, 3, 4);
        fp.set_bounds(y, 3, 4);
        fp.set_bounds(z, 3, 4);
        fp.run();
    }

    static void test4() {
        scoped_fp fp;
        var_t x = 0, y = 1, z = 2;        
        var_t ys[3] = { x, y, z };
        numeral coeffs[3] = { 1, 1, 1 };        
        fp.add_row(x, 3, ys, coeffs);
        fp.set_bounds(x, 3, 4);
        fp.set_bounds(y, 3, 6);
        fp.run();
        fp.propagate_bounds();
    }

}

void tst_fixplex() {
    polysat::test1();
    polysat::test2();
    polysat::test3();
    polysat::test4();
}
