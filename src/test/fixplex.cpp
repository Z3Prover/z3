#include "math/polysat/fixplex.h"
#include "math/polysat/fixplex_def.h"

namespace polysat {

    typedef uint64_ext::numeral numeral;

    static void test1() {
        reslimit lim;
        fixplex<uint64_ext> fp(lim);
        var_t x = 0, y = 1, z = 2, u = 3;
        
        var_t ys[3] = { x, y, z };
        numeral coeffs[3] = { 2, 1, 4 };        
        fp.add_row(x, 3, ys, coeffs);
        fp.set_bounds(x, 1, 2);
        std::cout << fp << "\n";
        fp.make_feasible();
        std::cout << fp << "\n";
        statistics st;
        fp.collect_statistics(st);
        std::cout << st << "\n";
    }
}

void tst_fixplex() {
    polysat::test1();
}
