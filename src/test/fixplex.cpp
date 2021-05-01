#include "math/polysat/fixplex.h"
#include "math/polysat/fixplex_def.h"

namespace polysat {

    typedef uint64_ext::numeral numeral;

    static void test1() {
        reslimit lim;
        fixplex<uint64_ext> fp(lim);
        var_t x = 0, y = 1, z = 2, u = 3;
        fp.ensure_var(3);
        
        var_t ys[2] = { y, z };
        numeral coeffs[2] = { 1, 4 };        
        fp.add_row(x, 2, ys, coeffs);
        fp.set_lo(x, 1);
        fp.set_hi(x, 2);
        fp.make_feasible();
    }
}

void tst_fixplex() {
    
}
