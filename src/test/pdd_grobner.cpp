#include "util/rlimit.h"
#include "math/grobner/pdd_grobner.h"

namespace dd {
    void print_eqs(ptr_vector<grobner::equation> const& eqs) {
        std::cout << "eqs\n";
        for (grobner::equation* e : eqs) {
            std::cout << e->poly() << "\n";
        }
    }
    void test1() {
        pdd_manager m(4);
        reslimit lim;
        pdd v0 = m.mk_var(0);
        pdd v1 = m.mk_var(1);
        pdd v2 = m.mk_var(2);
        pdd v3 = m.mk_var(3);
        
        grobner gb(lim, m);
        gb.add(v1*v2 + v1*v3);
        gb.add(v1 - 1);
        print_eqs(gb.equations());
        gb.saturate();
        print_eqs(gb.equations());
        gb.reset();

        gb.add(v1*v1*v2 + v2*v3);
        gb.add(v1*v1*v2 + v2*v1);
        gb.saturate();
        print_eqs(gb.equations());
        gb.reset();

        gb.add(v1*v1*v2 + v2*v1);
        gb.add(v1*v1*v2 + v2*v1);
        gb.saturate();
        print_eqs(gb.equations());
        gb.reset();

        // stop early on contradiction
        gb.add(v1*v3*v3 + v3*v1 + 2);
        gb.add(v1*v3*v3 + v3*v1);
        gb.add(v3*v1 + v1*v2 + v2*v3);
        gb.add(v3*v1 + v1*v2 + v2*v3 + v1);
        gb.add(v3*v1 + v1*v2 + v2*v3 + v2);
        gb.saturate();        
        print_eqs(gb.equations());
        gb.reset();

        // result is v1 = 0, v2 = 0.
        gb.add(v1*v3*v3 + v3*v1);
        gb.add(v3*v1 + v1*v2 + v2*v3);
        gb.add(v3*v1 + v1*v2 + v2*v3 + v1);
        gb.add(v3*v1 + v1*v2 + v2*v3 + v2);
        gb.saturate();        
        print_eqs(gb.equations());
        gb.reset();

        // everything rewrites to a multiple of v0
        gb.add(v3 - 2*v2);
        gb.add(v2 - 2*v1);
        gb.add(v1 - 2*v0);
        gb.saturate();        
        print_eqs(gb.equations());
        gb.reset();

        // 
    }
}

void tst_pdd_grobner() {
    dd::test1();
}
