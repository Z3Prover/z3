#include "math/polysat/slicing.h"
#include "math/polysat/solver.h"

namespace polysat {

    struct solver_scope_slicing {
        reslimit lim;
    };

    class scoped_solver_slicing : public solver_scope_slicing, public solver {
    public:
        scoped_solver_slicing(): solver(lim) {}
        slicing& sl() { return m_slicing; }
    };

    class test_slicing {
    public:

        static void test1() {
            std::cout << __func__ << "\n";
            scoped_solver_slicing s;
            slicing& sl = s.sl();
            pvar x = s.add_var(8);
        }

    };

}


void tst_slicing() {
    using namespace polysat;
    test_slicing::test1();
    std::cout << "ok\n";
}
