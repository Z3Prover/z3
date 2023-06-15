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

        // x[7:3] = a
        // y[5:0] = b
        // x = y
        static void test1() {
            std::cout << __func__ << "\n";
            scoped_solver_slicing s;
            slicing& sl = s.sl();
            pvar x = s.add_var(8);
            pvar y = s.add_var(8);
            pvar a = s.add_var(5);
            pvar b = s.add_var(6);

            std::cout << sl << "\n";
            slicing::slice_vector x_7_3;
            sl.mk_slice(sl.var2slice(x), 7, 3, x_7_3);
            std::cout << sl << "\n";
            slicing::slice_vector a_4_0;
            sl.mk_slice(sl.var2slice(a), 4, 0, a_4_0);
            std::cout << sl << "\n";
            sl.merge(x_7_3, a_4_0);
            std::cout << sl << "\n";

            slicing::slice_vector y_5_0;
            sl.mk_slice(sl.var2slice(y), 5, 0, y_5_0);
            sl.merge(y_5_0, sl.var2slice(b));
            std::cout << sl << "\n";

            slicing::slice_vector x_base;
            sl.find_base(sl.var2slice(x), x_base);
            std::cout << "v" << x << "_base: " << x_base << "\n";
            slicing::slice_vector y_base;
            sl.find_base(sl.var2slice(y), y_base);
            std::cout << "v" << y << "_base: " << y_base << "\n";
            sl.merge(x_base, y_base);
            std::cout << sl << "\n";
        }

        // x[7:3] = a
        // x = y
        // y[5:0] = b
        static void test2() {
        }

    };

}


void tst_slicing() {
    using namespace polysat;
    test_slicing::test1();
    std::cout << "ok\n";
}
