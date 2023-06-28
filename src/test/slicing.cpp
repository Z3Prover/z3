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
            VERIFY(sl.merge(x_7_3, a_4_0, sat::literal(1)));
            std::cout << sl << "\n";

            slicing::slice_vector y_5_0;
            sl.mk_slice(sl.var2slice(y), 5, 0, y_5_0);
            VERIFY(sl.merge(y_5_0, sl.var2slice(b), sat::literal(2)));
            std::cout << sl << "\n";

            slicing::slice_vector x_base;
            sl.find_base(sl.var2slice(x), x_base);
            slicing::slice_vector y_base;
            sl.find_base(sl.var2slice(y), y_base);
            VERIFY(sl.merge(x_base, y_base, sat::literal(3)));
            std::cout << sl << "\n";
        }

        // x[7:3] = a
        // x = y
        // y[5:0] = b
        static void test2() {
            std::cout << __func__ << "\n";
            scoped_solver_slicing s;
            slicing& sl = s.sl();
            pvar x = s.add_var(8);
            pvar y = s.add_var(8);

            pvar a = sl.mk_extract_var(x, 7, 3);
            std::cout << sl << "\n";

            VERIFY(sl.merge(sl.var2slice(x), sl.var2slice(y), sat::literal(1)));
            std::cout << sl << "\n";

            pvar b = sl.mk_extract_var(y, 5, 0);
            std::cout << sl << "\n";

            (void)a;
            (void)b;
        }

        // x[7:3] = a
        // y[5:0] = b
        // x[5:0] = c
        // x[5:4] ++ y[3:0] = d
        // x = y
        //
        // How easily can we find b=c and b=d?
        static void test3() {
            std::cout << __func__ << "\n";
            scoped_solver_slicing s;
            slicing& sl = s.sl();
            pvar x = s.add_var(8);
            pvar y = s.add_var(8);
            std::cout << sl << "\n";

            pvar a = sl.mk_extract_var(x, 7, 3);
            std::cout << "v" << a << " := v" << x << "[7:3]\n" << sl << "\n";
            pvar b = sl.mk_extract_var(y, 5, 0);
            std::cout << "v" << b << " := v" << y << "[5:0]\n" << sl << "\n";
            pvar c = sl.mk_extract_var(x, 5, 0);
            std::cout << "v" << c << " := v" << x << "[5:0]\n" << sl << "\n";
            pdd d = sl.mk_concat(sl.mk_extract(x, 5, 4), sl.mk_extract(y, 3, 0));
            std::cout << d << " := v" << x << "[5:4] ++ v" << y << "[3:0]\n" << sl << "\n";

            VERIFY(sl.merge(sl.var2slice(x), sl.var2slice(y), sat::literal(1)));
            std::cout << "v" << x << " = v" << y << "\n" << sl << "\n";

            std::cout << "v" << b << " = v" << c << "? " << sl.is_equal(sl.var2slice(b), sl.var2slice(c))
                      << "    find(v" << b << ") = " << sl.find(sl.var2slice(b))
                      << "    find(v" << c << ") = " << sl.find(sl.var2slice(c))
                      << "\n";
            std::cout << "v" << b << " = "  << d << "? " << sl.is_equal(sl.var2slice(b), sl.pdd2slice(d))
                      << "    find(v" << b << ") = " << sl.find(sl.var2slice(b))
                      << "    find("  << d << ") = " << sl.find(sl.pdd2slice(d))
                      << "\n";
        }

    };

}


void tst_slicing() {
    using namespace polysat;
    test_slicing::test1();
    test_slicing::test2();
    test_slicing::test3();
    std::cout << "ok\n";
}
