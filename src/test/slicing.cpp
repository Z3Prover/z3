#include "math/polysat/slicing.h"
#include "math/polysat/solver.h"
#include "smt/params/smt_params.h"

namespace {

    template <typename T>
    void permute_args(unsigned k, T& a, T& b, T& c) {
        using std::swap;
        SASSERT(k < 6);
        unsigned i = k % 3;
        unsigned j = k % 2;
        if (i == 1)
            swap(a, b);
        else if (i == 2)
            swap(a, c);
        if (j == 1)
            swap(b, c);
    }

}

namespace polysat {

    struct solver_scope_slicing {
        reslimit lim;
        smt_params pars;
    };

    class scoped_solver_slicing : public solver_scope_slicing, public solver {
    public:
        scoped_solver_slicing(): solver(lim, pars) {
            set_log_enabled(false);
        }
        slicing& sl() { return m_slicing; }
    };

    class test_slicing {
    public:

        static std::ostream& display_reason(scoped_solver_slicing& s, std::ostream& out, ptr_vector<void> deps) {
            char const* delim = "";
            for (void* dp : deps) {
                slicing::dep_t d = slicing::dep_t::decode(dp);
                if (d.is_null())
                    continue;
                s.sl().display(out << delim, d);
                delim = " ";
            }
            return out;
        }

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
            slicing::enode_vector x_7_3;
            sl.mk_slice(sl.var2slice(x), 7, 3, x_7_3);
            std::cout << sl << "\n";
            slicing::enode_vector a_4_0;
            sl.mk_slice(sl.var2slice(a), 4, 0, a_4_0);
            std::cout << sl << "\n";
            VERIFY(sl.merge(x_7_3, a_4_0, sat::literal(1)));
            std::cout << sl << "\n";

            slicing::enode_vector y_5_0;
            sl.mk_slice(sl.var2slice(y), 5, 0, y_5_0);
            VERIFY(sl.merge(y_5_0, sl.var2slice(b), sat::literal(2)));
            std::cout << sl << "\n";

/*
            slicing::enode_vector x_base;
            sl.get_root_base(sl.var2slice(x), x_base);
            slicing::enode_vector y_base;
            sl.get_root_base(sl.var2slice(y), y_base);
            VERIFY(sl.merge(x_base, y_base, sat::literal(3)));
            std::cout << sl << "\n";
*/

            sl.display_tree(std::cout);
            VERIFY(sl.invariant());
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

            pvar a = sl.mk_extract(x, 7, 3);
            std::cout << sl << "\n";

            VERIFY(sl.merge(sl.var2slice(x), sl.var2slice(y), sat::literal(1)));
            std::cout << sl << "\n";

            pvar b = sl.mk_extract(y, 5, 0);
            std::cout << sl << "\n";

            sl.display_tree(std::cout);
            VERIFY(sl.invariant());

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

            pvar a = sl.mk_extract(x, 7, 3);
            std::cout << "v" << a << " := v" << x << "[7:3]\n" << sl << "\n";
            pvar b = sl.mk_extract(y, 5, 0);
            std::cout << "v" << b << " := v" << y << "[5:0]\n" << sl << "\n";
            pvar c = sl.mk_extract(x, 5, 0);
            std::cout << "v" << c << " := v" << x << "[5:0]\n" << sl << "\n";
            pvar d = sl.mk_concat({sl.mk_extract(x, 5, 4), sl.mk_extract(y, 3, 0)});
            std::cout << "v" << d << " := v" << x << "[5:4] ++ v" << y << "[3:0]\n" << sl << "\n";

            std::cout << "v" << b << " = v" << c << "? " << sl.is_equal(sl.var2slice(b), sl.var2slice(c)) << "\n\n";
            std::cout << "v" << b << " = v" << d << "? " << sl.is_equal(sl.var2slice(b), sl.var2slice(d)) << "\n\n";

            VERIFY(sl.merge(sl.var2slice(x), sl.var2slice(y), sat::literal(123)));
            std::cout << "v" << x << " = v" << y << "\n" << sl << "\n";

            std::cout << "v" << b << " = v" << c << "? " << sl.is_equal(sl.var2slice(b), sl.var2slice(c))
                      << "    root(v" << b << ") = " << sl.var2slice(b)->get_root_id()
                      << "    root(v" << c << ") = " << sl.var2slice(c)->get_root_id()
                      << "\n";
            ptr_vector<void> reason;
            sl.explain_equal(sl.var2slice(b), sl.var2slice(c), reason);
            display_reason(s, std::cout << "    Reason: ", reason) << "\n";

            std::cout << "v" << b << " = v" << d << "? " << sl.is_equal(sl.var2slice(b), sl.var2slice(d))
                      << "    root(v" << b << ") = " << sl.var2slice(b)->get_root_id()
                      << "    root(v" << d << ") = " << sl.var2slice(d)->get_root_id()
                      << "\n";
            reason.reset();
            sl.explain_equal(sl.var2slice(b), sl.var2slice(d), reason);
            display_reason(s, std::cout << "    Reason: ", reason) << "\n";

            sl.display_tree(std::cout);
            VERIFY(sl.invariant());

            sl.propagate();
            sl.display_tree(std::cout);
            VERIFY(sl.invariant());

            for (pvar v : {x, y, a, b, c, d}) {
                pvar_vector vars;
                sl.collect_simple_overlaps(v, vars);
                std::cout << "Simple overlaps for v" << v << ": " << vars << "\n";
            }
        }

        // 1. a = b
        // 2. d = c[1:0]
        // 3. c = b[3:0]
        // 4. e = a[1:0]
        //
        // Explain(d = e) should be {1, 2, 3, 4}
        static void test4() {
            std::cout << __func__ << "\n";
            scoped_solver_slicing s;
            slicing& sl = s.sl();
            pvar a = s.add_var(8);
            pvar b = s.add_var(8);
            pvar c = s.add_var(4);
            pvar d = s.add_var(2);
            pvar e = s.add_var(2);

            VERIFY(sl.merge(sl.var2slice(a), sl.var2slice(b), sat::literal(101)));
            VERIFY(sl.merge(sl.var2slice(d), sl.var2slice(sl.mk_extract(c, 1, 0)), sat::literal(102)));
            VERIFY(sl.merge(sl.var2slice(c), sl.var2slice(sl.mk_extract(b, 3, 0)), sat::literal(103)));
            VERIFY(sl.merge(sl.var2slice(e), sl.var2slice(sl.mk_extract(a, 1, 0)), sat::literal(104)));

            // sl.propagate();
            sl.display_tree(std::cout);
            VERIFY(sl.invariant());

            std::cout << "v" << d << " = v" << e << "? " << sl.is_equal(sl.var2slice(d), sl.var2slice(e))
                      << "    root(v" << d << ") = " << sl.var2slice(d)->get_root_id()
                      << "    root(v" << e << ") = " << sl.var2slice(e)->get_root_id()
                      << "    slice(v" << d << ") = " << sl.var2slice(d)->get_id()
                      << "    slice(v" << e << ") = " << sl.var2slice(e)->get_id()
                      << "\n";
            ptr_vector<void> reason;
            sl.explain_equal(sl.var2slice(d), sl.var2slice(e), reason);
            display_reason(s, std::cout << "    Reason: ", reason) << "\n";
        }

        // x[5:2] = y
        // x[3:0] = z
        // y = 0b1001
        // z = 0b0111
        //
        // x:  xxxxxx
        // y:  1001
        // z:    0111
        // (no conflict)
        static void test5() {
            std::cout << __func__ << "\n";
            scoped_solver_slicing s;
            slicing& sl = s.sl();
            pvar x = s.add_var(6);
            std::cout << sl << "\n";

            pvar y = sl.mk_extract(x, 5, 2);
            std::cout << "v" << y << " := v" << x << "[5:2]\n" << sl << "\n";
            pvar z = sl.mk_extract(x, 3, 0);
            std::cout << "v" << z << " := v" << x << "[3:0]\n" << sl << "\n";

            slicing::enode* nine = sl.mk_value_slice(rational(9), 4);
            VERIFY(sl.merge(sl.var2slice(y), nine, sat::literal(109)));
            std::cout << "v" << y << " = 9\n" << sl << "\n";

            slicing::enode* seven = sl.mk_value_slice(rational(7), 4);
            VERIFY(sl.merge(sl.var2slice(z), seven, sat::literal(107)));
            std::cout << "v" << z << " = 7\n" << sl << "\n";

            VERIFY(!sl.is_conflict());

            sl.display_tree(std::cout);
            VERIFY(sl.invariant());
        }

        // x[5:2] = y
        // x[3:0] = z
        // y = 0b1001
        // z = 0b1011
        //
        // x:  xxxxxx
        // y:  1001
        // z:    1011
        // (conflict)
        static void test5b() {
            std::cout << __func__ << "\n";
            scoped_solver_slicing s;
            slicing& sl = s.sl();
            pvar x = s.add_var(6);
            std::cout << sl << "\n";

            pvar y = sl.mk_extract(x, 5, 2);
            std::cout << "v" << y << " := v" << x << "[5:2]\n" << sl << "\n";
            pvar z = sl.mk_extract(x, 3, 0);
            std::cout << "v" << z << " := v" << x << "[3:0]\n" << sl << "\n";

            slicing::enode* nine = sl.mk_value_slice(rational(9), 4);
            VERIFY(sl.merge(sl.var2slice(y), nine, sat::literal(109)));
            std::cout << "v" << y << " = 9\n" << sl << "\n";

            slicing::enode* eleven = sl.mk_value_slice(rational(11), 4);
            VERIFY(!sl.merge(sl.var2slice(z), eleven, sat::literal(107)));
            std::cout << "v" << z << " = 11\n" << sl << "\n";

            VERIFY(sl.is_conflict());

            sl.display_tree(std::cout);
            VERIFY(sl.invariant());
        }

        static void test6() {
            std::cout << __func__ << "\n";
            scoped_solver_slicing s;
            slicing& sl = s.sl();
            pdd x = s.var(s.add_var(8));
            pdd y = s.var(s.add_var(8));
            pdd z = s.var(s.add_var(8));
            sl.add_constraint(s.eq(x, z));
            sl.add_constraint(s.eq(y, z));
            sl.add_constraint(s.eq(x, rational(5)));
            sl.add_value(x.var(), rational(5));
            sl.add_value(y.var(), rational(7));

            SASSERT(sl.is_conflict());
            ptr_vector<void> reason;
            sl.explain(reason);
            display_reason(s, std::cout << "Conflict: ", reason) << "\n";

            sl.display_tree(std::cout);
            VERIFY(sl.invariant());
        }

        // x != z
        // x = y
        // y = z
        // in various permutations
        static void test7() {
            std::cout << __func__ << "\n";
            scoped_solver_slicing s;
            slicing& sl = s.sl();
            pdd x = s.var(s.add_var(8));
            pdd y = s.var(s.add_var(8));
            pdd z = s.var(s.add_var(8));

            for (unsigned k = 0; k < 6; ++k) {
                s.push();
                signed_constraint c1 = s.diseq(x, z);
                signed_constraint c2 = s.eq(x, y);
                signed_constraint c3 = s.eq(y, z);
                permute_args(k, c1, c2, c3);
                sl.add_constraint(c1);
                sl.add_constraint(c2);
                sl.add_constraint(c3);
                SASSERT(sl.is_conflict());
                ptr_vector<void> reason;
                sl.explain(reason);
                display_reason(s, std::cout << "Conflict: ", reason) << "\n";
                // sl.display_tree(std::cout);
                VERIFY(sl.invariant());
                s.pop();
            }
        }

        // a = x[3:0]
        // b = y[3:0]
        // c = x[7:4]
        // d = y[7:4]
        // a = b
        // c = d
        // x != y
        static void test8() {
            std::cout << __func__ << "\n";
            scoped_solver_slicing s;
            slicing& sl = s.sl();
            pvar x = s.add_var(8);
            pvar y = s.add_var(8);
            pvar a = sl.mk_extract(x, 3, 0);
            pvar b = sl.mk_extract(y, 3, 0);
            pvar c = sl.mk_extract(x, 7, 4);
            pvar d = sl.mk_extract(y, 7, 4);
            slicing::enode* sx = sl.var2slice(x);
            slicing::enode* sy = sl.var2slice(y);
            sl.add_constraint(s.eq(s.var(a), s.var(b)));
            VERIFY(!sl.is_equal(sx, sy));
            sl.add_constraint(s.eq(s.var(c), s.var(d)));
            VERIFY(sl.is_equal(sx, sy));
            sl.add_constraint(s.diseq(s.var(x), s.var(y)));
            // sl.propagate();
            VERIFY(sl.is_conflict());
            ptr_vector<void> reason;
            sl.explain(reason);
            display_reason(s, std::cout << "    Conflict: ", reason) << "\n";
            sl.display_tree(std::cout);
            VERIFY(sl.invariant());
        }

        // y = x[5:2]
        // y = b0111
        // x := b10000000
        static void test9() {
            std::cout << __func__ << "\n";
            scoped_solver_slicing s;
            slicing& sl = s.sl();
            pvar x = s.add_var(8);
            pvar y = sl.mk_extract(x, 5, 2);
            sl.add_constraint(s.eq(s.var(y), 7));
            sl.add_value(x, 128);
            VERIFY(sl.is_conflict());
            ptr_vector<void> reason;
            sl.explain(reason);
            display_reason(s, std::cout << "Conflict: ", reason) << "\n";
#if 0
            clause_ref cl = sl.build_conflict_clause();  // fails on insert_eval because we don't update the solver state
            std::cout << "Conflict Clause: " << clause_pp(s, cl) << "\n";
            // NOTE: creates a tautology because with literal x[5:2] = 7 the solver should never assign x := 128
#endif
            sl.display_tree(std::cout);
            VERIFY(sl.invariant());
        }

        // y = x[7:4]
        // z = x[3:0]
        // y = 1
        // z = 2
        // x := b10000000
        static void test10() {
            std::cout << __func__ << "\n";
            scoped_solver_slicing s;
            slicing& sl = s.sl();
            pvar x = s.add_var(8);
            pvar y = sl.mk_extract(x, 7, 4);
            pvar z = sl.mk_extract(x, 3, 0);
            sl.add_constraint(s.eq(s.var(y), 1));
            sl.add_constraint(s.eq(s.var(z), 2));
            sl.add_value(x, 128);
            VERIFY(sl.is_conflict());
            ptr_vector<void> reason;
            sl.explain(reason);
            display_reason(s, std::cout << "Conflict: ", reason) << "\n";
#if 0
            clause_ref cl = sl.build_conflict_clause();  // fails on insert_eval because we don't update the solver state
            std::cout << "Conflict Clause: " << clause_pp(s, cl) << "\n";
#endif
            sl.display_tree(std::cout);
            VERIFY(sl.invariant());
        }

        // x == 7
        // y == 7
        static void test11() {
            std::cout << __func__ << "\n";
            scoped_solver_slicing s;
            slicing& sl = s.sl();
            pvar x = s.add_var(8);
            sl.add_constraint(s.eq(s.var(x), 7));
            pvar a = sl.mk_extract(x, 7, 6);
            pvar b = sl.mk_extract(x, 3, 0);
            sl.display_tree(std::cout);

            pvar y = s.add_var(8);
            pvar c = sl.mk_extract(y, 7, 6);
            pvar d = sl.mk_extract(y, 1, 0);
            sl.display_tree(std::cout);

            sl.add_constraint(s.eq(s.var(y), 7));
            sl.display_tree(std::cout);
        }



        // x == 0
        // x != y
        // y <= 1
        // y[0:0] = z
        // z == w
        // w == 0
        static void test12() {
            std::cout << __func__ << "\n";
            // TODO
            scoped_solver_slicing s;
            slicing& sl = s.sl();
        }


        // mk_extract y := x[63:32]
        // a * x = 123
        // b * y = 456
        // a = 1, propagates x = 123 (by constraint)
        // b = 1, propagates y = 456 (by constraint), propagates x = 0 (by slicing)
        // Conflict in slicing.
        static void test13() {
            std::cout << __func__ << "\n";
            scoped_solver_slicing s;
            slicing& sl = s.sl();
            pvar x = s.add_var(64);
            pvar y = sl.mk_extract(x, 63, 32);
            pvar a = s.add_var(64);
            pvar b = s.add_var(32);
            sl.add_constraint(s.eq(s.var(a)*s.var(x), 123));  // NOTE: this does nothing inside slicing atm.
            sl.add_constraint(s.eq(s.var(b)*s.var(y), 456));
            sl.add_value(a, 1);
            sl.add_value(x, 123);
            sl.add_value(b, 1);
            sl.add_value(y, 456);
            VERIFY(sl.is_conflict());
            sl.display_tree(std::cout);
            VERIFY(sl.invariant());
        }

    };  // test_slicing

}  // namespace polysat


void tst_slicing() {
    using namespace polysat;
    test_slicing::test1();
    test_slicing::test2();
    test_slicing::test3();
    test_slicing::test4();
    test_slicing::test5();
    test_slicing::test5b();
    test_slicing::test6();
    test_slicing::test7();
    test_slicing::test8();
    test_slicing::test9();
    test_slicing::test10();
    test_slicing::test11();
    test_slicing::test13();
    std::cout << "ok\n";
}
