#include "math/polysat/fixplex.h"
#include "math/polysat/fixplex_def.h"
#include "ast/bv_decl_plugin.h"
#include "ast/reg_decl_plugins.h"
#include "smt/smt_kernel.h"
#include "smt/params/smt_params.h"


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
        uint64_t g = e.gcd(15, 27);
        std::cout << g << "\n";
        std::cout << 15 << " " << e.mul_inverse(15) << " " << 15*e.mul_inverse(15) << "\n";
        std::cout << 30 << " " << e.mul_inverse(30) << " " << 30*e.mul_inverse(30) << "\n";
        std::cout << 60 << " " << e.mul_inverse(60) << " " << 60*e.mul_inverse(60) << "\n";
        std::cout << 29 << " " << e.mul_inverse(29) << " " << 29*e.mul_inverse(29) << "\n";
    }

    static void test_ineq1() {
        std::cout << "ineq1\n";
        scoped_fp fp;
        var_t x = 0, y = 1;
        fp.add_lt(x, y, 1);
        fp.add_le(y, x, 2);
        fp.run();
    }

    static void test_ineqs() {
        var_t x = 0, y = 1;
        unsigned nb = 6;
        uint64_t bounds[6] = { 0, 1, 2, 10 , (uint64_t)-2, (uint64_t)-1 };
        ast_manager m;
        reg_decl_plugins(m);
        bv_util bv(m);
        expr_ref X(m.mk_const("x", bv.mk_sort(64)), m);
        expr_ref Y(m.mk_const("y", bv.mk_sort(64)), m);
        smt_params pa;
        smt::kernel solver(m, pa);

        auto mk_ult = [&](expr* a, expr* b) {
            return m.mk_not(bv.mk_ule(b, a));
        };

        auto add_bound = [&](expr* x, uint64_t i, uint64_t j) {
            expr_ref I(bv.mk_numeral(i, 64), m);
            expr_ref J(bv.mk_numeral(j, 64), m);
            if (i < j) {
                solver.assert_expr(bv.mk_ule(I, x));
                solver.assert_expr(mk_ult(x, J));
            }
            else if (i > j && j != 0)
                solver.assert_expr(m.mk_or(bv.mk_ule(I, x), mk_ult(x, J)));
            else if (i > j && j == 0)
                solver.assert_expr(bv.mk_ule(I, x));
        };

        auto test_le = [&](bool test_le, uint64_t i, uint64_t j, uint64_t k, uint64_t l) {
            if (i == j && i != 0)
                return;
            if (k == l && k != 0)
                return;
            scoped_fp fp;
            fp.set_bounds(x, i, j, 1);
            fp.set_bounds(y, k, l, 2);       
            if (test_le)
                fp.add_le(x, y, 3);
            else
                fp.add_lt(x, y, 3);

            lbool feas = fp.make_feasible();

            // validate result


            solver.push();
            if (test_le)
                solver.assert_expr(bv.mk_ule(X, Y));
            else 
                solver.assert_expr(mk_ult(X, Y));
            add_bound(X, i, j);
            add_bound(Y, k, l);

            lbool feas2 = solver.check();


            if (feas == feas2) {
                solver.pop(1);
                return;
            }


            if (feas2 == l_false && feas == l_true) {
                std::cout << "BUG!\n";
                solver.pop(1);
                return;
            }

            bool bad = false;

            switch (feas) {
            case l_false:     
                for (unsigned c : fp.get_unsat_core())
                    std::cout << c << "\n";
                std::cout << "\n";
                break;            
            case l_true:
            case l_undef:

                // Check for missed bounds:
                solver.push();
                solver.assert_expr(m.mk_eq(X, bv.mk_numeral(fp.lo(x), 64)));
                if (l_true != solver.check()) {
                    std::cout << "missed lower bound on x\n";
                    bad = true;
                }
                solver.pop(1);

                solver.push();
                solver.assert_expr(m.mk_eq(Y, bv.mk_numeral(fp.lo(y), 64)));
                if (l_true != solver.check()) {
                    std::cout << "missed lower bound on y\n";
                    bad = true;
                }
                solver.pop(1);

                if (fp.lo(x) != fp.hi(x) && fp.hi(x) != 0) {
                    solver.push();
                    solver.assert_expr(m.mk_eq(X, bv.mk_numeral(fp.hi(x)-1, 64)));
                    if (l_true != solver.check()) {
                        std::cout << "missed upper bound on x\n";
                        bad = true;
                    }
                    solver.pop(1);
                }

                if (fp.lo(y) != fp.hi(y) && fp.hi(y) != 0) {
                    solver.push();
                    solver.assert_expr(m.mk_eq(Y, bv.mk_numeral(fp.hi(y) - 1, 64)));
                    if (l_true != solver.check()) {
                        std::cout << "missed upper bound on y\n";
                        bad = true;
                    }
                    solver.pop(1);
                }

                if (bad) {
                    std::cout << fp << "\n";
                    std::cout << feas << " " << feas2 << "\n";
                }

                break;
            }

            // check assignment is valid when returning satisfiable.
            if (false && feas == l_true) {
                rational vx = fp.get_value(x);
                rational vy = fp.get_value(y);
                SASSERT(vx <= vy);
                SASSERT(i >= j || (rational(i, rational::ui64()) <= vx && vx < rational(j, rational::ui64())));
                SASSERT(k >= l || (rational(k, rational::ui64()) <= vy && vy < rational(l, rational::ui64())));

            }

            solver.pop(1);

            return;            
        };
        for (unsigned i = 0; i < nb; ++i)
            for (unsigned j = 0; j < nb; ++j)
                for (unsigned k = 0; k < nb; ++k)
                    for (unsigned l = 0; l < nb; ++l) {
                        test_le(true, bounds[i], bounds[j], bounds[k], bounds[l]);
                        test_le(false, bounds[i], bounds[j], bounds[k], bounds[l]);
                    }
    }
}

void tst_fixplex() {

    polysat::test_ineq1();
    polysat::test_ineqs();
    return;

    polysat::test1();
    polysat::test2();
    polysat::test3();
    polysat::test4();
    polysat::test5();

    polysat::test_gcd();
    polysat::test_eq();
}
