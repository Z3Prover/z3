
#include "math/polysat/fixplex.h"
#include "math/polysat/fixplex_def.h"
#include "ast/bv_decl_plugin.h"
#include "ast/reg_decl_plugins.h"
#include "smt/smt_kernel.h"
#include "smt/params/smt_params.h"
#include <iostream>


namespace polysat {

    typedef uint64_ext::numeral numeral;

    struct fp_scope {
        params_ref p;
        reslimit lim;
    };

    struct scoped_fp : public fp_scope, public fixplex<uint64_ext> {

        scoped_fp(): fixplex<uint64_ext>(p, lim) {}

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
        fp.reset();
        coeffs[2] = 0ull - 1;
        fp.add_row(x, 3, ys, coeffs);
        fp.set_bounds(x, 3, 4, 1);
        fp.set_bounds(y, 3, 6, 2);
        fp.run();
        fp.reset();
        fp.add_row(x, 3, ys, coeffs);
        fp.set_bounds(x, 3, 4, 1);
        fp.set_bounds(y, 3, 6, 2);
        fp.set_bounds(z, 1, 8, 3);
        fp.run();
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

    static void test_ineq_propagation1() {
        std::cout << "ineq propagation 1\n";
        scoped_fp fp;
        var_t x = 0, y = 1;
        fp.add_lt(x, y, 1);
        fp.add_le(y, x, 2);
        fp.run();
        std::cout << "core:" << fp.get_unsat_core() << "\n";
        SASSERT(fp.get_unsat_core().contains(1));
        SASSERT(fp.get_unsat_core().contains(2));
    }

    static void test_ineq_propagation2() {
        std::cout << "ineq propagation 2\n";
        scoped_fp fp;
        var_t x = 0, y = 1, z = 2, u = 3, v = 4;
        fp.add_le(x, y, 1);
        fp.add_le(y, z, 2);
        fp.add_le(z, u, 3);
        fp.add_le(u, v, 4);
        fp.add_le(v, x, 5);
        fp.run();
        for (unsigned i = 0; i < 4; ++i) {
            SASSERT(!fp.inconsistent());
            fp.push();
            fp.add_lt(i, i + 1, 6);
            fp.run();
            SASSERT(fp.inconsistent());
            std::cout << "core:" << fp.get_unsat_core() << "\n";
            for (unsigned j = 1; j < 5; ++j)
                SASSERT((j != i + 1) == fp.get_unsat_core().contains(j));
            fp.get_unsat_core().contains(6);
            fp.pop(1);
        }
    }

    static void test_ineqs() {
        unsigned num_bad = 0;
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

        auto add_not_bound = [&](expr* x, uint64_t i, uint64_t j) {
            expr_ref I(bv.mk_numeral(i, 64), m);
            expr_ref J(bv.mk_numeral(j, 64), m);
            if (i < j)
                solver.assert_expr(m.mk_not(m.mk_and(bv.mk_ule(I, x), mk_ult(x, J))));
            else if (i > j && j != 0)
                solver.assert_expr(m.mk_not(m.mk_or(bv.mk_ule(I, x), mk_ult(x, J))));
            else if (i > j && j == 0)
                solver.assert_expr(m.mk_not(bv.mk_ule(I, x)));
            else
                solver.assert_expr(m.mk_false());
        };

        auto test_le = [&](bool test_le, uint64_t i, uint64_t j, uint64_t k, uint64_t l) {
            if (i == j && i != 0)
                return;
            if (k == l && k != 0)
                return;
            // std::cout << "test " << i << " " << j << " " << k << " " << l << "\n";
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
                // TBD: check that core is sufficient and minimal
                break;            
            case l_true:
            case l_undef:

                if (feas2 == l_false) {
                    std::cout << "Missed conflict\n";
                    std::cout << fp << "\n";
                    break;
                }
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

                // check that inferred bounds are implied:
                solver.push();
                add_not_bound(X, fp.lo(x), fp.hi(x));
                if (l_false != solver.check()) {
                    std::cout << "Bound on x is not implied\n";
                    scoped_fp fp1;
                    fp1.set_bounds(x, i, j, 1);
                    fp1.set_bounds(y, k, l, 2);
                    std::cout << fp1 << "\n";
                    bad = true;
                }
                solver.pop(1);

                solver.push();
                add_not_bound(Y, fp.lo(y), fp.hi(y));
                if (l_false != solver.check()) {
                    std::cout << "Bound on y is not implied\n";
                    scoped_fp fp1;
                    fp1.set_bounds(x, i, j, 1);
                    fp1.set_bounds(y, k, l, 2);
                    std::cout << fp1 << "\n";
                    bad = true;
                }
                solver.pop(1);

                if (bad) {
                    std::cout << feas << " " << feas2 << "\n";
                    std::cout << fp << "\n"; 
                    std::cout << "original:\n";
                    scoped_fp fp1;
                    fp1.set_bounds(x, i, j, 1);
                    fp1.set_bounds(y, k, l, 2);
                    std::cout << fp1 << "\n";
                    ++num_bad;
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

        std::cout << "number of failures: " << num_bad << "\n";
    }

    static void save_scenario(
        unsigned id,
        vector<svector<std::pair<unsigned, uint64_t>>> const& rows,
        svector<ineq> const& ineqs,
        vector<mod_interval<uint64_t>> const& bounds) {
        std::cout << "static void scenario" << id << "() {\n";
        std::cout << "    vector<svector<std::pair<unsigned, uint64_t>>> rows;\n";
        std::cout << "    svector<ineq> ineqs;\n";
        std::cout << "    vector<mod_interval<uint64_t>> bounds;\n";
        for (auto const& row : rows) {
            std::cout << "    rows.push_back(svector<std::pair<unsigned, uint64_t>>());\n";
            for (auto col : row)
                std::cout << "    rows.back().push_back(std::make_pair(" << col.first << ", " << col.second << ");\n";
        }
        for (auto const& ineq : ineqs)
            std::cout << "    ineqs.push_back(ineq(" << ineq.v << ", " << ineq.w << ", 0, " << (ineq.strict?"true":"false") << ");\n";
        for (auto const& bound : bounds)
            std::cout << "    bounds.push_back(mod_interval<uint64_t>(" << bound.lo << ", " << bound.hi << ");\n";
        std::cout << "    test_lp(rows, ineqs, bounds); \n }\n";
    }

    //    static unsigned num_test = 0;

    static void test_lp(
        vector<svector<std::pair<unsigned, uint64_t>>> const& rows,
        svector<ineq> const& ineqs,
        vector<mod_interval<uint64_t>> const& bounds) {

        // save_scenario(++num_test, rows, ineqs, bounds);

        unsigned num_vars = 0;
        for (auto const& row : rows)
            for (auto [v, c] : row)
                num_vars = std::max(num_vars, v);
        for (auto const& i : ineqs)
            num_vars = std::max(num_vars, std::max(i.v, i.w));
        num_vars = std::max(bounds.size(), num_vars + 1);

        ast_manager m;
        reg_decl_plugins(m);
        bv_util bv(m);
        smt_params pa;
        smt::kernel solver(m, pa);
        expr_ref_vector variables(m);
        for (unsigned i = 0; i < num_vars; ++i)
            variables.push_back(m.mk_fresh_const("v", bv.mk_sort(32)));
        auto mk_ult = [&](expr* a, expr* b) {
            return m.mk_not(bv.mk_ule(b, a));
        };

        scoped_fp fp;
        params_ref p;
        p.set_uint("max_iterations", 100);
        fp.updt_params(p);

        for (auto& row : rows) {
            vector<rational> coeffs;
            svector<var_t> vars;
            expr_ref term(m);
            term = bv.mk_numeral(0, 32);
            for (auto [v, c] : row) {
                coeffs.push_back(rational(c, rational::ui64()));
                vars.push_back(v);
                term = bv.mk_bv_add(term, bv.mk_bv_mul(bv.mk_numeral(c, 32), variables.get(v)));
            }
            fp.add_row(row[0].first, row.size(), vars.data(), coeffs.data());
            solver.assert_expr(m.mk_eq(bv.mk_numeral(0, 32), term));
        }
        unsigned index = 0;
        for (auto const& i : ineqs) {
            ++index;
            if (i.strict) {
                fp.add_lt(i.v, i.w, index);
                solver.assert_expr(mk_ult(variables.get(i.v), variables.get(i.w)));
            }
            else {
                fp.add_le(i.v, i.w, index);
                solver.assert_expr(bv.mk_ule(variables.get(i.v), variables.get(i.w)));
            }
        }
        for (unsigned v = 0; v < bounds.size(); ++v) {
            auto const& b = bounds[v];
            ++index;

            fp.set_bounds(v, rational(b.lo, rational::ui64()), rational(b.hi, rational::ui64()), index);

            expr_ref A(mk_ult(variables.get(v), bv.mk_numeral(b.hi, 32)), m);
            expr_ref B(bv.mk_ule(bv.mk_numeral(b.lo, 32), variables.get(v)), m);

            if (b.lo < b.hi) 
                solver.assert_expr(m.mk_and(A, B));            
            else if (b.hi == 0)
                solver.assert_expr(B);
            else 
                solver.assert_expr(m.mk_or(A, B));            
        }

        lbool r1 = l_undef; // solver.check();
        lbool r2 = fp.make_feasible();

        std::cout << r1 << " " << r2 << "\n";

#define VALIDATE(_test_) if (!(_test_)) { std::cout << "failed " << #_test_ << "\n"; solver.display(std::cout << fp << "\n"); SASSERT(false);}

        if (r2 == l_true) {
            for (auto const& row : rows) {
                uint64_t sum = 0;
                for (auto col : row) 
                    sum += col.second * fp.value(col.first);
                if (sum != 0) {
                    std::cout << sum << " = ";
                    for (auto col : row)
                        std::cout << pp(col.second) << "*v" << col.first << "(" << pp(fp.value(col.first)) << ") ";
                    std::cout << "\n";
                }
                VALIDATE(sum == 0);
            }
            for (unsigned i = 0; i < bounds.size(); ++i) {
                uint64_t val = fp.value(i);
                uint64_t lo = bounds[i].lo;
                uint64_t hi = bounds[i].hi;
                VALIDATE(!(lo < hi) || (lo <= val && val < hi));
                VALIDATE(!(0 < lo && hi == 0) || lo <= val);
                VALIDATE(!(hi > lo) || val < hi || lo <= val);
            }
            for (auto const& i : ineqs) {
                VALIDATE(fp.value(i.v) <= fp.value(i.w));
                VALIDATE(!i.strict || fp.value(i.v) < fp.value(i.w));
            }
        }
        if (r1 == r2) {
            std::cout << "agree\n";
        }
        else if (r1 == l_false && r2 == l_true) {
            std::cout << "BUG should be unsat\n";
            solver.display(std::cout);
            std::cout << fp << "\n";
        }
        else if (r1 == l_true && r2 == l_false) {
            std::cout << "BUG should be sat\n";
            solver.display(std::cout);
            std::cout << fp << "\n";
        }
        else {
            
            std::cout << r2 << " missed with verdict " << r1 << "\n";
            std::cout << fp << "\n";

            if (r1 == l_false && false && rows.empty()) {
                std::cout << "BUG should not miss unsat verdict when there are no rows\n";
                solver.display(std::cout);
                std::cout << "\n";
                std::cout << fp << "\n";
                SASSERT(false);
            }
        }
    }


    static void test_lps(random_gen& r, unsigned num_vars, unsigned num_rows, unsigned num_vars_per_row, unsigned num_ineqs) {
        vector<svector<std::pair<unsigned, uint64_t>>> rows;
        svector<ineq> ineqs;
        vector<mod_interval<uint64_t>> bounds;
        for (unsigned i = 0; i < num_vars; ++i) {
            uint64_t l = (r() % 2 == 0) ? r() % 100 : (0 - r() % 10);
            uint64_t h = (r() % 2 == 0) ? r() % 100 : (0 - r() % 10);
            bounds.push_back(mod_interval<uint64_t>(l, h));
        }
        for (unsigned i = 0; i < num_ineqs; ++i) {
            var_t v = r() % num_vars;
            var_t w = r() % num_vars;
            ineqs.push_back(ineq(v, w, 0, 0 == r() % 2));
        }
        for (unsigned i = 0; i < num_rows; ++i) {
            svector<std::pair<unsigned, uint64_t>> row;
            uint64_t coeff = (r() % 2 == 0) ? (1 + r() % 100) : (0 - 1 - r() % 10);
            SASSERT(coeff != 0);
            row.push_back(std::make_pair(i, coeff));
            uint_set seen;
            for (unsigned j = 0; j + 1 < num_vars_per_row; ++j) {
                var_t v;
                do {
                    v = (r() % (num_vars - num_vars_per_row)) + num_vars_per_row;
                } 
                while (seen.contains(v));
                seen.insert(v);
                coeff = (r() % 2 == 0) ? (1 + r() % 100) : (0 - 1 - r() % 10);
                SASSERT(coeff != 0);
                row.push_back(std::make_pair(v, coeff));
            }
            rows.push_back(row);
        }

        test_lp(rows, ineqs, bounds);
    }

    static void test_lps() {
        random_gen r;
    	for (unsigned i = 0; i < 10000; ++i) 
            test_lps(r, 6, 3, 3, 3);
        return;
        for (unsigned i = 0; i < 10000; ++i)
            test_lps(r, 6, 3, 3, 0);
        return;
        for (unsigned i = 0; i < 10000; ++i)
            test_lps(r, 6, 0, 0, 5);


    }
}

void tst_fixplex() {

    polysat::test_lps();
    return;

    polysat::test_ineqs();
    polysat::test_ineq_propagation1();
    polysat::test_ineq_propagation2();


    polysat::test1();
    polysat::test2();
    polysat::test3();
    polysat::test4();
    polysat::test5();

    polysat::test_gcd();
    polysat::test_eq();
}
