#include "math/polysat/solver.h"
#include "ast/ast.h"

namespace polysat {
    // test resolve, factoring routines
    // auxiliary 

    struct solver_scope {
        reslimit lim;
        trail_stack stack;        
    };

    struct scoped_solver : public solver_scope, public solver {
        scoped_solver(): solver(stack, lim) {}

        void check() {
            std::cout << check_sat() << "\n";
            statistics st;
            collect_statistics(st);
            std::cout << st << "\n";
            std::cout << *this << "\n";
        }
    };

    /**
     * most basic linear equation solving.
     * they should be solvable.
     * they also illustrate some limitations of basic solver even if it solves them.
     * Example
     *   the value to a + 1 = 0 is fixed at 3, there should be no search.
     */

    static void test_l1() {
        scoped_solver s;
        auto a = s.var(s.add_var(2));
        s.add_eq(a + 1);
        s.check();
    }
    
    // TBD: we get the wrong result / conflicts.
    // it claims that v1 + 2*v0 + 1 with v0 replaced by 0 is 1.
    // it should be v1 + 1
    static void test_l2() {
        scoped_solver s;
        auto a = s.var(s.add_var(2));
        auto b = s.var(s.add_var(2));
        s.add_eq(2*a + b + 1);
        s.add_eq(2*b + a);
        s.check();
    }

    
    /**
     * This one is unsat because a*a*(a*a - 1)
     * is 0 for all values of a.
     */
    static void test_p1() {
        scoped_solver s;
        auto a = s.var(s.add_var(2));
        auto p = a*a*(a*a - 1) + 1;
        s.add_eq(p);
        s.check();
    }

    /**
     * has solution a = 3
     */
    static void test_p2() {
        scoped_solver s;
        auto a = s.var(s.add_var(2));
        auto p = a*(a-1) + 2;
        s.add_eq(p);
        s.check();
    }


    /**
     * Check unsat of:
     * u = v*q + r
     * r < u
     * v*q > u
     */
    static void test_ineq1() {
        scoped_solver s;
        auto u = s.var(s.add_var(5));
        auto v = s.var(s.add_var(5));
        auto q = s.var(s.add_var(5));
        auto r = s.var(s.add_var(5));
        s.add_eq(u - (v*q) - r, 0);
        s.add_ult(r, u, 0);
        s.add_ult(u, v*q, 0);
        s.check();
    }

    /**
     * Check unsat of:
     * n*q1 = a - b
     * n*q2 + r2 = c*a - c*b
     * n > r2 > 0
     */
    static void test_ineq2() {
        scoped_solver s;
        auto n = s.var(s.add_var(5));
        auto q1 = s.var(s.add_var(5));
        auto a = s.var(s.add_var(5));
        auto b = s.var(s.add_var(5));
        auto c = s.var(s.add_var(5));
        auto q2 = s.var(s.add_var(5));
        auto r2 = s.var(s.add_var(5));
        s.add_eq(n*q1 - a + b);
        s.add_eq(n*q2 + r2 - c*a + c*b);
        s.add_ult(r2, n);
        s.add_diseq(n);
        s.check();
    }

    // convert assertions into internal solver state
    // support small grammar of formulas.
    void internalize(solver& s, expr_ref_vector& fmls) {

    }
}


void tst_polysat() {
    polysat::test_l1();
    polysat::test_l2();
#if 0
    // worry about this later
    polysat::test_p1();
    polysat::test_p2();
    polysat::test_ineq1();
    polysat::test_ineq2();
#endif
}

// TBD also add test that loads from a file and runs the polysat engine.
// sketch follows below:

void tst_polysat_argv(char** argv, int argc, int& i) {
    // set up SMT2 parser to extract assertions
    // assume they are simple bit-vector equations (and inequations)
    // convert to solver state.
    // std::ifstream is(argv[0]);
    // cmd_context ctx(false, &m);
    // ctx.set_ignore_check(true);
    // VERIFY(parse_smt2_commands(ctx, is));
    // auto fmls = ctx.assertions();
    // trail_stack stack;
    // solver s(stack);
    // polysat::internalize(s, fmls);
    // std::cout << s.check() << "\n";
}
