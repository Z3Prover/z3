#include "math/polysat/log.h"
#include "math/polysat/solver.h"
#include "ast/ast.h"
#include "parsers/smt2/smt2parser.h"
#include <vector>

namespace polysat {
    // test resolve, factoring routines
    // auxiliary 

    struct solver_scope {
        reslimit lim;
    };

    class scoped_solver : public solver_scope, public solver {
        std::string m_name;
        lbool m_last_result = l_undef;

        lbool check_rec() {
            lbool result = check_sat();
            if (result != l_undef)
                return result;
            auto const new_lemma = get_lemma();
            // Empty lemma => check_sat() terminated for another reason, e.g., resource limits
            if (new_lemma.empty())
                return l_undef;
            for (auto lit : new_lemma) {
                push();
                assign_eh(lit, true);
                result = check_rec();
                pop();
                // Found a model => done
                if (result == l_true)
                    return l_true;
                if (result == l_undef)
                    return l_undef;
                // Unsat => try next literal
                SASSERT(result == l_false);
            }
            // No literal worked? unsat
            return l_false;
        }

    public:
        scoped_solver(std::string name): solver(lim), m_name(name) {
            std::cout << "\nSTART: " << m_name << "\n";
        }

        void check() {
            m_last_result = check_rec();
            std::cout << m_name << ": " << m_last_result << "\n";
            statistics st;
            collect_statistics(st);
            std::cout << st << "\n";
            std::cout << *this << "\n";
        }

        void expect_unsat() {
            if (m_last_result != l_false) {
                LOG_H1("FAIL: " << m_name << ": expected UNSAT, got " << m_last_result << "!");
                VERIFY(false);
            }
        }

        void expect_sat(std::vector<std::pair<dd::pdd, unsigned>> const& expected_assignment = {}) {
            if (m_last_result == l_true) {
                for (auto const& p : expected_assignment) {
                    auto const& v_pdd = p.first;
                    auto const expected_value = p.second;
                    SASSERT(v_pdd.is_monomial() && !v_pdd.is_val());
                    auto const v = v_pdd.var();
                    if (get_value(v) != expected_value) {
                        LOG_H1("FAIL: " << m_name << ": expected assignment v" << v << " := " << expected_value << ", got value " << get_value(v) << "!");
                        VERIFY(false);
                    }
                }
            }
            else {
                LOG_H1("FAIL: " << m_name << ": expected SAT, got " << m_last_result << "!");
                VERIFY(false);
            }
        }
    };


    /**
     * Testing the solver's internal state.
     */

    /// Creates two separate conflicts (from narrowing) before solving loop is started.
    static void test_add_conflicts() {
        scoped_solver s(__func__);
        auto a = s.var(s.add_var(3));
        auto b = s.var(s.add_var(3));
        s.add_eq(a + 1);
        s.add_eq(a + 2);
        s.add_eq(b + 1);
        s.add_eq(b + 2);
        s.check();
        s.expect_unsat();
    }

    /// Has constraints which must be inserted into other watchlist to discover UNSAT
    static void test_wlist() {
        scoped_solver s(__func__);
        auto a = s.var(s.add_var(3));
        auto b = s.var(s.add_var(3));
        auto c = s.var(s.add_var(3));
        auto d = s.var(s.add_var(3));
        s.add_eq(d + c + b + a + 1);
        s.add_eq(d + c + b + a);
        s.add_eq(d + c + b);
        s.add_eq(d + c);
        s.add_eq(d);
        s.check();
        s.expect_unsat();
    }

    /// Has a constraint in cjust[a] where a does not occur.
    static void test_cjust() {
        scoped_solver s(__func__);
        auto a = s.var(s.add_var(3));
        auto b = s.var(s.add_var(3));
        auto c = s.var(s.add_var(3));
        // 1. Decide a = 0.
        s.add_eq(a*a + b + 7);                  // 2. Propagate b = 1
        s.add_eq(b*b + c*c*c*(b+7) + c + 5);    // 3. Propagate c = 2
        s.add_eq(b*b + c*c);                    // 4. Conflict
        // Resolution fails because second constraint has c*c*c
        // => cjust[a] += b*b + c*c
        s.check();
        s.expect_unsat();
    }

    /**
     * most basic linear equation solving.
     * they should be solvable.
     * they also illustrate some limitations of basic solver even if it solves them.
     * Example
     *   the value to a + 1 = 0 is fixed at 3, there should be no search.
     */

    static void test_l1() {
        scoped_solver s(__func__);
        auto a = s.var(s.add_var(2));
        s.add_eq(a + 1);
        s.check();
        s.expect_sat({{a, 3}});
    }
    
    static void test_l2() {
        scoped_solver s(__func__);
        auto a = s.var(s.add_var(2));
        auto b = s.var(s.add_var(2));
        s.add_eq(2*a + b + 1);
        s.add_eq(2*b + a);
        s.check();
        s.expect_sat({{a, 2}, {b, 3}});
    }

    static void test_l3() {
        scoped_solver s(__func__);
        auto a = s.var(s.add_var(2));
        auto b = s.var(s.add_var(2));
        s.add_eq(3*b + a + 2);
        s.check();
        s.expect_sat();
    }

    static void test_l4() {
        scoped_solver s(__func__);
        auto a = s.var(s.add_var(3));
        s.add_eq(4*a + 2);
        s.check();
        s.expect_unsat();
    }

    static void test_l5() {
        scoped_solver s(__func__);
        auto a = s.var(s.add_var(3));
        auto b = s.var(s.add_var(3));
        s.add_diseq(b);
        s.add_eq(a + 2*b + 4);
        s.add_eq(a + 4*b + 4);
        s.check();
        s.expect_sat({{a, 4}, {b, 4}});
    }

    
    /**
     * This one is unsat because a*a*(a*a - 1)
     * is 0 for all values of a.
     */
    static void test_p1() {
        scoped_solver s(__func__);
        auto a = s.var(s.add_var(2));
        auto p = a*a*(a*a - 1) + 1;
        s.add_eq(p);
        s.check();
        s.expect_unsat();
    }

    /**
     * has solutions a = 2 and a = 3
     */
    static void test_p2() {
        scoped_solver s(__func__);
        auto a = s.var(s.add_var(2));
        auto p = a*(a-1) + 2;
        s.add_eq(p);
        s.check();
        s.expect_sat();
    }

    /**
     * unsat
     * - learns 3*x + 1 == 0 by polynomial resolution
     * - this forces x == 5, which means the first constraint is unsatisfiable by parity.
     */
    static void test_p3() {
        scoped_solver s(__func__);
        auto x = s.var(s.add_var(4));
        auto y = s.var(s.add_var(4));
        auto z = s.var(s.add_var(4));
        s.add_eq(x*x*y + 3*y + 7);
        s.add_eq(2*y + z + 8);
        s.add_eq(3*x + 4*y*z + 2*z*z + 1);
        s.check();
        s.expect_unsat();
    }


    // Unique solution: u = 5
    static void test_ineq_basic1() {
        scoped_solver s(__func__);
        auto u = s.var(s.add_var(4));
        auto zero = u - u;
        s.add_ule(u, zero + 5);
        s.add_ule(zero + 5, u);
        s.check();
        s.expect_sat({{u, 5}});
    }

    // Unsatisfiable
    static void test_ineq_basic2() {
        scoped_solver s(__func__);
        auto u = s.var(s.add_var(4));
        auto zero = u - u;
        s.add_ult(u, zero + 5);
        s.add_ule(zero + 5, u);
        s.check();
        s.expect_unsat();
    }

    // Solutions with u = v = w
    static void test_ineq_basic3() {
        scoped_solver s(__func__);
        auto u = s.var(s.add_var(4));
        auto v = s.var(s.add_var(4));
        auto w = s.var(s.add_var(4));
        s.add_ule(u, v);
        s.add_ule(v, w);
        s.add_ule(w, u);
        s.check();
        s.expect_sat();
        SASSERT_EQ(s.get_value(u.var()), s.get_value(v.var()));
        SASSERT_EQ(s.get_value(u.var()), s.get_value(w.var()));
    }

    // Unsatisfiable
    static void test_ineq_basic4() {
        scoped_solver s(__func__);
        auto u = s.var(s.add_var(4));
        auto v = s.var(s.add_var(4));
        auto w = s.var(s.add_var(4));
        s.add_ule(u, v);
        s.add_ult(v, w);
        s.add_ule(w, u);
        s.check();
        s.expect_unsat();
    }

    // Satisfiable
    // Without forbidden intervals, we just try values for u until it works
    static void test_ineq_basic5() {
        scoped_solver s(__func__);
        auto u = s.var(s.add_var(4));
        auto v = s.var(s.add_var(4));
        auto zero = u - u;
        s.add_ule(zero + 12, u + v);
        s.add_ule(v, zero + 2);
        s.check();
        s.expect_sat();  // e.g., u = 12, v = 0
    }

    // Like test_ineq_basic5 but the other forbidden interval will be the longest
    static void test_ineq_basic6() {
        scoped_solver s(__func__);
        auto u = s.var(s.add_var(4));
        auto v = s.var(s.add_var(4));
        auto zero = u - u;
        s.add_ule(zero + 14, u + v);
        s.add_ule(v, zero + 2);
        s.check();
        s.expect_sat();
    }


    /**
     * Check unsat of:
     * u = v*q + r
     * r < u
     * v*q > u
     */
    static void test_ineq1() {
        scoped_solver s(__func__);
        auto u = s.var(s.add_var(5));
        auto v = s.var(s.add_var(5));
        auto q = s.var(s.add_var(5));
        auto r = s.var(s.add_var(5));
        s.add_eq(u - (v*q) - r);
        s.add_ult(r, u);
        s.add_ult(u, v*q);
        s.check();
        s.expect_unsat();
    }

    /**
     * Check unsat of:
     * n*q1 = a - b
     * n*q2 + r2 = c*a - c*b
     * n > r2 > 0
     */
    static void test_ineq2() {
        scoped_solver s(__func__);
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
        s.expect_unsat();
    }


    /**
     * Monotonicity example from certora
     * 
     * We do overflow checks by doubling the base bitwidth here.
     */
    static void test_monot() {
        scoped_solver s(__func__);

        auto baseBw = 5;
        auto max_int_const = 31; // (2^5 - 1) -- change this when you change baseBw

        auto bw = 2 * baseBw;
        auto max_int = s.var(s.add_var(bw));
        s.add_eq(max_int - max_int_const);

        auto tb1 = s.var(s.add_var(bw));
        s.add_ule(tb1, max_int);
        auto tb2 = s.var(s.add_var(bw));
        s.add_ule(tb2, max_int);
        auto a = s.var(s.add_var(bw));
        s.add_ule(a, max_int);
        auto v = s.var(s.add_var(bw));
        s.add_ule(v, max_int);
        auto base1 = s.var(s.add_var(bw));
        s.add_ule(base1, max_int);
        auto base2 = s.var(s.add_var(bw));
        s.add_ule(base2, max_int);
        auto elastic1 = s.var(s.add_var(bw));
        s.add_ule(elastic1, max_int);
        auto elastic2 = s.var(s.add_var(bw));
        s.add_ule(elastic2, max_int);
        auto err = s.var(s.add_var(bw));
        s.add_ule(err, max_int);

        auto rem1 = s.var(s.add_var(bw));
        auto quot2 = s.var(s.add_var(bw));
        s.add_ule(quot2, max_int);
        auto rem2 = s.var(s.add_var(bw));
        auto rem3 = s.var(s.add_var(bw));
        auto quot4 = s.var(s.add_var(bw));
        s.add_ule(quot4, max_int);
        auto rem4 = s.var(s.add_var(bw));

        s.add_diseq(elastic1);

        // division: tb1 = (v * base1) / elastic1;
        s.add_eq((tb1 * elastic1) + rem1 - (v * base1));
        s.add_ult(rem1, elastic1);
        s.add_ule((tb1 * elastic1), max_int);

        // division: quot2 = (a * base1) / elastic1
        s.add_eq((quot2 * elastic1) + rem2 - (a * base1));
        s.add_ult(rem2, elastic1);
        s.add_ule((quot2 * elastic1), max_int);

        s.add_eq(base1 + quot2 - base2);

        s.add_eq(elastic1 + a - elastic2);

        // division: tb2 = ((v * base2) / elastic2);
        s.add_eq((tb2 * elastic2) + rem3 - (v * base2));
        s.add_ult(rem3, elastic2);
        s.add_ule((tb2 * elastic2), max_int);

        // division: quot4 = v / elastic2;
        s.add_eq((quot4 * elastic2) + rem4 - v);
        s.add_ult(rem4, elastic2);
        s.add_ule((quot4 * elastic2), max_int);

        s.add_eq(quot4 + 1 - err);

        s.push();
        s.add_ult(tb1, tb2);
        s.check();
        s.expect_unsat();
        s.pop();

        s.push();
        s.add_ult(tb2 + err, tb1);
        s.check();
        s.expect_unsat();
        s.pop();
    }

    /*
     * Mul-then-div in fixed point arithmetic is (roughly) neutral.
     *
     * I.e. we prove "(((a * b) / sf) * sf) / b" to be equal to a, up to some error margin.
     * 
     * sf is the scaling factor (we could leave this unconstrained, but non-zero, to make the benchmark a bit harder)
     * em is the error margin
     * 
     * We do overflow checks by doubling the base bitwidth here.
     */
    static void test_fixed_point_arith_mul_div_inverse() {
        scoped_solver s(__func__);

        auto baseBw = 5;
        auto max_int_const = 31; // (2^5 - 1) -- change this when you change baseBw

        auto bw = 2 * baseBw;
        auto max_int = s.var(s.add_var(bw));
        s.add_eq(max_int - max_int_const);

        auto zero = max_int - max_int;

        // "input" variables
        auto a = s.var(s.add_var(bw));
        s.add_ule(a, max_int);
        auto b = s.var(s.add_var(bw));
        s.add_ule(b, max_int);
        s.add_ult(zero, b); // b > 0

        // scaling factor (setting it, somewhat arbitrarily, to max_int/3)
        auto sf = s.var(s.add_var(bw));
        s.add_eq(sf - (max_int_const/3));

        // (a * b) / sf = quot1 <=> quot1 * sf + rem1 - (a * b) = 0
        auto quot1 = s.var(s.add_var(bw));
        auto rem1 = s.var(s.add_var(bw));
        s.add_eq((quot1 * sf) + rem1 - (a * b));
        s.add_ult(rem1, sf);
        s.add_ule(quot1 * sf, max_int);

        // (((a * b) / sf) * sf) / b <=> quot2 * b + rem2 - (((a * b) / sf) * sf) = 0
        auto quot2 = s.var(s.add_var(bw));
        auto rem2 = s.var(s.add_var(bw));
        s.add_eq((quot2 * b) + rem2 - (quot1 * sf));
        s.add_ult(rem2, b);
        s.add_ule(quot2 * b, max_int);

        // sf / b = quot3 <=> quot3 * b + rem3 = sf
        auto quot3 = s.var(s.add_var(bw));
        auto rem3 = s.var(s.add_var(bw));
        s.add_eq((quot3 * b) + rem3 - sf);
        s.add_ult(rem3, b);
        s.add_ule(quot3 * b, max_int);

        // em = sf / b + 1
        auto em = s.var(s.add_var(bw));
        s.add_eq(quot3 + 1 - em);

        // we prove quot3 <= a and quot3 + em >= a

        s.push();
        s.add_ult(a, quot3);
        s.check();
        s.expect_unsat();
        s.pop();

        s.push();
        s.add_ult(quot3 + em, a);
        s.check();
        s.expect_unsat();
        s.pop();
    }

    /*
     * Div-then-mul in fixed point arithmetic is (roughly) neutral.
     *
     * I.e. we prove "(b * ((a * sf) / b)) / sf" to be equal to a, up to some error margin.
     * 
     * sf is the scaling factor (we could leave this unconstrained, but non-zero, to make the benchmark a bit harder)
     * em is the error margin
     * 
     * We do overflow checks by doubling the base bitwidth here.
     */
    static void test_fixed_point_arith_div_mul_inverse() {
        scoped_solver s(__func__);

        auto baseBw = 5;
        auto max_int_const = 31; // (2^5 - 1) -- change this when you change baseBw

        auto bw = 2 * baseBw;
        auto max_int = s.var(s.add_var(bw));
        s.add_eq(max_int - max_int_const);

        auto zero = max_int - max_int;

        // "input" variables
        auto a = s.var(s.add_var(bw));
        s.add_ule(a, max_int);
        auto b = s.var(s.add_var(bw));
        s.add_ule(b, max_int);
        s.add_ult(zero, b); // b > 0

        // scaling factor (setting it, somewhat arbitrarily, to max_int/3)
        auto sf = s.var(s.add_var(bw));
        s.add_eq(sf - (max_int_const/3));

        // (a * sf) / b = quot1 <=> quot1 * b + rem1 - (a * sf) = 0
        auto quot1 = s.var(s.add_var(bw));
        auto rem1 = s.var(s.add_var(bw));
        s.add_eq((quot1 * b) + rem1 - (a * sf));
        s.add_ult(rem1, b);
        s.add_ule(quot1 * b, max_int);

        // (b * ((a * sf) / b)) / sf = quot2 <=> quot2 * sf + rem2 - (b * ((a * sf) / b)) = 0
        auto quot2 = s.var(s.add_var(bw));
        auto rem2 = s.var(s.add_var(bw));
        s.add_eq((quot2 * sf) + rem2 - (b * quot1));
        s.add_ult(rem2, sf);
        s.add_ule(quot2 * sf, max_int);

        // b / sf = quot3 <=> quot3 * sf + rem3 - b = 0
        auto quot3 = s.var(s.add_var(bw));
        auto rem3 = s.var(s.add_var(bw));
        s.add_eq((quot3 * sf) + rem3 - b);
        s.add_ult(rem3, sf);
        s.add_ule(quot3 * sf, max_int);

        // em = b / sf + 1
        auto em = s.var(s.add_var(bw));
        s.add_eq(quot3 + 1 - em);

        // we prove quot3 <= a and quot3 + em >= a

        s.push();
        s.add_ult(a, quot3);
        s.check();
        s.expect_unsat();
        s.pop();

        s.push();
        s.add_ult(quot3 + em, a);
        s.check();
        s.expect_unsat();
        s.pop();
    }

    /*
     * Transcribed from https://github.com/NikolajBjorner/polysat/blob/main/puzzles/bv.smt2 .

     * We do overflow checks by doubling the base bitwidth here.
     */
    static void test_fixed_point_arith_div_mul_inverse2() {
        scoped_solver s(__func__);

        auto baseBw = 5;
        auto max_int_const = 31; // (2^5 - 1) -- change this when you change baseBw

        auto bw = 2 * baseBw;
        auto max_int = s.var(s.add_var(bw));
        s.add_eq(max_int - max_int_const);

        auto zero = max_int - max_int;

        auto first = s.var(s.add_var(bw));
        s.add_ule(first, max_int);
        auto second = s.var(s.add_var(bw));
        s.add_ule(second, max_int);
        auto idx = s.var(s.add_var(bw));
        s.add_ule(idx, max_int);
        auto r = s.var(s.add_var(bw));
        s.add_ule(r, max_int);

        // q = max_int / idx <=> q * idx + r - max_int = 0
        auto q = s.var(s.add_var(bw));
        r = s.var(s.add_var(bw));
        s.add_eq((q * idx) + r - max_int);
        s.add_ult(r, idx);
        s.add_ule(q * idx, max_int);

        /*  last assertion:
                (not
                    (=> (bvugt second first) 
                        (=> 
                            (=> (not (= idx #x00000000)) 
                                (bvule (bvsub second first) q)) 
                            (bvumul_noovfl (bvsub second first) idx))))
            transforming negated boolean skeleton:
                (not (=> a (=> (or b c) d))) <=> (and a (not d) (or b c))
         */

        // (bvugt second first)
        s.add_ult(first, second);
        // (bvumul_noovfl (bvsub second first) idx)
        s.add_ule((second - first) * idx, max_int);

        // resolving disjunction via push/pop

        // first disjunct: (= idx #x00000000)
        s.push();
        s.add_eq(idx);
        s.check();
        s.expect_unsat();
        s.pop();

        // second disjunct: (bvule (bvsub second first) q)
        s.push();
        s.add_ule(second - first, q);
        s.check();
        s.expect_unsat();
        s.pop();
    }



    // Goal: we probably mix up polysat variables and PDD variables at several points; try to uncover such cases
    // NOTE: actually, add_var seems to keep them in sync, so this is not an issue at the moment (but we should still test it later)
    // static void test_mixed_vars() {
    //     scoped_solver s(__func__);
    //     auto a = s.var(s.add_var(2));
    //     auto b = s.var(s.add_var(4));
    //     auto c = s.var(s.add_var(2));
    //     s.add_eq(a + 2*c + 4);
    //     s.add_eq(3*b + 4);
    //     s.check();
    //     // Expected result:
    // }

    // convert assertions into internal solver state
    // support small grammar of formulas.
    void internalize(solver& s, expr_ref_vector& fmls) {

    }
}


void tst_polysat() {
    polysat::test_add_conflicts();
    polysat::test_wlist();
    polysat::test_cjust();
    polysat::test_l1();
    polysat::test_l2();
    polysat::test_l3();
    polysat::test_l4();
    polysat::test_l5();
    polysat::test_p1();
    polysat::test_p2();
    polysat::test_p3();
    polysat::test_ineq_basic1();
    polysat::test_ineq_basic2();
    polysat::test_ineq_basic3();
    polysat::test_ineq_basic4();
    polysat::test_ineq_basic5();
    polysat::test_ineq_basic6();
    polysat::test_fixed_point_arith_div_mul_inverse2();
    polysat::test_fixed_point_arith_div_mul_inverse();
    polysat::test_fixed_point_arith_mul_div_inverse();
#if 0
    // worry about this later
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
    if (argc != 2) {
        std::cerr << "Usage: " << argv[0] << " FILE\n";
        return;
    }
    std::ifstream is(argv[1]);
    // cmd_context ctx(false, &m);
    cmd_context ctx(false);
    ctx.set_ignore_check(true);
    VERIFY(parse_smt2_commands(ctx, is));
    auto fmls = ctx.assertions();
    polysat::scoped_solver s("polysat");
    for (expr* fm : fmls) {
        // fm->get_kind()
        if (is_app(fm)) {
            // is_app_of
        }
    }
    // polysat::internalize(s, fmls);
    // std::cout << s.check() << "\n";
    s.check();
}
