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

    public:
        scoped_solver(std::string name): solver(lim), m_name(name) {
            LOG("\n\n\n" << std::string(78, '#') << "\n\nSTART: " << m_name << "\n");
            set_max_conflicts(10);
        }

        void set_max_conflicts(unsigned c) {
            params_ref p;
            p.set_uint("max_conflicts", c);
            updt_params(p);
        }

        void check() {
            m_last_result = check_sat();
            LOG(m_name << ": " << m_last_result << "\n");
            statistics st;
            collect_statistics(st);
            LOG(st << "\n" << *this << "\n");
        }

        void expect_unsat() {
            if (m_last_result != l_false && m_last_result != l_undef) {
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
            else if (m_last_result == l_false) {
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
        s.add_ule(u, 5);
        s.add_ule(5, u);
        s.check();
        s.expect_sat({{u, 5}});
    }

    // Unsatisfiable
    static void test_ineq_basic2() {
        scoped_solver s(__func__);
        auto u = s.var(s.add_var(4));
        s.add_ult(u, 5);
        s.add_ule(5, u);
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
        s.add_ule(12, u + v);
        s.add_ule(v, 2);
        s.check();
        s.expect_sat();  // e.g., u = 12, v = 0
    }

    // Like test_ineq_basic5 but the other forbidden interval will be the longest
    static void test_ineq_basic6() {
        scoped_solver s(__func__);
        auto u = s.var(s.add_var(4));
        auto v = s.var(s.add_var(4));
        s.add_ule(14, u + v);
        s.add_ule(v, 2);
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
        s.add_diseq(r2);
        s.check();
        s.expect_unsat();
    }


    /**
     * Monotonicity example from certora
     * 
     * We do overflow checks by doubling the base bitwidth here.
     */
    static void test_monot(unsigned base_bw = 5) {
        scoped_solver s(std::string{__func__} + "(" + std::to_string(base_bw) + ")");

        auto max_int_const = rational::power_of_two(base_bw) - 1;

        unsigned bw = 2 * base_bw;
        auto max_int = s.var(s.add_var(bw));
        s.add_eq(max_int + (-max_int_const));

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

        // "input" variables
        auto a = s.var(s.add_var(bw));
        s.add_ule(a, max_int);
        auto b = s.var(s.add_var(bw));
        s.add_ule(b, max_int);
        s.add_ult(0, b); // b > 0

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


        // s.push();
        // s.add_ult(quot3 + em, a);
        // s.check();
        // s.expect_unsat();
        // s.pop();
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
    static void test_fixed_point_arith_div_mul_inverse(unsigned base_bw = 5) {
        scoped_solver s(__func__);

        auto max_int_const = rational::power_of_two(base_bw) - 1;

        auto bw = 2 * base_bw;
        auto max_int = s.var(s.add_var(bw));
        s.add_eq(max_int - max_int_const);

        // "input" variables
        auto a = s.var(s.add_var(bw));
        s.add_ule(a, max_int);
        auto b = s.var(s.add_var(bw));
        s.add_ule(b, max_int);
        s.add_ult(0, b); // b > 0

        // scaling factor (setting it, somewhat arbitrarily, to max_int/3)
        auto sf = s.var(s.add_var(bw));
        s.add_eq(sf - floor(max_int_const/3));

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
        s.add_ult(quot3 + em, a);
        s.check();
        //        s.expect_unsat();
        s.pop();

        s.push();
        s.add_ult(a, quot3);
        s.check();
//        s.expect_unsat();
        s.pop();



        //exit(0);
    }

    /** Monotonicity under bounds,
     * puzzle extracted from https://github.com/NikolajBjorner/polysat/blob/main/puzzles/bv.smt2
     *
     * x, y, z \in [0..2^64[
     * x, y, z < 2^32
     * y <= x
     * x*z < 2^32
     * y*z >= 2^32
     */
    static void test_monot_bounds(unsigned base_bw = 32) {
        scoped_solver s(std::string{__func__} + "(" + std::to_string(base_bw) + ")");
        unsigned bw = 2 * base_bw;
        auto y = s.var(s.add_var(bw));
        auto z = s.var(s.add_var(bw));
        auto x = s.var(s.add_var(bw));
        auto bound = rational::power_of_two(base_bw);
#if 1
        s.add_ult(x, bound);
        s.add_ult(y, bound);
        // s.add_ult(z, bound);   // not required
#else
        s.add_ule(x, bound - 1);
        s.add_ule(y, bound - 1);
        // s.add_ule(z, bound - 1);   // not required
#endif
        unsigned a = 13;
        s.add_ule(z, y);
        s.add_ult(x*y, a);
        s.add_ule(a, x*z);
        s.check();
        s.expect_unsat();
    }

    /** Monotonicity under bounds, simplified even more.
     *
     * x, y, z \in [0..2^64[
     * x, y, z < 2^32
     * z <= y
     * y*x < z*x
     */
    static void test_monot_bounds_simple(unsigned base_bw = 32) {
        scoped_solver s(__func__);
        unsigned bw = 2 * base_bw;
        /*
        auto z = s.var(s.add_var(bw));
        auto x = s.var(s.add_var(bw));
        auto y = s.var(s.add_var(bw));
        */
        auto y = s.var(s.add_var(bw));
        auto x = s.var(s.add_var(bw));
        auto z = s.var(s.add_var(bw));
        auto bound = rational::power_of_two(base_bw);
        s.add_ult(x, bound);
        s.add_ult(y, bound);
        s.add_ult(z, bound);
        s.add_ule(z, y);
        s.add_ult(y*x, z*x);
        s.check();
        s.expect_unsat();
    }

    /*
     * Transcribed from https://github.com/NikolajBjorner/polysat/blob/main/puzzles/bv.smt2
     *
     * We do overflow checks by doubling the base bitwidth here.
     */
    static void test_monot_bounds_full(unsigned base_bw = 5) {
        scoped_solver s(__func__);

        auto const max_int_const = rational::power_of_two(base_bw) - 1;

        auto const bw = 2 * base_bw;
        auto const max_int = s.var(s.add_var(bw));
        s.add_eq(max_int - max_int_const);

        auto const first = s.var(s.add_var(bw));
        s.add_ule(first, max_int);
        auto const second = s.var(s.add_var(bw));
        s.add_ule(second, max_int);
        auto const idx = s.var(s.add_var(bw));
        s.add_ule(idx, max_int);
        auto const q = s.var(s.add_var(bw));
        s.add_ule(q, max_int);
        auto const r = s.var(s.add_var(bw));
        s.add_ule(r, max_int);

        // q = max_int / idx <=> q * idx + r - max_int = 0
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
        // (not (bvumul_noovfl (bvsub second first) idx))
        s.add_ult(max_int, (second - first) * idx);
        // s.add_ule((second - first) * idx, max_int);

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

    static void test_var_minimize(unsigned bw = 32) {
        scoped_solver s(__func__);
        auto x = s.var(s.add_var(bw));
        auto y = s.var(s.add_var(bw));
        auto z = s.var(s.add_var(bw));
        s.add_eq(x);
        s.add_eq(4 * y + 8 * z + x + 2); // should only depend on assignment to x
        s.check();
        s.expect_unsat();
    }


    /**
     * x*x <= z
     * (x+1)*(x+1) <= z
     * y == x+1
     * ¬(y*y <= z)
     *
     * The original version had signed comparisons but that doesn't matter for the UNSAT result.
     * UNSAT can be seen easily by substituting the equality.
     *
     * Possible ways to solve:
     * - Integrate AC congruence closure
     *      See: Deepak Kapur. A Modular Associative Commutative (AC) Congruence Closure Algorithm, FSCD 2021. https://doi.org/10.4230/LIPIcs.FSCD.2021.15
     * - Propagate equalities as substitutions
     *      x=t /\ p(x) ==> p(t)
     *      Ackermann-like reduction
     *   (index, watch lists over boolean literals)
     * - Augment explain:
     *      conflict: y=x+1 /\ y^2 > z
     *      explain could then derive (x+1)^2 > z
     */
    static void test_subst(unsigned bw = 32) {
        scoped_solver s(__func__);
        auto x = s.var(s.add_var(bw));
        auto y = s.var(s.add_var(bw));
        auto z = s.var(s.add_var(bw));
        s.add_ule(x * x, z);  // optional
        s.add_ule((x + 1) * (x + 1), z);
        s.add_eq(x + 1 - y);
        s.add_ult(z, y*y);
        s.check();
        s.expect_unsat();
    }

    static void test_subst_signed(unsigned bw = 32) {
        scoped_solver s(__func__);
        auto x = s.var(s.add_var(bw));
        auto y = s.var(s.add_var(bw));
        auto z = s.var(s.add_var(bw));
        s.add_sle(x * x, z);  // optional
        s.add_sle((x + 1) * (x + 1), z);
        s.add_eq(x + 1 - y);
        s.add_slt(z, y*y);
        s.check();
        s.expect_unsat();
    }

    void permute_args(unsigned k, pdd& a, pdd& b, pdd& c) {
        SASSERT(k < 6);
        unsigned i = k % 3;
        unsigned j = k % 2;
        if (i == 1)
            std::swap(a, b);
        else if (i == 2)
            std::swap(a, c);
        if (j == 1)
            std::swap(b, c);
    }

    void permute_args(unsigned n, pdd& a, pdd& b, pdd& c, pdd& d) {
        SASSERT(n < 24);
        switch (n % 4) {
        case 1: 
            std::swap(a, b);
            break;
        case 2:
            std::swap(a, c);
            break;
        case 3:
            std::swap(a, d);
            break;
        default:
            break;
        }
        switch (n % 3) {
        case 1:
            std::swap(b, c);
            break;
        case 2:
            std::swap(b, d);
            break;
        default:
            break;
        }
        switch (n % 2) {
        case 1:
            std::swap(c, d);
            break;
        default:
            break;
        }
    }

    // xy < xz and !Omega(x*y) => y < z
    static void test_ineq_axiom1(unsigned bw = 32) {
        auto const bound = rational::power_of_two(bw/2);

        for (unsigned i = 0; i < 6; ++i) {
            scoped_solver s(__func__);
            auto x = s.var(s.add_var(bw));
            auto y = s.var(s.add_var(bw));
            auto z = s.var(s.add_var(bw));
            permute_args(i, x, y, z);
            s.add_ult(x * y, x * z);
            s.add_ule(z, y);
            s.add_ult(x, bound);
            s.add_ult(y, bound);
            s.check();
            s.expect_unsat();
        }
    }

    static void test_ineq_non_axiom1(unsigned bw = 32) {
        auto const bound = rational::power_of_two(bw - 1);

        for (unsigned i = 0; i < 6; ++i) {
            scoped_solver s(__func__);
            auto x = s.var(s.add_var(bw));
            auto y = s.var(s.add_var(bw));
            auto z = s.var(s.add_var(bw));
            permute_args(i, x, y, z);
            s.add_ult(x * y, x * z);
            s.add_ule(z, y);
            //s.add_ult(x, bound);
            //s.add_ult(y, bound);
            s.check();
            s.expect_sat();
        }
    }

    // xy <= xz & !Omega(x*y) => y <= z or x = 0
    static void test_ineq_axiom2(unsigned bw = 32) {
        auto const bound = rational::power_of_two(bw/2);
        for (unsigned i = 0; i < 6; ++i) {
            scoped_solver s(__func__);
            auto x = s.var(s.add_var(bw));
            auto y = s.var(s.add_var(bw));
            auto z = s.var(s.add_var(bw));
            permute_args(i, x, y, z);
            s.add_ult(x * y, x * z);
            s.add_ult(z, y);
            s.add_ult(x, bound);
            s.add_ult(y, bound);
            s.add_diseq(x);
            s.check();
            s.expect_unsat();
        }
    }

    // xy < b & a <= x  & !Omega(x*y) => a*y < b
    static void test_ineq_axiom3(unsigned bw = 32) {
        auto const bound = rational::power_of_two(bw/2);
        for (unsigned i = 0; i < 24; ++i) {
            scoped_solver s(__func__);
            auto x = s.var(s.add_var(bw));
            auto y = s.var(s.add_var(bw));
            auto a = s.var(s.add_var(bw));
            auto b = s.var(s.add_var(bw));
            permute_args(i, x, y, a, b);
            s.add_ult(x * y, b);
            s.add_ule(a, x);
            s.add_ult(x, bound);
            s.add_ult(y, bound);
            s.add_ule(b, a * y);
            s.check();
            s.expect_unsat();
        }
    }

    // x*y <= b & a <= x & !Omega(x*y) => a*y <= b
    static void test_ineq_axiom4(unsigned bw = 32) {
        auto const bound = rational::power_of_two(bw/2);
        for (unsigned i = 0; i < 24; ++i) {
            scoped_solver s(__func__);
            auto x = s.var(s.add_var(bw));
            auto y = s.var(s.add_var(bw));
            auto a = s.var(s.add_var(bw));
            auto b = s.var(s.add_var(bw));
            permute_args(i, x, y, a, b);
            s.add_ule(x * y, b);
            s.add_ule(a, x);
            s.add_ult(x, bound);
            s.add_ult(y, bound);
            s.add_ult(b, a * y);
            s.check();
            s.expect_unsat();
        }
    }

    // x*y <= b & a <= x & !Omega(x*y) => a*y <= b
    static void test_ineq_non_axiom4(unsigned bw, unsigned i) {
        auto const bound = rational::power_of_two(bw - 1);
        scoped_solver s(__func__);
        LOG("permutation: " << i);
        auto x = s.var(s.add_var(bw));
        auto y = s.var(s.add_var(bw));
        auto a = s.var(s.add_var(bw));
        auto b = s.var(s.add_var(bw));
        permute_args(i, x, y, a, b);
        s.add_ule(x * y, b);
        s.add_ule(a, x);
        s.add_ult(x, bound);
        s.add_ult(y, bound);
        s.add_ult(b, a * y);
        s.check();
        s.expect_sat();
    }
    
    static void test_ineq_non_axiom4(unsigned bw = 32) {
        for (unsigned i = 0; i < 24; ++i)
            test_ineq_non_axiom4(bw, i);
    }

    // a < xy & x <= b  & !Omega(x*y) => a < b*y
    static void test_ineq_axiom5(unsigned bw = 32) {
        auto const bound = rational::power_of_two(bw/2);
        for (unsigned i = 0; i < 24; ++i) {
            scoped_solver s(__func__);
            auto x = s.var(s.add_var(bw));
            auto y = s.var(s.add_var(bw));
            auto a = s.var(s.add_var(bw));
            auto b = s.var(s.add_var(bw));
            permute_args(i, x, y, a, b);
            s.add_ult(a, x * y);
            s.add_ule(x, b);
            s.add_ult(x, bound);
            s.add_ult(y, bound);
            s.add_ule(b * y, a);
            s.check();
            s.expect_unsat();
        }
    }

    // a <= xy & x <= b & !Omega(x*y) => a <= b*y
    static void test_ineq_axiom6(unsigned bw = 32) {
        auto const bound = rational::power_of_two(bw/2);
        for (unsigned i = 0; i < 24; ++i) {
            scoped_solver s(__func__);
            auto x = s.var(s.add_var(bw));
            auto y = s.var(s.add_var(bw));
            auto a = s.var(s.add_var(bw));
            auto b = s.var(s.add_var(bw));
            permute_args(i, x, y, a, b);
            s.add_ule(a, x * y);
            s.add_ule(x, b);
            s.add_ult(x, bound);
            s.add_ult(y, bound);
            s.add_ult(b * y, a);
            s.check();
            s.expect_unsat();
        }
    }

    static void test_quot_rem(unsigned bw = 32) {
        scoped_solver s(__func__);
        s.set_max_conflicts(5);
        auto a = s.var(s.add_var(bw));
        auto quot = s.var(s.add_var(bw));
        auto rem = s.var(s.add_var(bw));
        auto x = a * 123;
        auto y = 123;
        // quot = udiv(a*123, 123)
        s.add_eq(quot * y + rem - x);
        s.add_diseq(a - quot);
        s.add_noovfl(quot, y);     
        s.add_ult(rem, x);
        s.check();
        s.expect_sat();
    }

    static void test_quot_rem2(unsigned bw = 32) {
        scoped_solver s(__func__);
        s.set_max_conflicts(5);
        auto q = s.var(s.add_var(bw));
        auto r = s.var(s.add_var(bw));
        auto idx = s.var(s.add_var(bw));
        auto second = s.var(s.add_var(bw));
        auto first = s.var(s.add_var(bw));
        s.add_eq(q*idx + r, UINT_MAX);
        s.add_ult(r, idx);
        s.add_noovfl(q, idx);
        s.add_ult(first, second);
        s.add_diseq(idx, 0);
        s.add_ule(second - first, q);
        s.add_noovfl(second  - first, idx);
        s.check();       
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

    pdd to_pdd(ast_manager& m, solver& s, obj_map<expr, pdd*>& expr2pdd, expr* e) {
        pdd* r = nullptr;
        if (expr2pdd.find(e, r))
            return *r;
        bv_util bv(m);
        rational n;
        unsigned sz = bv.get_bv_size(e);
        expr* a, *b;
        if (bv.is_bv_add(e, a, b)) {
            auto pa = to_pdd(m, s, expr2pdd, a);
            auto pb = to_pdd(m, s, expr2pdd, b);
            r = alloc(pdd, pa + pb);
        }
        else if (bv.is_bv_sub(e, a, b)) {
            auto pa = to_pdd(m, s, expr2pdd, a);
            auto pb = to_pdd(m, s, expr2pdd, b);
            r = alloc(pdd, pa - pb);
        }
        else if (bv.is_bv_mul(e, a, b)) {
            auto pa = to_pdd(m, s, expr2pdd, a);
            auto pb = to_pdd(m, s, expr2pdd, b);
            r = alloc(pdd, pa * pb);
        }
        else if (bv.is_bv_udiv(e, a, b)) {
            auto pa = to_pdd(m, s, expr2pdd, a);
            auto pb = to_pdd(m, s, expr2pdd, b);  
            auto qr = s.quot_rem(pa, pb);            
            r = alloc(pdd, std::get<0>(qr));
        }
        else if (bv.is_bv_urem(e, a, b)) {
            auto pa = to_pdd(m, s, expr2pdd, a);
            auto pb = to_pdd(m, s, expr2pdd, b);
            auto qr = s.quot_rem(pa, pb);
            r = alloc(pdd, std::get<1>(qr));
        }
        else if (bv.is_bv_lshr(e, a, b)) {
            auto pa = to_pdd(m, s, expr2pdd, a);
            auto pb = to_pdd(m, s, expr2pdd, b);
            r = alloc(pdd, s.lshr(pa, pb));
        }
        else if (bv.is_numeral(e, n, sz)) 
            r = alloc(pdd, s.value(n, sz));
        else if (is_uninterp(e)) 
            r = alloc(pdd, s.var(s.add_var(sz)));
        else {
            std::cout << "UNKNOWN " << mk_pp(e, m) << "\n";
            r = alloc(pdd, s.var(s.add_var(sz)));
        }
        expr2pdd.insert(e, r);
        return *r;
    }

    void internalize(ast_manager& m, solver& s, ptr_vector<expr>& fmls) {
        bv_util bv(m);
        obj_map<expr, pdd*> expr2pdd;
        for (expr* fm : fmls) {
            bool is_not = m.is_not(fm, fm);
            expr* a, *b;
            if (m.is_eq(fm, a, b)) {
                auto pa = to_pdd(m, s, expr2pdd, a);
                auto pb = to_pdd(m, s, expr2pdd, b);
                if (is_not)
                    s.add_diseq(pa - pb);
                else 
                    s.add_eq(pa - pb);
            }
            else if (bv.is_ult(fm, a, b) || bv.is_ugt(fm, b, a)) {
                auto pa = to_pdd(m, s, expr2pdd, a);
                auto pb = to_pdd(m, s, expr2pdd, b);
                if (is_not)
                    s.add_ule(pb, pa);
                else 
                    s.add_ult(pa, pb);
            }
            else if (bv.is_ule(fm, a, b) || bv.is_uge(fm, b, a)) {
                auto pa = to_pdd(m, s, expr2pdd, a);
                auto pb = to_pdd(m, s, expr2pdd, b);
                if (is_not)
                    s.add_ult(pb, pa);
                else 
                    s.add_ule(pa, pb);
            }
            else if (bv.is_slt(fm, a, b) || bv.is_sgt(fm, b, a)) {
                auto pa = to_pdd(m, s, expr2pdd, a);
                auto pb = to_pdd(m, s, expr2pdd, b);
                if (is_not)
                    s.add_sle(pb, pa);
                else 
                    s.add_slt(pa, pb);
            }
            else if (bv.is_sle(fm, a, b) || bv.is_sge(fm, b, a)) {
                auto pa = to_pdd(m, s, expr2pdd, a);
                auto pb = to_pdd(m, s, expr2pdd, b);
                if (is_not)
                    s.add_slt(pb, pa);
                else 
                    s.add_sle(pa, pb);
            }
            else {
                std::cout << "SKIP: " << mk_pp(fm, m) << "\n";            
            }
        }
        for (auto const& [k,v] : expr2pdd)
            dealloc(v);
    }
}


void tst_polysat() {

    polysat::test_quot_rem();
    return;

    polysat::test_ineq_axiom1();
    polysat::test_ineq_axiom2();
    polysat::test_ineq_axiom3();
    polysat::test_ineq_axiom4();
    polysat::test_ineq_axiom5();
    polysat::test_ineq_axiom6();
    return;

    polysat::test_ineq_basic4();
    //return;

    polysat::test_ineq_basic6();
            
    // polysat::test_monot_bounds(8);

    polysat::test_add_conflicts();
    polysat::test_wlist();
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

    polysat::test_cjust();
    polysat::test_subst();
    polysat::test_monot_bounds(2);

    polysat::test_var_minimize();

    polysat::test_ineq1();
    polysat::test_ineq2();
    polysat::test_monot();

    return;

    polysat::test_ineq_axiom1();
    polysat::test_ineq_axiom2();
    polysat::test_ineq_axiom3();
    polysat::test_ineq_axiom4();
    polysat::test_ineq_axiom5();
    polysat::test_ineq_axiom6();
#if 0
    polysat::test_ineq_non_axiom4(32, 5);
#endif

    // inefficient conflicts:
    // Takes time: polysat::test_monot_bounds_full();

    polysat::test_monot_bounds_simple(8);
    polysat::test_fixed_point_arith_div_mul_inverse();

}


#include "ast/bv_decl_plugin.h"
#include <signal.h>

polysat::scoped_solver* g_solver = nullptr;

static void display_statistics() {
    if (g_solver) {
        statistics st;
        g_solver->collect_statistics(st);
        std::cout << st << "\n";
    }
}

static void STD_CALL on_ctrl_c(int) {
    signal (SIGINT, SIG_DFL);
    display_statistics();
    raise(SIGINT);
}

void tst_polysat_argv(char** argv, int argc, int& i) {
    // set up SMT2 parser to extract assertions
    // assume they are simple bit-vector equations (and inequations)
    // convert to solver state.

    signal(SIGINT, on_ctrl_c);
    
    if (argc < 3) {
        std::cerr << "Usage: " << argv[0] << " FILE\n";
        return;
    }
    std::cout << "processing " << argv[2] << "\n";
    std::ifstream is(argv[2]);
    if (is.bad() || is.fail()) {
        std::cout << "failed to open " << argv[2] << "\n";
        return;
    }
    cmd_context ctx(false);
    ast_manager& m = ctx.m();
    ctx.set_ignore_check(true);
    VERIFY(parse_smt2_commands(ctx, is));
    ptr_vector<expr> fmls = ctx.assertions();
    polysat::scoped_solver s("polysat");
    g_solver = &s;
    polysat::internalize(m, s, fmls);
    std::cout << "checking\n";
    s.check();
}
