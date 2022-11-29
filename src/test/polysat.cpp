#include "math/polysat/log.h"
#include "math/polysat/solver.h"
#include "ast/ast.h"
#include "parsers/smt2/smt2parser.h"
#include "util/util.h"
#include <vector>
#include <signal.h>

namespace {
    using namespace dd;

    template <typename... Args>
    std::string concat(Args... args) {
        std::stringstream s;
        int dummy[sizeof...(Args)] = {
            // use dummy initializer list to sequence stream writes, cf. https://en.cppreference.com/w/cpp/language/parameter_pack
            (s << args, 0)...
        };
        (void)dummy;
        return s.str();
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
}

namespace polysat {

    enum class test_result {
        undefined,
        ok,
        wrong_answer,
        wrong_model,
        resource_out,  // solver hit the resource limit
        error,
    };

    template <typename T>
    T* with_default(T* value, T* default_value) {
        return value ? value : default_value;
    }

    struct test_record {
        std::string m_name;
        unsigned m_index = 0;  ///< m_index-th check_sat() call in this unit test.
        lbool m_answer = l_undef;  ///< what the solver returned
        lbool m_expected = l_undef;  ///< the answer we expect (l_undef if unspecified)
        test_result m_result = test_result::undefined;
        std::string m_error_message;
        bool m_finished = false;

        using clock_t = std::chrono::steady_clock;
        clock_t::time_point m_start;
        clock_t::time_point m_end;

        void set_error(char const* msg) {
            m_result = test_result::error;
            m_error_message = msg;
            m_finished = true;
        }

        std::ostream& display(std::ostream& out, unsigned name_width = 0) const;
    };

    std::ostream& operator<<(std::ostream& out, test_record const& r) { return r.display(out); }

    class test_record_manager {
        scoped_ptr_vector<test_record> m_records;

        std::string m_name;
        unsigned m_index = 0;

    public:
        void begin_batch(std::string name);
        void end_batch();
        test_record* new_record();
        test_record* active_or_new_record();
        void display(std::ostream& out) const;
    };

    void test_record_manager::begin_batch(std::string name) {
        end_batch();
        if (m_name != name) {
            m_name = name;
            m_index = 0;
        }
    }

    void test_record_manager::end_batch() {
        // Kick out unfinished records (they have the wrong name)
        while (!m_records.empty() && !m_records.back()->m_finished)
            m_records.pop_back();
    }

    test_record* test_record_manager::new_record() {
        auto* rec = alloc(test_record);
        rec->m_name = m_name;
        rec->m_index = ++m_index;
        m_records.push_back(rec);
        return rec;
    }

    test_record* test_record_manager::active_or_new_record() {
        if (m_records.empty() || m_records.back()->m_finished)
            return new_record();
        else
            return m_records.back();
    }

    std::ostream& test_record::display(std::ostream& out, unsigned name_width) const {
        if (!m_finished)
            out << "UNFINISHED ";
        out << m_name;
        if (m_index != 1)
            out << " (" << m_index << ") ";
        else
            out << "     ";
        for (size_t i = m_name.length(); i < name_width; ++i)
            out << ' ';
        std::chrono::duration<double> d = m_end - m_start;
        if (d.count() >= 0.15) {
            out << std::fixed << std::setprecision(1);
            out << std::setw(4) << d.count() << "s ";
        }
        else
            out << "      ";
        switch (m_answer) {
        case l_undef: out << "      "; break;
        case l_true:  out << "SAT   "; break;
        case l_false: out << "UNSAT "; break;
        }
        switch (m_result) {
        case test_result::undefined: out << "???"; break;
        case test_result::ok: out << "ok"; break;
        case test_result::wrong_answer: out << color_red() << "wrong answer, expected " << m_expected << color_reset(); break;
        case test_result::wrong_model: out << color_red() << "wrong model" << color_reset(); break;
        case test_result::resource_out: out << color_yellow() << "resource out" << color_reset(); break;
        case test_result::error: out << color_red() << "error: " << m_error_message << color_reset(); break;
        }
        return out;
    }

    void test_record_manager::display(std::ostream& out) const {
        out << "\n\nTest Results:\n";

        size_t max_name_len = 0;
        for (test_record const* r : m_records) {
            if (!r->m_finished)
                continue;
            max_name_len = std::max(max_name_len, r->m_name.length());
        }

        size_t n_total = m_records.size();
        size_t n_sat = 0;
        size_t n_unsat = 0;
        size_t n_wrong = 0;
        size_t n_error = 0;

        for (test_record const* r : m_records) {
            if (!r->m_finished)
                continue;
            r->display(out, max_name_len);
            out << std::endl;
            if (r->m_result == test_result::ok && r->m_answer == l_true)
                n_sat++;
            if (r->m_result == test_result::ok && r->m_answer == l_false)
                n_unsat++;
            if (r->m_result == test_result::wrong_answer || r->m_result == test_result::wrong_model)
                n_wrong++;
            if (r->m_result == test_result::error)
                n_error++;
        }
        out << n_total << " tests, " << (n_sat + n_unsat) << " ok (" << n_sat << " sat, " << n_unsat << " unsat)";
        if (n_wrong)
            out << ", " << color_red() << n_wrong << " wrong!" << color_reset();
        if (n_error)
            out << ", " << color_red() << n_error << " error" << color_reset();
        out << std::endl;
    }

    test_record_manager test_records;
    bool collect_test_records = true;

    // test resolve, factoring routines
    // auxiliary

    struct solver_scope {
        reslimit lim;
    };

    class scoped_solver : public solver_scope, public solver {
        std::string m_name;
        lbool m_last_result = l_undef;
        test_record* m_last_finished = nullptr;

    public:
        scoped_solver(std::string name): solver(lim), m_name(name) {
            std::cout << std::string(78, '#') << "\n\n";
            std::cout << "START: " << m_name << "\n";
            set_max_conflicts(10);

            test_records.begin_batch(name);
        }

        ~scoped_solver() {
            test_records.end_batch();
        }

        void set_max_conflicts(unsigned c) {
            params_ref p;
            p.set_uint("max_conflicts", c);
            updt_params(p);
        }

        void check() {
            auto* rec = test_records.active_or_new_record();
            rec->m_finished = true;
            m_last_finished = rec;
            SASSERT(rec->m_answer == l_undef);
            SASSERT(rec->m_expected == l_undef);
            SASSERT(rec->m_result == test_result::undefined);
            SASSERT(rec->m_error_message == "");
            {
                rec->m_start = test_record::clock_t::now();
                on_scope_exit end_timer([rec]() {
                    rec->m_end = test_record::clock_t::now();
                });
                m_last_result = check_sat();
            }
            std::cout << "DONE: " << m_name << ": " << m_last_result << "\n";
            statistics st;
            collect_statistics(st);
            std::cout << st << "\n";

            rec->m_answer = m_last_result;
            rec->m_result = (m_last_result == l_undef) ? test_result::resource_out : test_result::ok;
        }

        void expect_unsat() {
            auto* rec = m_last_finished;
            SASSERT(rec);
            SASSERT_EQ(rec->m_expected, l_undef);
            SASSERT_EQ(rec->m_answer, m_last_result);
            rec->m_expected = l_false;
            if (rec->m_result == test_result::error)
                return;
            if (m_last_result != l_false && m_last_result != l_undef) {
                rec->m_result = test_result::wrong_answer;
                LOG_H1("FAIL: " << m_name << ": expected UNSAT, got " << m_last_result << "!");
                if (!collect_test_records)
                    VERIFY(false);
            }
        }

        void expect_sat(std::vector<std::pair<dd::pdd, unsigned>> const& expected_assignment = {}) {
            auto* rec = m_last_finished;
            SASSERT(rec);
            SASSERT_EQ(rec->m_expected, l_undef);
            SASSERT_EQ(rec->m_answer, m_last_result);
            rec->m_expected = l_true;
            if (rec->m_result == test_result::error)
                return;
            if (m_last_result == l_true) {
                for (auto const& p : expected_assignment) {
                    auto const& v_pdd = p.first;
                    auto const expected_value = p.second;
                    SASSERT(v_pdd.is_monomial() && !v_pdd.is_val());
                    auto const v = v_pdd.var();
                    if (get_value(v) != expected_value) {
                        rec->m_result = test_result::wrong_model;
                        LOG_H1("FAIL: " << m_name << ": expected assignment v" << v << " := " << expected_value << ", got value " << get_value(v) << "!");
                        if (!collect_test_records)
                            VERIFY(false);
                    }
                }
            }
            else if (m_last_result == l_false) {
                rec->m_result = test_result::wrong_answer;
                LOG_H1("FAIL: " << m_name << ": expected SAT, got " << m_last_result << "!");
                if (!collect_test_records)
                    VERIFY(false);
            }
        }
    };

    template <typename Test, typename... Args>
    void run(Test tst, Args... args)
    {
        try {
            tst(args...);
        }
        catch(z3_exception const& e) {
            test_records.active_or_new_record()->set_error(with_default(e.msg(), "unknown z3_exception"));
            if (!collect_test_records)
                throw;
        }
        catch(std::exception const& e) {
            test_records.active_or_new_record()->set_error(with_default(e.what(), "unknown std::exception"));
            if (!collect_test_records)
                throw;
        }
        catch(...) {
            test_records.active_or_new_record()->set_error("unknown throwable");
            if (!collect_test_records)
                throw;
        }
    }

    #define RUN(tst) run([]() { tst; })

    class test_polysat {
    public:

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
            s.add_eq(4*a + 2);  // always false due to parity
            s.check();
            s.expect_unsat();
        }

        static void test_l4b() {
            scoped_solver s(__func__);
            auto x = s.var(s.add_var(32));
            auto y = s.var(s.add_var(32));
            s.add_eq(2*x + 4*y + 1);  // always false due to parity
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

        static void test_l6() {
            scoped_solver s(__func__);
            auto x = s.var(s.add_var(6));
            s.add_ule(29*x + 3, 29*x + 1);
            s.check();
            s.expect_sat();
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
        static void test_ineq_basic1(unsigned bw = 32) {
            scoped_solver s(__func__);
            auto u = s.var(s.add_var(bw));
            s.add_ule(u, 5);
            s.add_ule(5, u);
            s.check();
            s.expect_sat({{u, 5}});
        }

        // Unsatisfiable
        static void test_ineq_basic2(unsigned bw = 32) {
            scoped_solver s(__func__);
            auto u = s.var(s.add_var(bw));
            s.add_ult(u, 5);
            s.add_ule(5, u);
            s.check();
            s.expect_unsat();
        }

        // Solutions with u = v = w
        static void test_ineq_basic3(unsigned bw = 32) {
            scoped_solver s(__func__);
            auto u = s.var(s.add_var(bw));
            auto v = s.var(s.add_var(bw));
            auto w = s.var(s.add_var(bw));
            s.add_ule(u, v);
            s.add_ule(v, w);
            s.add_ule(w, u);
            s.check();
            s.expect_sat();
        }

        // Unsatisfiable
        static void test_ineq_basic4(unsigned bw = 32) {
            scoped_solver s(__func__);
            auto u = s.var(s.add_var(bw));
            auto v = s.var(s.add_var(bw));
            auto w = s.var(s.add_var(bw));
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

	    // -43 \/ 3 \/ 4
        //   -43: v3 + -1 != 0
        //   3: v3 == 0
        //   4: v3 <= v5
        static void test_clause_simplify1() {
            scoped_solver s(__func__);
            simplify_clause simp(s);
            clause_builder cb(s);
            auto u = s.var(s.add_var(4));
            auto v = s.var(s.add_var(4));
            cb.insert(s.eq(u));
            cb.insert(~s.eq(u - 1));
            cb.insert(s.ule(u, v));
            auto cl = cb.build();
            simp.apply(*cl);
            std::cout << *cl << "\n";
            SASSERT(cl->size() == 2);
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
            scoped_solver s(concat(__func__, "(", base_bw, ")"));

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
        static void test_fixed_point_arith_mul_div_inverse(unsigned base_bw = 5) {
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
            auto sf_val = div(max_int_const, rational(3));
            auto sf = s.var(s.add_var(bw));
            s.add_eq(sf - sf_val);

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
            // s.expect_unsat();
            s.pop();

            s.push();
            s.add_ult(quot3 + em, a);
            s.check();
            // s.expect_unsat();
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

        // xy < xz and !Omega(x*y) => y < z
        static void test_ineq_axiom1(unsigned bw = 32, std::optional<unsigned> perm = std::nullopt) {
            if (perm) {
                scoped_solver s(concat(__func__, " bw=", bw, " perm=", *perm));
                auto const bound = rational::power_of_two(bw/2);
                auto x = s.var(s.add_var(bw));
                auto y = s.var(s.add_var(bw));
                auto z = s.var(s.add_var(bw));
                permute_args(*perm, x, y, z);
                s.add_ult(x * y, x * z);
                s.add_ule(z, y);
                s.add_ult(x, bound);
                s.add_ult(y, bound);
                s.check();
                s.expect_unsat();
            }
            else {
                for (unsigned i = 0; i < 6; ++i) {
                    test_ineq_axiom1(bw, i);
                }
            }
        }

        static void test_ineq_non_axiom1(unsigned bw, unsigned i) {
            auto const bound = rational::power_of_two(bw - 1);
            scoped_solver s(std::string(__func__) + " perm=" + std::to_string(i));
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

        static void test_ineq_non_axiom1(unsigned bw = 32) {
            for (unsigned i = 0; i < 6; ++i)
                test_ineq_non_axiom1(32, i);
        }

        // xy <= xz & !Omega(x*y) => y <= z or x = 0
        static void test_ineq_axiom2(unsigned bw = 32) {
            auto const bound = rational::power_of_two(bw/2);
            for (unsigned i = 0; i < 6; ++i) {
                scoped_solver s(std::string(__func__) + " perm=" + std::to_string(i));
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
                scoped_solver s(std::string(__func__) + " perm=" + std::to_string(i));
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
                scoped_solver s(std::string(__func__) + " perm=" + std::to_string(i));
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
            scoped_solver s(std::string(__func__) + " perm=" + std::to_string(i));
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

        // a < xy & x <= b & !Omega(b*y) => a < b*y
        static void test_ineq_axiom5(unsigned bw, unsigned i) {
            auto const bound = rational::power_of_two(bw/2);
            scoped_solver s(std::string(__func__) + " perm=" + std::to_string(i));
            auto x = s.var(s.add_var(bw));
            auto y = s.var(s.add_var(bw));
            auto a = s.var(s.add_var(bw));
            auto b = s.var(s.add_var(bw));
            permute_args(i, x, y, a, b);
            s.add_ult(a, x * y);
            s.add_ule(x, b);
            s.add_ult(b, bound);
            s.add_ult(y, bound);
            s.add_ule(b * y, a);
            s.check();
            s.expect_unsat();
        }

        static void test_ineq_axiom5(unsigned bw = 32) {
            for (unsigned i = 0; i < 24; ++i)
                test_ineq_axiom5(bw, i);
        }

        // a <= xy & x <= b & !Omega(b*y) => a <= b*y
        static void test_ineq_axiom6(unsigned bw, unsigned i) {
            auto const bound = rational::power_of_two(bw/2);
            scoped_solver s(std::string(__func__) + " perm=" + std::to_string(i));
            auto x = s.var(s.add_var(bw));
            auto y = s.var(s.add_var(bw));
            auto a = s.var(s.add_var(bw));
            auto b = s.var(s.add_var(bw));
            permute_args(i, x, y, a, b);
            s.add_ule(a, x * y);
            s.add_ule(x, b);
            s.add_ult(b, bound);
            s.add_ult(y, bound);
            s.add_ult(b * y, a);
            s.check();
            s.expect_unsat();
        }

        static void test_ineq_axiom6(unsigned bw = 32) {
            for (unsigned i = 0; i < 24; ++i)
                test_ineq_axiom6(bw, i);
        }

        static void test_quot_rem_incomplete() {
            unsigned bw = 4;
            scoped_solver s(__func__);
            s.set_max_conflicts(5);
            auto quot = s.var(s.add_var(bw));
            auto rem = s.var(s.add_var(bw));
            auto a = s.value(rational(2), bw);
            auto b = s.value(rational(5), bw);
            // Incomplete axiomatization of quotient/remainder.
            // quot_rem(2, 5) should have single solution (0, 2),
            // but with the usual axioms we also get (3, 3).
            s.add_eq(b * quot + rem - a);
            s.add_umul_noovfl(b, quot);
            s.add_ult(rem, b);
            // To force a solution that's different from the correct one.
            s.add_diseq(quot - 0);
            s.check();
            s.expect_sat({{quot, 3}, {rem, 3}});
        }

        static void test_quot_rem_fixed() {
            unsigned bw = 4;
            scoped_solver s(__func__);
            s.set_max_conflicts(5);
            auto a = s.value(rational(2), bw);
            auto b = s.value(rational(5), bw);
            auto [quot, rem] = s.quot_rem(a, b);
            s.add_diseq(quot - 0);  // to force a solution that's different from the correct one
            s.check();
            s.expect_unsat();
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
            s.add_umul_noovfl(quot, y);
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
            s.add_umul_noovfl(q, idx);
            s.add_ult(first, second);
            s.add_diseq(idx, 0);
            s.add_ule(second - first, q);
            s.add_umul_noovfl(second  - first, idx);
            s.check();
        }

        static void test_band1(unsigned bw = 32) {
            scoped_solver s(concat(__func__, " bw=", bw));
            auto p = s.var(s.add_var(bw));
            auto q = s.var(s.add_var(bw));
            s.add_diseq(p - s.band(p, q));
            s.add_diseq(p - q);
            s.check();
            s.expect_sat();
        }

        static void test_band2(unsigned bw = 32) {
            scoped_solver s(concat(__func__, " bw=", bw));
            auto p = s.var(s.add_var(bw));
            auto q = s.var(s.add_var(bw));
            s.add_ult(p, s.band(p, q));
            s.check();
            s.expect_unsat();
        }

        static void test_band3(unsigned bw = 32) {
            scoped_solver s(concat(__func__, " bw=", bw));
            auto p = s.var(s.add_var(bw));
            auto q = s.var(s.add_var(bw));
            s.add_ult(q, s.band(p, q));
            s.check();
            s.expect_unsat();
        }

        static void test_band4(unsigned bw = 32) {
            scoped_solver s(concat(__func__, " bw=", bw));
            auto p = s.var(s.add_var(bw));
            auto q = s.var(s.add_var(bw));
            s.add_ule(p, s.band(p, q));
            s.check();
            s.expect_sat();
        }

        static void test_band5(unsigned bw = 32) {
            scoped_solver s(concat(__func__, " bw=", bw));
            auto p = s.var(s.add_var(bw));
            auto q = s.var(s.add_var(bw));
            s.add_ule(p, s.band(p, q));
            s.add_diseq(p - s.band(p, q));
            s.check();
            s.expect_unsat();
        }

        static void test_fi_zero() {
            scoped_solver s(__func__);
            auto a = s.var(s.add_var(256));
            auto b = s.var(s.add_var(256));
            auto c = s.var(s.add_var(256));
            s.add_eq(a, 0);
            s.add_eq(c, 0);  // add c to prevent simplification by leading coefficient
            s.add_eq(4*a - 123456789*b + c);
            s.check();
            s.expect_sat({{a, 0}, {b, 0}});
        }

        static void test_fi_nonzero() {
            scoped_solver s(__func__);
            auto a = s.var(s.add_var(5));
            auto b = s.var(s.add_var(5));
            s.add_ult(b*b*b, 7*a + 6);
            s.check();
        }

        static void test_fi_nonmax() {
            scoped_solver s(__func__);
            auto a = s.var(s.add_var(5));
            auto b = s.var(s.add_var(5));
            s.add_ult(a + 8, b*b*b);
            s.check();
        }

        static void test_fi_disequal_mild() {
            {
                // small version
                scoped_solver s(__func__);
                auto a = s.var(s.add_var(6));
                auto b = s.var(s.add_var(6));
                // v > -3*v
                s.add_eq(a - 3);
                s.add_ult(-a*b, b);
                s.check();
            }
            {
                // large version
                scoped_solver s(__func__);
                auto a = s.var(s.add_var(256));
                auto b = s.var(s.add_var(256));
                // v > -100*v
                s.add_eq(a - 100);
                s.add_ult(-a*b, b);
                s.check();
            }
        }

        static void test_pop_conflict() {
            scoped_solver s(__func__);
            auto a = s.var(s.add_var(32));
            s.add_ule(a, 5);
            s.push();
            s.add_ult(5, a);
            s.push();
            s.add_ule(1, a);
            s.check();
            s.expect_unsat();
            s.pop();
            s.check();
            s.expect_unsat();
            s.pop();
            s.add_ult(4, a);
            // s.add_ule(100, a);
            s.check();
            s.expect_sat({{a, 5}});
        }

    };  // class test_polysat


    // Here we deal with linear constraints of the form
    //
    //     a1*x + b1 <= a2*x + b2   (mod m = 2^bw)
    //
    // and their negation.

    class test_fi {

        static bool is_violated(rational const& a1, rational const& b1, rational const& a2, rational const& b2,
                                rational const& val, bool negated, rational const& m) {
            rational const lhs = (a1*val + b1) % m;
            rational const rhs = (a2*val + b2) % m;
            if (negated)
                return lhs <= rhs;
            else
                return lhs > rhs;
        }

        // Returns true if the input is valid and the test did useful work
        static bool check_one(rational const& a1, rational const& b1, rational const& a2, rational const& b2, rational const& val, bool negated, unsigned bw) {
            rational const m = rational::power_of_two(bw);
            if (a1.is_zero() && a2.is_zero())
                return false;
            if (!is_violated(a1, b1, a2, b2, val, negated, m))
                return false;

            scoped_solver s(__func__);
            auto x = s.var(s.add_var(bw));
            signed_constraint c = s.ule(a1*x + b1, a2*x + b2);
            if (negated)
                c.negate();
            viable& v = s.m_viable;
            v.intersect(x.var(), c);
            // Trigger forbidden interval refinement
            v.is_viable(x.var(), val);
            auto* e = v.m_units[x.var()];
            if (!e) {
                std::cout << "test_fi: no interval for a1=" << a1 << " b1=" << b1 << " a2=" << a2 << " b2=" << b2 << " val=" << val << " neg=" << negated << std::endl;
                // VERIFY(false);
                return false;
            }
            VERIFY(e);
            auto* first = e;
            SASSERT(e->next() == e);  // the result is expected to be a single interval (although for this check it doesn't really matter if there's more...)
            do {
                rational const& lo = e->interval.lo_val();
                rational const& hi = e->interval.hi_val();
                for (rational x = lo; x != hi; x = (x + 1) % m) {
                    // LOG("lo=" << lo << " hi=" << hi << " x=" << x);
                    if (!is_violated(a1, b1, a2, b2, val, negated, m)) {
                        std::cout << "test_fi: unsound for a1=" << a1 << " b1=" << b1 << " a2=" << a2 << " b2=" << b2 << " val=" << val << " neg=" << negated << std::endl;
                        VERIFY(false);
                    }
                }
                e = e->next();
            }
            while (e != first);
            return true;
        }

    public:
        static void exhaustive(unsigned bw = 0) {
            if (bw == 0) {
                exhaustive(1);
                exhaustive(2);
                exhaustive(3);
                exhaustive(4);
                exhaustive(5);
            }
            else {
                std::cout << "test_fi::exhaustive for bw=" << bw << std::endl;
                rational const m = rational::power_of_two(bw);
                for (rational p(1); p < m; ++p) {
                    for (rational r(1); r < m; ++r) {
                        // TODO: remove this condition to test the cases other than disequal_lin! (also start p,q from 0)
                        if (p == r)
                            continue;
                        for (rational q(0); q < m; ++q)
                            for (rational s(0); s < m; ++s)
                                for (rational v(0); v < m; ++v)
                                    for (bool negated : {true, false})
                                        check_one(p, q, r, s, v, negated, bw);
                    }
                }
            }
        }

        static void randomized(unsigned num_rounds = 100000, unsigned bw = 16) {
            std::cout << "test_fi::randomized for bw=" << bw << " (" << num_rounds << " rounds)" << std::endl;
            rational const m = rational::power_of_two(bw);
            VERIFY(bw <= 32 && "random_gen generates 32-bit numbers");
            random_gen rng;
            unsigned round = num_rounds;
            while (round) {
                // rational a1 = (rational(rng()) % (m - 1)) + 1;
                // rational a2 = (rational(rng()) % (m - 1)) + 1;
                rational a1 = rational(rng()) % m;
                rational a2 = rational(rng()) % m;
                if (a1.is_zero() || a2.is_zero() || a1 == a2)
                    continue;
                rational b1 = rational(rng()) % m;
                rational b2 = rational(rng()) % m;
                rational val = rational(rng()) % m;
                bool useful =
                    check_one(a1, b1, a2, b2, val, true, bw)
                    || check_one(a1, b1, a2, b2, val, false, bw);
                if (useful)
                    round--;
            }
        }

    };  // class test_fi

}  // namespace polysat


static void STD_CALL polysat_on_ctrl_c(int) {
    signal(SIGINT, SIG_DFL);
    using namespace polysat;
    test_records.display(std::cout);
    raise(SIGINT);
}

void tst_polysat() {
    using namespace polysat;

#if 0  // Enable this block to run a single unit test with detailed output.
    collect_test_records = false;
    // test_polysat::test_ineq_axiom1(32, 1);
    // test_polysat::test_pop_conflict();
    // test_polysat::test_l2();
    // test_polysat::test_ineq1();
    // test_polysat::test_quot_rem();
    // test_polysat::test_ineq_non_axiom1(32, 3);
    // test_polysat::test_monot_bounds_full();
    // test_polysat::test_band2();
    // test_polysat::test_quot_rem_incomplete();
    // test_polysat::test_monot();
    // test_polysat::test_fixed_point_arith_div_mul_inverse();
    return;
#endif

    collect_test_records = true;

    if (collect_test_records) {
        signal(SIGINT, polysat_on_ctrl_c);
        set_default_debug_action(debug_action::throw_exception);
        set_log_enabled(false);
    }

    RUN(test_polysat::test_clause_simplify1());

    RUN(test_polysat::test_add_conflicts());
    RUN(test_polysat::test_wlist());
    RUN(test_polysat::test_cjust());
    // RUN(test_polysat::test_subst());
    // RUN(test_polysat::test_subst_signed());
    RUN(test_polysat::test_pop_conflict());

    RUN(test_polysat::test_l1());
    RUN(test_polysat::test_l2());
    RUN(test_polysat::test_l3());
    RUN(test_polysat::test_l4());
    RUN(test_polysat::test_l4b());
    RUN(test_polysat::test_l5());
    RUN(test_polysat::test_l6());

    RUN(test_polysat::test_p1());
    RUN(test_polysat::test_p2());
    RUN(test_polysat::test_p3());

    RUN(test_polysat::test_ineq_basic1());
    RUN(test_polysat::test_ineq_basic2());
    RUN(test_polysat::test_ineq_basic3());
    RUN(test_polysat::test_ineq_basic4());
    RUN(test_polysat::test_ineq_basic5());
    RUN(test_polysat::test_ineq_basic6());

    RUN(test_polysat::test_var_minimize()); // works but var_minimize isn't used (UNSAT before lemma is created)

    RUN(test_polysat::test_ineq1());
    RUN(test_polysat::test_ineq2());
    RUN(test_polysat::test_monot());
    RUN(test_polysat::test_monot_bounds(2));
    RUN(test_polysat::test_monot_bounds(8));
    RUN(test_polysat::test_monot_bounds());
    RUN(test_polysat::test_monot_bounds_full());
    RUN(test_polysat::test_monot_bounds_simple(8));
    RUN(test_polysat::test_fixed_point_arith_mul_div_inverse());
    RUN(test_polysat::test_fixed_point_arith_div_mul_inverse());

    RUN(test_polysat::test_ineq_axiom1());
    RUN(test_polysat::test_ineq_axiom2());
    RUN(test_polysat::test_ineq_axiom3());
    RUN(test_polysat::test_ineq_axiom4());
    RUN(test_polysat::test_ineq_axiom5());
    RUN(test_polysat::test_ineq_axiom6());
    RUN(test_polysat::test_ineq_non_axiom1());
    RUN(test_polysat::test_ineq_non_axiom4());

    RUN(test_polysat::test_quot_rem_incomplete());
    RUN(test_polysat::test_quot_rem_fixed());
    RUN(test_polysat::test_band1());
    RUN(test_polysat::test_band2());
    RUN(test_polysat::test_band3());
    RUN(test_polysat::test_band4());
    RUN(test_polysat::test_band5());
    RUN(test_polysat::test_quot_rem());

    RUN(test_polysat::test_fi_zero());
    RUN(test_polysat::test_fi_nonzero());
    RUN(test_polysat::test_fi_nonmax());
    RUN(test_polysat::test_fi_disequal_mild());

    // test_fi::exhaustive();
    // test_fi::randomized();

    if (collect_test_records)
        test_records.display(std::cout);
}
