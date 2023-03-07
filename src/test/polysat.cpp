#include "math/polysat/log.h"
#include "math/polysat/solver.h"
#include "math/polysat/variable_elimination.h"
#include "ast/ast.h"
#include "parsers/smt2/smt2parser.h"
#include "util/util.h"
#include <vector>
#include <signal.h>

// TODO: collect stats on how often each inference rule is used, so we can see which ones are useful or if any are useless/untested

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
        out << "\n\n\nTest Results:\n\n";

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
            r->display(out, static_cast<unsigned>(max_name_len));
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
        out << "\n" << n_total << " tests, " << (n_sat + n_unsat) << " ok (" << n_sat << " sat, " << n_unsat << " unsat)";
        if (n_wrong)
            out << ", " << color_red() << n_wrong << " wrong!" << color_reset();
        if (n_error)
            out << ", " << color_red() << n_error << " error" << color_reset();
        out << "\n" << std::endl;
    }

    test_record_manager test_records;
    bool collect_test_records = true;
    unsigned test_max_conflicts = 10;

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
            if (collect_test_records)
                std::cout << m_name << std::flush;
            else {
                std::cout << std::string(78, '#') << "\n\n";
                std::cout << "START: " << m_name << "\n";
            }
            set_max_conflicts(test_max_conflicts);

            test_records.begin_batch(name);
        }

        ~scoped_solver() {
            test_records.end_batch();
            if (collect_test_records)
                std::cout << "\n";
        }

        void set_max_conflicts(unsigned c) {
            params_ref p;
            p.set_uint("max_conflicts", c);
            updt_params(p);
        }

        void check() {
            if (collect_test_records)
                std::cout << " ..." << std::flush;
            auto* rec = test_records.active_or_new_record();
            m_last_finished = nullptr;
            SASSERT(rec->m_answer == l_undef);
            SASSERT(rec->m_expected == l_undef);
            SASSERT(rec->m_result == test_result::undefined);
            SASSERT(rec->m_error_message == "");
            SASSERT(!rec->m_finished);
            {
                rec->m_start = test_record::clock_t::now();
                on_scope_exit end_timer([rec]() {
                    rec->m_end = test_record::clock_t::now();
                });
                m_last_result = check_sat();
            }
            rec->m_finished = true;
            m_last_finished = rec;
            if (collect_test_records)
                std::cout << " " << m_last_result << std::flush;
            else
                std::cout << "DONE:  " << m_name << ": " << m_last_result << "\n";
            statistics st;
            collect_statistics(st);
            if (!collect_test_records)
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
                    SASSERT(v_pdd.is_var());
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

    std::string run_filter;

    template <typename Test, typename... Args>
    void run(char const* name, Test tst, Args... args)
    {
        if (!run_filter.empty()) {
            std::string sname = name;
            if (sname.find(run_filter) == std::string::npos)
                return;
        }
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

    #define RUN(tst) run(#tst, []() { tst; })

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
            VERIFY_EQ(cl->size(), 2);
        }

        // p <= q
        // p == q   (should be removed)
        static void test_clause_simplify2() {
            scoped_solver s(__func__);
            simplify_clause simp(s);
            clause_builder cb(s);
            auto u = s.var(s.add_var(32));
            auto v = s.var(s.add_var(32));
            auto w = s.var(s.add_var(32));
            auto p = 2*u*v;
            auto q = 7*v*w;
            cb.insert(s.ule(p, q));
            cb.insert(s.eq(p, q));
            auto cl = cb.build();
            simp.apply(*cl);
            VERIFY_EQ(cl->size(), 1);
            VERIFY_EQ((*cl)[0], s.ule(p, q).blit());
        }

        // p < q
        // p == q
        // should be merged into p <= q
        static void test_clause_simplify3() {
            scoped_solver s(__func__);
            simplify_clause simp(s);
            clause_builder cb(s);
            auto u = s.var(s.add_var(32));
            auto v = s.var(s.add_var(32));
            auto w = s.var(s.add_var(32));
            auto p = 2*u*v;
            auto q = 7*v*w;
            cb.insert(s.ult(p, q));
            cb.insert(s.eq(p, q));
            auto cl = cb.build();
            simp.apply(*cl);
            VERIFY_EQ(cl->size(), 1);
            VERIFY_EQ((*cl)[0], s.ule(p, q).blit());
        }

        // 2^1*x + 2^1 == 0 and 2^2*x == 0
        static void test_fi_quickcheck1() {
            scoped_solver s(__func__);
            auto x = s.var(s.add_var(3));
            signed_constraint c1 = s.eq(x * 2 + 2, 0);
            signed_constraint c2 = s.eq(4 * x, 0);
            s.add_clause(c1, false);
            s.add_clause(c2, false);
            s.m_viable.intersect(x.var(), c1);
            s.m_viable.intersect(x.var(), c2);
            svector<lbool> fixed;
            vector<ptr_vector<viable::entry>> justifications;
            VERIFY(!s.m_viable.collect_bit_information(x.var(), false, fixed, justifications));
        }
        
        // parity(x) >= 3 and bit_1(x)
        static void test_fi_quickcheck2() {
            scoped_solver s(__func__);
            auto x = s.var(s.add_var(4));
            signed_constraint c1 = s.parity_at_least(x, 3);
            signed_constraint c2 = s.bit(x, 1);
            s.add_clause(c1, false);
            s.add_clause(c2, false);
            s.m_viable.intersect(x.var(), c1);
            s.m_viable.intersect(x.var(), c2);
            svector<lbool> fixed;
            vector<ptr_vector<viable::entry>> justifications;
            VERIFY(!s.m_viable.collect_bit_information(x.var(), false, fixed, justifications));
        }

        // parity(x) >= 1 and bit_1(x)
        static void test_fi_quickcheck3() {
            scoped_solver s(__func__);
            auto x = s.var(s.add_var(256));
            signed_constraint c1 = s.eq(rational::power_of_two(255) * x);
            signed_constraint c2 = s.ult(rational::power_of_two(255), -rational::power_of_two(254) * x);
            s.add_clause(c1, false);
            s.add_clause(c2, false);
            s.m_viable.intersect(x.var(), c1);
            s.m_viable.intersect(x.var(), c2);
            svector<lbool> fixed;
            vector<ptr_vector<viable::entry>> justifications;
            VERIFY(!s.m_viable.collect_bit_information(x.var(), false, fixed, justifications));
        }

        // 8 * x + 3 == 0 or 8 * x + 5 == 0 is unsat
        static void test_parity1() {
            scoped_solver s(__func__);
            auto x = s.var(s.add_var(8));
            auto y = s.var(s.add_var(8));
            auto z = s.var(s.add_var(8));
            s.add_clause({s.eq(x * y + z), s.eq(x * y + 5)}, false);
            s.add_eq(y, 8);
            s.add_eq(z, 3);
            s.check();
            s.expect_unsat();
        }

        // 8 * u * x + 3 == 0 or 8 * u * x + 5 == 0 is unsat
        static void test_parity1b() {
            scoped_solver s(__func__);
            auto u = s.var(s.add_var(8));
            auto x = s.var(s.add_var(8));
            auto y = s.var(s.add_var(8));
            auto z = s.var(s.add_var(8));
            s.add_clause({s.eq(u * x * y + z), s.eq(u * x * y + 5)}, false);
            s.add_eq(y, 8);
            s.add_eq(z, 3);
            s.check();
            s.expect_unsat();
        }

        // 8 * x + 2 == 0 or 8 * x + 4 == 0 is unsat
        static void test_parity2() {
            scoped_solver s(__func__);
            auto x = s.var(s.add_var(8));
            auto y = s.var(s.add_var(8));
            s.add_clause({ s.eq(x * y + 2), s.eq(x * y + 4) }, false);
            s.add_eq(y, 8);
            s.check();
            s.expect_unsat();
        }

        // (x * y + 4 == 0 or x * y + 2 == 0) & 16 divides y is unsat
        static void test_parity3() {
            scoped_solver s(__func__);
            auto x = s.var(s.add_var(8));
            auto y = s.var(s.add_var(8));
            s.add_clause({ s.eq(x * y + 2), s.eq(x * y + 4) }, false);
            s.add_eq(16 * y);
            s.check();
            s.expect_unsat();
        }

        // x*y + 2 == 0
        // parity(y) >= 4  ||  parity(y) >= 8
        static void test_parity4(unsigned bw = 8) {
            scoped_solver s(concat(__func__, " bw=", bw));
            pdd x = s.var(s.add_var(bw));
            pdd y = s.var(s.add_var(bw));
            s.add_eq(x * y + 2);
            s.add_clause({ s.parity_at_least(y, 4), s.parity_at_least(y, 8) }, false);
            s.check();
            s.expect_unsat();
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
         * n*q1 = a - b                         3*1 == 3 - 0
         * n*q2 + r2 = c*a - c*b                3*0 + 1 == 11*3 - 11*0 (= 33 = 1 mod 32)
         * n > r2 > 0                           3 > 1 > 0
         * It is actually satisfiable, e.g.: { {n, 3}, {q1, 1}, {a, 3}, {b, 0}, {c, 11}, {q2, 0}, {r2, 1} } (not a unique solution)
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
            s.expect_sat();
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

        static void expect_lemma_cnt(conflict& cfl, unsigned cnt) {
            auto lemmas = cfl.lemmas();
            if (lemmas.size() == cnt)
                return;
            LOG_H1("FAIL: Expected " << cnt << " learned lemmas;  got " << lemmas.size() << "!");
            SASSERT(false);
            if (!collect_test_records)
                VERIFY(false);
        }

        static void expect_lemma(solver& s, conflict& cfl, signed_constraint c1) {
            LOG_H1("Looking for constraint: " << c1);
            auto lemmas = cfl.lemmas();

            for (auto& lemma : lemmas) {
                for (unsigned i = 0; i < lemma->size(); i++) {
                    if (s.lit2cnstr(lemma->operator[](i)) == c1)
                        return;
                    LOG_H1("Found different constraint " << s.lit2cnstr(lemma->operator[](i)));
                }
            }
            LOG_H1("FAIL: Lemma " << c1 << " not deduced!");
            SASSERT(false);
            if (!collect_test_records)
                VERIFY(false);
        }

        static void test_elim1(unsigned bw = 32) {
            scoped_solver s(__func__);
            free_variable_elimination elim(s);
            auto x = s.var(s.add_var(bw));
            auto y = s.var(s.add_var(bw));
            auto c1 = s.eq(7 * x, 3);
            auto c2 = s.ule(x - y, 5);

            conflict cfl(s);
            s.assign_eh(c1, dependency(0));
            cfl.insert(c1);

            s.assign_eh(c2, dependency(0));
            cfl.insert(c2);
            elim.find_lemma(cfl);

            rational res;
            rational(7).mult_inverse(bw, res);

            expect_lemma_cnt(cfl, 1);
            expect_lemma(s, cfl, s.ule(s.sz2pdd(bw).mk_val(res * 3) - y, 5));
        }

        static void test_elim2(unsigned bw = 32) {
            scoped_solver s(__func__);
            free_variable_elimination elim(s);
            auto x = s.var(s.add_var(bw));
            auto y = s.var(s.add_var(bw));
            auto c1 = s.eq(x * x, x * 3);
            auto c2 = s.ule(x + y, 5);

            conflict cfl(s);
            s.assign_eh(c1, dependency(0));
            cfl.insert(c1);

            s.assign_eh(c2, dependency(0));
            cfl.insert(c2);
            elim.find_lemma(cfl);

            expect_lemma_cnt(cfl, 0); // Non linear; should be skipped
        }

        static void test_elim3(unsigned bw = 32) {
            scoped_solver s(__func__);
            free_variable_elimination elim(s);
            auto x = s.var(s.add_var(bw));
            auto y = s.var(s.add_var(bw));
            auto c1 = s.eq(7 * x, 3);
            auto c2 = s.ule(x * x + y, 5);

            conflict cfl(s);
            s.assign_eh(c1, dependency(0));
            cfl.insert(c1);

            s.assign_eh(c2, dependency(0));
            cfl.insert(c2);
            elim.find_lemma(cfl);

            expect_lemma_cnt(cfl, 0); // also not linear; should be skipped
        }

        static void test_elim4(unsigned bw = 32) {
            scoped_solver s(__func__);
            free_variable_elimination elim(s);
            auto x = s.var(s.add_var(bw));
            auto y = s.var(s.add_var(bw));
            auto c1 = s.eq(7 * x, 3);
            auto c2 = s.ule(y * x, 5 + x + y);

            conflict cfl(s);
            s.assign_eh(c1, dependency(0));
            cfl.insert(c1);

            s.assign_eh(c2, dependency(0));
            cfl.insert(c2);
            elim.find_lemma(cfl);

            expect_lemma_cnt(cfl, 1);
            expect_lemma(s, cfl, s.ule(5 * y, 10 + y));
        }

        static void test_elim5(unsigned bw = 32) {
            scoped_solver s(__func__);
            free_variable_elimination elim(s);
            auto x = s.var(s.add_var(bw));
            auto y = s.var(s.add_var(bw));
            auto z = s.var(s.add_var(bw));
            auto c1 = s.eq(x * 7 + x * y, 3);
            auto c2 = s.ule(y * x * z, 2);

            conflict cfl(s);
            s.assign_eh(c1, dependency(0));
            cfl.insert(c1);

            s.assign_eh(c2, dependency(0));
            cfl.insert(c2);
            elim.find_lemma(cfl);

            expect_lemma_cnt(cfl, 1); // Eliminating "x" fails because there is no assignment for "y"; eliminating "y" works
            expect_lemma(s, cfl, s.ule(3 * z - 7 * x * z, 2));

            s.assign_core(y.var(), rational(2), justification::propagation(0));

            conflict cfl2(s);
            cfl2.insert(c1);
            cfl2.insert_vars(c1);
            cfl2.insert(c2);
            cfl2.insert_vars(c2);
            elim.find_lemma(cfl2);

            expect_lemma_cnt(cfl2, 2); // Now it uses the assignment
            expect_lemma(s, cfl2, s.ule(3 * z - 7 * x * z, 2));
            expect_lemma(s, cfl2, s.ule(6 * z, 2));
        }

        static void test_elim6(unsigned bw = 32) {
            scoped_solver s(__func__);
            free_variable_elimination elim(s);
            auto x = s.var(s.add_var(bw));
            auto y = s.var(s.add_var(bw));
            auto z = s.var(s.add_var(bw));
            auto c1 = s.eq(2 * x, z);
            auto c2 = s.ule(4 * x, y);

            conflict cfl(s);
            s.assign_eh(c1, dependency(0));
            cfl.insert(c1);

            s.assign_eh(c2, dependency(0));
            cfl.insert(c2);
            elim.find_lemma(cfl);

            expect_lemma_cnt(cfl, 1); // We have to multiply by 2 so this is an over-approximation (or we would increase bit-width by 1)
            expect_lemma(s, cfl, s.ule(2 * z, y));


            auto c3 = s.eq(4 * x, z);
            auto c4 = s.ule(2 * x, y);

            conflict cfl2(s);
            s.assign_eh(c3, dependency(0));
            cfl2.insert(c3);

            s.assign_eh(c4, dependency(0));
            cfl2.insert(c4);
            elim.find_lemma(cfl2);

            expect_lemma_cnt(cfl2, 0); // This does not work because of polarity
        }

        static void test_elim7(unsigned bw = 32) {
            scoped_solver s(__func__);
            free_variable_elimination elim(s);
            auto x = s.var(s.add_var(bw));
            auto y = s.var(s.add_var(bw));
            auto z = s.var(s.add_var(bw));
            auto c1 = s.eq(x * y, 3);
            auto c2 = s.ule(z * x, 2);

            conflict cfl(s);
            s.assign_eh(c1, dependency(0));
            cfl.insert(c1);

            s.assign_eh(c2, dependency(0));
            cfl.insert(c2);
            elim.find_lemma(cfl);

            expect_lemma_cnt(cfl, 1); // Should introduce polarity constraints
            // TODO: Check if this lemma is really correct
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
            scoped_solver s(concat(__func__, " bw=", bw, " perm=", i));
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
                scoped_solver s(concat(__func__, " bw=", bw, " perm=", i));
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
        static void test_ineq_axiom3(unsigned bw, unsigned i) {
            auto const bound = rational::power_of_two(bw/2);
            scoped_solver s(concat(__func__, " bw=", bw, " perm=", i));
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

        static void test_ineq_axiom3(unsigned bw = 32) {
            for (unsigned i = 0; i < 24; ++i)
                test_ineq_axiom3(bw, i);
        }

        // x*y <= b & a <= x & !Omega(x*y) => a*y <= b
        static void test_ineq_axiom4(unsigned bw = 32, unsigned i = 0) {
            auto const bound = rational::power_of_two(bw/2);
            for (; i < 24; ++i) {
                scoped_solver s(concat(__func__, " bw=", bw, " perm=", i));
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
            scoped_solver s(concat(__func__, " bw=", bw, " perm=", i));
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
            scoped_solver s(concat(__func__, " bw=", bw, " perm=", i));
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
            scoped_solver s(concat(__func__, " bw=", bw, " perm=", i));
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
            auto a = s.value(rational(2), bw);
            auto b = s.value(rational(5), bw);
            auto [quot, rem] = s.quot_rem(a, b);
            s.add_diseq(quot - 0);  // to force a solution that's different from the correct one
            s.check();
            s.expect_unsat();
        }

        static void test_quot_rem(unsigned bw = 32) {
            scoped_solver s(__func__);
            auto a = s.var(s.add_var(bw));
            auto quot = s.var(s.add_var(bw));
            auto rem = s.var(s.add_var(bw));
            auto x = a * 123;
            auto y = 123;
            // quot = udiv(a*123, 123)
            s.add_eq(x, quot * y + rem);  // 123*a = q*123 + r
            s.add_diseq(a, quot);         // a != quot
            s.add_umul_noovfl(quot, y);   // 123*quot < 2^K
            s.add_ult(rem, x);            // r < 123*a  ???
            s.check();
            s.expect_sat();  // dubious
        }

        static void test_quot_rem2(unsigned bw = 32) {
            scoped_solver s(__func__);
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

        /**
         * p <= p & q
         * p != p & q
         * is unsatisfiable.
         */
        static void test_band5(unsigned bw = 32) {
            scoped_solver s(concat(__func__, " bw=", bw));
            auto p = s.var(s.add_var(bw));
            auto q = s.var(s.add_var(bw));
            s.add_ule(p, s.band(p, q));
            s.add_diseq(p, s.band(p, q));
            // Immediate solution with clause: p <= r /\ r <= p  ==>  p = r
            // s.add_clause({ ~s.ule(p, s.band(p, q)), ~s.ule(s.band(p, q), p), s.eq(p, s.band(p, q)) }, true);
            s.check();
            s.expect_unsat();
        }

        /** Like test_band5, but represent disequality as clause of less-than constraints */
        static void test_band5_clause(unsigned bw = 32) {
            scoped_solver s(concat(__func__, " bw=", bw));
            auto p = s.var(s.add_var(bw));
            auto q = s.var(s.add_var(bw));
            s.add_ule(p, s.band(p, q));
            // Rewrite p - q > 0  -->  p < q || q < p
            s.add_clause({ s.ult(p, s.band(p, q)), s.ult(s.band(p, q), p) }, false);
            s.check();
            s.expect_unsat();
        }
        
        static void test_band6(unsigned bw = 32) {
            scoped_solver s(concat(__func__, " bw=", bw));
            auto a = s.var(s.add_var(bw));
            auto x = s.var(s.add_var(bw));
            auto y = s.var(s.add_var(bw));
            
            signed_constraint and1 = s.eq(a, s.band(x, x.manager().mk_val(rational::power_of_two((bw + 1) / 2) - 1)));
            signed_constraint and2 = s.eq(a, s.band(x, x.manager().mk_val((rational::power_of_two((bw + 1) / 2) - 1) * rational::power_of_two(bw / 2))));
            s.add_clause(and1, false);
            s.add_clause(and2, false);
            s.add_clause(~s.eq(a, 0), false);
            
            s.check();
            s.expect_unsat();
        }

        static void test_band6_complex_term(unsigned bw = 32) {
            scoped_solver s(concat(__func__, " bw=", bw));
            auto a = s.var(s.add_var(bw));
            auto x = s.var(s.add_var(bw));
            auto y = s.var(s.add_var(bw));
            
            signed_constraint and1 = s.eq(a, s.band(x * y, x.manager().mk_val(rational::power_of_two((bw + 1) / 2) - 1)));
            signed_constraint and2 = s.eq(a, s.band(x * y, x.manager().mk_val((rational::power_of_two((bw + 1) / 2) - 1) * rational::power_of_two(bw / 2))));
            s.add_clause(and1, false);
            s.add_clause(and2, false);
            s.add_clause(~s.eq(a, 0), false);
            
            s.check();
            s.expect_unsat();
        }
        
        static void test_band6_eq_order(unsigned bw = 32) {
            scoped_solver s(concat(__func__, " bw=", bw));
            auto a = s.var(s.add_var(bw));
            auto x = s.var(s.add_var(bw));
            auto y = s.var(s.add_var(bw));
            
            signed_constraint and1 = s.eq(a, s.band(x, x.manager().mk_val(rational::power_of_two((bw + 1) / 2) - 1)));
            signed_constraint and2 = s.eq(a, s.band(x, y));
            s.add_clause(and1, false);
            s.add_clause(and2, false);
            s.add_clause(s.eq(x.manager().mk_val((rational::power_of_two((bw + 1) / 2) - 1) * rational::power_of_two(bw / 2)), y), false);
            s.add_clause(~s.eq(a, 0), false);
            
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

        /**
         * Motivated by weak forbidden intervals lemma in bench23:
         *      v66 > v41  &&  v67 == v66  ==>  v67 != 0
         *
         * Cause by omitting v41 from the symbolic bounds of v66 > v41.
         *
         * The stronger lemma should be:
         *      v66 > v41  &&  v67 == v66  ==>  v41 + 1 <= v67
         *
         * The conclusion could also be v67 > v41 (note that -1 > v41 follows from premise v66 > v41, so both conclusions are equivalent in this lemma).
         */
        static void test_bench23_fi_lemma() {
            scoped_solver s(__func__);
            auto x = s.var(s.add_var(256));  // v41
            auto y = s.var(s.add_var(256));  // v66
            auto z = s.var(s.add_var(256));  // v67
            s.add_ult(x, y);  // v66 > v41
            s.add_eq(y, z);   // v66 == v67
            s.add_eq(z, 0);   // v67 == 0
            s.check();
            s.expect_unsat();
        }

        static void test_bench6_viable() {
            scoped_solver s(__func__);
            rational coeff("12737129816104781496592808350955669863859698313220462044340334240870444260393");
            auto a = s.var(s.add_var(256));
            auto b = s.var(s.add_var(256));
            s.add_eq(4 * b - coeff * a);
            s.add_eq(b - 1);
            // s.add_eq(a - 100);
            s.check();
        }

        static void test_bench27_viable(const char* coeff) {
            scoped_solver s(__func__);
            rational a(coeff);
            rational b = rational::power_of_two(128) - 1;
            auto x = s.var(s.add_var(256));
            s.add_ult(0, x);
            s.add_ule(a * x + b, b);
            s.check();
        }

        static void test_bench27_viable1() {
            test_bench27_viable("2787252867449406954228501409473613420036128");  // 2^5 * a'
        }

        static void test_bench27_viable2() {
            test_bench27_viable("5574846017265734846920466193554658608284160");  // 2^9 * a'
        }

        // -1*v12 <= -1*v12 + v8 + v7*v1 + 2^128*v7 + 1
        // v8 := 0 v12 := 1 v4 := 0 v9 := 1 v17 := 0 v1 := 5574846017265734846920466193554658608283648
        //
        // Substitute assignment:
        //      -1 <= (5574846017265734846920466193554658608283648 + 2^128) * v7
        //             ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ == 2^142
        //      this is actually an equation
        //
        //      2^142 * v7 == -1, unsatisfiable due to parity
        static void test_bench27_viable3() {
            scoped_solver s(__func__);
            rational const a("5574846017265734846920466193554658608283648");
            rational const b = rational::power_of_two(128);
            auto const v1 = s.var(s.add_var(256));
            auto const v7 = s.var(s.add_var(256));
            auto const v8 = s.var(s.add_var(256));
            auto const v12 = s.var(s.add_var(256));
            s.add_ule(-v12, -v12 + v8 + v7*v1 + b*v7 + 1);
            s.add_eq(v8, 0);
            s.add_eq(v12, 1);
            s.add_eq(v1, a);
            s.check();
            s.expect_unsat();
        }

        // similar as test_bench27_viable3, but satisfiable (to test the other branch)
        static void test_bench27_viable3_sat() {
            scoped_solver s(__func__);
            rational const a("5574846017265734846920466193554658608283648");
            rational const b = rational::power_of_two(128) - 1;
            auto const v1 = s.var(s.add_var(256));
            auto const v7 = s.var(s.add_var(256));
            auto const v8 = s.var(s.add_var(256));
            auto const v12 = s.var(s.add_var(256));
            s.add_ule(-v12, -v12 + v8 + v7*v1 + b*v7 + 1);
            s.add_eq(v8, 0);
            s.add_eq(v12, 1);
            s.add_eq(v1, a);
            s.check();
            s.expect_sat();
        }

        static void test_bench13_mulovfl_ineq() {
            scoped_solver s(__func__);
            rational const a = rational::power_of_two(128) - 1;
            rational const b = rational::power_of_two(128) - 1;
            auto const x = s.var(s.add_var(256));
            auto const y = s.var(s.add_var(256));
            s.add_ule(-x - 1, x * y);
            s.add_ule(x, a);
            s.add_ule(y, b);
            s.add_umul_noovfl(x, y);
            s.check();
            //s.expect_unsat();
        }

    };  // class test_polysat

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
    test_max_conflicts = 50;
    //test_polysat::test_bench13_mulovfl_ineq();
    test_polysat::test_ineq_axiom3(32, 3);  // TODO: assertion
    // test_polysat::test_ineq_axiom6(32, 0);  // TODO: assertion
    // test_polysat::test_band5();  // TODO: assertion when clause simplification (merging p>q and p=q) is enabled
    // test_polysat::test_bench27_viable1();   // TODO: refinement
    // test_polysat::test_bench27_viable2();   // TODO: refinement
    return;
#endif

    // If non-empty, only run tests whose name contains the run_filter
    run_filter = "";
    test_max_conflicts = 20;

    collect_test_records = true;

    if (collect_test_records) {
        signal(SIGINT, polysat_on_ctrl_c);
        set_default_debug_action(debug_action::throw_exception);
        set_log_enabled(false);
    }

#if 0
    RUN(test_polysat::test_elim1());
    RUN(test_polysat::test_elim2());
    RUN(test_polysat::test_elim3());
    RUN(test_polysat::test_elim4());
    RUN(test_polysat::test_elim5());
    RUN(test_polysat::test_elim6());
    RUN(test_polysat::test_elim7());
#endif

    RUN(test_polysat::test_parity1());
    RUN(test_polysat::test_parity1b());
    RUN(test_polysat::test_parity2());
    RUN(test_polysat::test_parity3());
    RUN(test_polysat::test_parity4());

    RUN(test_polysat::test_clause_simplify1());
    RUN(test_polysat::test_clause_simplify2());
    // RUN(test_polysat::test_clause_simplify3());  // TODO: corresponding simplification is disabled at the moment
    RUN(test_polysat::test_bench23_fi_lemma());

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

    RUN(test_polysat::test_quot_rem_incomplete());
    RUN(test_polysat::test_quot_rem_fixed());
    RUN(test_polysat::test_quot_rem());
    RUN(test_polysat::test_quot_rem2());

    RUN(test_polysat::test_band1());
    RUN(test_polysat::test_band2());
    RUN(test_polysat::test_band3());
    RUN(test_polysat::test_band4());
    RUN(test_polysat::test_band5());
    RUN(test_polysat::test_band5_clause());

    RUN(test_polysat::test_fi_zero());
    RUN(test_polysat::test_fi_nonzero());
    RUN(test_polysat::test_fi_nonmax());
    RUN(test_polysat::test_fi_disequal_mild());
    RUN(test_polysat::test_bench6_viable());
    // RUN(test_polysat::test_bench27_viable1());  // stuck in refinement loop + fallback solver
    // RUN(test_polysat::test_bench27_viable2());  // stuck in refinement loop + fallback solver
    RUN(test_polysat::test_bench27_viable3());
    RUN(test_polysat::test_bench27_viable3_sat());

    RUN(test_polysat::test_ineq_axiom1());
    RUN(test_polysat::test_ineq_axiom2());
    RUN(test_polysat::test_ineq_axiom3());
    RUN(test_polysat::test_ineq_axiom4());
    RUN(test_polysat::test_ineq_axiom5());
    RUN(test_polysat::test_ineq_axiom6());
    RUN(test_polysat::test_ineq_non_axiom1());
    RUN(test_polysat::test_ineq_non_axiom4());
    
    RUN(test_polysat::test_fi_quickcheck1());
    RUN(test_polysat::test_fi_quickcheck2());
    RUN(test_polysat::test_fi_quickcheck3());

    if (collect_test_records)
        test_records.display(std::cout);
}
