#include "math/polysat/log.h"
#include "math/polysat/solver.h"
#include "math/polysat/viable.h"
#include "math/polysat/univariate/univariate_solver.h"

namespace polysat {

    class big_random_gen {
        unsigned m_bit_width;
        random_gen m_rng32_int;
        rational m_two_to_32 = rational::power_of_two(32);
        rational m_mod_value;

        // create 32-bit random number
        unsigned rng32_unsigned() {
            return static_cast<unsigned>(m_rng32_int());
        }

    public:
        big_random_gen(unsigned bit_width):
            m_bit_width(bit_width),
            m_mod_value(rational::power_of_two(bit_width)) {}

        rational operator()() {
            rational x(rng32_unsigned());
            unsigned bw = m_bit_width;
            while (bw > 32) {
                x = x * m_two_to_32 + rng32_unsigned();
                bw -= 32;
            }
            return mod(x, m_mod_value);
        }
    };

    struct solver_scopev {
        reslimit lim;
    };

    class scoped_solverv : public solver_scopev, public solver {
    public:
        scoped_solverv(): solver(lim) {}
        viable& v() { return m_viable; }
    };

    static void test1() {
        scoped_solverv s;
        auto xv = s.add_var(3);
        auto x = s.var(xv);
        viable& v = s.v();
        rational val;
        s.add_ule(x + 3, x + 5);
        VERIFY_EQ(s.check_sat(), l_true);
        std::cout << v << "\n";
        std::cout << "min " << v.min_viable(xv, val) << " " << val << "\n";
        std::cout << "max " << v.max_viable(xv, val) << " " << val << "\n";
        s.add_ule(x, 2);
        VERIFY_EQ(s.check_sat(), l_true);
        std::cout << v << "\n";
        s.add_ule(1, x);
        VERIFY_EQ(s.check_sat(), l_true);
        std::cout << v << "\n";
        std::cout << "min " << v.min_viable(xv, val) << " " << val << "\n";
        std::cout << "max " << v.max_viable(xv, val) << " " << val << "\n";
        s.add_ule(x, 3);
        VERIFY_EQ(s.check_sat(), l_true);
        std::cout << v << "\n";
        std::cout << v.find_viable(xv, val) << " " << val << "\n";
        std::cout << "min " << v.min_viable(xv, val) << " " << val << "\n";
        std::cout << "max " << v.max_viable(xv, val) << " " << val << "\n";
        s.add_ule(3, x);
        VERIFY_EQ(s.check_sat(), l_false);
        std::cout << v << "\n";
    }

    static void add_interval(scoped_solverv& s, pvar xv, pdd x, unsigned lo, unsigned len) {
        if (lo == 0)
            s.v().intersect(xv, s.ule(x, len - 1));
        else if (lo + len == 8)
            s.v().intersect(xv, s.ule(lo, x));
        else
            s.v().intersect(xv, ~s.ule(x - ((lo + len)%8), x - lo));
    }

    static bool member(unsigned i, unsigned lo, unsigned len) {
        return (lo <= i && i < lo + len) ||
            (lo + len >= 8 && i < ((lo + len) % 8));
    }

    static bool member(unsigned i, vector<std::pair<unsigned, unsigned>> const& intervals) {
        for (auto [lo, len] : intervals)
            if (!member(i, lo, len))
                return false;
        return true;
    }

    static void validate_intervals(scoped_solverv& s, pvar xv, vector<std::pair<unsigned, unsigned>> const& intervals) {
        for (unsigned i = 0; i < 8; ++i) {
            bool mem1 = member(i, intervals);
            bool mem2 = s.v().is_viable(xv, rational(i));
            if (mem1 != mem2)
                std::cout << "test violation: " << i << " member of all intervals " << mem1 << " viable: " << mem2 << "\n";
            VERIFY_EQ(mem1, mem2);
        }
    }

    static void test_intervals(vector<std::pair<unsigned, unsigned>> const& intervals) {
        scoped_solverv s;
        auto xv = s.add_var(3);
        auto x = s.var(xv);
        for (auto const& [lo, len] : intervals)
            add_interval(s, xv, x, lo, len);
        std::cout << intervals << "\n";
        //std::cout << s.v() << "\n";
        validate_intervals(s, xv, intervals);
    }

    static void test_intervals(unsigned count, vector<std::pair<unsigned, unsigned>>& intervals) {
        if (count == 0) {
            test_intervals(intervals);
            return;
        }
        for (unsigned lo1 = 0; lo1 < 8; ++lo1) {
            for (unsigned len1 = 1; len1 <= 8; ++len1) {
                intervals.push_back(std::make_pair(lo1, len1));
                test_intervals(count - 1, intervals);
                intervals.pop_back();
            }
        }
    }

    static void test2() {
        vector<std::pair<unsigned, unsigned>> intervals;
        test_intervals(3, intervals);
    }

    static void test_univariate() {
        std::cout << "\ntest_univariate\n";
        unsigned const bw = 32;
        rational const modulus = rational::power_of_two(bw);
        auto factory = mk_univariate_bitblast_factory();
        auto solver = (*factory)(bw);

        vector<rational> lhs;
        vector<rational> rhs;

        // c0: 2x+10 <= 123
        lhs.clear();
        lhs.push_back(rational(10));
        lhs.push_back(rational(2));
        rhs.clear();
        rhs.push_back(rational(123));
        solver->add_ule(lhs, rhs, false, 0);
        std::cout << "status: " << solver->check() << "\n";
        std::cout << "model: " << solver->model() << "\n";

        solver->push();

        // c1: x*x == 16
        lhs.clear();
        lhs.push_back(modulus - 16);
        lhs.push_back(rational(0));
        lhs.push_back(rational(1));
        rhs.clear();
        solver->add_ule(lhs, rhs, false, 1);
        std::cout << "status: " << solver->check() << "\n";
        std::cout << "model: " << solver->model() << "\n";

        solver->push();

        // c2: x <= 1000
        lhs.clear();
        lhs.push_back(rational(0));
        lhs.push_back(rational(1));
        rhs.clear();
        rhs.push_back(rational(1000));
        solver->add_ule(lhs, rhs, false, 2);
        // std::cout << *solver << '\n';
        std::cout << "status: " << solver->check() << "\n";
        std::cout << "model: " << solver->model() << "\n";

        solver->pop(2);

        // c3: umul_ovfl(2, x)
        lhs.clear();
        lhs.push_back(rational(2));
        rhs.clear();
        rhs.push_back(rational(0));
        rhs.push_back(rational(1));
        solver->add_umul_ovfl(lhs, rhs, false, 3);
        std::cout << "status: " << solver->check() << "\n";
        std::cout << "model: " << solver->model() << "\n";

        // c4: 1000 > x
        lhs.clear();
        lhs.push_back(rational(1000));
        rhs.clear();
        rhs.push_back(rational(0));
        rhs.push_back(rational(1));
        solver->add_ule(lhs, rhs, true, 4);
        std::cout << "status: " << solver->check() << "\n";
        std::cout << "core: " << solver->unsat_core() << "\n";
    }

    static void test_univariate_minmax() {
        std::cout << "\ntest_univariate_min\n";
        unsigned const bw = 32;
        auto factory = mk_univariate_bitblast_factory();
        auto solver = (*factory)(bw);

        vector<rational> lhs;
        vector<rational> rhs;
        rational min;
        rational max;

        solver->push();

        // c0: 123 <= 2x + 10
        lhs.clear();
        lhs.push_back(rational(123));
        rhs.clear();
        rhs.push_back(rational(10));
        rhs.push_back(rational(2));
        solver->add_ule(lhs, rhs, false, 0);
        std::cout << "status:   " << solver->check() << "\n";
        std::cout << "model:    " << solver->model() << "\n";

        VERIFY(solver->find_min(min));
        std::cout << "find_min: " << min << "\n";
        VERIFY(min == 57);  // 57*2 + 10 = 124;  56*2 + 10 = 122

        VERIFY(solver->find_max(max));
        std::cout << "find_max: " << max << "\n";
        solver->push();
        solver->add_ugt_const(max, false, 5);
        VERIFY(solver->check() == l_false);
        solver->pop(1);

        solver->push();

        // c1: 127 <= x
        lhs.clear();
        lhs.push_back(rational(127));
        rhs.clear();
        rhs.push_back(rational(0));
        rhs.push_back(rational(1));
        solver->add_ule(lhs, rhs, false, 1);
        std::cout << "status:   " << solver->check() << "\n";
        std::cout << "model:    " << solver->model() << "\n";

        VERIFY(solver->find_min(min));
        std::cout << "find_min: " << min << "\n";
        VERIFY(min == 127);

        VERIFY(solver->find_max(max));
        std::cout << "find_max: " << max << "\n";
        solver->add_ugt_const(max, false, 5);
        VERIFY(solver->check() == l_false);

        solver->pop(1);

        // c2: umul_ovfl(2, x)
        lhs.clear();
        lhs.push_back(rational(2));
        rhs.clear();
        rhs.push_back(rational(0));
        rhs.push_back(rational(1));
        solver->add_umul_ovfl(lhs, rhs, false, 2);
        std::cout << "status:   " << solver->check() << "\n";
        std::cout << "model:    " << solver->model() << "\n";

        VERIFY(solver->find_min(min));
        std::cout << "find_min: " << min << "\n";
        solver->push();
        solver->add_ult_const(min, false, 5);
        VERIFY(solver->check() == l_false);
        solver->pop(1);

        VERIFY(solver->find_max(max));
        std::cout << "find_max: " << max << "\n";
        solver->add_ugt_const(max, false, 5);
        VERIFY(solver->check() == l_false);

        solver->pop(1);

        // c3: umul_ovfl(2, x)
        lhs.clear();
        lhs.push_back(rational(2));
        rhs.clear();
        rhs.push_back(rational(0));
        rhs.push_back(rational(1));
        solver->add_umul_ovfl(lhs, rhs, false, 3);
        std::cout << "status:   " << solver->check() << "\n";
        std::cout << "model:    " << solver->model() << "\n";

        VERIFY(solver->find_min(min));
        std::cout << "find_min: " << min << "\n";
        solver->push();
        solver->add_ult_const(min, false, 5);
        VERIFY(solver->check() == l_false);
        solver->pop(1);

        VERIFY(solver->find_max(max));
        std::cout << "find_max: " << max << "\n";
        solver->add_ugt_const(max, false, 5);
        VERIFY(solver->check() == l_false);
    }


    class test_fi {

        static bool is_violated(rational const& a1, rational const& b1, rational const& a2, rational const& b2, rational const& val, bool negated, rational const& M) {
            rational const lhs = mod(a1*val + b1, M);
            rational const rhs = mod(a2*val + b2, M);
            if (negated)
                return lhs <= rhs;
            else
                return lhs > rhs;
        }

    public:
        static bool check_one(unsigned a1, unsigned b1, unsigned a2, unsigned b2, unsigned val, unsigned bw) {
            return check_one(rational(a1), rational(b1), rational(a2), rational(b2), rational(val), bw);
        }

        // Returns true if the input is valid and the test did useful work
        static bool check_one(rational const& a1, rational const& b1, rational const& a2, rational const& b2, rational const& val, unsigned bw) {
            // std::cout << "a1=" << a1 << " b1=" << b1 << " a2=" << a2 << " b2=" << b2 << " val=" << val << " bw=" << bw << "\n";
            rational const M = rational::power_of_two(bw);
            if (a1.is_zero() && a2.is_zero())
                return false;
            bool negated = false;
            if (!is_violated(a1, b1, a2, b2, val, negated, M))
                negated = !negated;
            SASSERT(is_violated(a1, b1, a2, b2, val, negated, M));

            scoped_solverv s;
            auto x = s.var(s.add_var(bw));
            signed_constraint c = s.ule(a1*x + b1, a2*x + b2);
            if (negated)
                c.negate();
            if (c.is_always_true() || c.is_always_false())
                return false;
            bool expect_optimality =
                // refine-equal-lin should now find the optimal interval in all cases
                a1.is_zero() || a2.is_zero() || a1 == a2;
            SASSERT_EQ(c.vars().size(), 1);
            viable& v = s.v();
            v.intersect(x.var(), c);
            // Trigger forbidden interval refinement
            v.is_viable(x.var(), val);
            auto* e = v.m_units[x.var()];
            if (!e) {
                std::cout << "test_fi: no interval for a1=" << a1 << " b1=" << b1 << " a2=" << a2 << " b2=" << b2 << " val=" << val << " neg=" << negated << std::endl;
                VERIFY(false);
                return false;
            }
            VERIFY(e);
            auto* first = e;
            SASSERT(e->next() == e);  // the result is expected to be a single interval (although for this check it doesn't really matter if there's more...)

            auto check_is_violated = [&](rational const& x, bool expect_violated) -> bool {
                if (is_violated(a1, b1, a2, b2, x, negated, M) == expect_violated)
                    return true;
                std::cout << "ERROR: a1=" << a1 << " b1=" << b1 << " a2=" << a2 << " b2=" << b2 << " val=" << val << " negated=" << negated << " bw=" << bw << "\n";
                return false;
            };

            do {
                rational const& lo = e->interval.is_full() ? rational::zero() : e->interval.lo_val();
                rational const& hi = e->interval.is_full() ? M : e->interval.hi_val();
                rational const& len = e->interval.is_full() ? M : e->interval.current_len();
                unsigned max_offset = 1000;
                unsigned check_offset = len.is_unsigned() ? std::min(max_offset, len.get_unsigned() / 2) : max_offset;
                for (unsigned i = 0; i <= check_offset; ++i) {
                    for (rational x : { lo + i, hi - (i + 1), val - i, val + i }) {
                        x = mod(x, M);
                        if (!e->interval.currently_contains(x))
                            continue;
                        VERIFY(check_is_violated(x, true));
                    }
                }
                if (M > max_offset) {
                    big_random_gen rng(bw);
                    for (unsigned i = 0; i < 1000; ++i) {
                        rational const x = mod(lo + mod(rng(), len), M);
                        VERIFY(e->interval.currently_contains(x));
                        VERIFY(check_is_violated(x, true));
                    }
                }
                if (expect_optimality && !e->interval.is_full()) {
                    VERIFY(check_is_violated(lo - 1, false));
                    VERIFY(check_is_violated(hi, false));
                }
                e = e->next();
            }
            while (e != first);
            return true;
        }

    public:
        static void exhaustive() {
            exhaustive(1);
            exhaustive(2);
            exhaustive(3);
            exhaustive(4);
            exhaustive(5);
        }

        static void exhaustive(unsigned bw) {
            std::cout << "test_fi::exhaustive for bw=" << bw << std::endl;
            rational const m = rational::power_of_two(bw);
            for (rational p; p < m; ++p)
                for (rational r; r < m; ++r)
                    for (rational q; q < m; ++q)
                        for (rational s; s < m; ++s)
                            for (rational v; v < m; ++v)
                                check_one(p, q, r, s, v, bw);
        }

        static void randomized(unsigned num_rounds, unsigned bw) {
            std::cout << "test_fi::randomized for bw=" << bw << " (" << num_rounds << " rounds)" << std::endl;
            big_random_gen rng(bw);
            unsigned round = num_rounds;
            while (round) {
                std::cout << "round " << round << "\n";
                rational a1 = rng();
                rational a2 = rng();
                rational b1 = rng();
                rational b2 = rng();
                rational val = rng();
                bool useful = check_one(a1, b1, a2, b2, val, bw);
                if (!a1.is_zero() && !a2.is_zero() && a1 != a2) {
                    // make sure to trigger refine-equal-lin as well
                    useful |= check_one(a1, b1, a1, b2, val, bw);
                    useful |= check_one(rational::zero(), b1, a2, b2, val, bw);
                    useful |= check_one(a1, b1, rational::zero(), b2, val, bw);
                }
                if (useful)
                    round--;
            }
        }

    };  // class test_fi


}



void tst_viable() {
    set_log_enabled(false);
    polysat::test1();
    polysat::test_univariate();
    polysat::test_univariate_minmax();
    polysat::test2();
    polysat::test_fi::exhaustive();
    polysat::test_fi::randomized(10000, 16);
    polysat::test_fi::randomized(1000, 256);
#if 0
    // TODO: case where refine-equal-lin is still looping:
    polysat::test_fi::check_one(
        rational("359753528351133424343509264780402113166597651845926285955318862825137336"),
        rational("752856510718007431332405387553440539688023502087834331667662410998631117"),
        rational("359753528351133424343509264780402113166597651845926285955318862825137336"),
        rational("752856510698397765512447284907808137313109237627169307951559225462781625"),
        rational("453547182885518174546100861831801761371386469830527870060540275516786265"),
        256
    );
#endif
}
