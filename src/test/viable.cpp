#include "math/polysat/log.h"
#include "math/polysat/solver.h"
#include "math/polysat/viable2.h"

namespace polysat {

    struct solver_scopev {
        reslimit lim;
    };

    class scoped_solverv : public solver_scopev, public solver {
    public:
        viable2 v;
        scoped_solverv(): solver(lim), v(*this) {}
        ~scoped_solverv() {
            for (unsigned i = m_trail.size(); i-- > 0;) {
                switch (m_trail[i]) {
                case trail_instr_t::viable_add_i: 
                    v.pop_viable();
                    break;                
                case trail_instr_t::viable_rem_i: 
                    v.push_viable();
                    break;
                default:
                    break;
                }
            }
        }
    };

    static void test1() {
        scoped_solverv s;
        auto xv = s.add_var(3);
        auto x = s.var(xv);
        s.v.push(3);
        rational val;
        auto c = s.ule(x + 3, x + 5);
        s.v.intersect(xv, c);
        std::cout << s.v << "\n";
        std::cout << "min-max " << s.v.min_viable(xv) << " " << s.v.max_viable(xv) << "\n";
        s.v.intersect(xv, s.ule(x, 2));
        std::cout << s.v << "\n";
        s.v.intersect(xv, s.ule(1, x));
        std::cout << s.v << "\n";
        std::cout << "min-max " << s.v.min_viable(xv) << " " << s.v.max_viable(xv) << "\n";
        s.v.intersect(xv, s.ule(x, 3));
        std::cout << s.v << "\n";
        std::cout << s.v.find_viable(xv, val) << " " << val << "\n";        
        std::cout << "min-max " << s.v.min_viable(xv) << " " << s.v.max_viable(xv) << "\n";
        s.v.intersect(xv, s.ule(3, x));
        std::cout << s.v << "\n";
        std::cout << s.v.find_viable(xv, val) << " " << val << "\n";      
    }

    static void add_interval(scoped_solverv& s, pvar xv, pdd x, unsigned lo, unsigned len) {
        if (lo == 0)
            s.v.intersect(xv, s.ule(x, len - 1));
        else if (lo + len == 8)
            s.v.intersect(xv, s.ule(lo, x));
        else 
            s.v.intersect(xv, ~s.ule(x - ((lo + len)%8), x - lo));                        
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
            bool mem2 = s.v.is_viable(xv, rational(i));
            if (mem1 != mem2)
                std::cout << "test violation: " << i << " member of all intervals " << mem1 << " viable: " << mem2 << "\n";
            SASSERT(mem1 == mem2);
        }
    }

    static void test_intervals(vector<std::pair<unsigned, unsigned>> const& intervals) {
        scoped_solverv s;
        auto xv = s.add_var(3);
        auto x = s.var(xv);
        s.v.push(3);
        for (auto const& [lo, len] : intervals)
            add_interval(s, xv, x, lo, len);
        std::cout << intervals << "\n";
        //std::cout << s.v << "\n";
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
}



void tst_viable() {
    polysat::test1();
    polysat::test2();
}