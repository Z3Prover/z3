#include "math/lp/dioph_eq.h"
#include "math/lp/int_solver.h"
#include "math/lp/lar_solver.h"
#include "math/lp/lp_utils.h"

namespace lp {

    class dioph_eq::imp {
    public:
        int_solver& lia;
        lar_solver& lra;

        imp(int_solver& lia, lar_solver& lra): lia(lia), lra(lra) {}
        vector<lar_term> m_e;
            
        void init() {
            unsigned n_of_rows = static_cast<unsigned>(lra.r_basis().size());
            unsigned skipped = 0;
            for (unsigned i = 0; i < n_of_rows; i++) {
                auto & row = lra.get_row(i);
                lar_term t;
                bool is_int = true;
                for (const auto & p : row) {
                    if (!lia.column_is_int(p.var()))
                        is_int = false;
                }
                if (is_int) {
                    lar_term t;
                    const auto lcm = get_denominators_lcm(row);
                    for (const auto & p: row) {
                        t.add_monomial(lcm * p.coeff(), p.var());
                    }
                    m_e.push_back(t);
                } else {
                    skipped ++;
                }
            }
            if (m_e.size() > 0) {
                std::cout << "collected " << m_e.size() << ", skipped " << skipped << "\n";
                for (const auto & t: m_e) {
                    lra.print_term(t, std::cout) << "\n";
                }
                std::cout << "________________________\n";
            }
        }

        lia_move check() {
            init();
            return lia_move::undef;
        }
    };
// Constructor definition
    dioph_eq::dioph_eq(int_solver& lia): lia(lia) {
        m_imp = alloc(imp, lia, lia.lra);
    }
    dioph_eq::~dioph_eq() {
        dealloc(m_imp);
    }
    
    lia_move dioph_eq::check() {
        return m_imp->check();
        
    }
    
}
