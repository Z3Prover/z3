#include "math/lp/dioph_eq.h"
#include "math/lp/int_solver.h"
#include "math/lp/lar_solver.h"
#include "math/lp/lp_utils.h"
#include <list>

namespace lp {
    // This class represents a term with an added constant number c, in form sum {x_i*a_i} + c.
    
    class term_o:public lar_term {        
        mpq m_c;        
    public:
        const mpq& c() const { return m_c; }
        mpq& c() { return m_c; }
        term_o():m_c(0) {}
        term_o& operator*=(mpq const& k) {
            for (auto & t : m_coeffs)
                t.m_value *= k;
            return *this;
        }   
    };
    class dioph_eq::imp {
    public:
        int_solver& lia;
        lar_solver& lra;
        unsigned    m_fresh_x_vars_start;
        unsigned    m_last_fresh_x_var;
        
        // set F 
        std::list<term_o*> m_f;
        // set S
        std::list<term_o*> m_s;
        
    t    imp(int_solver& lia, lar_solver& lra): lia(lia), lra(lra) {
            m_fresh_x_vars_start = lra.number_of_vars();
            m_last_fresh_x_var = -1;
        }
        
        bool belongs_to_list(term_o* t, std::list<term_o*> l) {
            for (auto& item : l) {
                if (item == t) {
                    return true;
                }
            }
            return false;
        }
    
        void init() {
            unsigned n_of_rows = static_cast<unsigned>(lra.r_basis().size());
            unsigned skipped = 0;
            unsigned fn = 0;
            for (unsigned i = 0; i < n_of_rows; i++) {
                auto & row = lra.get_row(i);
                term_o t;
                bool all_vars_are_int = true;

                for (const auto & p : row) {                   
                    if (!lia.column_is_int(p.var())){
                        all_vars_are_int = false;
                        break;
                    }
                    
                }

                if (all_vars_are_int) {
                    term_o* t = new term_o();
                    const auto lcm = get_denominators_lcm(row);
                    for (const auto & p: row) {
                        t->add_monomial(lcm * p.coeff(), p.var());
                        if(lia.is_fixed(p.var())) {
                            t->c() += lia.lower_bound(p.var()).x;
                        }
                    }
                    m_f.push_back(t);
                }
            }
            
        }

        // returns true if no conflict is found and false otherwise
        bool normalize_e_by_gcd(term_o& e) {
            mpq g(0);
            for (auto & p : e) {
                if (g.is_zero()) {
                    g = abs(p.coeff());
                } else {
                    g = gcd(g, p.coeff());
                }                
            }
            if (g.is_zero()) {
                UNREACHABLE();
            }
            if (g.is_one())
                return true;
            std::cout << "reached\n";    
            e.c() *= (1/g);
            if (!e.c().is_int()) {
                // conlict: todo - collect the conflict
                NOT_IMPLEMENTED_YET();
                return false;                 
            }
            return true;
        }
        // returns true if no conflict is found and false otherwise
        bool normalize_by_gcd() {
            for (auto * e: m_f) {
                if (!normalize_e_by_gcd(*e)) {
                    return false;
                }
            }
            return true;
        }

        lia_move check() {
            init();
            while(m_f.size()) {
                if (!normalize_by_gcd()) 
                    return lia_move::unsat;
                rewrite_eqs();
            }
            return lia_move::sat;
        }
        std::list<term_o*>::iterator pick_eh() {
            return m_f.begin(); // TODO: make a smarter joice
        }

        void substitute(unsigned k, term_o* s)  {
            NOT_IMPLEMENTED_YET();
        }
        // this is the step 6 or 7 of the algorithm
        void rewrite_eqs() {
            auto eh_it = pick_eh();
            term_o* eh = *eh_it;
            // looking for minimal in absolute value coefficient
            bool first = true;
            mpq ahk;
            unsigned k;
            int k_sign;
            for (auto& p: *eh) {
                if (first || abs(p.coeff()) < ahk) {
                    ahk = abs(p.coeff());
                    k_sign = p.coeff().is_pos()? 1:-1;
                    k = p.j();
                    if (ahk.is_one())
                        break;
                    first = false;    
                }
            }
            if (ahk.is_one()) {
                // step 6
                term_o *s_term = new term_o();
                s_term->j() = k; // keep the assigned variable in m_j of the term
                for (auto& p:*eh) {
                    if (p.j() == k) continue;
                    s_term->add_monomial(-k_sign*p.coeff(), p.j());
                }
                m_f.erase(eh_it);
                m_s.push_back(s_term);
                substitute(k, s_term);
            } else {
                // step 7
                // the fresh variable 
                unsigned xt = m_last_fresh_x_var == -1? m_fresh_x_vars_start: m_last_fresh_x_var++;
                
                
            }
                
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
