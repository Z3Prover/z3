#include "math/lp/dioph_eq.h"
#include "math/lp/int_solver.h"
#include "math/lp/lar_solver.h"
#include "math/lp/lp_utils.h"
#include <list>

namespace lp {
    // This class represents a term with an added constant number c, in form sum {x_i*a_i} + c.
    
    class dioph_eq::imp {

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
            void substitute(const term_o& t, unsigned term_column) {
                auto it = this->m_coeffs.find_core(term_column);
                if (it == nullptr) return;
                mpq a = it->get_data().m_value;
                this->m_coeffs.erase(term_column);
                for (auto p : t) {
                    this->add_monomial(a * p.coeff(), p.j());
                }
                this->c() += a * t.c();
            }
        };

        std::ostream& print_term(term_o const& term, std::ostream& out, const std::string & var_prefix) const {
            if (term.size() == 0) {
                out << "0";
                return out;
            }
            bool first = true;
            for (const auto p : term) {
                mpq val = p.coeff();
                if (first) {
                    first = false;
                }
                else if (is_pos(val)) {
                    out << " + ";
                }
                else {
                    out << " - ";
                    val = -val;
                }
                if (val == -numeric_traits<mpq>::one())
                    out << " - ";
                else if (val != numeric_traits<mpq>::one())
                    out << T_to_string(val);
                out << var_prefix << p.j();
            }
            
            if (!term.c().is_zero())
                 out << " + " << term.c();
            return out;
        }
    
        /*
          An annotated state is a triple ⟨E′, λ, σ⟩, where E′ is a set of pairs ⟨e, ℓ⟩ in which
          e is an equation and ℓ is a linear combination of variables from L
        */
        struct eprime_pair {
            term_o * m_e;
            lar_term * m_l;
        };
        vector<eprime_pair> m_eprime;
        /*
          Let L be a set of variables disjoint from X, and let λ be a mapping from variables in
          L to linear combinations of variables in X and of integer constants
        */
        u_map<unsigned> m_lambda; // maps to the index of the term in m_eprime
        /* let σ be a partial mapping from variables in L united with X to linear combinations
           of variables in X and of integer constants showing the substitutions
        */
        u_map<lar_term*> m_sigma;
        
    public:
        int_solver& lia;
        lar_solver& lra;
        unsigned    m_last_fresh_x_var;
        
        // set F 
        std::list<unsigned> m_f;  // F = {λ(t):t in m_f} 
        // set S
        std::list<unsigned> m_s;     // S = {λ(t): t in m_s}
        
        imp(int_solver& lia, lar_solver& lra): lia(lia), lra(lra) {
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
                    unsigned lvar = static_cast<unsigned>(m_f.size());
                    lar_term* lt = new lar_term();
                    lt->add_var(lvar);
                    eprime_pair pair = {t, lt};
                    m_eprime.push_back(pair);
                    m_lambda.insert(lvar, lvar);
                    m_f.push_back(lvar);
                    
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
            for (unsigned l: m_f) {
                term_o* e = m_eprime[l].m_e;
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
        std::list<unsigned>::iterator pick_eh() {
            return m_f.begin(); // TODO: make a smarter joice
        }

        void substitute(unsigned k, term_o* s)  {
            print_term(*s, std::cout<< k<< "->", "x") << std::endl;
            for (unsigned e_index: m_f) {
                term_o* e = m_eprime[e_index].m_e;
                if (!e->contains(k)) continue;
                print_term(*e, std::cout << "before:", "x") << std::endl;
                e->substitute(*s, k);
                print_term(*e, std::cout << "after :", "x") << std::endl;
            }
        }
        // this is the step 6 or 7 of the algorithm
        void rewrite_eqs() {
            auto eh_it = pick_eh();            
            auto eprime_entry = m_eprime[*eh_it];
            std
            term_o* eh = m_eprime[*eh_it].m_e;

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
                m_s.push_back(*eh_it);                
                m_f.erase(eh_it);
                m_sigma.insert(k, s_term);
                substitute(k, s_term);
            } else {
                // step 7
                // the fresh variable 
                unsigned xt = m_last_fresh_x_var++;
                NOT_IMPLEMENTED_YET();
                
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
