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
            term_o clone() const { 
                term_o ret;
                for (const auto & p: *this) {
                    ret.add_monomial(p.coeff(), p.j());
                }
                ret.c() = c();
                return ret;
            }
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

        std::ostream& print_lar_term_L(lar_term & t, std::ostream & out) const {
            return print_linear_combination_customized(t.coeffs_as_vector(), [](int j)->std::string {return "y"+std::to_string(j);}, out );
        }
        
        std::ostream& print_term_o(term_o const& term, std::ostream& out, const std::string & var_prefix) const {
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
            
            if (!term.c().is_zero()) {
                if (term.c().is_pos())
                   out << " + " << term.c();
                else 
                   out << " - " << -term.c();
                
            }
            return out;
        }
    
        /*
          An annotated state is a triple ⟨E′, λ, σ⟩, where E′ is a set of pairs ⟨e, ℓ⟩ in which
          e is an equation and ℓ is a linear combination of variables from L
        */
        struct eprime_pair {
            term_o   m_e;
            lar_term m_l;
        };
        vector<eprime_pair> m_eprime;
        /*
          Let L be a set of variables disjoint from X, and let λ be a mapping from variables in
          L to linear combinations of variables in X and of integer constants
        */
        u_map<unsigned> m_lambda; // maps to the index of the eprime_pair in m_eprime
        /* let σ be a partial mapping from variables in L united with X to linear combinations
           of variables in X and of integer constants showing the substitutions
        */
        u_map<term_o> m_sigma;
        
    public:
        int_solver& lia;
        lar_solver& lra;
        unsigned    m_last_fresh_x_var;
        
        // set F 
        std::list<unsigned> m_f;  // F = {λ(t):t in m_f} 
        // set S
        std::list<unsigned> m_s;     // S = {λ(t): t in m_s}

        unsigned            m_conflict_index = -1;  // m_eprime[m_conflict_index] gives the conflict
        
        imp(int_solver& lia, lar_solver& lra): lia(lia), lra(lra) {
            m_last_fresh_x_var = -1;
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
                    term_o t;
                    const auto lcm = get_denominators_lcm(row);
                    for (const auto & p: row) {
                        t.add_monomial(lcm * p.coeff(), p.var());
                        if(lia.is_fixed(p.var())) {
                            t.c() += lia.lower_bound(p.var()).x;
                        }
                    }
                    unsigned lvar = static_cast<unsigned>(m_f.size());
                    lar_term lt = lar_term(lvar);
                    eprime_pair pair = {t, lt};
                    m_eprime.push_back(pair);
                    m_lambda.insert(lvar, lvar);
                    m_f.push_back(lvar);
                }
            }
            
        }

        // returns true if no conflict is found and false otherwise
        bool normalize_e_by_gcd(eprime_pair& ep) {
            mpq g(0);
            TRACE("dioph_eq", print_term_o(ep.m_e, tout << "m_e:", "x") << std::endl; 
                              print_lar_term_L(ep.m_l, tout << "m_l:") << std::endl;
            );
            for (auto & p : ep.m_e) {
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
            mpq new_c = ep.m_e.c() / g;
            if (new_c.is_int() == false) {
                // conlict: todo - collect the conflict
                TRACE("dioph_eq",
                      print_term_o(ep.m_e, tout << "conflict m_e:", "x") << std::endl; 
                                  tout << "g:" << g << std::endl; 
                      print_lar_term_L(ep.m_l, tout << "m_l:") << std::endl;
                      for (const auto & p: ep.m_l) {
                          tout << p.coeff() << "("; print_term_o(m_eprime[p.j()].m_e, tout, "x") << ")"<< std::endl;
                      }
                      tout << "S:\n";
                      for (const auto& t : m_sigma) {
                          tout << "x" << t.m_key << " -> ";
                              print_term_o(t.m_value, tout, "x") << std::endl;
                      }
                    );
                return false;                 
            } else {
                for (auto& p: ep.m_e.coeffs()) {
                    p.m_value /= g;
                }
                ep.m_e.c() = new_c;
                ep.m_l *= (1/g);

            }
            return true;
        }
        // returns true if no conflict is found and false otherwise
        bool normalize_by_gcd() {
            for (unsigned l: m_f) {
                if (!normalize_e_by_gcd(m_eprime[l])) {
                    m_conflict_index = l;
                    return false;
                }
            }
            return true;
        }

        lia_move check() {
            init();
            while(m_f.size()) {
                if (!normalize_by_gcd()) 
                    return lia_move::conflict;
                rewrite_eqs();
            }
            return lia_move::sat;
        }
        std::list<unsigned>::iterator pick_eh() {
            return m_f.begin(); // TODO: make a smarter joice
        }

        void substitute_var_on_f(unsigned k, int k_sign, const term_o& k_subst, const lar_term& l_term)  {
            TRACE("dioph_eq", print_term_o(k_subst, tout<< k<< "->", "x") << std::endl;);
            for (unsigned e_index: m_f) {
                term_o& e = m_eprime[e_index].m_e;
                if (!e.contains(k)) continue;
                const mpq& k_coeff = e.get_coeff(k);
                TRACE("dioph_eq", print_term_o(e, tout << "before:", "x") << std::endl;
                       tout << "k_coeff:" << k_coeff << std::endl;);
                m_eprime[e_index].m_l = k_sign*k_coeff*l_term  + lar_term(e_index); // m_l is set to k_sign*e + e_sub
                e.substitute(k_subst, k);
                TRACE("dioph_eq", print_term_o(e, tout << "after :", "x") << std::endl;
                       print_lar_term_L(m_eprime[e_index].m_l, tout) << std::endl;);
            }
        }

        std::tuple<mpq, unsigned, int> find_minimal_abs_coeff(const term_o& eh) const {
            bool first = true;
            mpq ahk;
            unsigned k;
            int k_sign;
            mpq t;
            for (auto& p : eh) {
                t = abs(p.coeff());
                if (first || t < ahk) {
                    ahk = t;
                    k_sign = p.coeff().is_pos() ? 1 : -1;
                    k = p.j();
                    if (ahk.is_one())
                        break;
                    first = false;
                }
            }
            return std::make_tuple(ahk, k, k_sign);
        }

        term_o get_term_to_subst(const term_o& eh, unsigned k, int k_sign) {
            term_o t;
            for (const auto & p: eh) {
                if (p.j() == k) continue;
                t.add_monomial(-k_sign*p.coeff(), p.j());
            }
            t.c() = eh.c();
            TRACE("dioph_eq", tout << "subst_term:"; print_term_o(t, tout, "x") << std::endl;);
            return t;
        }
        // this is the step 6 or 7 of the algorithm
        void rewrite_eqs() {
            auto eh_it = pick_eh();            
            auto eprime_entry = m_eprime[*eh_it];
            TRACE("dioph_eq", tout << "eprime_entry[" << *eh_it << "]{\n";
                  print_term_o(m_eprime[*eh_it].m_e, tout << "\tm_e:", "x") << "," << std::endl;
                  print_lar_term_L(m_eprime[*eh_it].m_l, tout<< "\tm_l:") << "\n}"<< std::endl;);
                  
            term_o& eh = m_eprime[*eh_it].m_e;
            auto [ahk, k, k_sign] = find_minimal_abs_coeff(eh);
            
            if (ahk.is_one()) {
                // step 6
                m_s.push_back(*eh_it);                
                m_f.erase(eh_it);
                term_o t = get_term_to_subst(eh, k, k_sign);
                m_sigma.insert(k, t);
                substitute_var_on_f(k, k_sign, t, eprime_entry.m_l) ;
            } else {
                // step 7
                // the fresh variable 
                unsigned xt = m_last_fresh_x_var++;
                NOT_IMPLEMENTED_YET();
                
            }
                
        }
        void explain(lp::explanation& ex) {
            auto & ep = m_eprime[m_conflict_index];
            for (const auto & p : ep.m_l) {
                remove_fresh_variables(m_eprime[p.j()].m_e);
            }
            u_dependency* dep = nullptr;
            for (const auto & pl : ep.m_l)
                for (const auto & p : m_eprime[pl.j()].m_e)
                    if (lra.column_is_fixed(p.j()))
                        lra.explain_fixed_column(p.j(), ex);
            
            TRACE("dioph_eq", lra.print_expl(tout, ex););
        }
        void remove_fresh_variables(term_o& t) {
            // TODO implement
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
    void dioph_eq::explain(lp::explanation& ex) {
        m_imp->explain(ex);
    }
    
}
