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
        
        std::ostream& print_term_o(term_o const& term, std::ostream& out) const {
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
                if (!is_fresh_var(p.j())) {   
                    out << "x" << p.j();
                } else {
                    out <<  "x~" << (UINT_MAX - p.j()); // ~ is for a fresh variable
                }
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
            lar_term m_l; // this term keeps the history of m_e : originally m_l = k, where k is the index of eprime_pair in m_eprime
        };
        vector<eprime_pair> m_eprime;
        
        /* let σ be a partial mapping from variables in L united with X to linear combinations
           of variables in X and of integer constants showing the substitutions
        */
        u_map<term_o> m_sigma;
        
    public:
        int_solver& lia;
        lar_solver& lra;
        // we start assigning with UINT_MAX an go down, print it as l(UINT_MAX - m_last_fresh_x_var)
        unsigned  m_last_fresh_x_var = UINT_MAX; 

        
        // set F 
        std::list<unsigned> m_f;  // F = {λ(t):t in m_f} 
        // set S
        std::list<unsigned> m_s;     // S = {λ(t): t in m_s}

        unsigned            m_conflict_index = -1;  // m_eprime[m_conflict_index] gives the conflict
        
        imp(int_solver& lia, lar_solver& lra): lia(lia), lra(lra) {}
        
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
                    for (const auto & p: row) 
                        if (lia.is_fixed(p.var())) 
                            t.c() += lia.lower_bound(p.var()).x;
                        else 
                            t.add_monomial(lcm * p.coeff(), p.var());
                    
                    t.j() = i; //hijach this field to point to the original tableau row

                    unsigned lvar = static_cast<unsigned>(m_f.size());
                    lar_term lt = lar_term(lvar);
                    eprime_pair pair = {t, lt};
                    m_eprime.push_back(pair);
                    m_f.push_back(lvar);
                }
            }
            
        }

        // returns true if no conflict is found and false otherwise
        bool normalize_e_by_gcd(eprime_pair& ep) {
            mpq g(0);
            TRACE("dioph_eq", print_term_o(ep.m_e, tout << "m_e:") << std::endl; 
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
                      print_term_o(ep.m_e, tout << "conflict m_e:") << std::endl; 
                                  tout << "g:" << g << std::endl; 
                      print_lar_term_L(ep.m_l, tout << "m_l:") << std::endl;
                      for (const auto & p: ep.m_l) {
                          tout << p.coeff() << "("; print_term_o(m_eprime[p.j()].m_e, tout) << ")"<< std::endl;
                      }
                      tout << "S:\n";
                      for (const auto& t : m_sigma) {
                          tout << "x" << t.m_key << " -> ";
                              print_term_o(t.m_value, tout) << std::endl;
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
            TRACE("dioph_eq", print_term_o(k_subst, tout<< k<< "->") << std::endl;);
            for (unsigned e_index: m_f) {
                term_o& e = m_eprime[e_index].m_e;
                if (!e.contains(k)) continue;
                const mpq& k_coeff = e.get_coeff(k);
                TRACE("dioph_eq", print_term_o(e, tout << "before:") << std::endl;
                       tout << "k_coeff:" << k_coeff << std::endl;);
                m_eprime[e_index].m_l = k_sign*k_coeff*l_term  + lar_term(e_index); // m_l is set to k_sign*e + e_sub
                e.substitute(k_subst, k);
                TRACE("dioph_eq", print_term_o(e, tout << "after :") << std::endl;
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
            TRACE("dioph_eq", tout << "subst_term:"; print_term_o(t, tout) << std::endl;);
            return t;
        }
        // this is the step 6 or 7 of the algorithm
        void rewrite_eqs() {
            auto eh_it = pick_eh();            
            auto eprime_entry = m_eprime[*eh_it];
            TRACE("dioph_eq", tout << "eprime_entry[" << *eh_it << "]{\n";
                  print_term_o(m_eprime[*eh_it].m_e, tout << "\tm_e:") << "," << std::endl;
                  print_lar_term_L(m_eprime[*eh_it].m_l, tout<< "\tm_l:") << "\n}"<< std::endl;);
                  
            term_o& eh = m_eprime[*eh_it].m_e;
            auto [ahk, k, k_sign] = find_minimal_abs_coeff(eh);
            TRACE("dioph_eq", tout << "ahk:" << ahk << ", k:" << k << ", k_sign:" << k_sign << std::endl;);
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
                unsigned xt = m_last_fresh_x_var--; // xt is a fresh variable
                ahk *= k_sign; // get the original value of ahk
                TRACE("dioph_eq", tout << "introduce fresh xt:" << "~x"<< UINT_MAX -xt << std::endl;
                tout << "eh:"; print_term_o(eh,tout) << std::endl;);
                /* Let eh = sum (a_i*x_i) + c = 0. 
                For each i != k, let a_i = a_qi*ahk + a_ri, and let c = c_q * ahk + c_r
                eh = ahk * (x_k + sum {a_qi*x_i) + c_q | i != k }) + sum {a_ri*x_i | i != k} + c_r = 0
                x_t = x_k + sum {a_qi*x_i) + c_q | i != k }, it will be x_t_term
                Then x_k -> - sum {a_qi*x_i) + c_q | i != k } + x_t, it will be subs_k
                eh = ahk*x_t + ...
                */
               term_o x_t_term;
               term_o k_subs;
               mpq c_r; 
               mpq c_q = machine_div_rem(eh.c(), ahk, c_r);
               x_t_term.add_var(k);
               x_t_term.c() = c_q;
               x_t_term.add_monomial(mpq(-1), xt);
               k_subs.add_var(xt);
               k_subs.c() = - c_q; 

               for (const auto & p: eh) {
                   mpq a_q, a_r;
                   if (p.j() == k) continue;
                   a_q = machine_div_rem(p.coeff(), ahk, a_r);
                   x_t_term.add_monomial(a_q, p.j());
                   k_subs.add_monomial(-a_q, p.j());
               }
               TRACE("dioph_eq", tout << "x_t_term:"; print_term_o(x_t_term, tout) << std::endl;
               tout << "k_subs:"; print_term_o(k_subs, tout) << std::endl;);
               eprime_pair x_t_entry = {x_t_term, lar_term()};  // 0 for m_l field
               m_eprime.push_back(x_t_entry);
               substitute_var_on_f(k, 1, k_subs, eprime_entry.m_l);

               term_o x_t_subs = x_t_term.clone();
               x_t_subs.add_monomial(mpq(1), xt);

               TRACE("dioph_eq", tout << "x_t_subs:"; print_term_o(x_t_subs, tout) << std::endl;);               
               m_sigma.insert(xt, x_t_subs);
            }
                
        }
        void explain(lp::explanation& ex) {
            SASSERT(ex.empty());
            auto & ep = m_eprime[m_conflict_index];
            for (const auto & p : ep.m_l) {
                remove_fresh_variables(m_eprime[p.j()].m_e);
            }
            u_dependency* dep = nullptr;
            for (const auto & pl : ep.m_l) {
                for (const auto & p : lra.get_row(m_eprime[pl.j()].m_e.j()))
                    if (lra.column_is_fixed(p.var()))
                        lra.explain_fixed_column(p.var(), ex);
            }
            TRACE("dioph_eq", lra.print_expl(tout, ex););
        }
        void remove_fresh_variables(term_o& t) {
             std::set<unsigned> seen_fresh_vars;
             for (auto p : t) {
                 auto j = p.j();
                 if (is_fresh_var(j)) 
                     seen_fresh_vars.insert(j);
             }
             CTRACE("dioph_eq_sub_terms", seen_fresh_vars.empty() == false, print_term_o(t, tout)<< std::endl);
             while (!seen_fresh_vars.empty()) {
                 unsigned j = *seen_fresh_vars.begin();
                 seen_fresh_vars.erase(j);
                 const term_o& ot = m_sigma.find(j);
                 TRACE("dioph_eq_sub_terms", tout << "ot:"; print_term_o(ot, tout) << std::endl;);
                 for (auto p : ot)
                     if (is_fresh_var(p.j())) 
                         seen_fresh_vars.insert(p.j());
                 t.substitute(ot, j);

                 TRACE("dioph_eq_sub_terms", tout << "ot:"; print_term_o(ot, tout) << std::endl;
                 tout << "after sub:";print_term_o(t, tout) << std::endl;);
             }
        }
        bool is_fresh_var(unsigned j) const {
            return j > lra.column_count();
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
