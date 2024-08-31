#include "math/lp/dioph_eq.h"
#include "math/lp/int_solver.h"
#include "math/lp/lar_solver.h"
#include "math/lp/lp_utils.h"
#include <list>
#include <queue>

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
                ret.j() = j();
                return ret;
            }
            const mpq& c() const { return m_c; }
            mpq& c() { return m_c; }
            term_o():m_c(0) {}
            void substitute(const term_o& t, unsigned term_column) {
                SASSERT(!t.contains(term_column));
                mpq a = get_coeff(term_column);  // need to copy it becase the pointer value can be changed during the next loop
                for (auto p : t) {
                    this->add_monomial(a * p.coeff(), p.j());
                }
                this->c() += a * t.c();
                this->m_coeffs.erase(term_column);
            }
            
            friend term_o operator*(const mpq& k, const term_o& term) {
               term_o r;
               for (const auto& p : term) 
                   r.add_monomial(p.coeff()*k, p.j());
               r.c() = k*term.c();    
               return r;
            }
#if Z3DEBUG
            friend bool operator== (const term_o & a, const term_o& b) {
                term_o t = a.clone();
                t += mpq(-1)*b;
                return t.c() == mpq(0) && t.size() == 0;
            }
#endif            
            term_o& operator += (const term_o& t) {
                for (const auto & p: t) {
                    add_monomial(p.coeff(), p.j());
                }
                m_c += t.c();
                return *this;
            }

        };
        std::ostream& print_S(std::ostream & out) const {
			out << "S:\n";
            for (unsigned i : m_s) {
                out << "x" << m_eprime[i].m_e.j() << " ->\n";
                print_eprime_entry(i, out);
            }
            return out;
        }

        std::ostream& print_lar_term_L(const lar_term & t, std::ostream & out) const {
            return print_linear_combination_customized(t.coeffs_as_vector(), [](int j)->std::string {return "y"+std::to_string(j);}, out );
        }
        
        std::ostream& print_term_o(term_o const& term, std::ostream& out) const {
            if (term.size() == 0 && term.c().is_zero()) {
                out << "0";
                out << ", j():"<< term.j();
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
            out << ", j():"<< term.j();
            return out;
        }
    
        /*
          An annotated state is a triple ⟨E′, λ, σ⟩, where E′ is a set of pairs ⟨e, ℓ⟩ in which
          e is an equation and ℓ is a linear combination of variables from L
        */
        struct eprime_pair {
            term_o   m_e;
            lar_term m_l; // this term keeps the history of m_e : originally m_l is i, the index of row m_e was constructed from
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

        term_o row_to_term(const row_strip<mpq>& row) const {
            const auto lcm = get_denominators_lcm(row);
            term_o t;
            for (const auto & p: row) 
                if (lia.is_fixed(p.var())) 
                    t.c() += p.coeff()*lia.lower_bound(p.var()).x;
                else 
                    t.add_monomial(lcm * p.coeff(), p.var());
            t.c() *= lcm;                            
            return t;
        }
        
        void init() {
            unsigned n_of_rows = lra.A_r().row_count();
            unsigned fn = 0;
                
            auto all_vars_are_int = [this](const auto& row) {
                for (const auto& p : row) {
                    if (!lia.column_is_int(p.var())) {
                        return false;
                    }
                }
                return true;
            };
            for (unsigned i = 0; i < n_of_rows; i++) {
                auto & row = lra.get_row(i);
                TRACE("dioph_eq", tout << "row "<< i <<":"; lia.display_row_info(tout, i) << "\n";);
                unsigned basic_var = lra.r_basis()[i];
                if (!lia.column_is_int(basic_var)) continue;
                if (!all_vars_are_int(row)) continue;
                term_o t = row_to_term(row);
                TRACE("dioph_eq", tout << "row = "; lra.print_row(row, tout) << std::endl;);
                if (t.size() == 0) {
                    SASSERT(t.c().is_zero());
                    continue;
                }
                eprime_pair pair = {t, lar_term(i)};
                m_f.push_back(m_f.size());                
                m_eprime.push_back(pair);
                TRACE("dioph_eq", print_eprime_entry(m_f.size() - 1, tout););
            }
            
        }

        mpq gcd_of_coeffs(const term_o& t) {
            mpq g(0);
            for (const auto & p : t) {
                if (g.is_zero()) {
                    g = abs(p.coeff());
                } else {
                    g = gcd(g, p.coeff());
                }                
            }
            return g;
        }
        // returns true if no conflict is found and false otherwise
        bool normalize_e_by_gcd(eprime_pair& ep) {
            TRACE("dioph_eq", print_term_o(ep.m_e, tout << "m_e:") << std::endl; 
                  print_lar_term_L(ep.m_l, tout << "m_l:") << std::endl;
                );
            mpq g = gcd_of_coeffs(ep.m_e);
            if (g.is_zero()) {
                SASSERT(ep.m_e.c().is_zero());
                return true;                
            }
            if (g.is_one())
                return true;
            TRACE("dioph_eq", tout << "g:" << g << std::endl;);
            mpq new_c = ep.m_e.c() / g;
            if (new_c.is_int() == false) {
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
                TRACE("dioph_eq",
                       tout << "ep_m_e:"; print_term_o(ep.m_e, tout) << std::endl;
                         tout << "ep.ml:";
                         print_lar_term_L(ep.m_l, tout ) << std::endl;);

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
            TRACE("dioph_eq", print_S(tout););
            NOT_IMPLEMENTED_YET();
            return lia_move::sat;
        }
        std::list<unsigned>::iterator pick_eh() {
            return m_f.begin(); // TODO: make a smarter joice
        }

        void add_operator(lar_term& t, const mpq& k, const lar_term& l) {
            for (const auto& p: l) {
                t.add_monomial(k*p.coeff(), p.j());
            }
        }

        void substitute_var_on_f(unsigned k, int k_sign, const term_o& k_subst, const lar_term& l_term, unsigned index_to_avoid)  {
            TRACE("dioph_eq", print_term_o(k_subst, tout<< "x" << k<< " -> ") << std::endl; tout << "l_term:"; print_lar_term_L(l_term, tout) << std::endl;);
            for (unsigned e_index: m_f) {
                if (e_index == index_to_avoid) continue;
                term_o& e = m_eprime[e_index].m_e;
                if (!e.contains(k)) continue;
                
                const mpq& k_coeff = e.get_coeff(k);
                TRACE("dioph_eq", print_eprime_entry(e_index, tout << "before:") << std::endl;
                       tout << "k_coeff:" << k_coeff << std::endl;);
                if (!l_term.is_empty()) {
                    add_operator(m_eprime[e_index].m_l, -k_sign*k_coeff, l_term);
                }
                e.substitute(k_subst, k);
                TRACE("dioph_eq", print_eprime_entry(e_index, tout << "after :") << std::endl;);                       
            }
        }

        std::tuple<mpq, unsigned, int> find_minimal_abs_coeff(const term_o& eh) const {
            bool first = true;
            mpq ahk;
            unsigned k;
            int k_sign;
            mpq t;
            for (const auto& p : eh) {
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
            t.c() = -k_sign*eh.c();
            TRACE("dioph_eq", tout << "subst_term:"; print_term_o(t, tout) << std::endl;);
            return t;
        }
        void eliminate_var_in_f(eprime_pair& e_pair, unsigned k, int k_sign) {
            term_o t = get_term_to_subst(e_pair.m_e, k, k_sign);
            substitute_var_on_f(k, k_sign, t, e_pair.m_l, -1) ; // -1 is for the index to ignore
        }

// k is the variable to substitute
        void fresh_var_step(unsigned e_index, unsigned k) {
            eprime_pair & e_pair = m_eprime[e_index];
// step 7 from the paper
            auto & eh = e_pair.m_e;
            // xt is the fresh variable 
            unsigned xt = m_last_fresh_x_var--;
            TRACE("dioph_eq", tout << "introduce fresh xt:" << "~x"<< fresh_index(xt) << std::endl;
                  tout << "eh:"; print_term_o(eh,tout) << std::endl;);
            /* Let eh = sum (a_i*x_i) + c  
               For each i != k, let a_i = a_qi*ahk + a_ri, and let c = c_q * ahk + c_r
               eh = ahk * (x_k + sum {a_qi*x_i) + c_q | i != k }) + sum {a_ri*x_i | i != k} + c_r = 0
               xt = x_k + sum {a_qi*x_i) + c_q | i != k }, it will be xt_term
               Then x_k -> - sum {a_qi*x_i) + c_q | i != k } + xt, it will be subs_k
               eh = ahk*xt + ...
            */
            term_o xt_term;
            term_o k_subs;
            // copy it aside
            const mpq ahk = eh.get_coeff(k);
            mpq r, q = machine_div_rem(eh.c(), ahk, r);
            xt_term.add_var(k);
            xt_term.c() = q;
            xt_term.add_monomial(mpq(-1), xt);
            k_subs.add_var(xt);
            k_subs.c() = - q; 
            term_o et; //et is the elimination k from eh, which is an optimization
            et.add_monomial(ahk, xt);
            et.c() = r;
            for (const auto & p: eh) {
                if (p.j() == k) continue;
                q = machine_div_rem(p.coeff(), ahk, r);
                xt_term.add_monomial(q, p.j());
                k_subs.add_monomial(-q, p.j());
                et.add_monomial(r, p.j());
            }
            m_eprime[e_index].m_e = et;
            eprime_pair xt_entry = {xt_term, lar_term()};  // 0 for m_l field
            m_eprime.push_back(xt_entry);
            TRACE("dioph_eq", tout << "xt_term:"; print_term_o(xt_term, tout) << std::endl;
                  tout << "k_subs:"; print_term_o(k_subs, tout) << std::endl;
                  print_eprime_entry(m_eprime.size()-1, tout););
            substitute_var_on_f(k, 1, k_subs, xt_entry.m_l, e_index);

             // the term to eliminate the fresh variable
            term_o xt_subs = xt_term.clone();
            xt_subs.add_monomial(mpq(1), xt);
            TRACE("dioph_eq", tout << "xt_subs: x~"<< fresh_index(xt) << " -> ";  print_term_o(xt_subs, tout) << std::endl;);               
            m_sigma.insert(xt, xt_subs);
        }
        std::ostream& print_eprime_entry(unsigned i, std::ostream& out) const {
            out << "m_eprime[" << i << "]:{\n";
                  print_term_o(m_eprime[i].m_e, out << "\tm_e:") << "," << std::endl;
                  print_lar_term_L(m_eprime[i].m_l, out<< "\tm_l:") << "\n}"<< std::endl;
                  return out;
        }
        // this is the step 6 or 7 of the algorithm
        void rewrite_eqs() {
            auto eh_it = pick_eh();            
            auto& eprime_entry = m_eprime[*eh_it];
            TRACE("dioph_eq", print_eprime_entry(*eh_it, tout););                  
            term_o& eh = eprime_entry.m_e;
            auto [ahk, k, k_sign] = find_minimal_abs_coeff(eh);
            TRACE("dioph_eq", tout << "ahk:" << ahk << ", k:" << k << ", k_sign:" << k_sign << std::endl;);
            if (ahk.is_one()) {
                eprime_entry.m_e.j() = k;
                TRACE("dioph_eq", tout << "push to S:\n"; print_eprime_entry(*eh_it, tout););
                m_s.push_back(*eh_it);                
                m_f.erase(eh_it);
                eliminate_var_in_f(eprime_entry, k , k_sign);                
            } else {
                fresh_var_step(*eh_it, k);
            }
        }

        void explain(lp::explanation& ex) {
            SASSERT(ex.empty());
            TRACE("dioph_eq", tout << "conflict:"; print_eprime_entry(m_conflict_index, tout) << std::endl;);
            auto & ep = m_eprime[m_conflict_index];
            u_dependency* dep = nullptr;
            for (const auto & pl : ep.m_l) {
                unsigned row_index = pl.j();
                for (const auto & p : lra.get_row(row_index))
                    if (lra.column_is_fixed(p.var()))
                        lra.explain_fixed_column(p.var(), ex);
            }
            TRACE("dioph_eq", lra.print_expl(tout, ex););
        }
        unsigned fresh_index(unsigned j) const {return UINT_MAX - j;}
        
        void remove_fresh_variables(term_o& t) {
             std::queue<unsigned> q;
             for (auto p : t) {
                 if (is_fresh_var(p.j())) { 
                     q.push(p.j());                     
                 }
             }
             CTRACE("dioph_eq_fresh", q.empty() == false, print_term_o(t, tout)<< std::endl);
             while (!q.empty()) {
                 unsigned j = q.front();
                 q.pop();
                 const term_o& sub_t = m_sigma.find(j);
                 TRACE("dioph_eq_fresh", tout << "x~" << fresh_index(j) << "; sub_t:"; print_term_o(sub_t, tout) << std::endl;);
                 t.substitute(sub_t, j);
                 TRACE("dioph_eq_fresh", tout << "sub_t:"; print_term_o(sub_t, tout) << std::endl;
                       tout << "after sub:";print_term_o(t, tout) << std::endl;);
                 for (auto p : sub_t)
                     if (is_fresh_var(p.j()) && t.contains(p.j())) 
                        q.push(p.j());                     
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
