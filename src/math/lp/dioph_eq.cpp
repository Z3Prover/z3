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
            void substitute_var_with_term(const term_o& t, unsigned term_column) {
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
        std::ostream& print_S(std::ostream & out) {
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
                out << "x";
                if (is_fresh_var(p.j())) out << "~";
                out << p.j();
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
            // we keep the dependency of the equation in m_l
            // a more expensive alternative is to keep the history term of m_e : originally m_l is i, the index of row m_e was constructed from
            u_dependency *m_l;
        };
        vector<eprime_pair> m_eprime;

        /* let σ be a partial mapping from variables in L united with X to linear combinations
           of variables in X and of integer constants showing the substitutions
        */
        u_map<term_o> m_sigma;
        
    public:
        int_solver& lia;
        lar_solver& lra;
        explanation m_infeas_explanation;

        // we start assigning with UINT_MAX and go down, print it as l(UINT_MAX - m_last_fresh_x_var)
        unsigned  m_last_fresh_x_var;
        bool m_report_branch = false;

        // set F
        std::list<unsigned> m_f;  // F = {λ(t):t in m_f}
        // set S
        std::list<unsigned> m_s;     // S = {λ(t): t in m_s}
        vector<unsigned> m_k2s; // k is substituted by using equation in m_eprime[m_k2s[k].first] and m_k2s[k].second  
        // gives the order of substitution
        
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
            m_last_fresh_x_var = lra.column_count();
            m_report_branch = false;
            unsigned n_of_rows = lra.A_r().row_count();
            m_k2s.clear();
            m_k2s.resize(lra.column_count(), -1);
            m_conflict_index = -1;
            m_infeas_explanation.clear();
            lia.get_term().clear();

            auto all_vars_are_int_and_small = [this](const auto& row) {
                for (const auto& p : row) {
                    if (!lia.column_is_int(p.var())) {
                        return false;
                    }
                    if (p.coeff().is_big())
                        return false;
                }
                return true;
            };
            for (unsigned i = 0; i < n_of_rows; i++) {
                auto & row = lra.get_row(i);
                TRACE("dioph_eq", tout << "row "<< i <<":"; lia.display_row_info(tout, i) << "\n";);
                if (!all_vars_are_int_and_small(row)) {
                    TRACE("dioph_eq", tout << "not all vars are int and small\n";);
                    continue;
                }
                term_o t = row_to_term(row);
                TRACE("dioph_eq", tout << "row = "; lra.print_row(row, tout) << std::endl;);
                if (t.size() == 0) {
                    SASSERT(t.c().is_zero());
                    continue;
                }
                // eprime_pair pair = {t, lar_term(i)};
                eprime_pair pair = {t, get_dep_from_row(row)};
                m_f.push_back(static_cast<unsigned>(m_f.size()));
                m_eprime.push_back(pair);
                TRACE("dioph_eq", print_eprime_entry(static_cast<unsigned>(m_f.size()) - 1, tout););
            }

        }

        // look only at the fixed columns
        u_dependency * get_dep_from_row(const row_strip<mpq>& row) {
            u_dependency* dep = nullptr;
            for (const auto & p: row) {
                if (!lia.is_fixed(p.var())) continue;
                u_dependency * bound_dep = lra.get_bound_constraint_witnesses_for_column(p.var());
                dep = lra.mk_join(dep, bound_dep);
            }
            return dep;
        }

        mpq gcd_of_coeffs(const term_o& t) {
            mpq g(0);
            for (const auto & p : t) {
                if (g.is_zero())
                    g = abs(p.coeff());
                else
                    g = gcd(g, p.coeff());
                if (g.is_one()) break;
            }
            return g;
        }
        std::ostream & print_dep(std::ostream& out, u_dependency* dep) {
            explanation ex(lra.flatten(dep));
            return lra.print_expl(out, ex);
        }

        std::string var_str(unsigned j) {
            return std::string(is_fresh_var(j)? "~":"") + std::to_string(j);
        }

        bool has_fresh_var(const term_o & t) const {
            for (const auto & p: t) {
                if (is_fresh_var(p.j()))
                    return true;
            }
            return false;
        }

        void prepare_lia_branch_report(const term_o & e, const mpq& g, const mpq new_c) {
            /* We have ep.m_e/g = 0, or sum((coff_i/g)*x_i) + new_c = 0,
               or sum((coeff_i/g)*x_i) = -new_c, where new_c is not an integer
               Then sum((coeff_i/g)*x_i) <= floor(-new_c) or sum((coeff_i/g)*x_i) >= ceil(-new_c)
            */
            lar_term& t = lia.get_term();
            for (const auto& p: e) {
                t.add_monomial(p.coeff()/g, p.j());
            }
            lia.offset() = floor(-new_c);
            lia.is_upper() = true;
            m_report_branch = true;
            TRACE("dioph_eq", tout << "prepare branch:"; print_lar_term_L(t, tout) << " <= " << lia.offset() << std::endl;);
        }
        
        // returns true if no conflict is found and false otherwise
        // this function devides all cooficients, and the free constant, of the ep.m_e  by the gcd of all coefficients,  
        // it is needed by the next steps
        // the conflict can be used to report "cuts from proofs"
        bool normalize_e_by_gcd(eprime_pair& ep) {
            TRACE("dioph_eq", print_eprime_entry(ep, tout) << std::endl;);
            mpq g = gcd_of_coeffs(ep.m_e);
            if (g.is_zero() || g.is_one()) {
                SASSERT(g.is_one() || ep.m_e.c().is_zero());
                return true;
            }
            TRACE("dioph_eq", tout << "g:" << g << std::endl;);
            mpq c_g = ep.m_e.c() / g;
            if (c_g.is_int()) {
                for (auto& p: ep.m_e.coeffs()) {
                    p.m_value /= g;
                }
                ep.m_e.c() = c_g;
                // ep.m_l *= (1/g);
                TRACE("dioph_eq",  tout << "ep_m_e:"; print_eprime_entry(ep, tout) << std::endl;);
                return true;
            }
            // c_g is not integral
            if (lra.settings().stats().m_dio_conflicts % lra.settings().dio_cut_from_proof_period() == 0 &&
                !has_fresh_var(ep.m_e))
                prepare_lia_branch_report(ep.m_e, g, c_g);
            return false;

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

        void init_term_from_constraint(term_o& t, const lar_base_constraint& c) {
            for (const auto& p: c.coeffs()) {
                t.add_monomial(p.first, p.second);
            }
            t.c() = - c.rhs();
        }

        // We look at term e.m_e: it is in form (+-)x_k + sum {a_i*x_i} + c = 0.
        // We substitute x_k in t by (+-)coeff*(sum {a_i*x_i} + c), where coeff is the coefficient of x_k in t.

        void substitute_k_with_S_entry_for_tigthening(const eprime_pair& e, unsigned k, term_o& t, std::queue<unsigned> & q) {
            SASSERT (t.contains(k) && e.m_e.contains(k));
            mpq coeff = t.get_coeff(k); // need to copy it because the pointer value can be changed during the next loop
            const mpq& k_coeff_in_e = e.m_e.get_coeff(k);
            bool is_one = k_coeff_in_e.is_one();
            SASSERT(is_one || k_coeff_in_e.is_minus_one());
            t.erase_var(k);
            if (is_one) {
                coeff = -coeff;
            }
            for (const auto& p: e.m_e) {
                if (p.j() == k) continue;
                t.add_monomial(coeff*p.coeff(), p.j());
            }
            t.c() += coeff*e.m_e.c();
            TRACE("dioph_eq", tout << "after subs_k\n"; print_term_o(t, tout) << std::endl;);
            for (const auto& p: t) {
                if (is_fresh_var(p.j())) {
                    continue;
                }
                if (m_k2s[p.j()] != null_lpvar)
                    q.push(p.j());
            }

        }

        const eprime_pair& k_th_entry(unsigned k) const {
            return m_eprime[m_k2s[k]];
        }

        const unsigned sub_index(unsigned k) const {
            return m_k2s[k];
        }
        
        void substitude_term_on_q_with_S_for_tightening(std::queue<unsigned> &q, term_o& t, u_dependency* &dep) {
           TRACE("dioph_eq_dep", tout << "dep:"; print_dep(tout, dep) << std::endl;);
            while (!q.empty()) {
                unsigned k = q.front();
                q.pop();
                const eprime_pair& e = k_th_entry(k);
                if (!t.contains(k)) {
                    continue;
                }
                TRACE("dioph_eq", tout << "k:" << k << " in: "; print_eprime_entry(sub_index(k), tout) << std::endl;);
                substitute_k_with_S_entry_for_tigthening(e, k, t, q);
                
                TRACE("dioph_eq", print_queue(q, tout););
                
                dep = lra.mk_join(dep, e.m_l);
                TRACE("dioph_eq", tout << "substituted t:"; print_term_o(t, tout) << std::endl;
                tout << "\ndep:"; print_dep(tout, dep) << std::endl;);
            }
        }


        lia_move tighten_with_S() {
             // Following the pattern of int_cube, but do not push/pop the state. Instead, we keep the new bounds.
            int change = 0;
            for (unsigned j = 0; j < lra.column_count(); j++) {
                if (!lra.column_has_term(j) || lra.column_is_free(j) ||
                    lra.column_is_fixed(j) || !lia.column_is_int(j)) continue;
                if (tighten_bounds_for_column(j)) {
                    change++;
                }
                if (!m_infeas_explanation.empty()) {
                    return lia_move::conflict;
                }   
            }
            if (!change)
                return lia_move::undef;
            auto st = lra.find_feasible_solution();
            if (st != lp::lp_status::FEASIBLE && st != lp::lp_status::OPTIMAL) {
                lra.get_infeasibility_explanation(m_infeas_explanation);
                return lia_move::conflict;
            }
            return lia_move::undef;
        }

        std::ostream& print_queue(std::queue<unsigned> q, std::ostream& out) {
            out << "qu: ";
            while (!q.empty()) {
                out << q.front() << " ";
                q.pop();
            }   
            out<< std::endl;
            return out;
        }   
        // j is the index of the column representing a term
        // return true if there is a change
        bool tighten_bounds_for_column(unsigned j) {
            TRACE("dioph_eq", tout << "j:"; tout << j << std::endl;);
            const lar_term& lar_t = lra.get_term(j);
            TRACE("dioph_eq", tout << "tighten_term_for_S: "; print_lar_term_L(lar_t, tout) << std::endl;);
            // create a copy: t is a copy of lar_t
            term_o t;
            std::queue<unsigned> q;
            for (const auto& p: lar_t) {
                if (sub_index(p.j()) != null_lpvar)
                    q.push(p.j());
                t.add_monomial(p.coeff(), p.j());
            }
            u_dependency * dep = nullptr;
        
            TRACE("dioph_eq", tout << "t:"; print_term_o(t, tout) << std::endl;
            /*tout << "dep:"; print_dep(tout, dep) << std::endl;*/);
            substitude_term_on_q_with_S_for_tightening(q, t, dep);
            TRACE("dioph_eq", tout << "after process_q_with_S\n t:"; print_term_o(t, tout) << std::endl;
                  tout << "dep:"; print_dep(tout, dep) << std::endl;);
            mpq g = gcd_of_coeffs(t);
            if (g.is_one()) {
                TRACE("dioph_eq", tout << "g is one" << std::endl;);
                return false;
            } else if (g.is_zero()) {
                handle_constant_term(t, j, dep);
                if (!m_infeas_explanation.empty())
                     return true;
                return false;
            } 
            
            return tighten_bounds_for_term(t, g, j, dep);
        }
        void handle_constant_term(term_o& t, unsigned j, u_dependency* dep) {
            if (t.c().is_zero()) {
                return;
            }
            mpq rs;
            bool is_strict;
            u_dependency *b_dep = nullptr;
            if (lra.has_upper_bound(j, b_dep, rs, is_strict)) {
                if (t.c() > rs || (is_strict && t.c() == rs)) {
                    for (const auto& p: lra.flatten(dep)) {
                        m_infeas_explanation.push_back(p);
                    }
                    for (const auto& p: lra.flatten(b_dep)) {
                        m_infeas_explanation.push_back(p);
                    }
                    return;
                }
            }
            if (lra.has_lower_bound(j, b_dep, rs, is_strict)) {
                if (t.c() < rs || (is_strict && t.c() == rs)) {
                    for (const auto& p: lra.flatten(dep)) {
                        m_infeas_explanation.push_back(p);
                    }
                    for (const auto& p: lra.flatten(b_dep)) {
                        m_infeas_explanation.push_back(p);
                    }
                }
            }
        }
        // returns true if there is a change
        // dep comes from the substitution with S
        bool tighten_bounds_for_term(term_o& t, const mpq& g, unsigned j, u_dependency* dep) {
            mpq rs;
            bool is_strict;
            bool change = false;
            u_dependency *b_dep = nullptr;
            SASSERT(!g.is_zero());

            if (lra.has_upper_bound(j, b_dep, rs, is_strict)) {
                TRACE("dioph_eq", tout << "tighten upper bound for x" << j << " with rs:" << rs << std::endl;);
                rs = (rs - t.c()) / g;
                TRACE("dioph_eq", tout << "tighten upper bound for x" << j << " with rs:" << rs << std::endl;);

                if (!rs.is_int()) {
                    tighten_bound_for_term_for_bound_kind(t, g, j, lra.mk_join(dep, b_dep), rs, true);
                    change = true;
                }
            }
            if (lra.has_lower_bound(j, b_dep, rs, is_strict)) {
                TRACE("dioph_eq", tout << "tighten lower bound for x" << j << " with rs:" << rs << std::endl;);
                rs = (rs - t.c()) / g;

                TRACE("dioph_eq", tout << "tighten lower bound for x" << j << " with rs:" << rs << std::endl;);

                if (!rs.is_int()) {
                    tighten_bound_for_term_for_bound_kind(t, g, j, lra.mk_join(b_dep, dep), rs, false);
                    change = true;
                }
            }
            return change;
        }

        void tighten_bound_for_term_for_bound_kind(term_o& t,
                                         const mpq& g, unsigned j, u_dependency* dep, const mpq & ub, bool upper) {
            // ub = (upper_bound(j) - t.c())/g.
            // we have x[j] = t = g*t_+ t.c() <= upper_bound(j), then
            // t_ <= floor((upper_bound(j) - t.c())/g) = floor(ub)
            //
            // so xj = g*t_+t.c() <= g*floor(ub) + t.c() is new upper bound
            // <= can be replaced with >= for lower bounds, with ceil instead of floor
            mpq bound = g * (upper?floor(ub):ceil(ub))+t.c();
            TRACE("dioph_eq", tout << "upper:" << upper << std::endl;
                  tout << "new " << (upper? "upper":"lower" ) <<  "bound:" << bound << std::endl;);
            
            dep = lra.mk_join(dep, upper? lra.get_column_upper_bound_witness(j): lra.get_column_lower_bound_witness(j) );
            SASSERT(upper && bound <= lra.get_upper_bound(j).x || !upper && bound >= lra.get_lower_bound(j).x);
            lconstraint_kind kind = upper? lconstraint_kind::LE: lconstraint_kind::GE;
            lra.update_column_type_and_bound(j, kind, bound, dep);
            TRACE("dioph_eq",
                tout << "new " << (upper? "upper":"lower" ) <<  "bound:" << bound << std::endl;
                tout << "bound_dep:\n";print_dep(tout, dep) << std::endl;);
        }

        lia_move check() {            
            init();
            while(m_f.size()) {
                if (!normalize_by_gcd()) {
                    lra.settings().stats().m_dio_conflicts++;
                    if (m_report_branch) {
                        m_report_branch = false;
                        return lia_move::branch;
                    }
                    return lia_move::conflict;
                }
                rewrite_eqs();
            }
            TRACE("dioph_eq", print_S(tout););
            lia_move ret = tighten_with_S();
            if (ret == lia_move::conflict) {
                lra.settings().stats().m_dio_conflicts++;
                return lia_move::conflict;
            }
            return lia_move::undef;
        }
        
        std::list<unsigned>::iterator pick_eh() {
            return m_f.begin(); // TODO: make a smarter joice
        }

        void add_operator(lar_term& t, const mpq& k, const lar_term& l) {
            for (const auto& p: l) {
                t.add_monomial(k*p.coeff(), p.j());
            }
        }

        void substitute_var_on_f(unsigned k, int k_sign, const term_o& k_subst, u_dependency * dep, unsigned index_to_avoid)  {
            TRACE("dioph_eq", print_term_o(k_subst, tout<< "x" << k<< " -> ") << std::endl; tout << "dep:"; print_dep(tout, dep) << std::endl;);
            for (unsigned e_index: m_f) {
                if (e_index == index_to_avoid) continue;
                term_o& e = m_eprime[e_index].m_e;
                if (!e.contains(k)) continue;

                TRACE("dioph_eq", print_eprime_entry(e_index, tout << "before:") << std::endl;
                      tout << "k_coeff:" << e.get_coeff(k) << std::endl;);

/*
                if (!l_term.is_empty()) {
                    if (k_sign == 1)
                        add_operator(m_eprime[e_index].m_l, -k_coeff, l_term);
                    else
                        add_operator(m_eprime[e_index].m_l, k_coeff, l_term);
                }
*/
                m_eprime[e_index].m_l = lra.mk_join(dep, m_eprime[e_index].m_l);
                e.substitute_var_with_term(k_subst, k);
                TRACE("dioph_eq", print_eprime_entry(e_index, tout << "after :") << std::endl;);
            }
        }

        std::tuple<mpq, unsigned, int> find_minimal_abs_coeff(const term_o& eh) const {
            bool first = true, first_fresh = true;
            mpq ahk, ahk_fresh;
            unsigned k, k_fresh;
            int k_sign, k_sign_fresh;
            mpq t;
            for (const auto& p : eh) {
                t = abs(p.coeff());
                if (first_fresh || t < ahk_fresh) {
                    ahk_fresh = t;
                    k_sign_fresh = p.coeff().is_pos() ? 1 : -1;
                    k_fresh = p.j();
                    first_fresh = false;
                } else if (first || t < ahk) { 
                    ahk = t;
                    k_sign = p.coeff().is_pos() ? 1 : -1;
                    k = p.j();
                    first = false;
                    if (ahk.is_one())
                        break;
                    
                }
            }
            if (first_fresh) // did not find any fresh variables
                return std::make_tuple(ahk, k, k_sign);
            if (first) // only fresh vars
                return std::make_tuple(ahk_fresh, k_fresh, k_sign_fresh);
            SASSERT(!first && !first_fresh);
            if (ahk <= ahk_fresh) {
                return std::make_tuple(ahk, k, k_sign);
            }
            return std::make_tuple(ahk_fresh, k_fresh, k_sign_fresh);
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
            unsigned xt = m_last_fresh_x_var++;
            TRACE("dioph_eq", tout << "introduce fresh xt:" << "x"<< var_str(xt) << std::endl;
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
	    // eprime_pair xt_entry = {xt_term, lar_term()};  // 0 for m_l field
            eprime_pair xt_entry = {xt_term, nullptr};  // nullptr for the dependency
            m_eprime.push_back(xt_entry);
            TRACE("dioph_eq", tout << "xt_term:"; print_term_o(xt_term, tout) << std::endl;
                  tout << "k_subs:"; print_term_o(k_subs, tout) << std::endl;
                  print_eprime_entry(m_eprime.size()-1, tout););
            substitute_var_on_f(k, 1, k_subs, xt_entry.m_l, e_index);

            // the term to eliminate the fresh variable
            term_o xt_subs = xt_term.clone();
            xt_subs.add_monomial(mpq(1), xt);
            TRACE("dioph_eq", tout << "xt_subs: x"<< var_str(xt) << " -> ";  print_term_o(xt_subs, tout) << std::endl;);
            m_sigma.insert(xt, xt_subs);
        }

        std::ostream& print_eprime_entry(unsigned i, std::ostream& out) {
            out << "m_eprime[" << i << "]:";
            return print_eprime_entry(m_eprime[i], out);
        }

        std::ostream& print_eprime_entry(const eprime_pair& e, std::ostream& out) {
            out << "{\n";
            print_term_o(e.m_e, out << "\tm_e:") << "," << std::endl;
            print_dep(out<< "\tm_l:", e.m_l) << "\n";
            out << "}"<< std::endl;
            return out;
        }

        // k is the index of the index of the variable with the coefficient +-1 that is being substituted
        void move_entry_from_f_to_s(unsigned k, std::list<unsigned>::iterator it) {
            if (k >= m_k2s.size()) { // k is a fresh variable
                m_k2s.resize(k+1, -1 );
            }
            m_s.push_back(*it);
            TRACE("dioph_eq", tout << "removed " << *it << "th entry from F" << std::endl;);
            m_k2s[k] = *it;
            m_f.erase(it);
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
                move_entry_from_f_to_s(k, eh_it);
                eliminate_var_in_f(eprime_entry, k , k_sign);
            } else {
                fresh_var_step(*eh_it, k);
            }
        }

        void explain(explanation& ex) {
            if (m_conflict_index == UINT_MAX) {
                SASSERT(!(lra.get_status() == lp_status::FEASIBLE || lra.get_status() == lp_status::OPTIMAL));
                for (auto ci: m_infeas_explanation) {
                    ex.push_back(ci.ci());
                }
                return;
            }
            SASSERT(ex.empty());
            TRACE("dioph_eq", tout << "conflict:"; print_eprime_entry(m_conflict_index, tout) << std::endl;);
            auto & ep = m_eprime[m_conflict_index];
            /*
              for (const auto & pl : ep.m_l) {
              unsigned row_index = pl.j();
              for (const auto & p : lra.get_row(row_index))
              if (lra.column_is_fixed(p.var()))
              lra.explain_fixed_column(p.var(), ex);
              }
            */
            for (auto ci: lra.flatten(ep.m_l)) {
                ex.push_back(ci);
            }
            TRACE("dioph_eq", lra.print_expl(tout, ex););
        }

        bool is_fresh_var(unsigned j) const {
            return j >= lra.column_count();
        }
    };
// Constructor definition
    dioph_eq::dioph_eq(int_solver& lia) {
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
