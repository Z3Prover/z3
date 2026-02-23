/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    nlsat_explain.cpp

Abstract:

    Functor that implements the "explain" procedure defined in Dejan and Leo's paper.

Author:

    Leonardo de Moura (leonardo) 2012-01-13.

Revision History:

--*/
#include "nlsat/nlsat_explain.h"
#include "nlsat/levelwise.h"
#include "nlsat/nlsat_assignment.h"
#include "nlsat/nlsat_evaluator.h"
#include "math/polynomial/algebraic_numbers.h"
#include "nlsat/nlsat_common.h"
#include "util/ref_buffer.h"
#include "util/mpq.h"

namespace nlsat {

    struct add_all_coeffs_restart {};

    typedef polynomial::polynomial_ref_vector polynomial_ref_vector;
    typedef ref_buffer<poly, pmanager> polynomial_ref_buffer;

    struct explain::imp {
        solver &                m_solver;
        atom_vector const &     m_atoms;
        atom_vector const &     m_x2eq;
        anum_manager &          m_am;
        polynomial::cache &     m_cache;
        pmanager &              m_pm;
        polynomial_ref_vector   m_ps;
        polynomial_ref_vector   m_ps2;
        polynomial_ref_vector   m_psc_tmp;
        polynomial_ref_vector   m_factors, m_factors_save;
        scoped_anum_vector      m_roots_tmp;
        bool                    m_simplify_cores;
        bool                    m_full_dimensional;
        bool                    m_minimize_cores;
        bool                    m_factor;
        bool                    m_add_all_coeffs;
        bool                    m_add_zero_disc;

        assignment const &      sample() const { return m_solver.sample(); }
        assignment &            sample() { return m_solver.sample(); }

        // temporary field for store todo set of polynomials
        todo_set                m_todo;
        
        // Track polynomials already processed in current projection to avoid cycles
        todo_set                m_todo_extracted;

        // temporary fields for preprocessing core
        scoped_literal_vector   m_core1;
        scoped_literal_vector   m_core2;
        
        // Lower-stage polynomials encountered during normalization that need to be projected
        polynomial_ref_vector   m_lower_stage_polys;
        
        // Store last levelwise input for debugging unsound lemmas
        polynomial_ref_vector   m_last_lws_input_polys;

        // temporary fields for storing the result
        scoped_literal_vector * m_result = nullptr;
        svector<char>           m_already_added_literal;

        evaluator &             m_evaluator;

        imp(solver & s, assignment const & x2v, polynomial::cache & u, atom_vector const & atoms, atom_vector const & x2eq,
            evaluator & ev, bool canonicalize):
            m_solver(s),
            m_atoms(atoms),
            m_x2eq(x2eq),
            m_am(x2v.am()),
            m_cache(u), 
            m_pm(u.pm()),
            m_ps(m_pm),
            m_ps2(m_pm),
            m_psc_tmp(m_pm),
            m_factors(m_pm),
            m_factors_save(m_pm),
            m_roots_tmp(m_am),
            m_todo(u, canonicalize),
            m_todo_extracted(u, canonicalize),
            m_core1(s),
            m_core2(s),
            m_lower_stage_polys(m_pm),
            m_last_lws_input_polys(m_pm),
            m_evaluator(ev) {
            m_simplify_cores   = false;
            m_full_dimensional = false;
            m_minimize_cores   = false;
            m_add_all_coeffs   = false;
            m_add_zero_disc    = false;
        }

    // display helpers moved to free functions in nlsat_common.h


        /**
           \brief Add literal to the result vector.
        */
        void add_literal(literal l) {
            SASSERT(m_result != 0);
            SASSERT(l != true_literal); 
            if (l == false_literal)
                return;
            unsigned lidx = l.index();
            if (m_already_added_literal.get(lidx, false))
                return;
            TRACE(nlsat_explain, tout << "adding literal: " << lidx << "\n"; m_solver.display(tout, l) << "\n";);
            m_already_added_literal.setx(lidx, true, false);
            m_result->push_back(l);
        }

        /**
           \brief Reset m_already_added vector using m_result
         */
        void reset_already_added() {
            SASSERT(m_result != nullptr);
            for (literal lit : *m_result) 
                m_already_added_literal[lit.index()] = false;
            SASSERT(check_already_added());
        }

        
        /**
           \brief Wrapper for psc chain computation
        */
        void psc_chain(polynomial_ref & p, polynomial_ref & q, unsigned x, polynomial_ref_vector & result) {
            // TODO caching
            SASSERT(max_var(p) == max_var(q));
            SASSERT(max_var(p) == x);
            m_cache.psc_chain(p, q, x, result);
        }
        
        /**
           \brief Store in ps the polynomials occurring in the given literals.
        */
        void collect_polys(unsigned num, literal const * ls, polynomial_ref_vector & ps) {
            ps.reset();
            for (unsigned i = 0; i < num; ++i) {
                atom * a = m_atoms[ls[i].var()];
                SASSERT(a != 0);
                if (a->is_ineq_atom()) {
                    unsigned sz = to_ineq_atom(a)->size();
                    for (unsigned j = 0; j < sz; ++j)
                        ps.push_back(to_ineq_atom(a)->p(j));
                }
                else {
                    ps.push_back(to_root_atom(a)->p());
                }
            }
        }

        /**
           \brief Add literal p != 0 into m_result.
        */
        ptr_vector<poly>  m_zero_fs;
        bool_vector     m_is_even;
        struct restore_factors {
            polynomial_ref_vector&   m_factors, &m_factors_save;
            unsigned num_saved = 0;
            restore_factors(polynomial_ref_vector&f, polynomial_ref_vector& fs):
                m_factors(f), m_factors_save(fs)
            {
                num_saved = m_factors_save.size();
                m_factors_save.append(m_factors);
            }

            ~restore_factors() {
                m_factors.reset();
                m_factors.append(m_factors_save.size() - num_saved, m_factors_save.data() + num_saved);
                m_factors_save.shrink(num_saved);
            }
            
        };

        struct cell_root_info {
            polynomial_ref m_eq;
            polynomial_ref m_lower;
            polynomial_ref m_upper;
            unsigned       m_eq_idx;
            unsigned       m_lower_idx;
            unsigned       m_upper_idx;
            bool           m_has_eq;
            bool           m_has_lower;
            bool           m_has_upper;
            cell_root_info(pmanager & pm): m_eq(pm), m_lower(pm), m_upper(pm) {
                reset();
            }
            void reset() {
                m_eq = nullptr;
                m_lower = nullptr;
                m_upper = nullptr;
                m_eq_idx = m_lower_idx = m_upper_idx = UINT_MAX;
                m_has_eq = m_has_lower = m_has_upper = false;
            }
        };

        void find_cell_roots(polynomial_ref_vector & ps, var y, cell_root_info & info) {
            info.reset();
            SASSERT(m_solver.sample().is_assigned(y));
            bool lower_inf = true;
            bool upper_inf = true;
            scoped_anum_vector & roots = m_roots_tmp;
            scoped_anum lower(m_am);
            scoped_anum upper(m_am);
            anum const & y_val = m_solver.sample().value(y);
            TRACE(nlsat_explain, tout << "adding literals for "; m_solver.display_var(tout, y); tout << " -> ";
                  m_am.display_decimal(tout, y_val); tout << "\n";);
            polynomial_ref p(m_pm);
            unsigned sz = ps.size();
            for (unsigned k = 0; k < sz; ++k) {
                p = ps.get(k);
                if (max_var(p) != y)
                    continue;
                roots.reset();
                // Variable y is assigned in m_solver.sample(). We must temporarily unassign it.
                // Otherwise, the isolate_roots procedure will assume p is a constant polynomial.
                m_am.isolate_roots(p, undef_var_assignment(m_solver.sample(), y), roots);
                unsigned num_roots = roots.size();
                TRACE(nlsat_explain,
                      tout << "isolated roots for "; m_solver.display_var(tout, y);
                      tout << " with polynomial: " << p << "\n";
                      for (unsigned ri = 0; ri < num_roots; ++ri) {
                          m_am.display_decimal(tout << "  root[" << (ri+1) << "] = ", roots[ri]);
                          tout << "\n";
                      });
                bool all_lt = true;
                for (unsigned i = 0; i < num_roots; ++i) {
                    int s = m_am.compare(y_val, roots[i]);
                    TRACE(nlsat_explain,
                          m_am.display_decimal(tout << "comparing root: ", roots[i]); tout << "\n";
                          m_am.display_decimal(tout << "with y_val:", y_val);
                          tout << "\nsign " << s << "\n";
                          tout << "poly: " << p << "\n";
                          );
                    if (s == 0) {
                        info.m_eq = p;
                        info.m_eq_idx = i + 1;
                        info.m_has_eq = true;
                        return;
                    }
                    else if (s < 0) {
                        if (i > 0) {
                            int j = i - 1;
                            if (lower_inf || m_am.lt(lower, roots[j])) {
                                lower_inf = false;
                                m_am.set(lower, roots[j]);
                                info.m_lower = p;
                                info.m_lower_idx = j + 1;
                            }
                        }
                        if (upper_inf || m_am.lt(roots[i], upper)) {
                            upper_inf = false;
                            m_am.set(upper, roots[i]);
                            info.m_upper = p;
                            info.m_upper_idx = i + 1;
                        }
                        all_lt = false;
                        break;
                    }
                }
                if (all_lt && num_roots > 0) {
                    int j = num_roots - 1;
                    if (lower_inf || m_am.lt(lower, roots[j])) {
                        lower_inf = false;
                        m_am.set(lower, roots[j]);
                        info.m_lower = p;
                        info.m_lower_idx = j + 1;
                    }
                }
            }
            if (!lower_inf) {
                info.m_has_lower = true;
            }
            if (!upper_inf) {
                info.m_has_upper = true;
            }
        }

         ::sign sign(polynomial_ref const & p) {
             return ::nlsat::sign(p, m_solver.sample(), m_am);
        }
        
        
        void add_zero_assumption(polynomial_ref& p) {
            // Build a square-free representative of p so that we can speak about
            // a specific root that coincides with the current assignment.
            polynomial_ref q(m_pm);
            m_pm.square_free(p, q);
            if (is_zero(q) || is_const(q)) {
                SASSERT(!sign(q));
                TRACE(nlsat_explain, tout << "cannot form zero assumption from constant polynomial " << q << "\n";);
                return;
            }
            var maxx = max_var(q);
            SASSERT(maxx != null_var);
            if (maxx == null_var)
                return;
            SASSERT(m_solver.sample().is_assigned(maxx));
            
            polynomial_ref_vector singleton(m_pm);
            singleton.push_back(q);
            cell_root_info info(m_pm);
            find_cell_roots(singleton, maxx, info);
            if (!info.m_has_eq)
                return; // there are no root functions and therefore no constraints are generated

            TRACE(nlsat_explain,
                  tout << "adding zero-assumption root literal for ";
                  m_solver.display_var(tout, maxx); tout << " using root[" << info.m_eq_idx << "] of " << q << "\n";);
            add_root_literal(atom::ROOT_EQ, maxx, info.m_eq_idx, info.m_eq);
        }

        void add_assumption(atom::kind k, poly * p, bool sign = false) {
            SASSERT(k == atom::EQ || k == atom::LT || k == atom::GT);
            bool is_even = false;
            bool_var b = m_solver.mk_ineq_atom(k, 1, &p, &is_even);
            literal l(b, !sign);
            add_literal(l);
        }

        
        /**
           \brief Eliminate "vanishing leading coefficients" of p.
           That is, coefficients that vanish in the current
           interpretation.  The resultant p is a reduct of p s.t. its
           leading coefficient does not vanish in the current
           interpretation. If all coefficients of p vanish, then 
           the resultant p is the zero polynomial.
        */
        void elim_vanishing(polynomial_ref & p) {
            SASSERT(!is_const(p));
            var x = max_var(p);
            unsigned k = degree(p, x);
            SASSERT(k > 0);
            polynomial_ref lc(m_pm);
            polynomial_ref reduct(m_pm);
            while (true) {
                if (is_const(p))
                    return;
                if (k == 0) {
                    // x vanished from p, peek next maximal variable
                    x = max_var(p);
                    SASSERT(x != null_var);
                    k = degree(p, x);
                }
                if (m_pm.nonzero_const_coeff(p, x, k)) {
                    TRACE(nlsat_explain, tout << "nonzero const x" << x << "\n";);
                    return; // lc is a nonzero constant
                }
                lc = m_pm.coeff(p, x, k, reduct);
                TRACE(nlsat_explain, tout << "lc: " << lc << " reduct: " << reduct << "\n";);
                insert_fresh_factors_in_todo(lc);
                if (!is_zero(lc) && sign(lc)) {
                    TRACE(nlsat_explain, tout << "lc does no vaninsh\n";);
                    return;
                }
                if (k == 0) {
                    // all coefficients of p vanished in the current interpretation,
                    // and were added as assumptions.
                    p = m_pm.mk_zero();
                    TRACE(nlsat_explain, tout << "all coefficients of p vanished\n";);
                    if (m_add_all_coeffs) {
                        add_zero_assumption(lc);
                        return;
                    }
                    TRACE(nlsat_explain, tout << "falling back to add-all-coeffs projection\n";);
                    m_add_all_coeffs = true;
                    throw add_all_coeffs_restart();
                }
                add_zero_assumption(lc);
                k--;
                p = reduct;
            }
        }
        
        /**
           Eliminate vanishing coefficients of polynomials in ps.
           The coefficients that are zero (i.e., vanished) are added 
           as assumptions into m_result.
        */
        void elim_vanishing(polynomial_ref_vector & ps) {
            unsigned j  = 0;
            unsigned sz = ps.size(); 
            polynomial_ref p(m_pm);
            for (unsigned i = 0; i < sz; ++i) {
                p = ps.get(i);
                elim_vanishing(p);
                if (!is_const(p)) {
                    ps.set(j, p);
                    j++;
                }
            }
            ps.shrink(j);
        }

        /**
           Normalize literal with respect to given maximal variable.
           The basic idea is to eliminate vanishing (leading) coefficients from a (arithmetic) literal,
           and factors from lower stages. 
           
           The vanishing coefficients and factors from lower stages are added as assumptions to the lemma
           being generated.
           
           Example 1) 
           Assume 
              - l is of the form  (y^2 - 2)*x^3 + y*x + 1 > 0 
              - x is the maximal variable
              - y is assigned to sqrt(2)
           Thus, (y^2 - 2) the coefficient of x^3 vanished. This method returns
           y*x + 1 > 0 and adds the assumption (y^2 - 2) = 0 to the lemma

           Example 2)
           Assume
              - l is of the form (x + 2)*(y - 1) > 0
              - x is the maximal variable
              - y is assigned to 0
           (x + 2) < 0 is returned and assumption (y - 1) < 0 is added as an assumption.   

           Remark: root atoms are not normalized
        */
        literal normalize(literal l, var max) {
            TRACE(nlsat_explain, display(tout << "l:", m_solver, l) << '\n';);
            bool_var b = l.var();
            if (b == true_bool_var)
                return l;
            SASSERT(m_atoms[b] != 0);
            if (m_atoms[b]->is_ineq_atom()) {
                polynomial_ref_buffer ps(m_pm);
                sbuffer<bool>         is_even;
                polynomial_ref p(m_pm);
                ineq_atom * a  = to_ineq_atom(m_atoms[b]);
                int atom_sign = 1;
                unsigned sz = a->size();
                bool normalized = false; // true if the literal needs to be normalized
                for (unsigned i = 0; i < sz; ++i) {
                    p = a->p(i);
                    if (max_var(p) == max)
                        elim_vanishing(p); // eliminate vanishing coefficients of max
                    if (is_const(p) || max_var(p) < max) {
                        int s = sign(p); 
                        if (!is_const(p)) {
                            SASSERT(max_var(p) != null_var);
                            SASSERT(max_var(p) < max);
                            // factor p is a lower stage polynomial, so we should add assumption to justify p being eliminated
                            // Also collect it for projection to ensure proper cell construction
                            m_lower_stage_polys.push_back(p);
                            if (s == 0)
                                add_assumption(atom::EQ, p);  // add assumption p = 0
                            else if (a->is_even(i))
                                add_assumption(atom::EQ, p, true); // add assumption p != 0 
                            else if (s < 0)
                                add_assumption(atom::LT, p); // add assumption p < 0
                            else
                                add_assumption(atom::GT, p); // add assumption p > 0
                        }
                        if (s == 0) {
                            bool atom_val = a->get_kind() == atom::EQ;
                            bool lit_val  = l.sign() ? !atom_val : atom_val;
                            return lit_val ? true_literal : false_literal;
                        }
                        else if (s < 0 && a->is_odd(i)) {
                            atom_sign = -atom_sign;
                        }
                        normalized = true;
                    }
                    else {
                        if (p != a->p(i)) {
                            SASSERT(!m_pm.eq(p, a->p(i)));
                            normalized = true;
                        }
                        is_even.push_back(a->is_even(i));
                        ps.push_back(p);
                    }
                }
                if (ps.empty()) {
                    SASSERT(atom_sign != 0);
                    // LHS is positive or negative. It is positive if atom_sign > 0 and negative if atom_sign < 0
                    bool atom_val;
                    if (a->get_kind() == atom::EQ)
                        atom_val = false;
                    else if (a->get_kind() == atom::LT)
                        atom_val = atom_sign < 0;
                    else 
                        atom_val = atom_sign > 0;
                    bool lit_val  = l.sign() ? !atom_val : atom_val;
                    return lit_val ? true_literal : false_literal;
                }
                else if (normalized) {
                    atom::kind new_k = a->get_kind();
                    if (atom_sign < 0)
                        new_k = atom::flip(new_k);
                    literal new_l = m_solver.mk_ineq_literal(new_k, ps.size(), ps.data(), is_even.data());
                    if (l.sign())
                        new_l.neg();
                    return new_l;
                }
                else {
                    SASSERT(atom_sign > 0);
                    return l;
                }
            }
            else {
                return l;
            }
        }

        /**
           Normalize literals (in the conflicting core) with respect
           to given maximal variable.  The basic idea is to eliminate
           vanishing (leading) coefficients (and factors from lower
           stages) from (arithmetic) literals,
        */
        void normalize(scoped_literal_vector & C, var max) {
            TRACE(nlsat_explain, display(tout << "C:\n", m_solver, C) << '\n';);
            unsigned sz = C.size();
            unsigned j  = 0;
            for (unsigned i = 0; i < sz; ++i) {
                literal new_l = normalize(C[i], max);
                if (new_l == true_literal)
                    continue;
                if (new_l == false_literal) {
                    // false literal was created. The assumptions added are sufficient for implying the conflict.
                    C.reset();
                    return;
                }
                C.set(j, new_l);
                j++;
            }
            C.shrink(j);
        }

        var max_var(poly const * p) { return m_pm.max_var(p); }

        /**
           \brief Return the maximal variable in a set of nonconstant polynomials.
        */
        var max_var(polynomial_ref_vector const & ps) {
            if (ps.empty())
                return null_var;
            var max = max_var(ps.get(0)); 
            SASSERT(max != null_var); // there are no constant polynomials in ps
            unsigned sz = ps.size();
            for (unsigned i = 1; i < sz; ++i) {
                var curr = m_pm.max_var(ps.get(i));
                SASSERT(curr != null_var);
                if (curr > max)
                    max = curr;
            }
            return max;
        }

        polynomial::var max_var(literal l) {
            atom * a  = m_atoms[l.var()];
            if (a != nullptr)
                return a->max_var();
            else
                return null_var;
        }

        /**
           \brief Return the maximal variable in the given set of literals
         */
        var max_var(unsigned sz, literal const * ls) {
            var max = null_var;
            for (unsigned i = 0; i < sz; ++i) {
                literal l = ls[i];
                atom * a  = m_atoms[l.var()];
                if (a != nullptr) {
                    var x = a->max_var();
                    SASSERT(x != null_var);
                    if (max == null_var || x > max) 
                        max = x;
                }
            }
            return max;
        }

        /**
           \brief Move the polynomials in q in ps that do not contain x to qs.
        */
        void keep_p_x(polynomial_ref_vector & ps, var x, polynomial_ref_vector & qs) {
            unsigned sz = ps.size();
            unsigned j  = 0;
            for (unsigned i = 0; i < sz; ++i) {
                poly * q = ps.get(i);
                if (max_var(q) != x) {
                    qs.push_back(q);
                }
                else {
                    ps.set(j, q);
                    j++;
                }
            }
            ps.shrink(j);
        }

        /**
           \brief Add factors of p to todo
        */
        void insert_fresh_factors_in_todo(polynomial_ref & p) {
            // Skip if already processed in this projection (prevents cycles)
            if (m_todo_extracted.contains(p))
                return;
            
            if (is_const(p))
                return;
            elim_vanishing(p);
            if (is_const(p))
                return;
            if (m_factor) {
                restore_factors _restore(m_factors, m_factors_save);
                factor(p, m_cache, m_factors);
                TRACE(nlsat_explain, display(tout << "adding factors of\n", m_solver, p); tout << "\n" << m_factors << "\n";);
                polynomial_ref f(m_pm);
                for (unsigned i = 0; i < m_factors.size(); ++i) {
                    f = m_factors.get(i);
                    elim_vanishing(f);
                    if (!is_const(f) && !m_todo_extracted.contains(f)) {
                        TRACE(nlsat_explain, tout << "adding factor:\n"; display(tout, m_solver, f); tout << "\n";);
                        m_todo.insert(f);
                    }
                }
            }
            else {
                m_todo.insert(p);
            }
        }

        
     	// If each p from ps is square-free then add the leading coefficents to the projection. 
	// Otherwise, add each coefficient of each p to the projection.
        void add_lcs(polynomial_ref_vector &ps, var x) {
            polynomial_ref p(m_pm);
            polynomial_ref coeff(m_pm);

            // Add the leading or all coeffs, depening on being square-free
            for (unsigned i = 0; i < ps.size(); ++i) {
                p = ps.get(i);
                unsigned k_deg = m_pm.degree(p, x);
                if (k_deg == 0) continue;
                // p depends on x
                TRACE(nlsat_explain, tout << "processing poly of degree " << k_deg << " w.r.t x" << x << ": "; m_solver.display(tout, p) << "\n";);
                for (int j_coeff_deg = k_deg; j_coeff_deg >= 0; j_coeff_deg--) { 
                    coeff = m_pm.coeff(p, x, j_coeff_deg);
                    TRACE(nlsat_explain, tout << "    coeff deg " << j_coeff_deg << ": "; display(tout, m_solver, coeff) << "\n";);
                    insert_fresh_factors_in_todo(coeff);
                    if (!m_add_all_coeffs)
                        break;
                }
            }
        }

        void psc_resultant_sample(polynomial_ref_vector &ps, var x, polynomial_ref_vector & samples){
            polynomial_ref p(m_pm);
            polynomial_ref q(m_pm);
            SASSERT(samples.size() <= 2);

            for (unsigned i = 0; i < ps.size(); ++i){
                p = ps.get(i);
                for (unsigned j = 0; j < samples.size(); ++j){
                    q = samples.get(j);
                    if (!m_pm.eq(p, q)) {
                        psc(p, q, x);
                    }
                }
            }
        }
        
        // this function also explains the value 0, if met
        bool coeffs_are_zeroes(polynomial_ref &s) {
            restore_factors _restore(m_factors, m_factors_save);
            factor(s, m_cache, m_factors);
            unsigned num_factors = m_factors.size();
            m_zero_fs.reset();
            m_is_even.reset();
            polynomial_ref f(m_pm);
            bool have_zero = false;
            for (unsigned i = 0; i < num_factors; ++i) {
                f = m_factors.get(i);
                if (coeffs_are_zeroes_on_sample(f,  m_pm, sample(), m_am)) {
                    have_zero = true;
                    break;
                } 
            }
            if (!have_zero)
                return false;
            var x = max_var(f);
            unsigned n = degree(f, x);
            auto c = polynomial_ref(this->m_pm);
            for (unsigned j = 0; j <= n; ++j) {
                c = m_pm.coeff(s, x, j);
                SASSERT(sign(c) == 0);
                ensure_sign(c);
            }
            return true;
        }
    

        bool coeffs_are_zeroes_in_factor(polynomial_ref & s) {
            var x = max_var(s);
            unsigned n = degree(s, x);
            auto c = polynomial_ref(this->m_pm);
            for (unsigned j = 0; j <= n; ++j) {
                c = m_pm.coeff(s, x, j);
                if (nlsat::sign(c, sample(), m_am) != 0)
                    return false;
            }
            return true;
        }

        /**
           \brief Add v-psc(p, q, x) into m_todo
        */
        void psc(polynomial_ref & p, polynomial_ref & q, var x) {
            polynomial_ref_vector & S = m_psc_tmp;
            polynomial_ref s(m_pm);

            psc_chain(p, q, x, S);
            unsigned sz = S.size();
            TRACE(nlsat_explain, tout << "computing psc of\n"; display(tout, m_solver, p); tout << "\n"; display(tout, m_solver, q); tout << "\n";
                  for (unsigned i = 0; i < sz; ++i) {
                      s = S.get(i);
                      tout << "psc: " << s << "\n";
                  });

            for (unsigned i = 0; i < sz; ++i) {
                s = S.get(i);
                TRACE(nlsat_explain, display(tout << "processing psc(" << i << ")\n", m_solver, s) << "\n";); 
                if (is_zero(s)) {
                    // PSC is identically zero - polynomials share a common factor.
                    // This can cause unsound lemmas. Fall back to add-all-coeffs projection.
                    TRACE(nlsat_explain, tout << "psc is zero polynomial - polynomials share common factor\n";);
                    if (m_add_all_coeffs)
                        continue;
                    TRACE(nlsat_explain, tout << "falling back to add-all-coeffs projection\n";);
                    m_add_all_coeffs = true;
                    throw add_all_coeffs_restart();
                }
                if (is_const(s)) {
                    TRACE(nlsat_explain, tout << "done, psc is a constant\n";);
                    return;
                }
                if (m_add_zero_disc && !sign(s)) {                    
                    add_zero_assumption(s);
                }
                TRACE(nlsat_explain, 
                      tout << "adding v-psc of\n";
                      display(tout, m_solver, p);
                      tout << "\n";
                      display(tout, m_solver, q);
                      tout << "\n---->\n";
                      display(tout, m_solver, s);
                      tout << "\n";);
                // s did not vanish completely, but its leading coefficient may have vanished
                insert_fresh_factors_in_todo(s);
                return; 
            }
        }
        
        /**
           \brief For each p in ps, add v-psc(x, p, p') into m_todo

           \pre all polynomials in ps contain x

           Remark: the leading coefficients do not vanish in the current model,
           since all polynomials in ps were pre-processed using elim_vanishing.
        */
        void psc_discriminant(polynomial_ref_vector & ps, var x) {
            polynomial_ref p(m_pm);
            polynomial_ref p_prime(m_pm);
            unsigned sz = ps.size();
            for (unsigned i = 0; i < sz; ++i) {
                p = ps.get(i);
                if (degree(p, x) < 2)
                    continue;
                p_prime = derivative(p, x);
                psc(p, p_prime, x);
            }
        }

        /**
           \brief For each p and q in ps, p != q, add v-psc(x, p, q) into m_todo

           \pre all polynomials in ps contain x

           Remark: the leading coefficients do not vanish in the current model,
           since all polynomials in ps were pre-processed using elim_vanishing.
        */
        void psc_resultant(polynomial_ref_vector & ps, var x) {
            polynomial_ref p(m_pm);
            polynomial_ref q(m_pm);
            unsigned sz = ps.size();
            for (unsigned i = 0; i < sz - 1; ++i) {
                p = ps.get(i);
                for (unsigned j = i + 1; j < sz; ++j) {
                    q = ps.get(j);
                    psc(p, q, x);
                }
            }
        }

        void test_root_literal(atom::kind k, var y, unsigned i, poly * p, scoped_literal_vector& result) {
            m_result = &result;
            add_root_literal(k, y, i, p);
            reset_already_added();
            m_result = nullptr;
        }

        
        void add_root_literal(atom::kind k, var y, unsigned i, poly * p) {
            polynomial_ref pr(p, m_pm);
        TRACE(nlsat_explain, 
            display(tout << "x" << y << " " << k << "[" << i << "](", m_solver, pr); tout << ")\n";);
            
            if (!mk_linear_root(k, y, i, p) &&
                !mk_quadratic_root(k, y, i, p)) {
                bool_var b = m_solver.mk_root_atom(k, y, i, p);
                literal l(b, true);
                TRACE(nlsat_explain, tout << "adding literal\n"; display(tout, m_solver, l); tout << "\n";);
                add_literal(l);
            }
        }

        /**
         * literal can be expressed using a linear ineq_atom
         */
        bool mk_linear_root(atom::kind k, var y, unsigned i, poly * p) {            
            scoped_mpz c(m_pm.m());
            if (m_pm.degree(p, y) == 1 && m_pm.const_coeff(p, y, 1, c)) {
                SASSERT(!m_pm.m().is_zero(c));
                mk_linear_root(k, y, i, p, m_pm.m().is_neg(c));
                return true;
            }
            return false;
        }


        /**
           Create pseudo-linear root depending on the sign of the coefficient to y.
         */
        bool mk_plinear_root(atom::kind k, var y, unsigned i, poly * p) {
            if (m_pm.degree(p, y) != 1) {
                return false;
            }
            polynomial_ref c(m_pm);
            c = m_pm.coeff(p, y, 1);
            int s = sign(c);
            if (s == 0) {
                return false;
            }
            ensure_sign(c);
            mk_linear_root(k, y, i, p, s < 0);                
            return true;
        }

        /**
           Encode root conditions for quadratic polynomials.
           
           Basically implements Thom's theorem. The roots are characterized by the sign of polynomials and their derivatives.

           b^2 - 4ac = 0:
              - there is only one root, which is -b/2a.
              - relation to root is a function of the sign of 
              - 2ax + b
           b^2 - 4ac > 0:
              - assert i == 1 or i == 2
              - relation to root is a function of the signs of:
                - 2ax + b
                - ax^2 + bx + c
         */

        bool mk_quadratic_root(atom::kind k, var y, unsigned i, poly * p) {
            if (m_pm.degree(p, y) != 2) {
                return false;
            }
            if (i != 1 && i != 2) {
                return false;
            }

            SASSERT(sample().is_assigned(y));
            polynomial_ref A(m_pm), B(m_pm), C(m_pm), q(m_pm), p_diff(m_pm), yy(m_pm);
            A = m_pm.coeff(p, y, 2);
            B = m_pm.coeff(p, y, 1);
            C = m_pm.coeff(p, y, 0);
            // TBD throttle based on degree of q?
            q = (B*B) - (4*A*C);
            yy = m_pm.mk_polynomial(y);
            p_diff = 2*A*yy + B;
            p_diff = m_pm.normalize(p_diff);
            int sq = ensure_sign_quad(q); 
            if (sq < 0) {
                return false;
            }
            int sa = ensure_sign_quad(A);
            if (sa == 0) {
                q = B*yy + C;
                return mk_plinear_root(k, y, i, q);
            } 
            ensure_sign(p_diff);
            if (sq > 0) {
                polynomial_ref pr(p, m_pm);
                ensure_sign(pr);
            }
            return true;
        }

        void ensure_sign(polynomial_ref & p) {
            if (is_const(p))
                return;
            int s = sign(p);
            TRACE(nlsat_explain, tout << p << "\n";);
            add_assumption(s == 0 ? atom::EQ : (s < 0 ? atom::LT : atom::GT), p);
            // Also add p to the projection to ensure proper cell construction
            insert_fresh_factors_in_todo(p);
        }

        // Specialized version for quadratic root handling.
        // Returns the sign value (-1, 0, or 1).
        int ensure_sign_quad(polynomial_ref & p) {
            int s = sign(p);
            if (!is_const(p)) {
                TRACE(nlsat_explain, tout << p << "\n";);
                add_assumption(s == 0 ? atom::EQ : (s < 0 ? atom::LT : atom::GT), p);
                insert_fresh_factors_in_todo(p);
            }
            return s;
        }

        /**
           Auxiliary function to linear roots.
           y > root[1](-2*y - z)
           y > -z/2
           y + z/2 > 0
           2y + z > 0
           
         */
        void mk_linear_root(atom::kind k, var y, unsigned i, poly * p, bool mk_neg) {
            TRACE(nlsat_explain, m_solver.display_var(tout, y); m_pm.display(tout << ": ", p, m_solver.display_proc()); tout << "\n");
            polynomial_ref p_prime(m_pm);
            p_prime = p;
            bool lsign = false;
            if (mk_neg)
                p_prime = neg(p_prime);
            p = p_prime.get();
            switch (k) {
            case atom::ROOT_EQ: k = atom::EQ; lsign = false; break;
            case atom::ROOT_LT: k = atom::LT; lsign = false; break;
            case atom::ROOT_GT: k = atom::GT; lsign = false; break;
            case atom::ROOT_LE: k = atom::GT; lsign = true; break;
            case atom::ROOT_GE: k = atom::LT; lsign = true; break;
            default:
                UNREACHABLE();
                break;
            }
            add_assumption(k, p, lsign);
        }
        void cac_add_cell_lits(polynomial_ref_vector & ps, var y, polynomial_ref_vector & res) {
            res.reset();
            cell_root_info info(m_pm);
            find_cell_roots(ps, y, info);
            if (info.m_has_eq) {
                res.push_back(info.m_eq);
                add_root_literal(atom::ROOT_EQ, y, info.m_eq_idx, info.m_eq);
                return;
            }
            if (info.m_has_lower) {
                res.push_back(info.m_lower);
                add_root_literal(m_full_dimensional ? atom::ROOT_GE : atom::ROOT_GT, y, info.m_lower_idx, info.m_lower);
            }
            if (info.m_has_upper) {
                res.push_back(info.m_upper);
                add_root_literal(m_full_dimensional ? atom::ROOT_LE : atom::ROOT_LT, y, info.m_upper_idx, info.m_upper);
            }
        }


        /**
           Add one or two literals that specify in which cell of variable y the current interpretation is.
           One literal is added for the cases: 
              - y in (-oo, min) where min is the minimal root of the polynomials p2 in ps
                 We add literal
                    ! (y < root_1(p2))
              - y in (max, oo)  where max is the maximal root of the polynomials p1 in ps
                 We add literal
                    ! (y > root_k(p1))  where k is the number of real roots of p
              - y = r           where r is the k-th root of a polynomial p in ps
                 We add literal
                    ! (y = root_k(p)) 
           Two literals are added when
              - y in (l, u) where (l, u) does not contain any root of polynomials p in ps, and
                  l is the i-th root of a polynomial p1 in ps, and u is the j-th root of a polynomial p2 in ps.
                We add literals
                    ! (y > root_i(p1)) or !(y < root_j(p2))
        */
        void add_cell_lits(polynomial_ref_vector & ps, var y) {
            cell_root_info info(m_pm);
            find_cell_roots(ps, y, info);
            if (info.m_has_eq) {
                add_root_literal(atom::ROOT_EQ, y, info.m_eq_idx, info.m_eq);
                return;
            }
            if (info.m_has_lower) {
                add_root_literal(m_full_dimensional ? atom::ROOT_GE : atom::ROOT_GT, y, info.m_lower_idx, info.m_lower);
            }
            if (info.m_has_upper) {
                add_root_literal(m_full_dimensional ? atom::ROOT_LE : atom::ROOT_LT, y, info.m_upper_idx, info.m_upper);
            }
        }

        /**
           \brief Return true if all polynomials in ps are univariate in x.
        */
        bool all_univ(polynomial_ref_vector const & ps, var x) {
            unsigned sz = ps.size();
            for (unsigned i = 0; i < sz; ++i) {
                poly * p = ps.get(i);
                if (max_var(p) != x)
                    return false;
                if (!m_pm.is_univariate(p))
                    return false;
            }
            return true;
        }
        
        /**
           \brief Apply model-based projection operation defined in our paper.
        */

        bool levelwise_single_cell(polynomial_ref_vector & ps, var max_x, polynomial::cache & cache) {
            // Store polynomials for debugging unsound lemmas
            m_last_lws_input_polys.reset();
            for (unsigned i = 0; i < ps.size(); i++)
                m_last_lws_input_polys.push_back(ps.get(i));
            
            levelwise lws(m_solver, ps, max_x, sample(), m_pm, m_am, cache);
            auto cell = lws.single_cell();
            TRACE(lws, for (unsigned i = 0; i < cell.size(); i++)
                                 display(tout << "I[" << i << "]:", m_solver, cell[i]) << "\n";);
            // Enumerate all intervals in the computed cell and add literals for each non-trivial interval.
            // Non-trivial = section, or sector with at least one finite bound (ignore (-oo,+oo)).
            for (auto const & I : cell) {
                if (I.is_section()) {
                    SASSERT(I.l && I.l_index);
                    add_root_literal(atom::ROOT_EQ, max_var(I.l.get()), I.l_index, I.l.get());
                    continue;
                }
                if (I.l_inf() && I.u_inf())
                    continue; // skip whole-line sector
                if (!I.l_inf())
                    add_root_literal(m_full_dimensional ? atom::ROOT_GE : 
                        atom::ROOT_GT, max_var(I.l.get()), I.l_index, I.l.get());
                if (!I.u_inf())
                    add_root_literal(m_full_dimensional ? atom::ROOT_LE : 
                        atom::ROOT_LT, max_var(I.u.get()), I.u_index, I.u.get());
            }
            return true;
        }

        var extract_max_polys(polynomial_ref_vector & ps) {
            var x = m_todo.extract_max_polys(ps);
            for (unsigned i = 0; i < ps.size(); ++i)
                m_todo_extracted.insert(ps.get(i));
            return x;
        }

        /**
         * Sample Projection
         * Reference:
         * Haokun Li and Bican Xia. 
         * "Solving Satisfiability of Polynomial Formulas By Sample - Cell Projection"
         * https://arxiv.org/abs/2003.00409 
         */
        void project(polynomial_ref_vector & ps, var max_x) {
            bool first = true;
            if (ps.empty())
                return;
            m_todo.reset();
            m_todo_extracted.reset();
            for (unsigned i = 0; i < ps.size(); ++i) {
                polynomial_ref p(m_pm);
                p = ps.get(i);
                insert_fresh_factors_in_todo(p);
            }
            // replace ps by the fresh factors
            ps.reset();
            for (auto p: m_todo.m_set)
                ps.push_back(p);

            if (m_solver.apply_levelwise()) {
                bool levelwise_ok = levelwise_single_cell(ps, max_x, m_cache);
                m_solver.record_levelwise_result(levelwise_ok);
                if (levelwise_ok)
                    return;
                // Levelwise failed, use add_all_coeffs mode for fallback projection
                m_add_all_coeffs = true;
            }
            
            var x = extract_max_polys(ps);
            polynomial_ref_vector samples(m_pm);
            if (x < max_x)
                cac_add_cell_lits(ps, x, samples);

            while (true) {
                if (all_univ(ps, x) && m_todo.empty()) {
                    m_todo.reset();
                    break;
                }
                TRACE(nlsat_explain, tout << "project loop, processing var "; m_solver.display_var(tout, x); tout << "\npolynomials\n";
                      display(tout, m_solver, ps); tout << "\n";);
                if (first) { // The first run is special because x is not constrained by the sample, we cannot surround it by the root functions.
                    // we make the polynomials in ps delinable
                    add_lcs(ps, x);
                    psc_discriminant(ps, x);
                    psc_resultant(ps, x);
                    first = false;
                }
                else {
                    add_lcs(ps, x);
                    psc_discriminant(ps, x);
                    psc_resultant_sample(ps, x, samples);
                }
                
                if (m_todo.empty())
                    break;
                x = extract_max_polys(ps);
                cac_add_cell_lits(ps, x, samples);
            }
            
        }

        bool check_already_added() const {
            for (bool b : m_already_added_literal) {
                (void)b;
                SASSERT(!b);
            }
            return true;
        }

        /*
           Conflicting core simplification using equations.
           The idea is to use equations to reduce the complexity of the 
           conflicting core.

           Basic idea:
           Let l be of the form 
             h > 0
           and eq of the form
             p = 0
           
           Using pseudo-division we have that:
             lc(p)^d h = q p + r
           where q and r are the pseudo-quotient and pseudo-remainder
                 d is the integer returned by the pseudo-division algorithm.
                 lc(p) is the leading coefficient of p
           If d is even or sign(lc(p)) > 0, we have that
                sign(h) =  sign(r)
           Otherwise
                sign(h) = -sign(r) flipped the sign
           
           We have the following rules
                
           If
              (C and h > 0) implies false
           Then
              1. (C and p = 0 and lc(p) != 0 and r > 0) implies false   if d is even
              2. (C and p = 0 and lc(p) > 0  and r > 0) implies false   if lc(p) > 0 and d is odd
              3. (C and p = 0 and lc(p) < 0  and r < 0) implies false   if lc(p) < 0 and d is odd
            
           If
              (C and h = 0) implies false
           Then
              (C and p = 0 and lc(p) != 0 and r = 0) implies false      

           If
              (C and h < 0) implies false
           Then
              1. (C and p = 0 and lc(p) != 0 and r < 0) implies false   if d is even
              2. (C and p = 0 and lc(p) > 0  and r < 0) implies false   if lc(p) > 0 and d is odd
              3. (C and p = 0 and lc(p) < 0  and r > 0) implies false   if lc(p) < 0 and d is odd

           Good cases:
           - lc(p) is a constant
           - p = 0 is already in the conflicting core
           - p = 0 is linear 

           We only use equations from the conflicting core and lower stages.
           Equations from lower stages are automatically added to the lemma.
        */
        struct eq_info {
            poly const *    m_eq;
            polynomial::var m_x;
            unsigned        m_k;
            poly *          m_lc;
            int             m_lc_sign;
            bool            m_lc_const;
            bool            m_lc_add;
            bool            m_lc_add_ineq;
            void add_lc_ineq() {
                m_lc_add = true;
                m_lc_add_ineq = true;
            }
            void add_lc_diseq() {
                if (!m_lc_add) {
                    m_lc_add = true;
                    m_lc_add_ineq = false;
                }
            }
        };
        void simplify(literal l, eq_info & info, var max, scoped_literal & new_lit) {
            bool_var b = l.var();
            atom * a   = m_atoms[b];
            SASSERT(a);
            if (a->is_root_atom()) {
                new_lit = l;
                return;
            }
            ineq_atom * _a = to_ineq_atom(a);
            unsigned num_factors = _a->size();
            if (num_factors == 1 && _a->p(0) == info.m_eq) {
                new_lit = l;
                return;
            }
            TRACE(nlsat_simplify_core, display(tout << "trying to simplify literal\n", m_solver, l) << "\nusing equation\n";
                  m_pm.display(tout, info.m_eq, m_solver.display_proc()); tout << "\n";);
            int  atom_sign = 1;
            bool modified_lit = false;
            polynomial_ref_buffer new_factors(m_pm);
            sbuffer<bool>         new_factors_even;
            polynomial_ref        new_factor(m_pm);
            for (unsigned s = 0; s < num_factors; ++s) {
                poly * f = _a->p(s);
                bool is_even = _a->is_even(s);
                if (m_pm.degree(f, info.m_x) < info.m_k) {
                    new_factors.push_back(f);
                    new_factors_even.push_back(is_even);
                    continue;
                }
                modified_lit = true;
                unsigned d;
                m_pm.pseudo_remainder(f, info.m_eq, info.m_x, d, new_factor);
                polynomial_ref        fact(f, m_pm), eq(const_cast<poly*>(info.m_eq), m_pm);
                
                TRACE(nlsat_simplify_core, tout << "d: " << d << " factor " << fact << " eq " << eq << " new factor " << new_factor << "\n";);
                // adjust sign based on sign of lc of eq
                if (d % 2 == 1 &&         // d is odd
                    !is_even   &&         // degree of the factor is odd
                    info.m_lc_sign < 0) { // lc of the eq is negative 
                    atom_sign = -atom_sign; // flipped the sign of the current literal
                    TRACE(nlsat_simplify_core, tout << "odd degree\n";);
                }
                if (is_const(new_factor)) {
                    TRACE(nlsat_simplify_core, tout << "new factor is const\n";);
                    auto s = sign(new_factor); 
                    if (is_zero(s)) {
                        bool atom_val = a->get_kind() == atom::EQ;
                        bool lit_val  = l.sign() ? !atom_val : atom_val;
                        new_lit = lit_val ? true_literal : false_literal;
                        TRACE(nlsat_simplify_core, tout << "zero sign: " << info.m_lc_const << "\n";);
                        if (!info.m_lc_const) {
                            // We have essentially shown the current factor must be zero If the leading coefficient is not zero.
                            // Note that, if the current factor is zero, then the whole polynomial is zero.
                            // The atom is true if it is an equality, and false otherwise.
                            // The sign of the leading coefficient (info.m_lc) of info.m_eq doesn't matter.
                            // However, we have to store the fact it is not zero.
                            info.add_lc_diseq();
                        }
                        return;
                    }
                    else {
                        TRACE(nlsat_simplify_core, tout << "non-zero sign: " << info.m_lc_const << "\n";);
                        // We have shown the current factor is a constant MODULO the sign of the leading coefficient (of the equation used to rewrite the factor). 
                        if (!info.m_lc_const) {
                            // If the leading coefficient is not a constant, we must store this information as an extra assumption.
                            if (d % 2 == 0 || // d is even
                                is_even ||  // rewriting a factor of even degree, sign flip doesn't matter
                                _a->get_kind() == atom::EQ)  // rewriting an equation, sign flip doesn't matter
                                info.add_lc_diseq();
                            else
                                info.add_lc_ineq();
                        }
                        if (s < 0 && !is_even) {
                            atom_sign = -atom_sign;
                        }
                    }
                }
                else {
                    new_factors.push_back(new_factor);
                    new_factors_even.push_back(is_even);
                    if (!info.m_lc_const) {
                        if (d % 2 == 0 || // d is even
                            is_even ||  // rewriting a factor of even degree, sign flip doesn't matter
                            _a->get_kind() == atom::EQ)  // rewriting an equation, sign flip doesn't matter
                            info.add_lc_diseq();
                        else
                            info.add_lc_ineq();
                    }
                }
            }
            if (modified_lit) {
                atom::kind new_k = _a->get_kind();
                if (atom_sign < 0)
                    new_k = atom::flip(new_k);
                new_lit = m_solver.mk_ineq_literal(new_k, new_factors.size(), new_factors.data(), new_factors_even.data());
                if (l.sign())
                    new_lit.neg();
                TRACE(nlsat_simplify_core, tout << "simplified literal:\n"; display(tout, m_solver, new_lit) << " " << m_solver.value(new_lit) << "\n";);
                
                if (max_var(new_lit) < max) {
                    if (m_solver.value(new_lit) == l_true) {
                        TRACE(nlsat_simplify_bug,
                              tout << "literal normalized away because it is already true after rewriting:\n";
                              m_solver.display(tout << "  original: ", l) << "\n";
                              m_solver.display(tout << "  rewritten: ", new_lit) << "\n";
                              if (info.m_eq) {
                                  polynomial_ref eq_ref(const_cast<poly*>(info.m_eq), m_pm);
                                  m_pm.display(tout << "  equation used: ", eq_ref, m_solver.display_proc());
                                  tout << " = 0\n";
                              });
                        new_lit = l;
                    }
                    else {
                        literal assumption = new_lit;
                        TRACE(nlsat_simplify_bug,
                              tout << "literal replaced by lower-stage assumption due to rewriting:\n";
                              m_solver.display(tout << "  original: ", l) << "\n";
                              m_solver.display(tout << "  assumption: ", assumption) << "\n";
                              if (info.m_eq) {
                                  polynomial_ref eq_ref(const_cast<poly*>(info.m_eq), m_pm);
                                  m_pm.display(tout << "  equation used: ", eq_ref, m_solver.display_proc());
                                  tout << " = 0\n";
                              });
                        add_literal(assumption);
                        new_lit = true_literal;
                    }
                }
                else {
                    literal before = new_lit;
                    (void)before;
                    new_lit = normalize(new_lit, max);
                    TRACE(nlsat_simplify_core, tout << "simplified literal after normalization:\n"; m_solver.display(tout, new_lit); tout << " " << m_solver.value(new_lit) << "\n";);
                    if (new_lit == true_literal || new_lit == false_literal) {
                        TRACE(nlsat_simplify_bug,
                              tout << "normalize() turned rewritten literal into constant value:\n";
                              m_solver.display(tout << "  original: ", l) << "\n";
                              m_solver.display(tout << "  rewritten: ", before) << "\n";
                              tout << "  result: " << (new_lit == true_literal ? "true" : "false") << "\n";
                              if (info.m_eq) {
                                  polynomial_ref eq_ref(const_cast<poly*>(info.m_eq), m_pm);
                                  m_pm.display(tout << "  equation used: ", eq_ref, m_solver.display_proc());
                                  tout << " = 0\n";
                              });
                    }
                }
            }
            else {
                new_lit = l;
            }
        }
        
        bool simplify(scoped_literal_vector & C, poly const * eq, var max) {
            bool modified_core = false;
            eq_info info;
            info.m_eq = eq;
            info.m_x  = m_pm.max_var(info.m_eq);
            info.m_k  = m_pm.degree(eq, info.m_x);
            polynomial_ref lc_eq(m_pm);
            lc_eq           = m_pm.coeff(eq, info.m_x, info.m_k);
            info.m_lc       = lc_eq.get();
            info.m_lc_sign  = sign(lc_eq);
            info.m_lc_add   = false;
            info.m_lc_add_ineq = false;
            info.m_lc_const = m_pm.is_const(lc_eq);
            SASSERT(info.m_lc != 0);
            scoped_literal new_lit(m_solver);
            unsigned sz   = C.size();
            unsigned j    = 0;
            for (unsigned i = 0; i < sz; ++i) {
                literal  l = C[i];
                new_lit = null_literal;
                simplify(l, info, max, new_lit);
                SASSERT(new_lit != null_literal);
                if (l == new_lit) {
                    C.set(j, l);
                    j++;
                    continue;
                }
                modified_core = true;
                if (new_lit == true_literal)
                    continue;
                if (new_lit == false_literal) {
                    // false literal was created. The assumptions added are sufficient for implying the conflict.
                    j = 0; // force core to be reset
                    break;
                }
                C.set(j, new_lit);
                j++;
            }
            C.shrink(j);
            if (info.m_lc_add) {
                if (info.m_lc_add_ineq)
                    add_assumption(info.m_lc_sign < 0 ? atom::LT : atom::GT, info.m_lc);
                else
                    add_assumption(atom::EQ, info.m_lc, true);
            }
            return modified_core;
        }

        /**
           \brief (try to) Select an equation from C. Returns 0 if C does not contain any equality.
           This method selects the equation of minimal degree in max.
        */
        poly * select_eq(scoped_literal_vector & C, var max) {
            poly * r       = nullptr;
            unsigned min_d = UINT_MAX;
            unsigned sz    = C.size();
            for (unsigned i = 0; i < sz; ++i) {
                literal l = C[i];
                if (l.sign())
                    continue;
                bool_var b = l.var();
                atom * a   = m_atoms[b];
                SASSERT(a != 0);
                if (a->get_kind() != atom::EQ)
                    continue;
                ineq_atom * _a = to_ineq_atom(a);
                if (_a->size() > 1)
                    continue;
                if (_a->is_even(0))
                    continue;
                unsigned d = m_pm.degree(_a->p(0), max);
                SASSERT(d > 0);
                if (d < min_d) {
                    r     = _a->p(0);
                    min_d = d;
                    if (min_d == 1)
                        break;
                }
            }
            return r;
        }

        /**
           \brief Select an equation eq s.t.
               max_var(eq) < max, and
               it can be used to rewrite a literal in C.
           Return 0, if such equation was not found.
        */
        var_vector m_select_tmp;
        ineq_atom * select_lower_stage_eq(scoped_literal_vector & C, var max) {
            var_vector & xs = m_select_tmp;
            for (literal l : C) {
                bool_var b = l.var();
                atom * a = m_atoms[b];
                if (a->is_root_atom())
                    continue; // we don't rewrite root atoms
                ineq_atom * _a = to_ineq_atom(a);
                unsigned num_factors = _a->size();
                for (unsigned j = 0; j < num_factors; ++j) {
                    poly * p = _a->p(j);
                    xs.reset();
                    m_pm.vars(p, xs);
                    for (var y : xs) {
                        if (y >= max)
                            continue;
                        atom * eq = m_x2eq[y];
                        if (eq == nullptr)
                            continue;
                        SASSERT(eq->is_ineq_atom());
                        SASSERT(to_ineq_atom(eq)->size() == 1);
                        SASSERT(!to_ineq_atom(eq)->is_even(0));
                        poly * eq_p = to_ineq_atom(eq)->p(0);
                        SASSERT(m_pm.degree(eq_p, y) > 0);
                        // TODO: create a parameter
                        // In the current experiments, using equations with non constant coefficients produces a blowup
                        if (!m_pm.nonzero_const_coeff(eq_p, y, m_pm.degree(eq_p, y))) 
                            continue;
                        if (m_pm.degree(p, y) >= m_pm.degree(eq_p, y))
                            return to_ineq_atom(eq);
                    }
                }
            }
            return nullptr;
        }
        
        /**
           \brief Simplify the core using equalities.
        */
        void simplify(scoped_literal_vector & C, var max) {
            // Simplify using equations in the core
            while (!C.empty()) {
                poly * eq = select_eq(C, max);
                if (eq == nullptr)
                    break;
                TRACE(nlsat_simplify_core, tout << "using equality for simplifying core\n"; 
                      m_pm.display(tout, eq, m_solver.display_proc()); tout << "\n";);
                if (!simplify(C, eq, max))
                    break;
            }
            // Simplify using equations using variables from lower stages.
            while (!C.empty()) {
                ineq_atom * eq = select_lower_stage_eq(C, max);
                if (eq == nullptr)
                    break;
                SASSERT(eq->size() == 1);
                SASSERT(!eq->is_even(0));
                poly * eq_p = eq->p(0);
                VERIFY(simplify(C, eq_p, max));
                // add equation as an assumption                
                TRACE(nlsat_simpilfy_core, display(tout << "adding equality as assumption ", m_solver, literal(eq->bvar(), true)); tout << "\n";);
                add_literal(literal(eq->bvar(), true));
            }
        }

        /**
           \brief Main procedure. The explain the given unsat core, and store the result in m_result
        */
        void main(unsigned num, literal const * ls) {
            if (num == 0) {
                TRACE(nlsat_explain, tout << "num:" << num << "\n";);
                return;
            }
            collect_polys(num, ls, m_ps);
            
            // Add lower-stage polynomials collected during normalization
            // These polynomials had assumptions added but need to be projected as well
            for (unsigned i = 0; i < m_lower_stage_polys.size(); i++) {
                m_ps.push_back(m_lower_stage_polys.get(i));
            }
            
            var max_x = max_var(m_ps);
            TRACE(nlsat_explain, tout << "polynomials in the conflict:\n"; display(tout, m_solver, m_ps); tout << "\n";);

            // Note: levelwise is now called in process2() before normalize()
            // to ensure it receives the original polynomials

            elim_vanishing(m_ps);
            TRACE(nlsat_explain, tout << "after elim_vanishing m_ps:\n"; display(tout, m_solver, m_ps); tout << "\n";);
            project(m_ps, max_x);
            TRACE(nlsat_explain, tout << "after projection\n"; display(tout, m_solver, m_ps); tout << "\n";);
        }

        void process2(unsigned num, literal const * ls) {
            // Reset lower-stage polynomials collection
            m_lower_stage_polys.reset();
            
            // Try levelwise with ORIGINAL polynomials BEFORE any normalization
          
            if (m_simplify_cores) {
                TRACE(nlsat_explain, tout << "m_simplify_cores is true\n";);
                m_core2.reset();
                m_core2.append(num, ls);
                var max = max_var(num, ls);
                SASSERT(max != null_var);
                TRACE(nlsat_explain, display(tout << "core before normalization\n", m_solver, m_core2) << "\n";);
                normalize(m_core2, max);
                TRACE(nlsat_explain, display(tout << "core after normalization\n", m_solver, m_core2) << "\n";);
                simplify(m_core2, max);
                TRACE(nlsat_explain, display(tout << "core after simplify\n", m_solver, m_core2) << "\n";);
                main(m_core2.size(), m_core2.data());
                m_core2.reset();
            }
            else {
                TRACE(nlsat_explain, display(tout << "core befor normalization\n", m_solver, m_core2) << "\n";);
                main(num, ls);
            }
        }
        
        // Auxiliary method for core minimization.
        literal_vector m_min_newtodo;
        bool minimize_core(literal_vector & todo, literal_vector & core) {
            SASSERT(!todo.empty());
            literal_vector & new_todo = m_min_newtodo;
            new_todo.reset();
            interval_set_manager & ism = m_evaluator.ism();
            interval_set_ref r(ism);
            // Copy the union of the infeasible intervals of core into r.
            unsigned sz = core.size();
            for (unsigned i = 0; i < sz; ++i) {
                literal l = core[i];
                atom * a  = m_atoms[l.var()];
                SASSERT(a != 0);
                interval_set_ref inf = m_evaluator.infeasible_intervals(a, l.sign(), nullptr);
                r = ism.mk_union(inf, r);
                if (ism.is_full(r)) {
                    // Done
                    return false;
                }
            }
            TRACE(nlsat_minimize, tout << "interval set after adding partial core:\n" << r << "\n";);
            if (todo.size() == 1) {
                // Done
                core.push_back(todo[0]);
                return false;
            }
            // Copy the union of the infeasible intervals of todo into r until r becomes full.
            sz = todo.size();
            for (unsigned i = 0; i < sz; ++i) {
                literal l = todo[i];
                atom * a  = m_atoms[l.var()];
                SASSERT(a != 0);
                interval_set_ref inf = m_evaluator.infeasible_intervals(a, l.sign(), nullptr);
                r = ism.mk_union(inf, r);
                if (ism.is_full(r)) {
                    // literal l must be in the core
                    core.push_back(l);
                    new_todo.swap(todo);
                    return !todo.empty();
                }
                else {
                    new_todo.push_back(l);
                }
            }
            UNREACHABLE();
            return true;
        }

        literal_vector m_min_todo;
        literal_vector m_min_core;
        void minimize(unsigned num, literal const * ls, scoped_literal_vector & r) {
            literal_vector & todo = m_min_todo;
            literal_vector & core = m_min_core;
            todo.reset(); core.reset();
            todo.append(num, ls);
            while (true) {
                TRACE(nlsat_minimize, tout << "core minimization:\n"; display(tout, m_solver, todo); tout << "\nCORE:\n"; display(tout, m_solver, core) << "\n";);
                if (!minimize_core(todo, core))
                    break;
                std::reverse(todo.begin(), todo.end());
                TRACE(nlsat_minimize, tout << "core minimization:\n"; display(tout, m_solver, todo); tout << "\nCORE:\n"; display(tout, m_solver, core) << "\n";);
                if (!minimize_core(todo, core))
                    break;
            }
            TRACE(nlsat_minimize, tout << "core:\n"; display(tout, m_solver, core););
            r.append(core.size(), core.data());
        }

        void process(unsigned num, literal const * ls) {
            if (m_minimize_cores && num > 1) {
                TRACE(nlsat_explain, tout << "m_minimize_cores:" << m_minimize_cores << ", num:" << num;);
                m_core1.reset();
                minimize(num, ls, m_core1);
                process2(m_core1.size(), m_core1.data());
                m_core1.reset();
            }
            else {
                TRACE(nlsat_explain, tout << "directly to process2\n";);
                process2(num, ls);
            }
        }
      
        void compute_conflict_explanation(unsigned num, literal const * ls, scoped_literal_vector & result) {
            SASSERT(check_already_added());
            SASSERT(num > 0);
            flet<bool> _restore_add_all_coeffs(m_add_all_coeffs, m_add_all_coeffs);
            TRACE(nlsat_explain, 
                  tout << "the infeasible clause:\n"; 
                  display(tout, m_solver, num, ls) << "\n";
                  
                  m_solver.display_assignment(tout << "assignment:\n");
                  );
            if (max_var(num, ls) == 0 && !m_solver.sample().is_assigned(0)) {
                TRACE(nlsat_explain, tout << "all literals use unassigned max var; returning justification\n";);
                result.reset();
                return;
            }
            unsigned base = result.size();
            while (true) {
                try {
                    m_result = &result;
                    process(num, ls);
                    reset_already_added();
                    m_result = nullptr;
                    TRACE(nlsat_explain, display(tout << "[explain] result\n", m_solver, result) << "\n";);
                    CASSERT("nlsat", check_already_added());
                    break;
                }
                catch (add_all_coeffs_restart const&) {
                    TRACE(nlsat_explain, tout << "restarting explanation with all coefficients\n";);
                    reset_already_added();
                    result.shrink(base);
                    m_result = nullptr;
                }
            }
        }


        void project(var x, unsigned num, literal const * ls, scoped_literal_vector & result) {
            unsigned base = result.size();
            while (true) {
                bool reordered = false;
                try {
                    m_result = &result;
                    svector<literal> lits;
                    TRACE(nlsat, tout << "project x" << x << "\n"; 
                          m_solver.display(tout, num, ls);
                          m_solver.display(tout););
                    
#ifdef Z3DEBUG
                    for (unsigned i = 0; i < num; ++i) {
                        SASSERT(m_solver.value(ls[i]) == l_true);
                        atom* a = m_atoms[ls[i].var()];
                        SASSERT(!a || m_evaluator.eval(a, ls[i].sign()));
                    }
#endif   
                    split_literals(x, num, ls, lits);
                    collect_polys(lits.size(), lits.data(), m_ps);
                    var mx_var = max_var(m_ps);
                    if (!m_ps.empty()) {                
                        svector<var> renaming;
                        if (x != mx_var) {
                            for (var i = 0; i < m_solver.num_vars(); ++i) {
                                renaming.push_back(i);
                            }
                            std::swap(renaming[x], renaming[mx_var]);
                            m_solver.reorder(renaming.size(), renaming.data());
                            reordered = true;
                            TRACE(qe, tout << "x: " << x << " max: " << mx_var << " num_vars: " << m_solver.num_vars() << "\n";
                                  m_solver.display(tout););
                        }
                        elim_vanishing(m_ps);
                        project(m_ps, mx_var);
                        reset_already_added();
                        m_result = nullptr;
                        if (reordered) {
                            m_solver.restore_order();
                        }
                    }
                    else {
                        reset_already_added();
                        m_result = nullptr;
                    }
                    for (unsigned i = 0; i < result.size(); ++i) {
                        result.set(i, ~result[i]);
                    }
#ifdef Z3DEBUG
                    TRACE(nlsat, m_solver.display(tout, result.size(), result.data()) << "\n"; );
                    if (max_var(result.size(), result.data()) > 0) { // avoid checking something like that x0 = 0 & x0 > 0 with empty sample
                        for (literal l : result) {
                            CTRACE(nlsat, l_true != m_solver.value(l), m_solver.display(tout, l) << " " << m_solver.value(l) << "\n";);
                            SASSERT(l_true == m_solver.value(l));
                        }
                    }
#endif                
                    break;
                }
                catch (add_all_coeffs_restart const&) {
                    TRACE(nlsat_explain, tout << "restarting projection with all coefficients\n";);
                    reset_already_added();
                    if (reordered) {
                        m_solver.restore_order();
                    }
                    result.shrink(base);
                    m_result = nullptr;
                }
            }
        }

        void split_literals(var x, unsigned n, literal const* ls, svector<literal>& lits) {
            var_vector vs;
            for (unsigned i = 0; i < n; ++i) {                  
                vs.reset();
                m_solver.vars(ls[i], vs);
                if (vs.contains(x)) {
                    lits.push_back(ls[i]);
                }
                else {
                    add_literal(~ls[i]);
                }
            }
        }
        
        
        void project_pairs(var x, unsigned idx, polynomial_ref_vector const& ps) {
            TRACE(nlsat_explain, tout << "project pairs\n";);
            polynomial_ref p(m_pm);
            p = ps.get(idx);
            for (unsigned i = 0; i < ps.size(); ++i) {
                if (i != idx) {
                    project_pair(x, ps.get(i), p);
                }
            }
        }

        void project_pair(var x, polynomial::polynomial* p1, polynomial::polynomial* p2) {
            m_ps2.reset();
            m_ps2.push_back(p1);
            m_ps2.push_back(p2);
            project(m_ps2, x);
        }

        void project_single(var x, polynomial::polynomial* p) {
            m_ps2.reset();
            m_ps2.push_back(p);
            project(m_ps2, x);
        }

        
        void maximize(var x, unsigned num, literal const * ls, scoped_anum& val, bool& unbounded) {
            svector<literal> lits;
            polynomial_ref p(m_pm);
            split_literals(x, num, ls, lits);
            collect_polys(lits.size(), lits.data(), m_ps);
            unbounded = true;
            scoped_anum x_val(m_am);
            x_val = sample().value(x);
            for (unsigned i = 0; i < m_ps.size(); ++i) {
                p = m_ps.get(i);
                scoped_anum_vector & roots = m_roots_tmp;
                roots.reset();
                m_am.isolate_roots(p, undef_var_assignment(sample(), x), roots);
                for (unsigned j = 0; j < roots.size(); ++j) {
                    int s = m_am.compare(x_val, roots[j]);
                    if (s <= 0 && (unbounded || m_am.compare(roots[j], val) <= 0)) {
                        unbounded = false;
                        val = roots[j];
                    }
                }
            }
        }

    };

    explain::explain(solver & s, assignment const & x2v, polynomial::cache & u, 
                     atom_vector const& atoms, atom_vector const& x2eq, evaluator & ev, bool canonicalize) {
        m_imp = alloc(imp, s, x2v, u, atoms, x2eq, ev, canonicalize);
    }

    explain::~explain() {
        dealloc(m_imp);
    }

    void explain::reset() {
        m_imp->m_core1.reset();
        m_imp->m_core2.reset();
    }

    void explain::set_simplify_cores(bool f) {
        m_imp->m_simplify_cores = f;
    }

    void explain::set_full_dimensional(bool f) {
        m_imp->m_full_dimensional = f;
    }

    void explain::set_minimize_cores(bool f) {
        m_imp->m_minimize_cores = f;
    }

    void explain::set_factor(bool f) {
        m_imp->m_factor = f;
    }

    void explain::set_add_all_coeffs(bool f) {
        m_imp->m_add_all_coeffs = f;
    }

    void explain::set_add_zero_disc(bool f) {
        m_imp->m_add_zero_disc = f;
    }

    void explain::compute_conflict_explanation(unsigned n, literal const * ls, scoped_literal_vector & result) {
        m_imp->compute_conflict_explanation(n, ls, result);
    }

    void explain::project(var x, unsigned n, literal const * ls, scoped_literal_vector & result) {
        m_imp->project(x, n, ls, result);
    }

    void explain::maximize(var x, unsigned n, literal const * ls, scoped_anum& val, bool& unbounded) {
        m_imp->maximize(x, n, ls, val, unbounded);
    }

    void explain::display_last_lws_input(std::ostream& out) {
        out << "=== POLYNOMIALS PASSED TO LEVELWISE ===\n";
        for (unsigned i = 0; i < m_imp->m_last_lws_input_polys.size(); i++) {
            out << "  p[" << i << "]: ";
            m_imp->m_pm.display(out, m_imp->m_last_lws_input_polys.get(i));
            out << "\n";
        }
        out << "=== END LEVELWISE INPUT (" << m_imp->m_last_lws_input_polys.size() << " polynomials) ===\n";
    }

    void explain::test_root_literal(atom::kind k, var y, unsigned i, poly* p, scoped_literal_vector & result) {
        m_imp->test_root_literal(k, y, i, p, result);
    }

};
#ifdef Z3DEBUG
#include <iostream>
void pp(nlsat::explain::imp & ex, unsigned num, nlsat::literal const * ls) {
    display(std::cout, ex.m_solver, num, ls);
}
void pp(nlsat::explain::imp & ex, nlsat::scoped_literal_vector & ls) {
    display(std::cout, ex.m_solver, ls);
}
void pp(nlsat::explain::imp & ex, polynomial_ref const & p) {
    display(std::cout, ex.m_solver, p);
    std::cout << std::endl;
}
void pp(nlsat::explain::imp & ex, polynomial::polynomial * p) {
    polynomial_ref _p(p, ex.m_pm);
    display(std::cout, ex.m_solver, _p);
    std::cout << std::endl;
}
void pp(nlsat::explain::imp & ex, polynomial_ref_vector const & ps) {
    display(std::cout, ex.m_solver, ps);
}
void pp_var(nlsat::explain::imp & ex, nlsat::var x) {
    display_var(std::cout, ex.m_solver, x);
    std::cout << std::endl;
}
void pp_lit(nlsat::explain::imp & ex, nlsat::literal l) {
    display(std::cout, ex.m_solver, l);
    std::cout << std::endl;
}
#endif
