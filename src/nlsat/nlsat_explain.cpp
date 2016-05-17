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
#include"nlsat_explain.h"
#include"nlsat_assignment.h"
#include"nlsat_evaluator.h"
#include"algebraic_numbers.h"
#include"ref_buffer.h"

namespace nlsat {

    typedef polynomial::polynomial_ref_vector polynomial_ref_vector;
    typedef ref_buffer<poly, pmanager> polynomial_ref_buffer;

    struct explain::imp {
        solver &                m_solver;
        assignment const &      m_assignment;
        atom_vector const &     m_atoms;
        atom_vector const &     m_x2eq;
        anum_manager &          m_am;
        polynomial::cache &     m_cache;
        pmanager &              m_pm;
        polynomial_ref_vector   m_ps;
        polynomial_ref_vector   m_ps2;
        polynomial_ref_vector   m_psc_tmp;
        polynomial_ref_vector   m_factors;
        scoped_anum_vector      m_roots_tmp;
        bool                    m_simplify_cores;
        bool                    m_full_dimensional;
        bool                    m_minimize_cores;
        bool                    m_factor;
        bool                    m_signed_project;

        struct todo_set {
            polynomial::cache  &    m_cache;
            polynomial_ref_vector   m_set;
            svector<char>           m_in_set;
            
            todo_set(polynomial::cache & u):m_cache(u), m_set(u.pm()) {}

            void reset() {
                pmanager & pm = m_set.m();
                unsigned sz = m_set.size();
                for (unsigned i = 0; i < sz; i++) {
                    m_in_set[pm.id(m_set.get(i))] = false;
                }
                m_set.reset();
            }
            
            void insert(poly * p) {
                pmanager & pm = m_set.m();
                p = m_cache.mk_unique(p);
                unsigned pid = pm.id(p);
                if (m_in_set.get(pid, false))
                    return;
                m_in_set.setx(pid, true, false);
                m_set.push_back(p);
            }
            
            bool empty() const { return m_set.empty(); }
            
            // Return max variable in todo_set
            var max_var() const {
                pmanager & pm = m_set.m();
                var max = null_var;
                unsigned sz = m_set.size();
                for (unsigned i = 0; i < sz; i++) {
                    var x = pm.max_var(m_set.get(i));
                    SASSERT(x != null_var);
                    if (max == null_var || x > max)
                        max = x;
                }
                return max;
            }
            
            /**
               \brief Remove the maximal polynomials from the set and store
               them in max_polys. Return the maximal variable
             */
            var remove_max_polys(polynomial_ref_vector & max_polys) {
                max_polys.reset();
                var x = max_var();
                pmanager & pm = m_set.m();
                unsigned sz = m_set.size();
                unsigned j  = 0;
                for (unsigned i = 0; i < sz; i++) {
                    poly * p = m_set.get(i);
                    var y = pm.max_var(p);
                    SASSERT(y <= x);
                    if (y == x) {
                        max_polys.push_back(p);
                        m_in_set[pm.id(p)] = false;
                    }
                    else {
                        m_set.set(j, p);
                        j++;
                    }
                }
                m_set.shrink(j);
                return x;
            }
        };
        
        // temporary field for store todo set of polynomials
        todo_set                m_todo;

        // temporary fields for preprocessing core
        scoped_literal_vector   m_core1;
        scoped_literal_vector   m_core2;

        // temporary fields for storing the result
        scoped_literal_vector * m_result;
        svector<char>           m_already_added_literal;

        evaluator &             m_evaluator;

        imp(solver & s, assignment const & x2v, polynomial::cache & u, atom_vector const & atoms, atom_vector const & x2eq,
            evaluator & ev):
            m_solver(s),
            m_assignment(x2v),
            m_atoms(atoms),
            m_x2eq(x2eq),
            m_am(x2v.am()),
            m_cache(u), 
            m_pm(u.pm()),
            m_ps(m_pm),
            m_ps2(m_pm),
            m_psc_tmp(m_pm),
            m_factors(m_pm),
            m_roots_tmp(m_am),
            m_todo(u),
            m_core1(s),
            m_core2(s),
            m_result(0),
            m_evaluator(ev) {
            m_simplify_cores   = false;
            m_full_dimensional = false;
            m_minimize_cores   = false;
            m_signed_project   = false;
        }
        
        ~imp() {
        }

        void display(std::ostream & out, polynomial_ref const & p) const {
            m_pm.display(out, p, m_solver.display_proc());
        }
        
        void display(std::ostream & out, polynomial_ref_vector const & ps, char const * delim = "\n") const {
            for (unsigned i = 0; i < ps.size(); i++) {
                if (i > 0)
                    out << delim;
                m_pm.display(out, ps.get(i), m_solver.display_proc());
            }
        }
        
        void display(std::ostream & out, literal l) const { m_solver.display(out, l); }
        void display_var(std::ostream & out, var x) const { m_solver.display(out, x); }
        void display(std::ostream & out, unsigned sz, literal const * ls) {
            for (unsigned i = 0; i < sz; i++) {
                display(out, ls[i]);
                out << "\n";
            }
        }
        void display(std::ostream & out, literal_vector const & ls) {
            display(out, ls.size(), ls.c_ptr()); 
        }
        void display(std::ostream & out, scoped_literal_vector const & ls) {
            display(out, ls.size(), ls.c_ptr()); 
        }

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
            TRACE("nlsat_explain", tout << "adding literal: " << lidx << "\n"; m_solver.display(tout, l); tout << "\n";);
            m_already_added_literal.setx(lidx, true, false);
            m_result->push_back(l);
        }

        /**
           \brief Reset m_already_added vector using m_result
         */
        void reset_already_added() {
            SASSERT(m_result != 0);
            unsigned sz = m_result->size();
            for (unsigned i = 0; i < sz; i++) 
                m_already_added_literal[(*m_result)[i].index()] = false;
        }


        /**
           \brief evaluate the given polynomial in the current interpretation.
           max_var(p) must be assigned in the current interpretation.
        */
        int sign(polynomial_ref const & p) {
            TRACE("nlsat_explain", tout << "p: " << p << " var: " << max_var(p) << "\n";);
            SASSERT(max_var(p) == null_var || m_assignment.is_assigned(max_var(p)));
            return m_am.eval_sign_at(p, m_assignment);
        }
        
        /**
           \brief Wrapper for factorization
        */
        void factor(polynomial_ref & p, polynomial_ref_vector & fs) {
            // TODO: add params, caching
            TRACE("nlsat_factor", tout << "factor\n" << p << "\n";);
            fs.reset();
            m_cache.factor(p.get(), fs);
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
           \breif Store in ps the polynomials occurring in the given literals.
        */
        void collect_polys(unsigned num, literal const * ls, polynomial_ref_vector & ps) {
            ps.reset();
            for (unsigned i = 0; i < num; i++) {
                atom * a = m_atoms[ls[i].var()];
                SASSERT(a != 0);
                if (a->is_ineq_atom()) {
                    unsigned sz = to_ineq_atom(a)->size();
                    for (unsigned j = 0; j < sz; j++)
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
        svector<bool>     m_is_even;
        void add_zero_assumption(polynomial_ref & p) {
            // If p is of the form p1^n1 * ... * pk^nk,
            // then only the factors that are zero in the current interpretation needed to be considered.
            // I don't want to create a nested conjunction in the clause. 
            // Then, I assert p_i1 * ... * p_im  != 0
            factor(p, m_factors);
            unsigned num_factors = m_factors.size();
            m_zero_fs.reset();
            m_is_even.reset();
            polynomial_ref f(m_pm);
            for (unsigned i = 0; i < num_factors; i++) {
                f = m_factors.get(i);
                if (sign(f) == 0) {
                    m_zero_fs.push_back(m_factors.get(i));
                    m_is_even.push_back(false);
                } 
            }
            SASSERT(!m_zero_fs.empty()); // one of the factors must be zero in the current interpretation, since p is zero in it.
            literal l = m_solver.mk_ineq_literal(atom::EQ, m_zero_fs.size(), m_zero_fs.c_ptr(), m_is_even.c_ptr());
            l.neg();
            TRACE("nlsat_explain", tout << "adding (zero assumption) literal:\n"; display(tout, l); tout << "\n";);
            add_literal(l);
        }

        void add_simple_assumption(atom::kind k, poly * p, bool sign = false) {
            SASSERT(k == atom::EQ || k == atom::LT || k == atom::GT);
            bool is_even = false;
            bool_var b = m_solver.mk_ineq_atom(k, 1, &p, &is_even);
            literal l(b, !sign);
            add_literal(l);
        }

        void add_assumption(atom::kind k, poly * p, bool sign = false) {
            // TODO: factor
            add_simple_assumption(k, p, sign);
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
                if (m_pm.nonzero_const_coeff(p, x, k))
                    return; // lc is a nonzero constant
                lc = m_pm.coeff(p, x, k, reduct);
                if (!is_zero(lc)) {
                    if (sign(lc) != 0)
                        return;
                    // lc is not the zero polynomial, but it vanished in the current interpretaion.
                    // so we keep searching...
                    add_zero_assumption(lc);
                }
                if (k == 0) {
                    // all coefficients of p vanished in the current interpretation,
                    // and were added as assumptions.
                    p = m_pm.mk_zero();
                    return;
                }
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
            for (unsigned i = 0; i < sz; i++) {
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
                for (unsigned i = 0; i < sz; i++) {
                    p = a->p(i);
                    if (max_var(p) == max)
                        elim_vanishing(p); // eliminate vanishing coefficients of max
                    if (is_const(p) || max_var(p) < max) {
                        int s = sign(p); 
                        if (!is_const(p)) {
                            SASSERT(max_var(p) != null_var);
                            SASSERT(max_var(p) < max);
                            // factor p is a lower stage polynomial, so we should add assumption to justify p being eliminated
                            if (s == 0)
                                add_simple_assumption(atom::EQ, p);  // add assumption p = 0
                            else if (a->is_even(i))
                                add_simple_assumption(atom::EQ, p, true); // add assumption p != 0 
                            else if (s < 0)
                                add_simple_assumption(atom::LT, p); // add assumption p < 0
                            else
                                add_simple_assumption(atom::GT, p); // add assumption p > 0
                        }
                        if (s == 0) {
                            bool atom_val = a->get_kind() == atom::EQ;
                            bool lit_val  = l.sign() ? !atom_val : atom_val;
                            return lit_val ? true_literal : false_literal;
                        }
                        else if (s == -1 && a->is_odd(i)) {
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
                    literal new_l = m_solver.mk_ineq_literal(new_k, ps.size(), ps.c_ptr(), is_even.c_ptr());
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
            unsigned sz = C.size();
            unsigned j  = 0;
            for (unsigned i = 0; i < sz; i++) {
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
            for (unsigned i = 1; i < sz; i++) {
                var curr = m_pm.max_var(ps.get(i));
                SASSERT(curr != null_var);
                if (curr > max)
                    max = curr;
            }
            return max;
        }

        polynomial::var max_var(literal l) {
            atom * a  = m_atoms[l.var()];
            if (a != 0)
                return a->max_var();
            else
                return null_var;
        }

        /**
           \brief Return the maximal variable in the given set of literals
         */
        var max_var(unsigned sz, literal const * ls) {
            var max = null_var;
            for (unsigned i = 0; i < sz; i++) {
                literal l = ls[i];
                atom * a  = m_atoms[l.var()];
                if (a != 0) {
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
            for (unsigned i = 0; i < sz; i++) {
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
        void add_factors(polynomial_ref & p) {
            if (is_const(p))
                return;
            elim_vanishing(p);
            if (is_const(p))
                return;
            if (m_factor) {
                TRACE("nlsat_explain", tout << "adding factors of\n"; display(tout, p); tout << "\n";);
                factor(p, m_factors);
                polynomial_ref f(m_pm);
                for (unsigned i = 0; i < m_factors.size(); i++) {
                    f = m_factors.get(i);
                    elim_vanishing(f);
                    if (!is_const(f)) {
                        TRACE("nlsat_explain", tout << "adding factor:\n"; display(tout, f); tout << "\n";);
                        m_todo.insert(f);
                    }
                }
            }
            else {
                m_todo.insert(p);
            }
        }
        
        /**
           \brief Add leading coefficients of the polynomials in ps.

           \pre all polynomials in ps contain x
           
           Remark: the leading coefficients do not vanish in the current model,
           since all polynomials in ps were pre-processed using elim_vanishing.
        */
        void add_lc(polynomial_ref_vector & ps, var x) {
            polynomial_ref p(m_pm);
            polynomial_ref lc(m_pm);
            unsigned sz = ps.size();
            for (unsigned i = 0; i < sz; i++) {
                p = ps.get(i);
                unsigned k = degree(p, x);
                SASSERT(k > 0);
                TRACE("nlsat_explain", tout << "add_lc, x: "; display_var(tout, x); tout << "\nk: " << k << "\n"; display(tout, p); tout << "\n";);
                if (m_pm.nonzero_const_coeff(p, x, k)) {
                    TRACE("nlsat_explain", tout << "constant coefficient, skipping...\n";);
                    continue;
                }
                lc = m_pm.coeff(p, x, k);
                SASSERT(sign(lc) != 0);
                SASSERT(!is_const(lc));
                add_factors(lc);
            }
        }

        /**
           \brief Add v-psc(p, q, x) into m_todo
        */
        void psc(polynomial_ref & p, polynomial_ref & q, var x) {
            polynomial_ref_vector & S = m_psc_tmp;
            polynomial_ref s(m_pm);
            TRACE("nlsat_explain", tout << "computing psc of\n"; display(tout, p); tout << "\n"; display(tout, q); tout << "\n";);

            psc_chain(p, q, x, S);
            unsigned sz = S.size();
            for (unsigned i = 0; i < sz; i++) {
                s = S.get(i);
                TRACE("nlsat_explain", tout << "processing psc(" << i << ")\n"; display(tout, s); tout << "\n";); 
                if (is_zero(s)) {
                    TRACE("nlsat_explain", tout << "skipping psc is the zero polynomial\n";);
                    continue;
                }
                if (is_const(s)) {
                    TRACE("nlsat_explain", tout << "done, psc is a constant\n";);
                    return;
                }
                if (sign(s) == 0) {
                    TRACE("nlsat_explain", tout << "psc vanished, adding zero assumption\n";);
                    add_zero_assumption(s);
                    continue;
                }
                TRACE("nlsat_explain", 
                      tout << "adding v-psc of\n";
                      display(tout, p);
                      tout << "\n";
                      display(tout, q);
                      tout << "\n---->\n";
                      display(tout, s);
                      tout << "\n";);
                // s did not vanish completely, but its leading coefficient may have vanished
                add_factors(s);
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
            for (unsigned i = 0; i < sz; i++) {
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
            for (unsigned i = 0; i < sz - 1; i++) {
                p = ps.get(i);
                for (unsigned j = i + 1; j < sz; j++) {
                    q = ps.get(j);
                    psc(p, q, x);
                }
            }
        }

        void test_root_literal(atom::kind k, var y, unsigned i, poly * p, scoped_literal_vector& result) {
            m_result = &result;
            add_root_literal(k, y, i, p);
            reset_already_added();
            m_result = 0;
        }

        void add_root_literal(atom::kind k, var y, unsigned i, poly * p) {
            polynomial_ref pr(p, m_pm);
            TRACE("nlsat_explain", 
                  display(tout << "x" << y << " " << k << "[" << i << "](", pr); tout << ")\n";);

            if (!mk_linear_root(k, y, i, p) &&
                //!mk_plinear_root(k, y, i, p) &&
                !mk_quadratic_root(k, y, i, p)&&
                true) {                
                bool_var b = m_solver.mk_root_atom(k, y, i, p);
                literal l(b, true);
                TRACE("nlsat_explain", tout << "adding literal\n"; display(tout, l); tout << "\n";);
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

            SASSERT(m_assignment.is_assigned(y));
            polynomial_ref A(m_pm), B(m_pm), C(m_pm), q(m_pm), p_diff(m_pm), yy(m_pm);
            A = m_pm.coeff(p, y, 2);
            B = m_pm.coeff(p, y, 1);
            C = m_pm.coeff(p, y, 0);
            // TBD throttle based on degree of q?
            q = (B*B) - (4*A*C);
            yy = m_pm.mk_polynomial(y);
            p_diff = 2*A*yy + B;
            p_diff = m_pm.normalize(p_diff);
            int sq = ensure_sign(q); 
            if (sq < 0) {
                return false;
            }
            int sa = ensure_sign(A);
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

        int ensure_sign(polynomial_ref & p) {
#if 0
            polynomial_ref f(m_pm);
            factor(p, m_factors);
            m_is_even.reset();
            unsigned num_factors = m_factors.size();
            int s = 1;
            for (unsigned i = 0; i < num_factors; i++) {
                f = m_factors.get(i);
                s *= sign(f);
                m_is_even.push_back(false);
            } 
            if (num_factors > 0) {
                atom::kind k = atom::EQ;
                if (s == 0) k = atom::EQ;
                if (s < 0)  k = atom::LT;
                if (s > 0)  k = atom::GT;
                bool_var b = m_solver.mk_ineq_atom(k, num_factors, m_factors.c_ptr(), m_is_even.c_ptr());
                add_literal(literal(b, true));
            }
            return s;
#else
            int s = sign(p);
            if (!is_const(p)) {
                add_simple_assumption(s == 0 ? atom::EQ : (s < 0 ? atom::LT : atom::GT), p);
            }
            return s;
#endif
        }

        /**
           Auxiliary function to linear roots.
         */
        void mk_linear_root(atom::kind k, var y, unsigned i, poly * p, bool mk_neg) {
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
            add_simple_assumption(k, p, lsign);
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
            SASSERT(m_assignment.is_assigned(y));
            bool lower_inf = true;
            bool upper_inf = true;
            scoped_anum_vector & roots = m_roots_tmp;
            scoped_anum lower(m_am);
            scoped_anum upper(m_am);
            anum const & y_val = m_assignment.value(y);
            TRACE("nlsat_explain", tout << "adding literals for "; display_var(tout, y); tout << " -> ";
                  m_am.display_decimal(tout, y_val); tout << "\n";);
            polynomial_ref p_lower(m_pm);
            unsigned i_lower;
            polynomial_ref p_upper(m_pm);
            unsigned i_upper;
            polynomial_ref p(m_pm);
            unsigned sz = ps.size();
            for (unsigned k = 0; k < sz; k++) {
                p = ps.get(k);
                if (max_var(p) != y)
                    continue;
                roots.reset();
                // Variable y is assigned in m_assignment. We must temporarily unassign it.
                // Otherwise, the isolate_roots procedure will assume p is a constant polynomial.
                m_am.isolate_roots(p, undef_var_assignment(m_assignment, y), roots);
                unsigned num_roots = roots.size();
                for (unsigned i = 0; i < num_roots; i++) {
                    TRACE("nlsat_explain", tout << "comparing root: "; m_am.display_decimal(tout, roots[i]); tout << "\n";);
                    int s = m_am.compare(y_val, roots[i]);
                    if (s == 0) {
                        // y_val == roots[i]
                        // add literal
                        // ! (y = root_i(p))
                        add_root_literal(atom::ROOT_EQ, y, i+1, p);
                        return;
                    }
                    else if (s < 0) {
                        // y_val < roots[i]
                        
                        // check if roots[i] is a better upper bound
                        if (upper_inf || m_am.lt(roots[i], upper)) {
                            upper_inf = false;
                            m_am.set(upper, roots[i]);
                            p_upper = p;
                            i_upper = i+1;
                        }
                    }
                    else if (s > 0) {
                        // roots[i] < y_val

                        // check if roots[i] is a better lower bound
                        if (lower_inf || m_am.lt(lower, roots[i])) {
                            lower_inf = false;
                            m_am.set(lower, roots[i]);
                            p_lower = p;
                            i_lower = i+1;
                        }
                    }
                }
            }
            
            if (!lower_inf) 
                add_root_literal(m_full_dimensional ? atom::ROOT_GE : atom::ROOT_GT, y, i_lower, p_lower);
            if (!upper_inf)
                add_root_literal(m_full_dimensional ? atom::ROOT_LE : atom::ROOT_LT, y, i_upper, p_upper);
        }

        /**
           \brief Return true if all polynomials in ps are univariate in x.
        */
        bool all_univ(polynomial_ref_vector const & ps, var x) {
            unsigned sz = ps.size();
            for (unsigned i = 0; i < sz; i++) {
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
        void project(polynomial_ref_vector & ps, var max_x) {
            if (ps.empty())
                return;
            m_todo.reset();
            for (unsigned i = 0; i < ps.size(); i++) 
                m_todo.insert(ps.get(i));
            var x = m_todo.remove_max_polys(ps);
            // Remark: after vanishing coefficients are eliminated, ps may not contain max_x anymore
            if (x < max_x)
                add_cell_lits(ps, x);
            while (true) {
                if (all_univ(ps, x) && m_todo.empty()) {
                    m_todo.reset();
                    break;
                }
                TRACE("nlsat_explain", tout << "project loop, processing var "; display_var(tout, x); tout << "\npolynomials\n";
                      display(tout, ps); tout << "\n";);
                add_lc(ps, x);
                psc_discriminant(ps, x);
                psc_resultant(ps, x);
                if (m_todo.empty())
                    break;
                x = m_todo.remove_max_polys(ps);
                add_cell_lits(ps, x);
            }
        }

        bool check_already_added() const {
            for (unsigned i = 0; i < m_already_added_literal.size(); i++) {
                SASSERT(m_already_added_literal[i] == false);
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
            SASSERT(a != 0);
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
            TRACE("nlsat_simplify_core", tout << "trying to simplify literal\n"; display(tout, l); tout << "\nusing equation\n";
                  m_pm.display(tout, info.m_eq, m_solver.display_proc()); tout << "\n";);
            int  atom_sign = 1;
            bool modified_lit = false;
            polynomial_ref_buffer new_factors(m_pm);
            sbuffer<bool>         new_factors_even;
            polynomial_ref        new_factor(m_pm);
            for (unsigned s = 0; s < num_factors; s++) {
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
                // adjust sign based on sign of lc of eq
                if (d % 2 == 1 && // d is odd
                    !is_even   && // degree of the factor is odd
                    info.m_lc_sign < 0 // lc of the eq is negative 
                    ) {
                    atom_sign = -atom_sign; // flipped the sign of the current literal
                }
                if (is_const(new_factor)) {
                    int s = sign(new_factor); 
                    if (s == 0) {
                        bool atom_val = a->get_kind() == atom::EQ;
                        bool lit_val  = l.sign() ? !atom_val : atom_val;
                        new_lit = lit_val ? true_literal : false_literal;
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
                        // We have shown the current factor is a constant MODULO the sign of the leading coefficient (of the equation used to rewrite the factor). 
                        if (!info.m_lc_const) {
                            // If the leading coefficient is not a constant, we must store this information as an extra assumption.
                            if (d % 2 == 0 || // d is even
                                is_even ||  // rewriting a factor of even degree, sign flip doesn't matter
                                _a->get_kind() == atom::EQ) {  // rewriting an equation, sign flip doesn't matter
                                info.add_lc_diseq();
                            }
                            else {
                                info.add_lc_ineq();
                            }
                        }
                        if (s == -1 && !is_even) {
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
                            _a->get_kind() == atom::EQ) {  // rewriting an equation, sign flip doesn't matter
                            info.add_lc_diseq();
                        }
                        else {
                            info.add_lc_ineq();
                        }
                    }
                }
            }
            if (modified_lit) {
                atom::kind new_k = _a->get_kind();
                if (atom_sign < 0)
                    new_k = atom::flip(new_k);
                new_lit = m_solver.mk_ineq_literal(new_k, new_factors.size(), new_factors.c_ptr(), new_factors_even.c_ptr());
                if (l.sign())
                    new_lit.neg();
                TRACE("nlsat_simplify_core", tout << "simplified literal:\n"; display(tout, new_lit); tout << "\n";);
                if (max_var(new_lit) < max) {
                    // The conflicting core may have redundant literals.
                    // We should check whether new_lit is true in the current model, and discard it if that is the case
                    VERIFY(m_solver.value(new_lit) != l_undef);
                    if (m_solver.value(new_lit) == l_false)
                        add_literal(new_lit);
                    new_lit = true_literal;
                    return;
                }
                new_lit = normalize(new_lit, max);
                TRACE("nlsat_simplify_core", tout << "simplified literal after normalization:\n"; display(tout, new_lit); tout << "\n";);
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
            info.m_lc_const = m_pm.is_const(lc_eq);
            SASSERT(info.m_lc != 0);
            scoped_literal new_lit(m_solver);
            unsigned sz   = C.size();
            unsigned j    = 0;
            for (unsigned i = 0; i < sz; i++) {
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
            poly * r       = 0;
            unsigned min_d = UINT_MAX;
            unsigned sz    = C.size();
            for (unsigned i = 0; i < sz; i++) {
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
            unsigned sz = C.size();
            for (unsigned i = 0; i < sz; i++) {
                literal l = C[i];
                bool_var b = l.var();
                atom * a   = m_atoms[b];
                if (a->is_root_atom())
                    continue; // we don't rewrite root atoms
                ineq_atom * _a = to_ineq_atom(a);
                unsigned num_factors = _a->size();
                for (unsigned j = 0; j < num_factors; j++) {
                    poly * p = _a->p(j);
                    xs.reset();
                    m_pm.vars(p, xs);
                    unsigned xs_sz = xs.size();
                    for (unsigned k = 0; k < xs_sz; k++) {
                        var y = xs[k];
                        if (y >= max)
                            continue;
                        atom * eq = m_x2eq[y];
                        if (eq == 0)
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
            return 0;
        }
        
        /**
           \brief Simplify the core using equalities.
        */
        void simplify(scoped_literal_vector & C, var max) {
            // Simplify using equations in the core
            while (!C.empty()) {
                poly * eq = select_eq(C, max);
                if (eq == 0)
                    break;
                TRACE("nlsat_simplify_core", tout << "using equality for simplifying core\n"; 
                      m_pm.display(tout, eq, m_solver.display_proc()); tout << "\n";);
                if (!simplify(C, eq, max))
                    break;
            }
            // Simplify using equations using variables from lower stages.
            while (!C.empty()) {
                ineq_atom * eq = select_lower_stage_eq(C, max);
                if (eq == 0)
                    break;
                SASSERT(eq->size() == 1);
                SASSERT(!eq->is_even(0));
                poly * eq_p = eq->p(0);
                VERIFY(simplify(C, eq_p, max));
                // add equation as an assumption                
                add_literal(literal(eq->bvar(), true));
            }
        }

        /**
           \brief Main procedure. The explain the given unsat core, and store the result in m_result
        */
        void main(unsigned num, literal const * ls) {
            if (num == 0)
                return;
            collect_polys(num, ls, m_ps);
            var max_x = max_var(m_ps);
            TRACE("nlsat_explain", tout << "polynomials in the conflict:\n"; display(tout, m_ps); tout << "\n";);
            elim_vanishing(m_ps);
            project(m_ps, max_x);
        }

        void process2(unsigned num, literal const * ls) {
            if (m_simplify_cores) {
                m_core2.reset();
                m_core2.append(num, ls);
                var max = max_var(num, ls);
                SASSERT(max != null_var);
                normalize(m_core2, max);
                TRACE("nlsat_explain", tout << "core after normalization\n"; display(tout, m_core2););
                simplify(m_core2, max);
                TRACE("nlsat_explain", tout << "core after simplify\n"; display(tout, m_core2););
                main(m_core2.size(), m_core2.c_ptr());
                m_core2.reset();
            }
            else {
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
            for (unsigned i = 0; i < sz; i++) {
                literal l = core[i];
                atom * a  = m_atoms[l.var()];
                SASSERT(a != 0);
                interval_set_ref inf = m_evaluator.infeasible_intervals(a, l.sign());
                r = ism.mk_union(inf, r);
                if (ism.is_full(r)) {
                    // Done
                    return false;
                }
            }
            TRACE("nlsat_mininize", tout << "interval set after adding partial core:\n" << r << "\n";);
            if (todo.size() == 1) {
                // Done
                core.push_back(todo[0]);
                return false;
            }
            // Copy the union of the infeasible intervals of todo into r until r becomes full.
            sz = todo.size();
            for (unsigned i = 0; i < sz; i++) {
                literal l = todo[i];
                atom * a  = m_atoms[l.var()];
                SASSERT(a != 0);
                interval_set_ref inf = m_evaluator.infeasible_intervals(a, l.sign());
                r = ism.mk_union(inf, r);
                if (ism.is_full(r)) {
                    // literal l must be in the core
                    core.push_back(l);
                    new_todo.swap(todo);
                    return true;
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
                TRACE("nlsat_mininize", tout << "core minimization:\n"; display(tout, todo); tout << "\nCORE:\n"; display(tout, core););
                if (!minimize_core(todo, core))
                    break;
                std::reverse(todo.begin(), todo.end());
                TRACE("nlsat_mininize", tout << "core minimization:\n"; display(tout, todo); tout << "\nCORE:\n"; display(tout, core););
                if (!minimize_core(todo, core))
                    break;
            }
            TRACE("nlsat_mininize", tout << "core:\n"; display(tout, core););
            r.append(core.size(), core.c_ptr());
        }

        void process(unsigned num, literal const * ls) {
            if (m_minimize_cores && num > 1) {
                m_core1.reset();
                minimize(num, ls, m_core1);
                process2(m_core1.size(), m_core1.c_ptr());
                m_core1.reset();
            }
            else {
                process2(num, ls);
            }
        }
      
        void operator()(unsigned num, literal const * ls, scoped_literal_vector & result) {
            SASSERT(check_already_added());
            SASSERT(num > 0);
            TRACE("nlsat_explain", tout << "[explain] set of literals is infeasible in the current interpretation\n"; display(tout, num, ls););
            // exit(0);
            m_result = &result;
            process(num, ls);
            reset_already_added();
            m_result = 0;
            TRACE("nlsat_explain", tout << "[explain] result\n"; display(tout, result););
            CASSERT("nlsat", check_already_added());
        }


        void project(var x, unsigned num, literal const * ls, scoped_literal_vector & result) {
            m_result = &result;
            svector<literal> lits;
            TRACE("nlsat", tout << "project x" << x << "\n"; m_solver.display(tout););
                  
            DEBUG_CODE(
                for (unsigned i = 0; i < num; ++i) {
                    SASSERT(m_solver.value(ls[i]) == l_true);
                    atom* a = m_atoms[ls[i].var()];
                    SASSERT(!a || m_evaluator.eval(a, ls[i].sign()));
                });
            split_literals(x, num, ls, lits);
            collect_polys(lits.size(), lits.c_ptr(), m_ps);
            var mx_var = max_var(m_ps);
            if (!m_ps.empty()) {                
                svector<var> renaming;
                if (x != mx_var) {
                    for (var i = 0; i < m_solver.num_vars(); ++i) {
                        renaming.push_back(i);
                    }
                    std::swap(renaming[x], renaming[mx_var]);
                    m_solver.reorder(renaming.size(), renaming.c_ptr());
                    TRACE("qe", tout << "x: " << x << " max: " << mx_var << " num_vars: " << m_solver.num_vars() << "\n";
                          m_solver.display(tout););
                }
                elim_vanishing(m_ps);
                if (m_signed_project) {
                    signed_project(m_ps, mx_var);
                }
                else {
                    project(m_ps, mx_var);
                }
                reset_already_added();
                m_result = 0;
                if (x != mx_var) {
                    m_solver.restore_order();
                }
            }
            else {
                reset_already_added();
                m_result = 0;
            }
            for (unsigned i = 0; i < result.size(); ++i) {
                result.set(i, ~result[i]);
            }
            DEBUG_CODE(
                for (unsigned i = 0; i < result.size(); ++i) {
                    SASSERT(l_true == m_solver.value(result[i]));
                });

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

        /**
           Signed projection. 

           Assumptions:
           - any variable in ps is at most x.
           - root expressions are satisfied (positive literals)
           
           Effect:
           - if x not in p, then
              - if sign(p) < 0:   p < 0
              - if sign(p) = 0:   p = 0
              - if sign(p) > 0:   p > 0
           else:
           - let roots_j be the roots of p_j or roots_j[i] 
           - let L = { roots_j[i] | M(roots_j[i]) < M(x) }
           - let U = { roots_j[i] | M(roots_j[i]) > M(x) }
           - let E = { roots_j[i] | M(roots_j[i]) = M(x) }
           - let glb in L, s.t. forall l in L . M(glb) >= M(l)
           - let lub in U, s.t. forall u in U . M(lub) <= M(u)
           - if root in E, then 
              - add E x . x = root & x > lb  for lb in L
              - add E x . x = root & x < ub  for ub in U
              - add E x . x = root & x = root2  for root2 in E \ { root }
           - else 
             - assume |L| <= |U| (other case is symmetric)
             - add E x . lb <= x & x <= glb for lb in L
             - add E x . x = glb & x < ub  for ub in U
         */


        void signed_project(polynomial_ref_vector& ps, var x) {
            
            TRACE("nlsat_explain", tout << "Signed projection\n";);
            polynomial_ref p(m_pm);
            unsigned eq_index = 0;
            bool eq_valid = false;
            unsigned eq_degree = 0;
            for (unsigned i = 0; i < ps.size(); ++i) {
                p = ps.get(i);
                int s = sign(p);
                if (max_var(p) != x) {
                    atom::kind k = (s == 0)?(atom::EQ):((s < 0)?(atom::LT):(atom::GT));
                    add_simple_assumption(k, p, false);
                    ps[i] = ps.back();
                    ps.pop_back();
                    --i;
                }
                else if (s == 0) {
                    if (!eq_valid || degree(p, x) < eq_degree) {
                        eq_index = i;
                        eq_valid = true;
                        eq_degree = degree(p, x);
                    }
                }
            }

            if (ps.empty()) {
                return;
            }

            if (ps.size() == 1) {
                project_single(x, ps.get(0));
                return;
            }

            // ax + b = 0, p(x) > 0 -> 

            if (eq_valid) {
                p = ps.get(eq_index);
                if (degree(p, x) == 1) {
                    // ax + b = 0
                    // let d be maximal degree of x in p.
                    // p(x) -> a^d*p(-b/a), a
                    // perform virtual substitution with equality.
                    solve_eq(x, eq_index, ps);
                }
                else {
                    project_pairs(x, eq_index, ps);
                }
                return;
            }
            
            unsigned num_lub = 0, num_glb = 0;
            unsigned glb_index = 0, lub_index = 0;
            scoped_anum lub(m_am), glb(m_am), x_val(m_am);
            x_val = m_assignment.value(x);
            for (unsigned i = 0; i < ps.size(); ++i) {
                p = ps.get(i);
                scoped_anum_vector & roots = m_roots_tmp;
                roots.reset();
                m_am.isolate_roots(p, undef_var_assignment(m_assignment, x), roots);
                bool glb_valid = false, lub_valid = false;
                for (unsigned j = 0; j < roots.size(); ++j) {
                    int s = m_am.compare(x_val, roots[j]);
                    SASSERT(s != 0);
                    lub_valid |= s < 0;
                    glb_valid |= s > 0;

                    if (s < 0 && m_am.lt(roots[j], lub)) {
                        lub_index = i;
                        m_am.set(lub, roots[j]);
                    }

                    if (s > 0 && m_am.lt(glb, roots[j])) {
                        glb_index = i;
                        m_am.set(glb, roots[j]);                        
                    }
                }
                if (glb_valid) {
                    ++num_glb;
                }
                if (lub_valid) {
                    ++num_lub;
                }
            }

            if (num_lub == 0) {
                project_plus_infinity(x, ps);
                return;
            }
                
            if (num_glb == 0) {
                project_minus_infinity(x, ps);
                return;
            }

            if (num_lub <= num_glb) {
                glb_index = lub_index;
            }

            project_pairs(x, glb_index, ps);
        }

        void project_plus_infinity(var x, polynomial_ref_vector const& ps) {
            polynomial_ref p(m_pm), lc(m_pm);
            for (unsigned i = 0; i < ps.size(); ++i) {
                p = ps.get(i);
                unsigned d = degree(p, x);
                lc = m_pm.coeff(p, x, d);
                if (!is_const(lc)) {                    
                    unsigned s = sign(p);
                    SASSERT(s != 0);
                    atom::kind k = (s > 0)?(atom::GT):(atom::LT);
                    add_simple_assumption(k, lc);
                }
            }
        }

        void project_minus_infinity(var x, polynomial_ref_vector const& ps) {
            polynomial_ref p(m_pm), lc(m_pm);
            for (unsigned i = 0; i < ps.size(); ++i) {
                p = ps.get(i);
                unsigned d = degree(p, x);
                lc = m_pm.coeff(p, x, d);
                if (!is_const(lc)) {
                    unsigned s = sign(p);
                    SASSERT(s != 0);
                    atom::kind k;
                    if (s > 0) {
                        k = (d % 2 == 0)?(atom::GT):(atom::LT);
                    }
                    else {
                        k = (d % 2 == 0)?(atom::LT):(atom::GT);
                    }
                    add_simple_assumption(k, lc);
                }
            }
        }

        void project_pairs(var x, unsigned idx, polynomial_ref_vector const& ps) {
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

        void solve_eq(var x, unsigned idx, polynomial_ref_vector const& ps) {
            polynomial_ref p(m_pm), A(m_pm), B(m_pm), C(m_pm), D(m_pm), E(m_pm), q(m_pm), r(m_pm);
            polynomial_ref_vector qs(m_pm);
            p = ps.get(idx);
            SASSERT(degree(p, x) == 1);
            A = m_pm.coeff(p, x, 1);
            B = m_pm.coeff(p, x, 0);
            B = neg(B);
            TRACE("nlsat_explain", tout << "p: " << p << " A: " << A << " B: " << B << "\n";);
            // x = B/A
            for (unsigned i = 0; i < ps.size(); ++i) {
                if (i != idx) {
                    q = ps.get(i);
                    unsigned d = degree(q, x);
                    D = m_pm.mk_const(rational(1));
                    E = D;
                    r = m_pm.mk_zero();
                    for (unsigned j = 0; j <= d; ++j) {                       
                        qs.push_back(D);
                        D = D*A;
                    }
                    for (unsigned j = 0; j <= d; ++j) {
                        // A^d*p0 + A^{d-1}*B*p1 + ... + B^j*A^{d-j}*pj + ... + B^d*p_d
                        C = m_pm.coeff(q, x, j);
                        if (!is_zero(C)) {
                            D = qs.get(d-j);
                            r = r + D*E*C;
                        }
                        E = E*B;
                    }
                    TRACE("nlsat_explain", tout << "q: " << q << " r: " << r << "\n";);
                    ensure_sign(r);
                }
                else {
                    ensure_sign(A);
                }
            }

        }

        void maximize(var x, unsigned num, literal const * ls, scoped_anum& val, bool& unbounded) {
            svector<literal> lits;
            polynomial_ref p(m_pm);
            split_literals(x, num, ls, lits);
            collect_polys(lits.size(), lits.c_ptr(), m_ps);
            unbounded = true;
            scoped_anum x_val(m_am);
            x_val = m_assignment.value(x);
            for (unsigned i = 0; i < m_ps.size(); ++i) {
                p = m_ps.get(i);
                scoped_anum_vector & roots = m_roots_tmp;
                roots.reset();
                m_am.isolate_roots(p, undef_var_assignment(m_assignment, x), roots);
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
                     atom_vector const& atoms, atom_vector const& x2eq, evaluator & ev) {
        m_imp = alloc(imp, s, x2v, u, atoms, x2eq, ev);
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

    void explain::set_signed_project(bool f) {
        m_imp->m_signed_project = f;
    }

    void explain::operator()(unsigned n, literal const * ls, scoped_literal_vector & result) {
        (*m_imp)(n, ls, result);
    }

    void explain::project(var x, unsigned n, literal const * ls, scoped_literal_vector & result) {
        m_imp->project(x, n, ls, result);
    }

    void explain::maximize(var x, unsigned n, literal const * ls, scoped_anum& val, bool& unbounded) {
        m_imp->maximize(x, n, ls, val, unbounded);
    }

    void explain::test_root_literal(atom::kind k, var y, unsigned i, poly* p, scoped_literal_vector & result) {
        m_imp->test_root_literal(k, y, i, p, result);
    }

};

#ifdef Z3DEBUG
void pp(nlsat::explain::imp & ex, unsigned num, nlsat::literal const * ls) {
    ex.display(std::cout, num, ls);
}
void pp(nlsat::explain::imp & ex, nlsat::scoped_literal_vector & ls) {
    ex.display(std::cout, ls);
}
void pp(nlsat::explain::imp & ex, polynomial_ref const & p) {
    ex.display(std::cout, p);
    std::cout << std::endl;
}
void pp(nlsat::explain::imp & ex, polynomial::polynomial * p) {
    polynomial_ref _p(p, ex.m_pm);
    ex.display(std::cout, _p);
    std::cout << std::endl;
}
void pp(nlsat::explain::imp & ex, polynomial_ref_vector const & ps) {
    ex.display(std::cout, ps);
}
void pp_var(nlsat::explain::imp & ex, nlsat::var x) {
    ex.display(std::cout, x);
    std::cout << std::endl;
}
void pp_lit(nlsat::explain::imp & ex, nlsat::literal l) {
    ex.display(std::cout, l);
    std::cout << std::endl;
}
#endif

