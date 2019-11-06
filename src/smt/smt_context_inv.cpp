/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_context_inv.cpp

Abstract:

    SMT logical contexts: invariant

Author:

    Leonardo de Moura (leonardo) 2008-02-21.

Revision History:

--*/
#include "smt/smt_context.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_smt2_pp.h"

namespace smt {

#ifdef Z3DEBUG
    bool context::is_watching_clause(literal l, clause const * cls) const {
        watch_list & wl = const_cast<watch_list &>(m_watches[l.index()]);
        return wl.find_clause(cls) != wl.end_clause();
    }

    bool context::check_clause(clause const * cls) const {
        SASSERT(is_watching_clause(~cls->get_literal(0), cls));        
        SASSERT(is_watching_clause(~cls->get_literal(1), cls));        
        if (lit_occs_enabled()) {
            for (literal l : *cls) {
                SASSERT(m_lit_occs[l.index()].contains(const_cast<clause*>(cls)));
            }
        }
        return true;
    }

    bool context::check_clauses(clause_vector const & v) const {
        for (clause* cls : v) 
            if (!cls->deleted())
                check_clause(cls);
        return true;
    }

    bool context::check_watch_list(literal l) const {
        watch_list & wl = const_cast<watch_list &>(m_watches[l.index()]);
        l.neg();
        watch_list::clause_iterator it  = wl.begin_clause();
        watch_list::clause_iterator end = wl.end_clause();
        for (; it != end; ++it) {
            clause * cls = *it;
            TRACE("watch_list", tout << "l: "; display_literal(tout, l); tout << "\n";
                  display_clause(tout, cls); tout << "\n";);
            SASSERT(l == cls->get_literal(0) || l == cls->get_literal(1));
        }
        return true;
    }

    bool context::check_watch_list(unsigned l_idx) const {
        return check_watch_list(to_literal(l_idx));
    }

    bool context::check_bin_watch_lists() const {
        if (binary_clause_opt_enabled()) {
            vector<watch_list>::const_iterator it  = m_watches.begin();
            vector<watch_list>::const_iterator end = m_watches.end();
            for (unsigned l_idx = 0; it != end; ++it, ++l_idx) {
                literal l1            = to_literal(l_idx);
                watch_list const & wl = *it;
                literal const * it2   = wl.begin_literals();
                literal const * end2  = wl.end_literals();
                for (; it2 != end2; ++it2) {
                    literal l2 = *it2;
                    watch_list const & wl = m_watches[(~l2).index()];
                    SASSERT(wl.find_literal(~l1) != wl.end_literals());
                }
            }
        }
        return true;
    }

    bool context::check_lit_occs(literal l) const {
        clause_set const & v = m_lit_occs[l.index()];
        for (clause * cls : v) {
            unsigned num = cls->get_num_literals();
            unsigned i   = 0;
            for (; i < num; i++)
                if (cls->get_literal(i) == l)
                    break;
            CTRACE("lit_occs", !(i < num), tout << i << " " << num << "\n"; display_literal(tout, l); tout << "\n"; 
                   display_clause(tout, cls); tout << "\n"; 
                   tout << "l: " << l.index() << " cls: ";
                   for (unsigned j = 0; j < num; j++) {
                       tout << cls->get_literal(j).index() << " ";
                   }
                   tout << "\n";
                   display_clause_detail(tout, cls); tout << "\n";);
            SASSERT(i < num);
        }
        return true;
    }

    bool context::check_lit_occs() const {
        if (lit_occs_enabled()) {
            unsigned num_lits = get_num_bool_vars() * 2;
            for (unsigned l_idx = 0; l_idx < num_lits; ++l_idx) {
                check_lit_occs(to_literal(l_idx));
            }
        }
        return true;
    }

    bool context::check_enode(enode * n) const {
        SASSERT(n->check_invariant());
        bool is_true_eq = n->is_true_eq();
        bool cg_inv = 
            n->get_num_args() == 0 || 
            (!is_true_eq && (!n->is_cgc_enabled() || n->is_cgr() == (m_cg_table.contains_ptr(n)))) ||
            (is_true_eq && !m_cg_table.contains_ptr(n));
        CTRACE("check_enode", !cg_inv,
               tout << "n: #" << n->get_owner_id() << ", m_cg: #" << n->m_cg->get_owner_id() << ", contains: " << m_cg_table.contains(n) << "\n"; display(tout););
        SASSERT(cg_inv);
        return true;
    }

    bool context::check_enodes() const {
        for (enode* n : m_enodes) {
            check_enode(n);
        }
        return true;
    }

    bool context::check_invariant() const {
        check_lit_occs();
        check_bin_watch_lists();
        check_clauses(m_aux_clauses);
        check_clauses(m_lemmas);
        check_enodes();
        SASSERT(m_cg_table.check_invariant());
        return true;
    }

    bool context::check_missing_clause_propagation(clause_vector const & v) const {
        for (clause * cls : v) {
            CTRACE("missing_propagation", is_unit_clause(cls), display_clause_detail(tout, cls); tout << "\n";);
            SASSERT(!is_unit_clause(cls));
        }
        return true;
    }

    bool context::check_missing_bin_clause_propagation() const {
        if (binary_clause_opt_enabled()) {
            SASSERT(m_watches.size() == m_assignment.size());
            vector<watch_list>::const_iterator it  = m_watches.begin();
            vector<watch_list>::const_iterator end = m_watches.end();
            for (unsigned l_idx = 0; it != end; ++it, ++l_idx) {
                literal l             = to_literal(l_idx);
                watch_list const & wl = *it;
                if (get_assignment(l) == l_true) {
                    literal const * it2   = wl.begin_literals();
                    literal const * end2  = wl.end_literals();
                    for (; it2 != end2; ++it2) {
                        literal l2 = *it2;
                        SASSERT(get_assignment(l2) == l_true);
                    }
                }
            }
        }
        return true;
    }
    
    bool context::check_missing_eq_propagation() const {
        for (enode* n : m_enodes) {
            SASSERT(!n->is_true_eq() || get_assignment(n) == l_true);
            if (n->is_eq() && get_assignment(n) == l_true) {
                SASSERT(n->is_true_eq());
            }
        }
        return true;
    }

    bool context::check_missing_congruence() const {
        for (enode* n : m_enodes) {
            for (enode* n2 : m_enodes) {
                if (n->get_root() != n2->get_root()) {
                    if (n->is_true_eq() && n2->is_true_eq())
                        continue;
                    CTRACE("missing_propagation", congruent(n, n2),
                           tout << mk_pp(n->get_owner(), m) << "\n" << mk_pp(n2->get_owner(), m) << "\n";
                           display(tout););
                    SASSERT(!congruent(n, n2));
                }
            }
        }
        return true;
    }

    bool context::check_missing_bool_enode_propagation() const {
        for (enode* n : m_enodes) {
            if (m.is_bool(n->get_owner()) && get_assignment(n) == l_undef) {
                enode * first = n;
                do {
                    CTRACE("missing_propagation", get_assignment(n) != l_undef,
                           tout << mk_pp(first->get_owner(), m) << "\nassignment: " << get_assignment(first) << "\n" 
                           << mk_pp(n->get_owner(), m) << "\nassignment: " << get_assignment(n) << "\n";);
                    SASSERT(get_assignment(n) == l_undef);
                    n = n->get_next();
                }
                while (n != first);
            }
        }
        return true;
    }

    bool context::check_missing_propagation() const {
        check_missing_clause_propagation(m_lemmas);
        check_missing_clause_propagation(m_aux_clauses);
        check_missing_bin_clause_propagation();
        // check_missing_eq_propagation();
        check_missing_congruence();
        check_missing_bool_enode_propagation();
        return true;
    }

    bool context::check_relevancy(expr_ref_vector const & v) const {
        return m_relevancy_propagator->check_relevancy(v);
    }

    bool context::check_relevancy() const {
        if (!relevancy())
            return true;
        check_relevancy(m_b_internalized_stack);
        check_relevancy(m_e_internalized_stack);
        unsigned sz = m_asserted_formulas.get_num_formulas();
        for (unsigned i = 0; i < sz; i++) {
            expr * n = m_asserted_formulas.get_formula(i);
            if (m.is_or(n)) {
                CTRACE("relevancy_bug", !is_relevant(n), tout << "n: " << mk_ismt2_pp(n, m) << "\n";);
                SASSERT(is_relevant(n));
                TRACE("check_relevancy", tout << "checking:\n" << mk_ll_pp(n, m) << "\n";);
                SASSERT(m_relevancy_propagator->check_relevancy_or(to_app(n), true));
            }
            else if (m.is_not(n)) {
                CTRACE("relevancy_bug", !is_relevant(to_app(n)->get_arg(0)), tout << "n: " << mk_ismt2_pp(n, m) << "\n";);
                SASSERT(is_relevant(to_app(n)->get_arg(0)));
            }
            else {
                CTRACE("relevancy_bug", !is_relevant(n), tout << "n: " << mk_ismt2_pp(n, m) << "\n";);
                SASSERT(is_relevant(n));
            }
        }
        return true;
    }

    /**
       \brief Check if expressions attached to bool_variables and enodes have a consistent assignment.
       For all a, b.  root(a) == root(b) ==> get_assignment(a) == get_assignment(b)
    */
    bool context::check_eqc_bool_assignment() const {
        for (enode* e : m_enodes) {
            if (m.is_bool(e->get_owner())) {
                enode * r = e->get_root();
                CTRACE("eqc_bool", get_assignment(e) != get_assignment(r), 
                       tout << "#" << e->get_owner_id() << "\n" << mk_pp(e->get_owner(), m) << "\n";
                       tout << "#" << r->get_owner_id() << "\n" << mk_pp(r->get_owner(), m) << "\n";
                       tout << "assignments: " << get_assignment(e) << " " << get_assignment(r) << "\n";
                       display(tout););
                SASSERT(get_assignment(e) == get_assignment(r));
            }
        }
        return true;
    }

    bool context::check_bool_var_vector_sizes() const {
        SASSERT(m_assignment.size()    == 2 * m_bdata.size());
        SASSERT(m_watches.size()       == 2 * m_bdata.size());
        SASSERT(m_bdata.size()         == m_activity.size());
        SASSERT(m_bool_var2expr.size() == m_bdata.size());
        return true;
    }

    /**
       \brief Check the following property:
       
       - for every equality atom (= lhs rhs) assigned to false, relevant:
            if lhs->get_root() and rhs->get_root() are attached to theory variables v1 and v2 of theory t,
            then there is an entry (t, v1', v2') in m_propagated_th_diseqs such that,
            (= get_enode(v1') get_enode(v2')) is congruent to (= lhs rhs).
    */
    bool context::check_th_diseq_propagation() const {
        TRACE("check_th_diseq_propagation", tout << "m_propagated_th_diseqs.size() " << m_propagated_th_diseqs.size() << "\n";);
        int num = get_num_bool_vars();
        if (inconsistent()) {
            return true;
        }
        for (bool_var v = 0; v < num; v++) {
            if (has_enode(v)) {
                enode * n = bool_var2enode(v);
                if (n->is_eq() && is_relevant(n) && get_assignment(v) == l_false && !m.is_iff(n->get_owner())) {
                    TRACE("check_th_diseq_propagation", tout << "checking: #" << n->get_owner_id() << " " << mk_bounded_pp(n->get_owner(), m) << "\n";);
                    enode * lhs = n->get_arg(0)->get_root();
                    enode * rhs = n->get_arg(1)->get_root();
                    if (rhs->is_interpreted() && lhs->is_interpreted())
                        continue;
                    TRACE("check_th_diseq_propagation", tout << "num. theory_vars: " << lhs->get_num_th_vars() << " " 
                          << mk_pp(m.get_sort(lhs->get_owner()), m) << "\n";);
                    theory_var_list * l = lhs->get_th_var_list();
                    while (l) {
                        theory_id th_id = l->get_th_id();
                        theory * th = get_theory(th_id);
                        TRACE("check_th_diseq_propagation", tout << "checking theory: " << m.get_family_name(th_id) << "\n";);
                        // if the theory doesn't use diseqs, then the diseqs are not propagated.
                        if (th->use_diseqs() && rhs->get_th_var(th_id) != null_theory_var) {
                            bool found = false;
                            // lhs and rhs are attached to theory th_id
                            for (new_th_eq const& eq : m_propagated_th_diseqs) {
                                if (eq.m_th_id == th_id) {
                                    enode * lhs_prime = th->get_enode(eq.m_lhs)->get_root();
                                    enode * rhs_prime = th->get_enode(eq.m_rhs)->get_root();
                                    TRACE("check_th_diseq_propagation", 
                                          tout << m.get_family_name(eq.m_th_id) << "\n";);

                                    if ((lhs == lhs_prime && rhs == rhs_prime) ||
                                        (rhs == lhs_prime && lhs == rhs_prime)) {
                                        TRACE("check_th_diseq_propagation", tout << "ok v" << v << " " << get_assignment(v) << "\n";);
                                        found = true;
                                        break;
                                    }
                                }
                            }
                            if (!found) {
                            // missed theory diseq propagation
                                display(std::cout);
                                std::cout << "checking theory: " << m.get_family_name(th_id) << "\n";
                                std::cout << "root: #" << n->get_root()->get_owner_id() << " node: #" << n->get_owner_id() << "\n";
                                std::cout << mk_pp(n->get_owner(), m) << "\n";
                                std::cout << "lhs: #" << lhs->get_owner_id() << ", rhs: #" << rhs->get_owner_id() << "\n";
                                std::cout << mk_bounded_pp(lhs->get_owner(), m) << " " << mk_bounded_pp(rhs->get_owner(), m) << "\n";
                            }
                            VERIFY(found);
                        }
                        l = l->get_next();
                    }
                }
            }
        }
        return true;
    }

    bool context::check_missing_diseq_conflict() const {
        for (enode_pair const& p :  m_diseq_vector) {
            enode * n1 = p.first;
            enode * n2 = p.second;
            if (n1->get_root() == n2->get_root()) {
                TRACE("diseq_bug", 
                      tout << "n1: #" << n1->get_owner_id() << ", n2: #" << n2->get_owner_id() <<
                      ", r: #" << n1->get_root()->get_owner_id() << "\n";
                      tout << "n1 parents:\n"; display_parent_eqs(tout, n1);
                      tout << "n2 parents:\n"; display_parent_eqs(tout, n2);
                      tout << "r parents:\n"; display_parent_eqs(tout, n1->get_root());
                      );
                UNREACHABLE();
            }
        }
        return true;
    }

#endif

    bool context::validate_justification(bool_var v, bool_var_data const& d, b_justification const& j) {
        if (j.get_kind() == b_justification::CLAUSE && v != true_bool_var) {
            clause* cls = j.get_clause();
            literal l = cls->get_literal(0);
            if (l.var() != v) {
                l = cls->get_literal(1);
            }
            SASSERT(l.var() == v);
            SASSERT(m_assignment[l.index()] == l_true);
        }
        return true;
    }

    bool context::validate_model() {
        if (!m_proto_model) {
            return true;
        }
        for (literal lit : m_assigned_literals) {
            if (!is_relevant(lit)) {
                continue;
            }
            expr_ref n(m), res(m);
            literal2expr(lit, n);
            if (!is_ground(n)) {
                continue;
            }
            if (is_quantifier(n) && m.is_rec_fun_def(to_quantifier(n))) {
                continue;
            }
            switch (get_assignment(lit)) {
            case l_undef:
                break;
            case l_true:
                if (!m_proto_model->eval(n, res, false)) return true;
                CTRACE("mbqi_bug", !m.is_true(res), tout << n << " evaluates to " << res << "\n";); 
                if (m.is_false(res)) {
                    return false;
                }
                break;
            case l_false:
                if (!m_proto_model->eval(n, res, false)) return true;
                CTRACE("mbqi_bug", !m.is_false(res), tout << n << " evaluates to " << res << "\n";); 
                if (m.is_true(res)) {
                    return false;
                }
                break;
            }
        }
        return true;
    }

    /**
       \brief validate unsat core returned by 
     */
    void context::validate_unsat_core() {
        if (!get_fparams().m_core_validate) {
            return;
        }
        context ctx(get_manager(), get_fparams(), get_params());
        ptr_vector<expr> assertions;
        get_assertions(assertions);
        unsigned sz = assertions.size();
        for (unsigned i = 0; i < sz; ++i) {
            ctx.assert_expr(assertions[i]);
        }
        sz = m_unsat_core.size();
        for (unsigned i = 0; i < sz; ++i) {
            ctx.assert_expr(m_unsat_core.get(i));
        }
        lbool res = ctx.check();
        switch (res) {
        case l_false:
            break;
        default: 
            throw default_exception("Core could not be validated");
        }
    }

};

