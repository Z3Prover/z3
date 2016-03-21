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
#include"smt_context.h"
#include"ast_pp.h"
#include"ast_ll_pp.h"
#include"ast_smt2_pp.h"

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
            unsigned num_lits = cls->get_num_literals();
            for (unsigned i = 0; i < num_lits; i++) {
                literal l = cls->get_literal(i);
                SASSERT(m_lit_occs[l.index()].contains(const_cast<clause*>(cls)));
            }
        }
        return true;
    }

    bool context::check_clauses(clause_vector const & v) const {
        clause_vector::const_iterator it  = v.begin();
        clause_vector::const_iterator end = v.end();
        for (; it != end; ++it) {
            clause * cls = *it;
            if (!cls->deleted())
                check_clause(cls);
        }
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
        clause_set::iterator it  = v.begin();
        clause_set::iterator end = v.end();
        for (; it != end; ++it) {
            clause * cls = *it;
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
        ptr_vector<enode>::const_iterator it  = m_enodes.begin();
        ptr_vector<enode>::const_iterator end = m_enodes.end();
        for (; it != end; ++it) {
            check_enode(*it);
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
        clause_vector::const_iterator it  = v.begin();
        clause_vector::const_iterator end = v.end();
        for (; it != end; ++it) {
            CTRACE("missing_propagation", is_unit_clause(*it), display_clause_detail(tout, *it); tout << "\n";);
            SASSERT(!is_unit_clause(*it));
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
        ptr_vector<enode>::const_iterator it  = m_enodes.begin();
        ptr_vector<enode>::const_iterator end = m_enodes.end();
        for (; it != end; ++it) {
            enode * n = *it;
            SASSERT(!n->is_true_eq() || get_assignment(n) == l_true);
            if (n->is_eq() && get_assignment(n) == l_true) {
                SASSERT(n->is_true_eq());
            }
        }
        return true;
    }

    bool context::check_missing_congruence() const {
        ptr_vector<enode>::const_iterator it  = m_enodes.begin();
        ptr_vector<enode>::const_iterator end = m_enodes.end();
        for (; it != end; ++it) {
            enode * n = *it;
            ptr_vector<enode>::const_iterator it2 = m_enodes.begin();
            for (; it2 != end; ++it2) {
                enode * n2 = *it2;
                if (n->get_root() != n2->get_root()) {
                    if (n->is_true_eq() && n2->is_true_eq())
                        continue;
                    CTRACE("missing_propagation", congruent(n, n2),
                           tout << mk_pp(n->get_owner(), m_manager) << "\n" << mk_pp(n2->get_owner(), m_manager) << "\n";
                           display(tout););
                    SASSERT(!congruent(n, n2));
                }
            }
        }
        return true;
    }

    bool context::check_missing_bool_enode_propagation() const {
        ptr_vector<enode>::const_iterator it  = m_enodes.begin();
        ptr_vector<enode>::const_iterator end = m_enodes.end();
        for (; it != end; ++it) {
            enode * n = *it;
            if (m_manager.is_bool(n->get_owner()) && get_assignment(n) == l_undef) {
                enode * first = n;
                do {
                    CTRACE("missing_propagation", get_assignment(n) != l_undef,
                           tout << mk_pp(first->get_owner(), m_manager) << "\nassignment: " << get_assignment(first) << "\n" 
                           << mk_pp(n->get_owner(), m_manager) << "\nassignment: " << get_assignment(n) << "\n";);
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
            if (m_manager.is_or(n)) {
                CTRACE("relevancy_bug", !is_relevant(n), tout << "n: " << mk_ismt2_pp(n, m_manager) << "\n";);
                SASSERT(is_relevant(n));
                TRACE("check_relevancy", tout << "checking:\n" << mk_ll_pp(n, m_manager) << "\n";);
                SASSERT(m_relevancy_propagator->check_relevancy_or(to_app(n), true));
            }
            else if (m_manager.is_not(n)) {
                CTRACE("relevancy_bug", !is_relevant(to_app(n)->get_arg(0)), tout << "n: " << mk_ismt2_pp(n, m_manager) << "\n";);
                SASSERT(is_relevant(to_app(n)->get_arg(0)));
            }
            else {
                CTRACE("relevancy_bug", !is_relevant(n), tout << "n: " << mk_ismt2_pp(n, m_manager) << "\n";);
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
        ptr_vector<enode>::const_iterator it  = m_enodes.begin();
        ptr_vector<enode>::const_iterator end = m_enodes.end();
        for (; it != end; ++it) {
            enode * e = *it;
            if (m_manager.is_bool(e->get_owner())) {
                enode * r = e->get_root();
                CTRACE("eqc_bool", get_assignment(e) != get_assignment(r), 
                       tout << "#" << e->get_owner_id() << "\n" << mk_pp(e->get_owner(), m_manager) << "\n";
                       tout << "#" << r->get_owner_id() << "\n" << mk_pp(r->get_owner(), m_manager) << "\n";
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
        for (bool_var v = 0; v < num; v++) {
            if (has_enode(v)) {
                enode * n = bool_var2enode(v);
                if (n->is_eq() && is_relevant(n) && get_assignment(v) == l_false) {
                    TRACE("check_th_diseq_propagation", tout << "checking: #" << n->get_owner_id() << " " << mk_bounded_pp(n->get_owner(), m_manager) << "\n";);
                    enode * lhs = n->get_arg(0)->get_root();
                    enode * rhs = n->get_arg(1)->get_root();
                    if (rhs->is_interpreted() && lhs->is_interpreted())
                        continue;
                    TRACE("check_th_diseq_propagation", tout << "num. theory_vars: " << lhs->get_num_th_vars() << " " 
                          << mk_pp(m_manager.get_sort(lhs->get_owner()), m_manager) << "\n";);
                    theory_var_list * l = lhs->get_th_var_list();
                    while (l) {
                        theory_id th_id = l->get_th_id();
                        theory * th = get_theory(th_id);
                        TRACE("check_th_diseq_propagation", tout << "checking theory: " << m_manager.get_family_name(th_id) << "\n";);
                        // if the theory doesn't use diseqs, then the diseqs are not propagated.
                        if (th->use_diseqs() && rhs->get_th_var(th_id) != null_theory_var) {
                            // lhs and rhs are attached to theory th_id
                            svector<new_th_eq>::const_iterator it  = m_propagated_th_diseqs.begin();
                            svector<new_th_eq>::const_iterator end = m_propagated_th_diseqs.end();
                            for (; it != end; ++it) {
                                if (it->m_th_id == th_id) {
                                    enode * lhs_prime = th->get_enode(it->m_lhs)->get_root();
                                    enode * rhs_prime = th->get_enode(it->m_rhs)->get_root();
                                    TRACE("check_th_diseq_propagation", 
                                          tout << m_manager.get_family_name(it->m_th_id) << "\n";);

                                    if ((lhs == lhs_prime && rhs == rhs_prime) ||
                                        (rhs == lhs_prime && lhs == rhs_prime)) {
                                        TRACE("check_th_diseq_propagation", tout << "ok v" << v << " " << get_assignment(v) << "\n";);
                                        break;
                                    }
                                }
                            }
                            if (it == end) {
                            // missed theory diseq propagation
                                display(std::cout);
                                std::cout << "checking theory: " << m_manager.get_family_name(th_id) << "\n";
                                std::cout << "root: #" << n->get_root()->get_owner_id() << " node: #" << n->get_owner_id() << "\n";
                                std::cout << mk_pp(n->get_owner(), m_manager) << "\n";
                                std::cout << "lhs: #" << lhs->get_owner_id() << ", rhs: #" << rhs->get_owner_id() << "\n";
                                std::cout << mk_bounded_pp(lhs->get_owner(), m_manager) << " " << mk_bounded_pp(rhs->get_owner(), m_manager) << "\n";
                            }
                        
                            SASSERT(it != end);
                        }
                        l = l->get_next();
                    }
                }
            }
        }
        return true;
    }

    bool context::check_missing_diseq_conflict() const {
        svector<enode_pair>::const_iterator it  = m_diseq_vector.begin();
        svector<enode_pair>::const_iterator end = m_diseq_vector.end();        
        for (; it != end; ++it) {
            enode * n1 = it->first;
            enode * n2 = it->second;
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

    bool context::validate_model() {
        if (!m_proto_model) {
            return true;
        }
        ast_manager& m = m_manager;
        literal_vector::const_iterator it  = m_assigned_literals.begin();
        literal_vector::const_iterator end = m_assigned_literals.end();
        for (; it != end; ++it) {
            literal lit = *it;
            if (!is_relevant(lit)) {
                continue;
            }
            expr_ref n(m), res(m);
            literal2expr(lit, n);
            if (!is_ground(n)) {
                continue;
            }
            switch (get_assignment(*it)) {
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

