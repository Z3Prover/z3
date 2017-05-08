/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_conflict_resolution.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-25.

Revision History:

--*/
#include"smt_context.h"
#include"smt_conflict_resolution.h"
#include"ast_pp.h"
#include"ast_ll_pp.h"

namespace smt {

    // ---------------------------
    //
    // Base class
    //
    // ---------------------------

    conflict_resolution::conflict_resolution(ast_manager & m,
                                             context & ctx,
                                             dyn_ack_manager & dyn_ack_manager,
                                             smt_params const & params,
                                             literal_vector const & assigned_literals,
                                             vector<watch_list> & watches
                                             ):
        m_manager(m),
        m_params(params),
        m_ctx(ctx),
        m_dyn_ack_manager(dyn_ack_manager),
        m_assigned_literals(assigned_literals),
        m_lemma_atoms(m),
        m_todo_js_qhead(0),
        m_antecedents(0),
        m_watches(watches),
        m_new_proofs(m),
        m_lemma_proof(m)
    {
    }

    /**
       \brief Mark all enodes in a 'proof' tree brach starting at n
       n -> ... -> root
    */
    template<bool Set>
    void conflict_resolution::mark_enodes_in_trans(enode * n) {
        SASSERT(n->trans_reaches(n->get_root()));
        while (n) {
            if (Set)
                n->set_mark2();
            else
                n->unset_mark2();
            n = n->m_trans.m_target;
        }
    }

    /**
       \brief Find a common ancestor (anc) of n1 and n2 in the 'proof' tree.
       The common ancestor is used to produce irredundant transitivity proofs.

       n1 = a1 = ... = ai = ANC = ... = root
       n2 = b1 = ... = bj = ANC = ... = root

       The equalities ANC = ... = root should not be included in the proof of n1 = n2.

       The irredundant proof for n1 = n2 is:

       n1 = a1 = ... = ai = ANC = bj = ... = b1 = n2
    */
    enode * conflict_resolution::find_common_ancestor(enode * n1, enode * n2) {
        SASSERT(n1->get_root() == n2->get_root());
        mark_enodes_in_trans<true>(n1);
        while (true) {
            SASSERT(n2);
            if (n2->is_marked2()) {
                mark_enodes_in_trans<false>(n1);
                return n2;
            }
            n2 = n2->m_trans.m_target;
        }
    }

    /**
       \brief Process a eq_justification of lhs and rhs.
       This method executes a step of eq_justification2literals

       This method may update m_antecedents, m_todo_js and m_todo_eqs.
    */
    void conflict_resolution::eq_justification2literals(enode * lhs, enode * rhs, eq_justification js) {
        SASSERT(m_antecedents);
        TRACE("conflict_detail",
              ast_manager& m = get_manager();
              tout << mk_pp(lhs->get_owner(), m) << " = " << mk_pp(rhs->get_owner(), m);
              switch (js.get_kind()) {
              case eq_justification::AXIOM: tout << " axiom\n";  break;
              case eq_justification::EQUATION:
                  tout << " was asserted\nliteral: "; m_ctx.display_literal(tout, js.get_literal()); tout << "\n";
                  break;
              case eq_justification::JUSTIFICATION: tout << " justification\n";  break;
              case eq_justification::CONGRUENCE: tout << " congruence\n"; break;
              default:  break;
              });

        switch(js.get_kind()) {
        case eq_justification::AXIOM:
            break;
        case eq_justification::EQUATION:
            m_antecedents->push_back(js.get_literal());
            break;
        case eq_justification::JUSTIFICATION:
            mark_justification(js.get_justification());
            break;
        case eq_justification::CONGRUENCE: {
            CTRACE("dyn_ack_target", !lhs->is_eq(), tout << "dyn_ack_target2: " << lhs->get_owner_id() << " " << rhs->get_owner_id() << "\n";);
            m_dyn_ack_manager.used_cg_eh(lhs->get_owner(), rhs->get_owner());
            unsigned num_args = lhs->get_num_args();
            SASSERT(num_args == rhs->get_num_args());
            if (js.used_commutativity()) {
                SASSERT(num_args == 2);
                mark_eq(lhs->get_arg(0), rhs->get_arg(1));
                mark_eq(lhs->get_arg(1), rhs->get_arg(0));
            }
            else {
                for (unsigned i = 0; i < num_args; i++)
                    mark_eq(lhs->get_arg(i), rhs->get_arg(i));
            }
            break;
        }
        default:
            UNREACHABLE();
        }
    }

    /**
       \brief Process the transitivity 'proof' from n1 and n2, where
       n1 and n2 are in the same branch

       n1 -> ... -> n2

       This method may update m_antecedents, m_todo_js and m_todo_eqs.

       The resultant set of literals is stored in m_antecedents.
    */
    void conflict_resolution::eq_branch2literals(enode * n1, enode * n2) {
        SASSERT(n1->trans_reaches(n2));
        while (n1 != n2) {
            eq_justification2literals(n1, n1->m_trans.m_target, n1->m_trans.m_justification);
            n1 = n1->m_trans.m_target;
        }
    }

    /**
       \brief Process the justification of n1 = n2.

       This method may update m_antecedents, m_todo_js and m_todo_eqs.

       The resultant set of literals is stored in m_antecedents.
    */
    void conflict_resolution::eq2literals(enode * n1, enode * n2) {
        enode * c = find_common_ancestor(n1, n2);
        eq_branch2literals(n1, c);
        eq_branch2literals(n2, c);
        m_dyn_ack_manager.used_eq_eh(n1->get_owner(), n2->get_owner(), c->get_owner());
    }

    /**
       \brief Extract the antecedent literals from a justification object.

       The result is stored in result.

       \remark This method does not reset the vectors m_antecedents, m_todo_js, m_todo_eqs, nor reset the
       marks in the justification objects.
    */
    void conflict_resolution::justification2literals_core(justification * js, literal_vector & result) {
        SASSERT(m_todo_js_qhead <= m_todo_js.size());
        m_antecedents = &result;
        mark_justification(js);
        process_justifications();
    }

    void conflict_resolution::process_justifications() {
        while (true) {
            unsigned sz = m_todo_js.size();
            while (m_todo_js_qhead < sz) {
                justification * js = m_todo_js[m_todo_js_qhead];
                m_todo_js_qhead++;
                js->get_antecedents(*this);
            }
            while (!m_todo_eqs.empty()) {
                enode_pair p = m_todo_eqs.back();
                m_todo_eqs.pop_back();
                eq2literals(p.first, p.second);
            }
            if (m_todo_js_qhead == m_todo_js.size()) {
                m_antecedents = 0;
                return;
            }
        }
    }

    /**
       \brief Unset the mark of the justifications stored in m_todo_js
    */
    void conflict_resolution::unmark_justifications(unsigned old_js_qhead) {
        SASSERT(old_js_qhead <= m_todo_js.size());
        justification_vector::iterator it  = m_todo_js.begin() + old_js_qhead;
        justification_vector::iterator end = m_todo_js.end();
        for (; it != end; ++it) {
            (*it)->unset_mark();
        }
        m_todo_js.shrink(old_js_qhead);
        m_todo_js_qhead = old_js_qhead;
        m_todo_eqs.reset();
        m_already_processed_eqs.reset();
    }

    /**
       \brief Extract the antecedent literals from a justification object.
    */
    void conflict_resolution::justification2literals(justification * js, literal_vector & result) {
        SASSERT(m_todo_js.empty());
        SASSERT(m_todo_js_qhead == 0);
        SASSERT(m_todo_eqs.empty());
        justification2literals_core(js, result);
        unmark_justifications(0);
        SASSERT(m_todo_eqs.empty());
    }

    void conflict_resolution::eq2literals(enode* n1, enode* n2, literal_vector & result) {
        SASSERT(m_todo_js.empty());
        SASSERT(m_todo_js_qhead == 0);
        SASSERT(m_todo_eqs.empty());
        m_antecedents = &result;
        m_todo_eqs.push_back(enode_pair(n1, n2));
        process_justifications();
        unmark_justifications(0);
        SASSERT(m_todo_eqs.empty());
    }

    /**
       \brief Return maximum scope level of an antecedent literal of js.
    */
    unsigned conflict_resolution::get_justification_max_lvl(justification * js) {
        unsigned r = 0;
        literal_vector & antecedents = m_tmp_literal_vector;
        antecedents.reset();
        justification2literals(js, antecedents);
        literal_vector::iterator it  = antecedents.begin();
        literal_vector::iterator end = antecedents.end();
        for(; it != end; ++it)
            r = std::max(r, m_ctx.get_assign_level(*it));
        return r;
    }

    /**
       \brief Return the maximum scope level of the antecedent literals of the given
       justified literal.
    */
    unsigned conflict_resolution::get_max_lvl(literal consequent, b_justification js) {
        unsigned r = 0;
        if (consequent != false_literal)
            r = m_ctx.get_assign_level(consequent);

        switch (js.get_kind()) {
        case b_justification::CLAUSE: {
            clause * cls      = js.get_clause();
            unsigned num_lits = cls->get_num_literals();
            unsigned i        = 0;
            if (consequent != false_literal) {
                SASSERT(cls->get_literal(0) == consequent || cls->get_literal(1) == consequent);
                if (cls->get_literal(0) == consequent) {
                    i = 1;
                }
                else {
                    r = std::max(r, m_ctx.get_assign_level(cls->get_literal(0)));
                    i = 2;
                }
            }
            for(; i < num_lits; i++)
                r = std::max(r, m_ctx.get_assign_level(cls->get_literal(i)));
            justification * js = cls->get_justification();
            if (js)
                r = std::max(r, get_justification_max_lvl(js));
            break;
        }
        case b_justification::BIN_CLAUSE:
            r = std::max(r, m_ctx.get_assign_level(js.get_literal()));
            break;
        case b_justification::AXIOM:
            break;
        case b_justification::JUSTIFICATION:
            r = std::max(r, get_justification_max_lvl(js.get_justification()));
            break;
        default:
            UNREACHABLE();
        }
        return r;
    }

    void conflict_resolution::process_antecedent(literal antecedent, unsigned & num_marks) {
        bool_var var = antecedent.var();
        unsigned lvl = m_ctx.get_assign_level(var);
        SASSERT(var < static_cast<int>(m_ctx.get_num_bool_vars()));
        TRACE("conflict", tout << "processing antecedent (level " << lvl << "):";
              m_ctx.display_literal(tout, antecedent);
              m_ctx.display_detailed_literal(tout << " ", antecedent); tout << "\n";);

        if (!m_ctx.is_marked(var) && lvl > m_ctx.get_base_level()) {
            m_ctx.set_mark(var);
            m_ctx.inc_bvar_activity(var);
            expr * n = m_ctx.bool_var2expr(var);
            if (is_app(n)) {
                family_id fid = to_app(n)->get_family_id();
                theory * th   = m_ctx.get_theory(fid);
                if (th)
                    th->conflict_resolution_eh(to_app(n), var);
            }

            if (get_manager().has_trace_stream()) {
                get_manager().trace_stream() << "[resolve-lit] " << m_conflict_lvl - lvl << " ";
                m_ctx.display_literal(get_manager().trace_stream(), ~antecedent);
                get_manager().trace_stream() << "\n";
            }

            if (lvl == m_conflict_lvl) {
                num_marks++;
            }
            else {
                m_lemma.push_back(~antecedent);
                m_lemma_atoms.push_back(m_ctx.bool_var2expr(var));
            }
        }
    }

    void conflict_resolution::process_justification(justification * js, unsigned & num_marks) {
        literal_vector & antecedents = m_tmp_literal_vector;
        antecedents.reset();
        justification2literals_core(js, antecedents);
        literal_vector::iterator it  = antecedents.begin();
        literal_vector::iterator end = antecedents.end();
        for(; it != end; ++it)
            process_antecedent(*it, num_marks);
    }

    /**
       \brief Skip literals from levels above m_conflict_lvl.
       It returns an index idx such that m_assigned_literals[idx] <= m_conflict_lvl, and
       for all idx' > idx, m_assigned_literals[idx'] > m_conflict_lvl
    */
    unsigned conflict_resolution::skip_literals_above_conflict_level() {
        unsigned idx = m_assigned_literals.size();
        if (idx == 0) {
            return idx;
        }
        idx--;
        // skip literals from levels above the conflict level
        while (m_ctx.get_assign_level(m_assigned_literals[idx]) > m_conflict_lvl) {
            SASSERT(idx > 0);
            idx--;
        }
        return idx;
    }

    /**
       \brief Initialize conflict resolution data-structures.
       Return false if the conflict cannot be resolved (it is at the search level).
    */
    bool conflict_resolution::initialize_resolve(b_justification conflict, literal not_l, b_justification & js, literal & consequent) {
        TRACE("conflict_detail", m_ctx.display(tout););
        m_lemma.reset();
        m_lemma_atoms.reset();
        SASSERT(m_ctx.get_search_level() >= m_ctx.get_base_level());
        js                  = conflict;
        consequent          = false_literal;
        if (not_l != null_literal)
            consequent      = ~not_l;

        m_conflict_lvl      = get_max_lvl(consequent, js);

        TRACE("conflict_bug",
              tout << "conflict_lvl: " << m_conflict_lvl << " scope_lvl: " << m_ctx.get_scope_level() << " base_lvl: " << m_ctx.get_base_level()
              << " search_lvl: " << m_ctx.get_search_level() << "\n";
              tout << "js.kind: " << js.get_kind() << "\n";
              tout << "consequent: " << consequent << ": ";
              m_ctx.display_literal_verbose(tout, consequent); tout << "\n";
              m_ctx.display(tout, js); tout << "\n";
          );

        // m_conflict_lvl can be smaller than m_ctx.get_search_level() when:
        // there are user level scopes created using the Z3 API, and
        // the previous levels were already inconsistent, or the inconsistency was
        // triggered by an axiom or justification proof wrapper, this two kinds
        // of justification are considered level zero.
        if (m_conflict_lvl <= m_ctx.get_search_level()) {
            TRACE("conflict", tout << "problem is unsat\n";);
            if (m_manager.proofs_enabled())
                mk_conflict_proof(conflict, not_l);
            if (m_ctx.tracking_assumptions())
                mk_unsat_core(conflict, not_l);
            return false;
        }

        TRACE("conflict", tout << "conflict_lvl: " << m_conflict_lvl << "\n";);

        SASSERT(!m_assigned_literals.empty());

        SASSERT(m_todo_js.empty());
        SASSERT(m_todo_js_qhead == 0);
        SASSERT(m_todo_eqs.empty());
        return true;
    }

    /**
       \brief Cleanup datastructures used during resolve(), minimize lemma (when minimization is enabled),
       compute m_new_scope_lvl and m_lemma_iscope_lvl, generate proof if needed.

       This method assumes that the lemma is stored in m_lemma (and the associated atoms in m_lemma_atoms).

       \warning This method assumes the literals in m_lemma[1] ... m_lemma[m_lemma.size() - 1] are marked.
    */
    void conflict_resolution::finalize_resolve(b_justification conflict, literal not_l) {
        unmark_justifications(0);

        TRACE("conflict",
              tout << "before minimization:\n";
              m_ctx.display_literals(tout, m_lemma);
              tout << "\n";);

        TRACE("conflict_verbose",
              tout << "before minimization:\n";
              m_ctx.display_literals_verbose(tout, m_lemma);
              tout << "\n";);

        if (m_params.m_minimize_lemmas)
            minimize_lemma();

        TRACE("conflict",
              tout << "after minimization:\n";
              m_ctx.display_literals(tout, m_lemma);
              tout << "\n";);

        TRACE("conflict_verbose",
              tout << "after minimization:\n";
              m_ctx.display_literals_verbose(tout, m_lemma);
              tout << "\n";);

        TRACE("conflict_bug",
              m_ctx.display_literals_verbose(tout, m_lemma);
              tout << "\n";);

        literal_vector::iterator it  = m_lemma.begin();
        literal_vector::iterator end = m_lemma.end();
        m_new_scope_lvl              = m_ctx.get_search_level();
        m_lemma_iscope_lvl           = m_ctx.get_intern_level((*it).var());
        SASSERT(!m_ctx.is_marked((*it).var()));
        ++it;
        for(; it != end; ++it) {
            bool_var var = (*it).var();
            if (var != null_bool_var) {
                m_ctx.unset_mark(var);
                unsigned lvl = m_ctx.get_assign_level(var);
                if (lvl > m_new_scope_lvl)
                    m_new_scope_lvl    = lvl;
                lvl = m_ctx.get_intern_level(var);
                if (lvl > m_lemma_iscope_lvl)
                    m_lemma_iscope_lvl = lvl;
            }
        }

        TRACE("conflict",
              tout << "new scope level:     " << m_new_scope_lvl << "\n";
              tout << "intern. scope level: " << m_lemma_iscope_lvl << "\n";);

        if (m_manager.proofs_enabled())
            mk_conflict_proof(conflict, not_l);
    }

    bool conflict_resolution::resolve(b_justification conflict, literal not_l) {
        b_justification js;
        literal consequent;

        if (!initialize_resolve(conflict, not_l, js, consequent))
            return false;

        unsigned idx = skip_literals_above_conflict_level();

        TRACE("conflict", m_ctx.display_literal_verbose(tout, not_l); m_ctx.display(tout << " ", conflict););

        // save space for first uip
        m_lemma.push_back(null_literal);
        m_lemma_atoms.push_back(0);

        unsigned num_marks = 0;
        if (not_l != null_literal) {
            TRACE("conflict", tout << "not_l: "; m_ctx.display_literal_verbose(tout, not_l); tout << "\n";);
            process_antecedent(not_l, num_marks);
        }

        do {

            if (get_manager().has_trace_stream()) {
                get_manager().trace_stream() << "[resolve-process] ";
                m_ctx.display_literal(get_manager().trace_stream(), ~consequent);
                get_manager().trace_stream() << "\n";
            }

            TRACE("conflict", tout << "processing consequent: "; m_ctx.display_literal_verbose(tout, consequent); tout << "\n";
                  tout << "num_marks: " << num_marks << ", js kind: " << js.get_kind() << "\n";);
            SASSERT(js != null_b_justification);
            switch (js.get_kind()) {
            case b_justification::CLAUSE: {
                clause * cls = js.get_clause();
                if (cls->is_lemma())
                    cls->inc_clause_activity();
                unsigned num_lits = cls->get_num_literals();
                unsigned i        = 0;
                if (consequent != false_literal) {
                    SASSERT(cls->get_literal(0) == consequent || cls->get_literal(1) == consequent);
                    if (cls->get_literal(0) == consequent) {
                        i = 1;
                    }
                    else {
                        literal l = cls->get_literal(0);
                        SASSERT(consequent.var() != l.var());
                        process_antecedent(~l, num_marks);
                        i = 2;
                    }
                }
                for(; i < num_lits; i++) {
                    literal l = cls->get_literal(i);
                    SASSERT(consequent.var() != l.var());
                    process_antecedent(~l, num_marks);
                }
                justification * js = cls->get_justification();
                if (js)
                    process_justification(js, num_marks);
                break;
            }
            case b_justification::BIN_CLAUSE:
                SASSERT(consequent.var() != js.get_literal().var());
                process_antecedent(js.get_literal(), num_marks);
                break;
            case b_justification::AXIOM:
                break;
            case b_justification::JUSTIFICATION:
                process_justification(js.get_justification(), num_marks);
                break;
            default:
                UNREACHABLE();
            }

            while (true) {
                literal l = m_assigned_literals[idx];
                if (m_ctx.is_marked(l.var()))
                    break;
                CTRACE("conflict", m_ctx.get_assign_level(l) != m_conflict_lvl && m_ctx.get_assign_level(l) != m_ctx.get_base_level(),
                       tout << "assign_level(l): " << m_ctx.get_assign_level(l) << ", conflict_lvl: " << m_conflict_lvl << ", l: "; m_ctx.display_literal(tout, l);
                       tout << "\n";);
                SASSERT(m_ctx.get_assign_level(l) == m_conflict_lvl ||
                        // it may also be an (out-of-order) asserted literal
                        m_ctx.get_assign_level(l) == m_ctx.get_base_level());
                SASSERT(idx > 0);
                idx--;
            }

            consequent     = m_assigned_literals[idx];
            bool_var c_var = consequent.var();
            SASSERT(m_ctx.get_assign_level(c_var) == m_conflict_lvl);
            js             = m_ctx.get_justification(c_var);
            idx--;
            num_marks--;
            m_ctx.unset_mark(c_var);
        }
        while (num_marks > 0);

        TRACE("conflict", tout << "FUIP: "; m_ctx.display_literal(tout, consequent); tout << "\n";);

        m_lemma[0]       = ~consequent;
        m_lemma_atoms.set(0, m_ctx.bool_var2expr(consequent.var()));

        // TODO:
        //
        // equality optimization should go here.
        //

        finalize_resolve(conflict, not_l);

        return true;
    }

    /**
       \brief Return an approximation for the set of scope levels where the literals in m_lemma
       were assigned.
    */
    level_approx_set conflict_resolution::get_lemma_approx_level_set() {
        level_approx_set result;
        literal_vector::const_iterator it  = m_lemma.begin();
        literal_vector::const_iterator end = m_lemma.end();
        for(; it != end; ++it)
            result.insert(m_ctx.get_assign_level(*it));
        return result;
    }

    /**
       \brief Restore the size of m_unmark to old_size, and
       unmark literals at positions [old_size, m_unmark.size()).
    */
    void conflict_resolution::reset_unmark(unsigned old_size) {
        unsigned curr_size = m_unmark.size();
        for(unsigned i = old_size; i < curr_size; i++)
            m_ctx.unset_mark(m_unmark[i]);
        m_unmark.shrink(old_size);
    }

    /**
       \brief Restore the size of m_unmark to old_size, and
       unmark literals at positions [old_size, m_unmark.size()).
       And unmark all justifications at positions [old_js_qhead, m_todo_js.size()).
    */
    void conflict_resolution::reset_unmark_and_justifications(unsigned old_size, unsigned old_js_qhead) {
        reset_unmark(old_size);
        unmark_justifications(old_js_qhead);
    }

    /**
       \brief Process an antecedent for lemma minimization.
    */
    bool conflict_resolution::process_antecedent_for_minimization(literal antecedent) {
        bool_var var = antecedent.var();
        unsigned lvl = m_ctx.get_assign_level(var);
        if (!m_ctx.is_marked(var) && lvl > m_ctx.get_base_level()) {
            if (m_lvl_set.may_contain(lvl)) {
                m_ctx.set_mark(var);
                m_unmark.push_back(var);
                m_lemma_min_stack.push_back(var);
            }
            else {
                return false;
            }
        }
        return true;
    }

    bool conflict_resolution::process_justification_for_minimization(justification * js) {
        literal_vector & antecedents = m_tmp_literal_vector;
        antecedents.reset();
        // Invoking justification2literals_core will not reset the caches for visited justifications and eqs.
        // The method unmark_justifications must be invoked to reset these caches.
        // Remark: The method reset_unmark_and_justifications invokes unmark_justifications.
        justification2literals_core(js, antecedents);
        literal_vector::iterator it  = antecedents.begin();
        literal_vector::iterator end = antecedents.end();
        for(; it != end; ++it)
            if (!process_antecedent_for_minimization(*it))
                return false;
        return true;
    }

    /**
       \brief Return true if lit is implied by other marked literals
       and/or literals assigned at the base level.
       The set lvl_set is used as an optimization.
       The idea is to stop the recursive search with a failure
       as soon as we find a literal assigned in a level that is not in lvl_set.
    */
    bool conflict_resolution::implied_by_marked(literal lit) {
        m_lemma_min_stack.reset();  // avoid recursive function
        m_lemma_min_stack.push_back(lit.var());
        unsigned old_size     = m_unmark.size();
        unsigned old_js_qhead = m_todo_js_qhead;

        while (!m_lemma_min_stack.empty()) {
            bool_var var       = m_lemma_min_stack.back();
            m_lemma_min_stack.pop_back();
            b_justification js = m_ctx.get_justification(var);
            SASSERT(js != null_b_justification);
            switch(js.get_kind()) {
            case b_justification::CLAUSE: {
                clause * cls      = js.get_clause();
                unsigned num_lits = cls->get_num_literals();
                unsigned pos      = cls->get_literal(1).var() == var;
                for (unsigned i = 0; i < num_lits; i++) {
                    if (pos != i) {
                        literal l = cls->get_literal(i);
                        SASSERT(l.var() != var);
                        if (!process_antecedent_for_minimization(~l)) {
                            reset_unmark_and_justifications(old_size, old_js_qhead);
                            return false;
                        }
                    }
                }
                justification * js = cls->get_justification();
                if (js && !process_justification_for_minimization(js)) {
                    reset_unmark_and_justifications(old_size, old_js_qhead);
                    return false;
                }
                break;
            }
            case b_justification::BIN_CLAUSE:
                if (!process_antecedent_for_minimization(js.get_literal())) {
                    reset_unmark_and_justifications(old_size, old_js_qhead);
                    return false;
                }
                break;
            case b_justification::AXIOM:
                // it is a decision variable from a previous scope level or an assumption
                if (m_ctx.get_assign_level(var) > m_ctx.get_base_level()) {
                    reset_unmark_and_justifications(old_size, old_js_qhead);
                    return false;
                }
                break;
            case b_justification::JUSTIFICATION:
                if (m_ctx.is_assumption(var) || !process_justification_for_minimization(js.get_justification())) {
                    reset_unmark_and_justifications(old_size, old_js_qhead);
                    return false;
                }
                break;
            }
        }
        return true;
    }

    /**
       \brief Minimize the number of literals in learned_clause_lits. The main idea is to remove
       literals that are implied by other literals in m_lemma and/or literals
       assigned in the base levels.
    */
    void conflict_resolution::minimize_lemma() {
        m_unmark.reset();

        m_lvl_set   = get_lemma_approx_level_set();

        unsigned sz   = m_lemma.size();
        unsigned i    = 1; // the first literal is the FUIP
        unsigned j    = 1;
        for (; i < sz; i++) {
            literal l = m_lemma[i];
            if (implied_by_marked(l)) {
                m_unmark.push_back(l.var());
            }
            else {
                if (j != i) {
                    m_lemma[j]       = m_lemma[i];
                    m_lemma_atoms.set(j, m_lemma_atoms.get(i));
                }
                j++;
            }
        }

        reset_unmark_and_justifications(0, 0);
        m_lemma      .shrink(j);
        m_lemma_atoms.shrink(j);
        m_ctx.m_stats.m_num_minimized_lits += sz - j;
    }

    /**
       \brief Return the proof object associated with the equality (= n1 n2)
       if it already exists. Otherwise, return 0 and add p to the todo-list.
    */
    proof * conflict_resolution::get_proof(enode * n1, enode * n2) {
        SASSERT(n1 != n2);
        proof * pr;
        if (m_eq2proof.find(n1, n2, pr)) {
            TRACE("proof_gen_bug", tout << "eq2_pr_cached: #" << n1->get_owner_id() << " #" << n2->get_owner_id() << "\n";);
            return pr;
        }
        m_todo_pr.push_back(tp_elem(n1, n2));
        return 0;
    }

    /**
       \brief Apply symmetry if pr is a proof of (= n2 n1).
    */
    proof * conflict_resolution::norm_eq_proof(enode * n1, enode * n2, proof * pr) {
        if (!pr)
            return 0;
        SASSERT(m_manager.has_fact(pr));
        app * fact     = to_app(m_manager.get_fact(pr));
        app * n1_owner = n1->get_owner();
        app * n2_owner = n2->get_owner();
        bool is_eq = m_manager.is_eq(fact) || m_manager.is_iff(fact);
        if (!is_eq || (fact->get_arg(0) != n2_owner && fact->get_arg(1) != n2_owner)) {
            CTRACE("norm_eq_proof_bug", !m_ctx.is_true(n2) && !m_ctx.is_false(n2),
                   tout << "n1: #" << n1->get_owner_id() << ", n2: #" << n2->get_owner_id() << "\n";
                   if (fact->get_num_args() == 2) {
                       tout << "fact(0): #" << fact->get_arg(0)->get_id() << ", fact(1): #" << fact->get_arg(1)->get_id() << "\n";
                   }
                   tout << mk_bounded_pp(n1->get_owner(), m_manager, 10) << "\n";
                   tout << mk_bounded_pp(n2->get_owner(), m_manager, 10) << "\n";
                   tout << mk_bounded_pp(fact, m_manager, 10) << "\n";
                   tout << mk_ll_pp(pr, m_manager, true, false););
            SASSERT(m_ctx.is_true(n2) || m_ctx.is_false(n2));
            SASSERT(fact == n1_owner || (m_manager.is_not(fact) && fact->get_arg(0) == n1_owner));
            if (m_ctx.is_true(n2))
                pr = m_manager.mk_iff_true(pr);
            else
                pr = m_manager.mk_iff_false(pr);
            m_new_proofs.push_back(pr);
            return pr;
        }
        if (m_manager.coarse_grain_proofs())
            return pr;
        TRACE("norm_eq_proof",
              tout << "#" << n1->get_owner_id() << " = #" << n2->get_owner_id() << "\n";
              tout << mk_ll_pp(pr, m_manager, true, false););
        SASSERT(m_manager.is_eq(fact) || m_manager.is_iff(fact));
        SASSERT((fact->get_arg(0) == n1->get_owner() && fact->get_arg(1) == n2->get_owner()) ||
                (fact->get_arg(1) == n1->get_owner() && fact->get_arg(0) == n2->get_owner()));
        if (fact->get_arg(0) == n1_owner && fact->get_arg(1) == n2_owner)
            return pr;
        pr = m_manager.mk_symmetry(pr);
        m_new_proofs.push_back(pr);
        return pr;
    }

    /**
       \brief Return a proof object for n1 = n2 using the given eq_justification
       if its antecedents are already available. Otherwise, return 0 and add
       the missing antecedents to the todo-list.
    */
    proof * conflict_resolution::get_proof(enode * n1, enode * n2, eq_justification js) {
        unsigned num_args;
        switch (js.get_kind()) {
        case eq_justification::AXIOM:
            UNREACHABLE();
            return 0;
        case eq_justification::EQUATION:
            TRACE("proof_gen_bug", tout << js.get_literal() << "\n"; m_ctx.display_literal_info(tout, js.get_literal()););
            return norm_eq_proof(n1, n2, get_proof(js.get_literal()));
        case eq_justification::JUSTIFICATION:
            return norm_eq_proof(n1, n2, get_proof(js.get_justification()));
        case eq_justification::CONGRUENCE:
            num_args = n1->get_num_args();
            SASSERT(num_args == n2->get_num_args());
            SASSERT(n1->get_owner()->get_decl() == n2->get_owner()->get_decl());
            if (js.used_commutativity()) {
                bool visited = true;
                SASSERT(num_args == 2);
                enode * c1_1 = n1->get_arg(0);
                enode * c1_2 = n1->get_arg(1);
                enode * c2_1 = n2->get_arg(0);
                enode * c2_2 = n2->get_arg(1);
                ptr_buffer<proof> prs;
                if (c1_1 != c2_2) {
                    proof * pr = get_proof(c1_1, c2_2);
                    prs.push_back(pr);
                    if (!pr)
                        visited = false;
                }
                if (c1_2 != c2_1) {
                    proof * pr = get_proof(c1_2, c2_1);
                    prs.push_back(pr);
                    if (!pr)
                        visited = false;
                }
                if (!visited)
                    return 0;
                app * e1 = n1->get_owner();
                app * e2 = n2->get_owner();
                app * e2_prime = m_manager.mk_app(e2->get_decl(), e2->get_arg(1), e2->get_arg(0));
                proof * pr1 = 0;
                if (!prs.empty()) {
                    pr1 = m_manager.mk_congruence(e1, e2_prime, prs.size(), prs.c_ptr());
                    m_new_proofs.push_back(pr1);
                }
                else {
                    TRACE("comm_proof_bug", tout << "e1: #" << e1->get_id() << " e2: #" << e2->get_id() << "\n" << mk_bounded_pp(e1, m_manager, 10) <<
                          "\n" << mk_bounded_pp(e2, m_manager, 10) << "\n";);
                    // SASSERT(e1 == e2);
                }
                proof * pr2 = m_manager.mk_commutativity(e2_prime);
                m_new_proofs.push_back(pr2);
                return m_manager.mk_transitivity(pr1, pr2);
            }
            else {
                bool visited = true;
                ptr_buffer<proof> prs;
                for (unsigned i = 0; i < num_args; i++) {
                    enode * c1 = n1->get_arg(i);
                    enode * c2 = n2->get_arg(i);
                    if (c1 != c2) {
                        proof * pr = get_proof(c1, c2);
                        prs.push_back(pr);
                        if (!pr)
                            visited = false;
                    }
                }
                if (!visited)
                    return 0;
                proof * pr = m_manager.mk_congruence(n1->get_owner(), n2->get_owner(), prs.size(), prs.c_ptr());
                m_new_proofs.push_back(pr);
                return pr;
            }
        default:
            UNREACHABLE();
            return 0;
        }
    }

    /**
       \brief Return the proof object associated with the given literal if it already
       exists. Otherwise, return 0 and add l to the todo-list.
    */
    proof * conflict_resolution::get_proof(literal l) {
        proof * pr;
        if (m_lit2proof.find(l, pr)) {
            TRACE("proof_gen_bug", tout << "lit2pr_cached: #" << l << "\n";);
            return pr;
        }
        m_todo_pr.push_back(tp_elem(l));
        return 0;
    }

    /**
       \brief Return a proof object for l using the given b_justification
       if its antecedents are already available. Otherwise, return 0 and add
       the missing antecedents to the todo-list.
    */
    proof * conflict_resolution::get_proof(literal l, b_justification js) {
#ifdef _TRACE
        static unsigned invocation_counter = 0;
        invocation_counter++;
        #define DUMP_AFTER_NUM_INVOCATIONS 213473
        CTRACE("get_proof_bug_after", invocation_counter >= DUMP_AFTER_NUM_INVOCATIONS, tout << "START get_proof\n";);
#endif
        // l is a hypothesis: if it is marked, and the justification for the variable l.var() is js.
        // we need the second condition, because the core builds proofs as:
        //
        //  p1: is a proof of "A"
        //  p2: is a proof of "not A"
        //  [unit-resolution p1 p2]: false
        //
        // Let us assume that "A" was assigned first during propagation.
        // Then, the "resolve" method will never select "not A" as a hypothesis.
        // "not_A" will be the not_l argument in this method.
        // Since we are assuming that "A" was assigned first", m_ctx.get_justification("A") will be
        // p1.
        //
        // So, the test "m_ctx.get_justification(l.var()) == js" is used to check
        // if l was assigned before ~l.
        if ((m_ctx.is_marked(l.var()) && m_ctx.get_justification(l.var()) == js) || (js.get_kind() == b_justification::AXIOM)) {
            expr_ref l_expr(m_manager);
            m_ctx.literal2expr(l, l_expr);
            proof * pr = m_manager.mk_hypothesis(l_expr.get());
            m_new_proofs.push_back(pr);
            return pr;
        }
        else {
            SASSERT(js.get_kind() != b_justification::BIN_CLAUSE);
            SASSERT(js.get_kind() != b_justification::AXIOM);
            if (js.get_kind() == b_justification::CLAUSE) {
                clause * cls       = js.get_clause();
                justification * js = cls->get_justification();
                SASSERT(js);
                proof * pr         = get_proof(js);
                ptr_buffer<proof> prs;
                bool visited       = pr != 0;
                TRACE("get_proof_bug", if (pr != 0) tout << js->get_name() << "\n";);
                CTRACE("get_proof_bug_after", invocation_counter >= DUMP_AFTER_NUM_INVOCATIONS, if (pr != 0) tout << js->get_name() << "\n";);
                CTRACE("get_proof_bug_after", invocation_counter >= DUMP_AFTER_NUM_INVOCATIONS, if (pr != 0) js->display_debug_info(*this, tout););
                prs.push_back(pr);
                unsigned num_lits = cls->get_num_literals();
                unsigned i = 0;
                SASSERT(l == false_literal || l == cls->get_literal(0) || l == cls->get_literal(1));
                if (l != false_literal) {
                    if (cls->get_literal(0) == l) {
                        i = 1;
                    }
                    else {
                        SASSERT(l == cls->get_literal(1));
                        proof * pr = get_proof(~cls->get_literal(0));
                        prs.push_back(pr);
                        if (!pr)
                            visited = false;
                        i = 2;
                    }
                }
                for (; i < num_lits; i++) {
                    proof * pr = get_proof(~cls->get_literal(i));
                    prs.push_back(pr);
                    if (!pr)
                        visited = false;
                }
                if (!visited)
                    return 0;
                expr_ref l_exr(m_manager);
                m_ctx.literal2expr(l, l_exr);
                TRACE("get_proof_bug",
                      tout << "clause:\n";
                      for (unsigned i = 0; i < num_lits; i++) {
                          tout << cls->get_literal(i).index() << "\n";
                          expr_ref l_expr(m_manager);
                          m_ctx.literal2expr(cls->get_literal(i), l_expr);
                          tout << mk_pp(l_expr, m_manager) << "\n";
                      }
                      tout << "antecedents:\n";
                      for (unsigned i = 0; i < prs.size(); i++) {
                          tout << mk_pp(m_manager.get_fact(prs[i]), m_manager) << "\n";
                      }
                      tout << "consequent:\n" << mk_pp(l_exr, m_manager) << "\n";);
                CTRACE("get_proof_bug_after",
                       invocation_counter >= DUMP_AFTER_NUM_INVOCATIONS,
                       tout << "clause, num_lits: " << num_lits << ":\n";
                       for (unsigned i = 0; i < num_lits; i++) {
                           tout << cls->get_literal(i).index() << "\n";
                           expr_ref l_expr(m_manager);
                           m_ctx.literal2expr(cls->get_literal(i), l_expr);
                           tout << mk_pp(l_expr, m_manager) << "\n";
                       }
                       tout << "antecedents:\n";
                       for (unsigned i = 0; i < prs.size(); i++) {
                           tout << mk_pp(m_manager.get_fact(prs[i]), m_manager) << "\n";
                       }
                       tout << "consequent:\n" << mk_pp(l_exr, m_manager) << "\n";);
                TRACE("get_proof",
                      tout << l.index() << " " << true_literal.index() << " " << false_literal.index() << " ";
                      m_ctx.display_literal(tout, l); tout << " --->\n";
                      tout << mk_ll_pp(l_exr, m_manager););
                CTRACE("get_proof_bug_after",
                       invocation_counter >= DUMP_AFTER_NUM_INVOCATIONS,
                       tout << l.index() << " " << true_literal.index() << " " << false_literal.index() << " ";
                       m_ctx.display_literal(tout, l); tout << " --->\n";
                       tout << mk_ll_pp(l_exr, m_manager););
                pr = m_manager.mk_unit_resolution(prs.size(), prs.c_ptr(), l_exr);
                m_new_proofs.push_back(pr);
                return pr;
            }
            else {
                return get_proof(js.get_justification());
            }
        }
    }

    /**
       \brief Return the proof object associated with the given justification
       if it already exists. Otherwise, return 0 and add js to the todo-list.
    */
    proof * conflict_resolution::get_proof(justification * js) {
        proof * pr;
        if (m_js2proof.find(js, pr)) {
            TRACE("proof_gen_bug", tout << "js2pr_cached: #" << js << "\n";);
            return pr;
        }
        SASSERT(js != 0);
        m_todo_pr.push_back(tp_elem(js));
        return 0;
    }

    void conflict_resolution::init_mk_proof() {
        TRACE("proof_gen_bug", tout << "reset_caches\n";);
        m_new_proofs.reset();
        m_todo_pr.reset();
        m_eq2proof.reset();
        m_lit2proof.reset();
        m_js2proof.reset();
        literal_vector::iterator it  = m_lemma.begin();
        literal_vector::iterator end = m_lemma.end();
        for (; it != end;  ++it)
            m_ctx.set_mark((*it).var());
    }

    bool conflict_resolution::visit_b_justification(literal l, b_justification js) {
        // l is a hypothesis: if it is marked, and the justification for the variable l.var() is js.
        // See: get_proof(literal l, b_justification js)
        if (m_ctx.is_marked(l.var()) && m_ctx.get_justification(l.var()) == js)
            return true;
        SASSERT(js.get_kind() != b_justification::BIN_CLAUSE);
        CTRACE("visit_b_justification_bug", js.get_kind() == b_justification::AXIOM, tout << "l: " << l << "\n"; m_ctx.display(tout););

        if (js.get_kind() == b_justification::AXIOM) 
            return true;
        SASSERT(js.get_kind() != b_justification::AXIOM);
        if (js.get_kind() == b_justification::CLAUSE) {
            clause * cls      = js.get_clause();
            bool visited      = get_proof(cls->get_justification()) != 0;
            unsigned num_lits = cls->get_num_literals();
            unsigned i        = 0;
            if (l != false_literal) {
                if (cls->get_literal(0) == l) {
                    i = 1;
                }
                else {
                    SASSERT(cls->get_literal(1) == l);
                    if (get_proof(~cls->get_literal(0)) == 0)
                        visited = false;
                    i = 2;
                }
            }
            for (; i < num_lits; i++) {
                SASSERT(cls->get_literal(i) != l);
                if (get_proof(~cls->get_literal(i)) == 0)
                    visited = false;
            }
            return visited;
        }
        else
            return get_proof(js.get_justification()) != 0;
    }

    void conflict_resolution::mk_proof(literal l, b_justification js) {
        SASSERT(!m_lit2proof.contains(l));
        proof * pr = get_proof(l, js);
        SASSERT(pr);
        TRACE("proof_gen_bug", tout << "lit2pr_saved: #" << l << "\n";);
        m_lit2proof.insert(l, pr);
        TRACE("mk_proof",
              tout << mk_bounded_pp(m_ctx.bool_var2expr(l.var()), m_manager, 10) << "\n";
              tout << "storing proof for: "; m_ctx.display_literal(tout, l); tout << "\n";
              tout << mk_ll_pp(pr, m_manager););
    }

    /**
       \brief Given that lhs = ... = rhs, and lhs reaches rhs in the 'proof' tree branch.
       Then, return true if all proof objects needed to create the proof steps are already
       available. Otherwise return false and update m_todo_pr with info about the proof
       objects that need to be created.
    */
    bool conflict_resolution::visit_trans_proof(enode * lhs, enode * rhs) {
        SASSERT(lhs->trans_reaches(rhs));
        bool visited = true;
        while (lhs != rhs) {
            eq_justification js = lhs->m_trans.m_justification;
            switch (js.get_kind()) {
            case eq_justification::AXIOM:
                UNREACHABLE();
                break;
            case eq_justification::EQUATION:
                if (get_proof(js.get_literal()) == 0)
                    visited = false;
                break;
            case eq_justification::JUSTIFICATION:
                if (get_proof(js.get_justification()) == 0)
                    visited = false;
                break;
            case eq_justification::CONGRUENCE: {
                enode * n1 = lhs;
                enode * n2 = lhs->m_trans.m_target;
                unsigned num_args = n1->get_num_args();
                SASSERT(num_args == n2->get_num_args());
                if (js.used_commutativity()) {
                    SASSERT(num_args == 2);
                    enode * c1_1 = n1->get_arg(0);
                    enode * c1_2 = n1->get_arg(1);
                    enode * c2_1 = n2->get_arg(0);
                    enode * c2_2 = n2->get_arg(1);
                    if (c1_1 != c2_2 && get_proof(c1_1, c2_2) == 0)
                        visited = false;
                    if (c1_2 != c2_1 && get_proof(c1_2, c2_1) == 0)
                        visited = false;
                }
                else {
                    for (unsigned i = 0; i < num_args; i++) {
                        enode * c1 = n1->get_arg(i);
                        enode * c2 = n2->get_arg(i);
                        if (c1 != c2 && get_proof(c1, c2) == 0)
                            visited = false;
                    }
                }
                break;
            }
            default:
                UNREACHABLE();
            }
            lhs = lhs->m_trans.m_target;
        }
        return visited;
    }

    /**
       \brief Return true if all proof objects that are used to build the proof that lhs = rhs were
       already built. If the result is false, then m_todo_pr is updated with info about the proof
       objects that need to be created.
    */
    bool conflict_resolution::visit_eq_justications(enode * lhs, enode * rhs) {
        enode * c = find_common_ancestor(lhs, rhs);
        bool v1 = visit_trans_proof(lhs, c);
        bool v2 = visit_trans_proof(rhs, c);
        return v1 && v2;
    }

    /**
       \brief Given that lhs = ... = rhs, and lhs reaches rhs in the
       trans proof branch, then build a proof object for each equality
       in the sequence, and insert them into result.
    */
    void conflict_resolution::mk_proof(enode * lhs, enode * rhs, ptr_buffer<proof> & result) {
        SASSERT(lhs->trans_reaches(rhs));
        while (lhs != rhs) {
            eq_justification js = lhs->m_trans.m_justification;
            enode * n1          = lhs;
            enode * n2          = lhs->m_trans.m_target;
            proof * pr          = get_proof(n1, n2, js);
            SASSERT(pr);
            result.push_back(pr);
            lhs = lhs->m_trans.m_target;
        }
    }

    void conflict_resolution::mk_proof(enode * lhs, enode * rhs) {
        SASSERT(!m_eq2proof.contains(lhs, rhs));
        enode * c = find_common_ancestor(lhs, rhs);
        ptr_buffer<proof> prs1;
        mk_proof(lhs, c, prs1);
        ptr_buffer<proof> prs2;
        mk_proof(rhs, c, prs2);
        while (!prs2.empty()) {
            proof * pr = prs2.back();
            if (m_manager.fine_grain_proofs()) {
                pr = m_manager.mk_symmetry(pr);
                m_new_proofs.push_back(pr);
                prs1.push_back(pr);
            }
            else {
                prs1.push_back(pr);
            }
            prs2.pop_back();
        }
        proof * pr = 0;
        SASSERT(!prs1.empty());
        if (prs1.size() == 1)
            pr = prs1[0];
        else {
            TRACE("mk_transitivity",
                  unsigned sz = prs1.size();
                  for (unsigned i = 0; i < sz; i++) {
                      tout << mk_ll_pp(prs1[i], m_manager) << "\n";
                  });
            pr = m_manager.mk_transitivity(prs1.size(), prs1.c_ptr(), lhs->get_owner(), rhs->get_owner());
        }
        m_new_proofs.push_back(pr);
        TRACE("proof_gen_bug", tout << "eq2pr_saved: #" << lhs->get_owner_id() << " #" << rhs->get_owner_id() << "\n";);
        m_eq2proof.insert(lhs, rhs, pr);
    }

    void conflict_resolution::mk_conflict_proof(b_justification conflict, literal not_l) {
        SASSERT(conflict.get_kind() != b_justification::BIN_CLAUSE);
        SASSERT(conflict.get_kind() != b_justification::AXIOM);
        SASSERT(not_l == null_literal || conflict.get_kind() == b_justification::JUSTIFICATION);
        TRACE("mk_conflict_proof", tout << "lemma literals: ";
              literal_vector::iterator it  = m_lemma.begin();
              literal_vector::iterator end = m_lemma.end();
              for (; it != end; ++it) {
                  m_ctx.display_literal(tout, *it);
                  tout << " ";
              }
              tout << "\n";);
        init_mk_proof();
        literal consequent;
        if (not_l == null_literal) {
            consequent = false_literal;
        }
        else {
            consequent = ~not_l;
            m_todo_pr.push_back(tp_elem(not_l));
        }
        visit_b_justification(consequent, conflict);
        
        while (!m_todo_pr.empty()) {
            tp_elem & elem = m_todo_pr.back();

            switch (elem.m_kind) {
            case tp_elem::EQUALITY: {
                enode * lhs        = elem.m_lhs;
                enode * rhs        = elem.m_rhs;
                if (m_eq2proof.contains(lhs, rhs))
                    m_todo_pr.pop_back();
                else if (visit_eq_justications(lhs, rhs)) {
                    m_todo_pr.pop_back();
                    mk_proof(lhs, rhs);
                }
                break;
            }
            case tp_elem::JUSTIFICATION: {
                justification * js = elem.m_js;
                if (m_js2proof.contains(js))
                    m_todo_pr.pop_back();
                else {
                    proof * pr         = js->mk_proof(*this);
                    if (pr) {
                        m_todo_pr.pop_back();
                        m_new_proofs.push_back(pr);
                        TRACE("proof_gen_bug", tout << "js2pr_saved: #" << js << "\n";);
                        m_js2proof.insert(js, pr);
                    }
                }
                break;
            }
            case tp_elem::LITERAL: {
                literal l = to_literal(elem.m_lidx);
                if (m_lit2proof.contains(l))
                    m_todo_pr.pop_back();
                else {
                    b_justification js = m_ctx.get_justification(l.var());
                    if (visit_b_justification(l, js)) {
                        m_todo_pr.pop_back();
                        mk_proof(l, js);
                    }
                }
                break;
            }
            default:
                UNREACHABLE();
            }
        }

        SASSERT(visit_b_justification(consequent, conflict));
        proof * pr = 0;
        if (not_l == null_literal) {
            pr = get_proof(false_literal, conflict);
            SASSERT(pr);
        }
        else {
            proof * prs[2] = { 0, 0};
            m_lit2proof.find(not_l, prs[0]);
            SASSERT(prs[0]);
            prs[1]         = get_proof(consequent, conflict);
            SASSERT(prs[1]);
            pr = m_manager.mk_unit_resolution(2, prs);
        }
        expr_ref_buffer lits(m_manager);
        literal_vector::iterator it  = m_lemma.begin();
        literal_vector::iterator end = m_lemma.end();
        for (; it != end; ++it) {
            m_ctx.unset_mark((*it).var());
            expr_ref l_expr(m_manager);
            m_ctx.literal2expr(*it, l_expr);
            lits.push_back(l_expr);
        }
        expr * fact = 0;
        switch (lits.size()) {
        case 0:  fact = 0; break;
        case 1:  fact = lits[0]; break;
        default: fact = m_manager.mk_or(lits.size(), lits.c_ptr());
        }
        if (fact == 0)
            m_lemma_proof = pr;
        else
            m_lemma_proof = m_manager.mk_lemma(pr, fact);
        m_new_proofs.reset();
    }

    void conflict_resolution::process_antecedent_for_unsat_core(literal antecedent) {
        bool_var var = antecedent.var();
        TRACE("conflict", tout << "processing antecedent: ";
          m_ctx.display_literal_info(tout << antecedent << " ", antecedent);
          tout << (m_ctx.is_marked(var)?"marked":"not marked");
          tout << "\n";);

        if (!m_ctx.is_marked(var)) {
            m_ctx.set_mark(var);
            m_unmark.push_back(var);
        }
        if (m_ctx.is_assumption(var)) {
            m_assumptions.push_back(antecedent);
        }
    }

    void conflict_resolution::process_justification_for_unsat_core(justification * js) {
        literal_vector & antecedents = m_tmp_literal_vector;
        antecedents.reset();
        justification2literals_core(js, antecedents);
        literal_vector::iterator it  = antecedents.begin();
        literal_vector::iterator end = antecedents.end();
        for(; it != end; ++it)
            process_antecedent_for_unsat_core(*it);
    }

    void conflict_resolution::mk_unsat_core(b_justification conflict, literal not_l) {
        SASSERT(m_ctx.tracking_assumptions());
        m_assumptions.reset();
        m_unmark.reset();

        SASSERT(m_conflict_lvl <= m_ctx.get_search_level());
        unsigned search_lvl = m_ctx.get_search_level();

        b_justification js  = conflict;
        literal consequent  = false_literal;
        if (not_l != null_literal) {
            consequent      = ~not_l;
        }

        int idx = skip_literals_above_conflict_level();

        if (not_l != null_literal)
            process_antecedent_for_unsat_core(consequent);

        if (m_assigned_literals.empty()) {
            goto end_unsat_core;
        }

        while (true) {
            TRACE("unsat_core_bug", tout << consequent << " js.get_kind(): " << js.get_kind() << ", idx: " << idx << "\n";);
            switch (js.get_kind()) {
            case b_justification::CLAUSE: {
                clause * cls = js.get_clause();
                unsigned num_lits = cls->get_num_literals();
                unsigned i        = 0;
                if (consequent != false_literal) {
                    SASSERT(cls->get_literal(0) == consequent || cls->get_literal(1) == consequent);
                    if (cls->get_literal(0) == consequent) {
                        i = 1;
                    }
                    else {
                        process_antecedent_for_unsat_core(~cls->get_literal(0));
                        i = 2;
                    }
                }
                for(; i < num_lits; i++) {
                    literal l = cls->get_literal(i);
                    process_antecedent_for_unsat_core(~l);
                }
                justification * js = cls->get_justification();
                if (js)
                    process_justification_for_unsat_core(js);
                break;
            }
            case b_justification::BIN_CLAUSE:
                SASSERT(consequent.var() != js.get_literal().var());
                process_antecedent_for_unsat_core(js.get_literal());
                break;
            case b_justification::AXIOM:
                break;
            case b_justification::JUSTIFICATION:
                process_justification_for_unsat_core(js.get_justification());
                break;
            default:
                UNREACHABLE();
            }

            if (m_ctx.is_assumption(consequent.var())) {
                m_assumptions.push_back(consequent);
            }
            while (idx >= 0) {
                literal l = m_assigned_literals[idx];
                TRACE("unsat_core_bug", tout << "l: " << l << ", get_assign_level(l): " << m_ctx.get_assign_level(l) << ", is_marked(l): " << m_ctx.is_marked(l.var()) << "\n";);
                if (m_ctx.get_assign_level(l) < search_lvl)
                    goto end_unsat_core;
                if (m_ctx.is_marked(l.var()))
                    break;
                idx--;
            }
            if (idx < 0) {
                goto end_unsat_core;
            }

            SASSERT(idx >= 0);
            consequent     = m_assigned_literals[idx];
            bool_var c_var = consequent.var();
            SASSERT(m_ctx.get_assign_level(c_var) == search_lvl);
            js             = m_ctx.get_justification(c_var);
            idx--;
        }

    end_unsat_core:
        TRACE("unsat_core", tout << "assumptions:\n"; m_ctx.display_literals(tout, m_assumptions); tout << "\n";);
        reset_unmark_and_justifications(0, 0);
    }

    conflict_resolution * mk_conflict_resolution(ast_manager & m,
                                                 context & ctx,
                                                 dyn_ack_manager & dack_manager,
                                                 smt_params const & params,
                                                 literal_vector const & assigned_literals,
                                                 vector<watch_list> & watches) {
        return alloc(conflict_resolution, m, ctx, dack_manager, params, assigned_literals, watches);
    }

};

