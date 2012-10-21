/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    spc_superposition.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-15.

Revision History:

--*/
#include"spc_superposition.h"
#include"ast_pp.h"

namespace spc {

    superposition::superposition(ast_manager & m, order & o, statistics & s):
        m_manager(m),
        m_order(o),
        m_stats(s),
        m_subst(m),
        m_p(m),
        m_r(m),
        m_normalize_vars(m),
        m_spc_fid(m.get_family_id("spc")) {
        m_subst.reserve_offsets(3);
        m_deltas[0] = 0;
        m_deltas[1] = 0;
    }

    superposition::~superposition() {
    }
    
    void superposition::insert_p(clause * cls, expr * lhs, unsigned i) {
        m_p.insert(lhs);
        m_subst.reserve_vars(m_p.get_approx_num_regs());
        m_p2clause_set.insert(clause_pos_pair(cls, i), lhs);
    }

    void superposition::insert_p(clause * cls, literal & l, unsigned i) {
        l.set_p_indexed(true);
        expr * atom = l.atom();
        if (!m_manager.is_eq(atom))
            return;
        if (l.is_oriented())
            insert_p(cls, l.is_left() ? l.lhs() : l.rhs(), i);
        else {
            insert_p(cls, l.lhs(), i);
            insert_p(cls, l.rhs(), i);
        }
    }

    void superposition::insert_r(clause * cls, expr * n, unsigned i, bool lhs) {
        if (is_app(n)) {
            unsigned idx = (i << 1) | static_cast<unsigned>(lhs);
            
            clause_pos_pair new_pair(cls, idx);
            SASSERT(m_todo.empty());
            m_todo.push_back(to_app(n));
            while (!m_todo.empty()) {
                app * n = m_todo.back();
                m_todo.pop_back();
                clause_pos_set * s = m_r2clause_set.get_parents(n);
                if (s == 0 || !s->contains(new_pair)) {
                    m_r.insert(n);
                    m_r2clause_set.insert(new_pair, n);
                    unsigned num_args = n->get_num_args();
                    for (unsigned i = 0; i < num_args; i++) {
                        expr * c = n->get_arg(i);
                        if (is_app(c))
                            m_todo.push_back(to_app(c));
                    }
                }
            }
        }
    }

    void superposition::insert_r(clause * cls, literal & l, unsigned i) {
        l.set_r_indexed(true);
        expr * atom = l.atom();
        if (m_manager.is_eq(atom)) {
            expr * lhs = l.lhs();
            expr * rhs = l.rhs();
            if (l.is_oriented()) {
                bool left = true;
                if (!l.is_left()) {
                    left  = false;
                    std::swap(lhs, rhs);
                }
                insert_r(cls, lhs, i, left);
            }
            else {
                insert_r(cls, lhs, i, true);
                insert_r(cls, rhs, i, false);
            }
        }
        else {
            insert_r(cls, atom, i, false);
        }
        m_subst.reserve_vars(m_r.get_approx_num_regs());
    }

    void superposition::insert(clause * cls) {
        unsigned num_lits = cls->get_num_literals();
        for (unsigned i = 0; i < num_lits; i++) {
            literal & l = cls->get_literal(i);
            if (l.is_p_indexed() || cls->is_eligible_for_paramodulation(m_order, l)) {
                if (!l.sign() && m_manager.is_eq(l.atom()))
                    insert_p(cls, l, i);
                insert_r(cls, l, i);
            }
            else if (l.is_r_indexed() || cls->is_eligible_for_resolution(m_order, l)) {
                insert_r(cls, l, i);
            }
        }
        TRACE("superposition_detail",
              tout << "adding clause: "; cls->display(tout, m_manager); tout << "\n";
              tout << "p index:\n";
              m_p.display(tout);
              tout << "r index:\n";
              m_r.display(tout););
    }

    void superposition::erase_p(clause * cls, expr * lhs, unsigned i) {
        m_p2clause_set.erase(clause_pos_pair(cls, i), lhs);
        if (m_p2clause_set.empty(lhs))
            m_p.erase(lhs);
    }

    void superposition::erase_p(clause * cls, literal & l, unsigned i) {
        expr * atom = l.atom();
        if (!m_manager.is_eq(atom))
            return;
        if (l.is_oriented()) 
            erase_p(cls, l.is_left() ? l.lhs() : l.rhs(), i);
        else {
            erase_p(cls, l.lhs(), i);
            erase_p(cls, l.rhs(), i);
        }
    }

    void superposition::erase_r(clause * cls, literal & l, unsigned i) {
        clause_pos_pair pair(cls, i);

        expr * atom = l.atom();
        SASSERT(is_app(atom));
        SASSERT(m_todo.empty());
        m_todo.push_back(to_app(atom));

        while (!m_todo.empty()) {
            app * n = m_todo.back();
            m_todo.pop_back();
            switch (m_r2clause_set.erase(pair, n)) {
            case 0: // pair is not a parent of n
                break;
            case 1: // pair is the last parent of n
                m_r.erase(n);
            default:
                unsigned num_args = n->get_num_args();
                for (unsigned i = 0; i < num_args; i++) {
                    expr * c = n->get_arg(i);
                    if (is_app(c))
                        m_todo.push_back(to_app(c));
                }
            }
        }
    }

    void superposition::erase(clause * cls) {
        unsigned num_lits = cls->get_num_literals();
        for (unsigned i = 0; i < num_lits; i++) {
            literal & l = cls->get_literal(i);
            if (l.is_p_indexed())
                erase_p(cls, l, i);
            if (l.is_r_indexed())
                erase_r(cls, l, i);
        }
    }

    void superposition::reset() {
        m_p.reset();
        m_p2clause_set.reset();
        m_r.reset();
        m_r2clause_set.reset();
    }

    /**
       \brief Copy to result the literals of s except literal at position idx. Apply the substitution m_subst,
       assuming that the variables of s are in the variable bank offset. The deltas for each bank are
       stored in m_deltas.
    */
    void superposition::copy_literals(clause * s, unsigned idx, unsigned offset, literal_buffer & result) {
        unsigned num_lits = s->get_num_literals();
        for (unsigned i = 0; i < num_lits; i++)
            if (i != idx) {
                literal const & l = s->get_literal(i);
                expr_ref new_atom(m_manager);
                m_subst.apply(2, m_deltas, expr_offset(l.atom(), offset), new_atom);
                TRACE("superposition_copy", tout << "i: " << i << ", idx: " << idx << ", offset: " << offset << "\natom:\n";
                      tout << mk_pp(l.atom(), m_manager) << "\nnew_atom:\n" << mk_pp(new_atom, m_manager) << "\n";);
                result.push_back(literal(new_atom, l.sign()));
            }
    }

    void superposition::normalize_literals(unsigned num_lits, literal * lits, literal_buffer & result) {
        m_normalize_vars.reset();
        for (unsigned i = 0; i < num_lits; i++) {
            literal const & l = lits[i];
            result.push_back(literal(m_normalize_vars(l.atom()), l.sign()));
        }
    }

    void superposition::mk_sp_clause(unsigned num_lits, literal * lits, justification * p1, justification * p2) {
        literal_buffer new_literals(m_manager);
        normalize_literals(num_lits, lits, new_literals);
        justification * js = mk_superposition_justification(m_manager, m_spc_fid, p1, p2, 
                                                            new_literals.size(), new_literals.c_ptr(),
                                                            m_normalize_vars.get_num_vars(), m_normalize_vars.get_vars());
        clause * new_cls = clause::mk(m_manager, new_literals.size(), new_literals.c_ptr(), js, 0);
        m_new_clauses->push_back(new_cls);
        TRACE("superposition", tout << "new superposition clause:\n"; new_cls->display(tout, m_manager); tout << "\n";);
        m_stats.m_num_superposition++;
    }

    void superposition::mk_res_clause(unsigned num_lits, literal * lits, justification * p1, justification * p2) {
        literal_buffer new_literals(m_manager);
        normalize_literals(num_lits, lits, new_literals);
        justification * js = mk_resolution_justification(m_manager, m_spc_fid, p1, p2, 
                                                         new_literals.size(), new_literals.c_ptr(),
                                                         m_normalize_vars.get_num_vars(), m_normalize_vars.get_vars());
        clause * new_cls = clause::mk(m_manager, new_literals.size(), new_literals.c_ptr(), js, 0);
        m_new_clauses->push_back(new_cls);
        TRACE("superposition", tout << "new resolution clause:\n"; new_cls->display(tout, m_manager); tout << "\n";);
        m_stats.m_num_resolution++;
    }

    /**
       \brief Given the equation (= lhs rhs) of the clause being
       added, try to apply resolution where the clause being added
       is the main clause in the superposition rule.
    */
    void superposition::try_superposition_main(expr * lhs, expr * rhs) {
        m_lhs    = lhs;
        m_rhs    = rhs;
        m_subst.reset_subst();
        TRACE("spc_superposition", tout << "try_superposition_main, lhs:\n" << mk_pp(m_lhs, m_manager) << "\nrhs:\n" << mk_pp(m_rhs, m_manager) << "\n";
              tout << "substitution:\n"; m_subst.display(tout););
        r_visitor v(*this, m_subst);
        m_r.unify(lhs, v);
    }

    /**
       \brief Try to apply superposition rule using the clause
       being added (m_clause) as main clause, and its literal m_lit
       as the equation.
    */
    void superposition::try_superposition_main() {
        expr * lhs = m_lit->lhs();
        expr * rhs = m_lit->rhs();
        TRACE("spc_superposition", tout << "trying superposition:\n" << mk_pp(lhs, m_manager) << "\n" << mk_pp(rhs, m_manager) << "\nis_oriented: " << m_lit->is_oriented() << "\n";);
        if (m_lit->is_oriented()) {
            if (!m_lit->is_left())
                std::swap(lhs, rhs);
            try_superposition_main(lhs, rhs);
        }
        else {
            try_superposition_main(lhs, rhs);
            try_superposition_main(rhs, lhs);
        }
    }

    void superposition::found_r(expr * r) {
        TRACE("spc_superposition", tout << "found_r:\n" << mk_pp(r, m_manager) << "\n";
              tout << "substitution:\n"; m_subst.display(tout););
        if (m_r2clause_set.empty(r))
            return;
        TRACE("spc_superposition", tout << "r2clause is not empty.\n";);
        if (!m_lit->is_oriented() && m_order.greater(m_rhs, m_lhs, &m_subst))
            return;
        TRACE("spc_superposition", tout << "order restriction was met.\n";);
        if (!m_clause->is_eligible_for_paramodulation(m_order, *m_lit, 0, &m_subst))
            return;
        TRACE("spc_superposition", tout << "literal is eligible for paramodulation.\n";);
        r2clause_set::iterator it  = m_r2clause_set.begin(r);
        r2clause_set::iterator end = m_r2clause_set.end(r);
        for (; it != end; ++it) {
            clause_pos_pair & p = *it;
            clause * aux_cls    = p.first;
            unsigned aux_idx    = p.second >> 1;
            //
            // The following optimization is incorrect (if statement).
            // For example, it prevents the Z3 from proving the trivial benchmark
            // c = X, 
            // a != b
            // using the order a < b < c
            //
            // To prove, this example we need to generate the clause Y = X by applying superposition of c = X on itself.
            // We can see that by renaming the first clause to c = Y, and then, substituting c in the original by Y.
            //
            // Actually, this optimization is correct when the set of variables in m_lhs is a superset of the set of variables in m_rhs, 
            // because in this case, the new literal will be equivalent to true. In the example above, this is not the case,
            // since m_lhs does not contain any variable, and m_rhs contains one.
            // 
            
            //
            // if (r == m_lhs && m_clause == aux_cls && m_idx == aux_idx)
            //    continue;
            //
            bool     in_lhs     = (p.second & 1) != 0;
            TRACE("spc_superposition", tout << "aux_cls:\n"; aux_cls->display(tout, m_manager); tout << "\naux_idx: " << aux_cls << ", in_lhs: " << in_lhs << "\n";);
            literal & aux_lit   = aux_cls->get_literal(aux_idx);
            if (!aux_cls->is_eligible_for_resolution(m_order, aux_lit, 1, &m_subst))
                continue;
            literal_buffer new_literals(m_manager);
            m_subst.reset_cache();
            if (m_manager.is_eq(aux_lit.atom())) {
                expr * lhs = aux_lit.lhs();
                expr * rhs = aux_lit.rhs();
                TRACE("spc_superposition", tout << "aux_lit lhs:\n" << mk_pp(lhs, m_manager) << "\nrhs:\n" << mk_pp(rhs, m_manager) << "\n";);
                if (!in_lhs)
                    std::swap(lhs, rhs);
                if (!aux_lit.is_oriented() && m_order.greater(rhs, lhs, 1, &m_subst)) {
                    TRACE("spc_superposition", tout << "failed order constraint.\n";);
                    continue;
                }
                expr_ref new_lhs(m_manager), new_rhs(m_manager);
                m_subst.apply(2, m_deltas, expr_offset(lhs, 1), expr_offset(r, 1), expr_offset(m_rhs, 0), new_lhs);
                m_subst.apply(2, m_deltas, expr_offset(rhs, 1), new_rhs);
                TRACE("spc_superposition", tout << "aux_lit new_lhs:\n" << mk_pp(new_lhs, m_manager) << "\nnew_rhs:\n" << mk_pp(new_rhs, m_manager) << "\n";);
                expr * new_eq  = m_manager.mk_eq(new_lhs, new_rhs);
                new_literals.push_back(literal(new_eq, aux_lit.sign()));
            }
            else {
                expr_ref new_atom(m_manager);
                m_subst.apply(2, m_deltas, expr_offset(aux_lit.atom(), 1), new_atom);
                new_literals.push_back(literal(new_atom, aux_lit.sign()));
            }
            copy_literals(m_clause, m_idx, 0,   new_literals);
            copy_literals(aux_cls,  aux_idx, 1, new_literals);
            TRACE("superposition", tout << "found r target: " << mk_pp(r, m_manager) << " for \n" <<
                  mk_pp(m_lhs, m_manager) << "\nmain clause: "; m_clause->display(tout, m_manager);
                  tout << "\naux clause: "; aux_cls->display(tout, m_manager); tout << "\nat pos: " <<
                  aux_idx << "\n";);
            mk_sp_clause(new_literals.size(), new_literals.c_ptr(), m_clause->get_justification(), aux_cls->get_justification());
        }
    }

    /**
       \brief Try to apply superposition rule using the clause
       being added (m_clause) as the aux clause, and its literal m_lit
       as the target.
    */
    void superposition::try_superposition_aux() {
        TRACE("superposition_aux", tout << "superposition aux:\n"; m_clause->display(tout, m_manager); 
              tout << "\nusing literal: " << m_idx << "\n";);
        if (m_manager.is_eq(m_lit->atom())) {
            expr * lhs = m_lit->lhs();
            expr * rhs = m_lit->rhs();
            if (m_lit->is_oriented()) {
                if (!m_lit->is_left())
                    std::swap(lhs, rhs);
                try_superposition_aux(lhs, rhs);
            }
            else {
                try_superposition_aux(lhs, rhs);
                try_superposition_aux(rhs, lhs);
            }
        }
        else {
            try_superposition_aux(m_lit->atom(), 0);
        }
    }

    /**
       \brief Use the clause being added as the auxiliary clause in the superposition rule.
    */
    void superposition::try_superposition_aux(expr * lhs, expr * rhs) {
        TRACE("superposition_aux", tout << "try_superposition_aux\n" << mk_pp(lhs, m_manager) << "\n" << mk_pp(rhs, m_manager) << "\n";);
        if (is_var(lhs))
            return;
        m_lhs = lhs;
        m_rhs = rhs;
        SASSERT(m_todo.empty());
        m_todo.push_back(to_app(lhs));
        while (!m_todo.empty()) {
            m_target = m_todo.back();
            m_todo.pop_back();
            m_subst.reset_subst();
            p_visitor v(*this, m_subst);
            TRACE("superposition_aux", tout << "trying to find unifier for:\n" << mk_pp(m_target, m_manager) << "\n";);
            m_p.unify(m_target, v);
            unsigned j = m_target->get_num_args();
            while (j > 0) {
                --j;
                expr * arg = m_target->get_arg(j);
                if (is_app(arg))
                    m_todo.push_back(to_app(arg));
            }
        }
    }

    void superposition::found_p(expr * p) {
        TRACE("superposition_found_p", tout << "found p:\n" << mk_pp(p, m_manager) << "\n";);
        if (m_p2clause_set.empty(p)) {
            TRACE("superposition_found_p", tout << "clause set is empty.\n";);
            return;
        }
        if (m_rhs && !m_lit->is_oriented() && m_order.greater(m_rhs, m_lhs, &m_subst)) {
            TRACE("superposition_found_p", tout << "aux clause failed not rhs > lhs constraint.\n";);
            return;
        }
        if (!m_clause->is_eligible_for_resolution(m_order, *m_lit, 0, &m_subst)) {
            TRACE("superposition_found_p", tout << "aux literal is not eligible for resolution.\n";);
            return;
        }
        p2clause_set::iterator it  = m_p2clause_set.begin(p);
        p2clause_set::iterator end = m_p2clause_set.end(p);
        for (; it != end; ++it) {
            clause_pos_pair & pair   = *it;
            clause * main_cls        = pair.first;
            TRACE("superposition_found_p", tout << "p clause:\n"; main_cls->display(tout, m_manager); tout << "\n";);
            unsigned lit_idx         = pair.second;
            if (p == m_lhs && m_clause == main_cls && m_idx == lit_idx)
                continue;
            literal const & main_lit = main_cls->get_literal(lit_idx);
            SASSERT(m_manager.is_eq(main_lit.atom()));
            expr * lhs               = main_lit.lhs();
            expr * rhs               = main_lit.rhs();
            if (rhs == p)
                std::swap(lhs, rhs);
            SASSERT(lhs == p);
            TRACE("superposition_found_p", tout << "lhs: " << mk_pp(lhs, m_manager) << "\nrhs: " << mk_pp(rhs, m_manager) << "\n";);
            if (!main_lit.is_oriented() && m_order.greater(rhs, lhs, 1, &m_subst))
                continue;
            if (!main_cls->is_eligible_for_paramodulation(m_order, main_lit, 1, &m_subst))
                continue;
            literal_buffer new_literals(m_manager);
            m_subst.reset_cache();
            TRACE("superposition_found_p", tout << "creating new_lhs\n";);
            expr_ref new_lhs(m_manager);
            m_subst.apply(2, m_deltas, expr_offset(m_lhs, 0), expr_offset(m_target, 0), expr_offset(rhs, 1), new_lhs);
            // FIX: m_subst.reset_cache();
            TRACE("superposition_found_p", tout << "new_lhs: " << mk_pp(new_lhs, m_manager) << "\n";
                  m_subst.display(tout););
            expr * new_atom = 0;
            if (m_rhs) {
                TRACE("superposition_found_p", tout << "creating new_rhs\n";);
                expr_ref new_rhs(m_manager);
                m_subst.apply(2, m_deltas, expr_offset(m_rhs, 0), new_rhs);
                TRACE("superposition_found_p", tout << "new_rhs: " << mk_pp(new_rhs, m_manager) << "\n";);
                new_atom = m_manager.mk_eq(new_lhs, new_rhs);
            }
            else
                new_atom = new_lhs;
            TRACE("superposition_found_p", tout << "new_atom: " << mk_pp(new_atom, m_manager) << "\n"; m_subst.display(tout););
            new_literals.push_back(literal(new_atom, m_lit->sign()));
            TRACE("superposition_found_p", tout << "copying literals\n";);
            copy_literals(main_cls, lit_idx, 1, new_literals);
            copy_literals(m_clause, m_idx, 0, new_literals);
            TRACE("superposition", tout << "found p target: " << mk_pp(p, m_manager) << " for \n" <<
                  mk_pp(m_lhs, m_manager) << "\nmain clause: "; main_cls->display(tout, m_manager);
                  tout << "\naux clause: "; m_clause->display(tout, m_manager); tout << "\n";);
            mk_sp_clause(new_literals.size(), new_literals.c_ptr(), main_cls->get_justification(), m_clause->get_justification());
        }
    }

    /**
       \brief Try to apply resolution rule using the clause being added (m_clause).
    */
    void superposition::try_resolution() {
        m_subst.reset_subst();
        res_visitor v(*this, m_subst);
        m_r.unify(m_lit->atom(), v);
    }

    void superposition::found_res(expr * r) {
        if (m_r2clause_set.empty(r))
            return;
        if (!m_clause->is_eligible_for_resolution(m_order, *m_lit, 0, &m_subst))
            return;
        r2clause_set::iterator it  = m_r2clause_set.begin(r);
        r2clause_set::iterator end = m_r2clause_set.end(r);
        for (; it != end; ++it) {
            clause_pos_pair & pair  = *it;
            clause * aux_cls        = pair.first;
            unsigned aux_idx        = pair.second >> 1;
            literal const & aux_lit = aux_cls->get_literal(aux_idx);
            if (aux_lit.sign() == m_lit->sign())
                continue;
            if (aux_lit.atom() != r)
                continue;
            if (!aux_cls->is_eligible_for_resolution(m_order, aux_lit, 1, &m_subst))
                continue;
            literal_buffer new_literals(m_manager);
            m_subst.reset_cache();
            copy_literals(m_clause, m_idx, 0, new_literals);
            copy_literals(aux_cls, aux_idx, 1, new_literals);
            mk_res_clause(new_literals.size(), new_literals.c_ptr(), m_clause->get_justification(), aux_cls->get_justification());
        }
    }
        
    void superposition::operator()(clause * cls, ptr_vector<clause> & new_clauses) {
        m_subst.reserve_vars(cls->get_num_vars());
        m_clause      = cls;
        m_new_clauses = &new_clauses;
        SASSERT(m_deltas[0] == 0);
        m_deltas[1]   = m_clause->get_num_vars();
        unsigned num_lits = cls->get_num_literals();
        for (m_idx = 0; m_idx < num_lits; m_idx++) {
            m_lit      = &(cls->get_literal(m_idx));
            bool is_eq = m_manager.is_eq(m_lit->atom());
            if (!m_lit->sign() && m_lit->is_p_indexed() && is_eq)
                try_superposition_main();
            if (m_lit->is_r_indexed()) {
                try_superposition_aux();
                if (!is_eq)
                    try_resolution();
            }
        }
    }

};


