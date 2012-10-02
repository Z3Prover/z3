/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    spc_rewrite.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-12.

Revision History:

--*/
#include"spc_rewriter.h"
#include"spc_decl_plugin.h"
#include"ast_pp.h"

namespace spc {

    rewriter::rewriter(ast_manager & m, simplifier & simp, order & ord, asserted_literals & al):
        simplifier(m),
        m_asserted_literals(al),
        m_order(ord),
        m_spc_fid(m.get_family_id("spc")),
        m_subst(m),
        m_st(m),
        m_visitor(m_order, m_subst, m_cls_use_list) {

        reserve_offsets(3);

        borrow_plugins(simp);
    }

    rewriter::~rewriter() {
        release_plugins();
    }
    
    inline void rewriter::reserve_vars(unsigned num_vars) {
        m_subst.reserve_vars(num_vars);
        m_order.reserve_vars(num_vars);
        m_asserted_literals.reserve_vars(num_vars);
    }

    void rewriter::reserve_offsets(unsigned num_offsets) {
        m_subst.reserve_offsets(num_offsets);
        m_order.reserve_offsets(num_offsets);
    }

    inline bool rewriter::demodulator(clause * cls) const {
        if (cls->get_num_literals() != 1)
            return false;
        literal const & l = cls->get_literal(0);
        return !l.sign() && m_manager.is_eq(l.atom());
    }

    inline void rewriter::insert(clause * cls, expr * source) {
        if (!is_var(source)) {
            TRACE("rewriter_detail", tout << "inserting into rewriter index:\n"; cls->display(tout, m_manager); tout << "\n";);
            flush_cache();
            m_st.insert(to_app(source));
            m_cls_use_list.insert(cls, source);
        }
    }
    
    void rewriter::insert(clause * cls) {
        if (demodulator(cls)) {
            reserve_vars(cls->get_num_vars());
            literal const & l = cls->get_literal(0);
            app * eq = to_app(l.atom());
            if (l.is_oriented()) {
                expr * source = l.is_left() ? eq->get_arg(0) : eq->get_arg(1);
                insert(cls, source);
            }
            else {
                insert(cls, eq->get_arg(0));
                insert(cls, eq->get_arg(1));
            }
        }
    }

    inline void rewriter::erase(clause * cls, expr * source) {
        if (!is_var(source)) {
            flush_cache();
            m_cls_use_list.erase(cls, source);
            if (m_cls_use_list.empty(source))
                m_st.erase(to_app(source));
        }
    }

    void rewriter::erase(clause * cls) {
        if (demodulator(cls)) {
            literal const & l = cls->get_literal(0);
            app * eq = to_app(l.atom());
            if (l.is_oriented()) {
                expr * source = l.is_left() ? eq->get_arg(0) : eq->get_arg(1);
                erase(cls, source);
            }
            else {
                erase(cls, eq->get_arg(0));
                erase(cls, eq->get_arg(1));
            }
        }
    }

    bool rewriter::visitor::operator()(expr * e) {
        if (m_cls_use_list.empty(e)) 
            return true; // continue;
        clause_use_list::iterator it  = m_cls_use_list.begin(e);
        clause_use_list::iterator end = m_cls_use_list.end(e);
        for (; it != end; ++it) {
            m_clause = *it;
            SASSERT(m_clause->get_num_literals() == 1);
            literal & l = m_clause->get_literal(0);
            expr * atom = l.atom();
            SASSERT(!l.sign() && m_manager.is_eq(atom));
            SASSERT(to_app(atom)->get_arg(0) == e || to_app(atom)->get_arg(1) == e);
            m_source = to_app(atom)->get_arg(0);
            m_target = to_app(atom)->get_arg(1);
            if (m_source != e)
                std::swap(m_source, m_target);
            SASSERT(m_source == e);
            TRACE("rewriter", tout << "found generalization:\n" << mk_pp(m_source, m_manager) << "\n" << 
                  mk_pp(m_target, m_manager) << "\nsubstitution\n";
                  m_subst.display(tout); tout << "m_subst: " << &m_subst << "\n";
                  tout << "checking ordering constraints...\n";);
            if (l.is_oriented() || m_order.greater(expr_offset(m_source, 1), expr_offset(m_target, 1), &m_subst)) {
                m_found = true;
                return false; // stop
            }
            TRACE("rewriter", tout << "failed ordering constraints...\n";);
        }
        return true; // continue
    }

    void rewriter::save_justification(justification * j) {
        if (std::find(m_justifications.begin(), m_justifications.end(), j) == m_justifications.end())
            m_justifications.push_back(j);
    }

    proof * rewriter::mk_demodulation_proof(expr * old_expr, expr * new_expr, proof * parent) {
        if (m_manager.fine_grain_proofs()) {
            SASSERT(parent);
            return m_manager.mk_app(m_spc_fid, PR_DEMODULATION, parent, m_manager.mk_eq(old_expr, new_expr));
        }
        return 0;
    }

    void rewriter::reset() {
        m_st.reset();
        m_cls_use_list.reset();
    }

    void rewriter::reduce_literal(literal const & l, literal & l_r, proof * & l_pr) {
        if (m_st.empty()) {
            l_r = l;
            l_pr = 0;
            return;
        }

        expr * atom = l.atom();
        expr *  r;
        proof * r_pr;
        m_proofs.reset();
        while (true) {
            reduce_core(atom);
            get_cached(atom, r, r_pr);
            if (m_manager.fine_grain_proofs() && r_pr)
                m_proofs.push_back(r_pr);
            if (atom == r)
                break;
            atom = r;
        }
        l_r = literal(atom, l.sign());
        if (m_manager.fine_grain_proofs())
            l_pr = m_proofs.empty() ? 0 : m_manager.mk_transitivity(m_proofs.size(), m_proofs.c_ptr());
    }

    clause * rewriter::operator()(clause * cls) {
        reserve_vars(cls->get_num_vars());
        SASSERT(m_found_literals.empty());
        m_justifications.reset();
        m_max_scope_lvl = cls->get_scope_lvl();
        
        literal_buffer    new_literals(m_manager);
        proof_ref_buffer  new_proofs(m_manager);
        bool              changed = false;

        unsigned num_lits = cls->get_num_literals();
        for (unsigned i = 0; i < num_lits; i++) {
            literal & l = cls->get_literal(i);
            literal l_r;
            proof * l_pr = 0;
            reduce_literal(l, l_r, l_pr);
         
            if (l != l_r) {
                changed = true;
            }

            if (!l_r.is_false(m_manager) && !m_found_literals.contains(l_r)) {
                m_found_literals.insert(l_r);

                // apply simplify reflect rules
                expr * atom     = l_r.atom();
                clause * unit = 0;
                TRACE("rewriter", tout << "adding literal: " << mk_pp(atom, m_manager) << "\n";);
                if (l_r.sign()) {
                    if (m_manager.is_eq(atom))
                        unit = m_asserted_literals.subsumes(to_app(atom)->get_arg(0), to_app(atom)->get_arg(1));
                    else
                        unit = m_asserted_literals.gen(atom, false);
                }
                else {
                    // check if there is a generalization of the negation of the current literal.
                    unit = m_asserted_literals.gen(atom, true);
                }

                if (unit) {
                    // new literal was resolved
                    justification * j = unit->get_justification();
                    m_justifications.push_back(j);
                    changed = true;
                }
                else {
                    // keep new literal
                    new_literals.push_back(l_r);
                }
            }
            else {
                // removed duplicate or resolved literal.
                changed = true;
            }

            if (m_manager.fine_grain_proofs() && l_pr != 0) {
                new_proofs.push_back(l_pr);
            }
        }

        m_found_literals.reset();

        if (!changed) {
            m_found_literals.reset();
            return cls;
        }

        proof * new_pr = mk_rewrite_proof(m_manager, m_spc_fid, new_literals.size(), new_literals.c_ptr(), cls->get_justification()->get_proof(), 
                                          new_proofs.size(), new_proofs.c_ptr());

        justification * new_j = rewrite_justification::mk(m_manager, cls->get_justification(), m_justifications.size(), m_justifications.c_ptr(), new_pr);
        
        if (m_max_scope_lvl == cls->get_scope_lvl()) {
            // peform destructive update
            cls->update_lits(m_manager, new_literals.size(), new_literals.c_ptr(), new_j);
            return cls;
        }
        else {
            SASSERT(m_max_scope_lvl > cls->get_scope_lvl());
            // create new clause
            // the old clause will be frozen
            return clause::mk(m_manager, new_literals.size(), new_literals.c_ptr(), new_j, m_max_scope_lvl);
        }
    }

};

