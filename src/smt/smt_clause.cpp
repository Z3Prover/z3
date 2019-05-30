/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_clause.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-19.

Revision History:

--*/
#include "smt/smt_clause.h"
#include "smt/smt_justification.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_pp.h"

namespace smt {
    /**
       \brief Create a new clause.
       bool_var2expr_map is a mapping from bool_var -> expr, it is only used if save_atoms == true.
    */
    clause * clause::mk(ast_manager & m, unsigned num_lits, literal * lits, clause_kind k, justification * js,
                        clause_del_eh * del_eh, bool save_atoms, expr * const * bool_var2expr_map) {
        SASSERT(smt::is_axiom(k) || js == nullptr || !js->in_region());
        SASSERT(num_lits >= 2);
        unsigned sz                = get_obj_size(num_lits, k, save_atoms, del_eh != nullptr, js != nullptr);
        void * mem                 = m.get_allocator().allocate(sz);
        clause * cls               = new (mem) clause();
        cls->m_num_literals        = num_lits;
        cls->m_capacity            = num_lits;
        cls->m_kind                = k;
        cls->m_reinit              = save_atoms;
        cls->m_reinternalize_atoms = save_atoms;
        cls->m_has_atoms           = save_atoms;
        cls->m_has_del_eh          = del_eh != nullptr;
        cls->m_has_justification   = js != nullptr;
        cls->m_deleted             = false;
        SASSERT(!m.proofs_enabled() || js != 0);
        memcpy(cls->m_lits, lits, sizeof(literal) * num_lits);
        if (cls->is_lemma())
            cls->set_activity(1);
        if (del_eh)
            *(const_cast<clause_del_eh **>(cls->get_del_eh_addr())) = del_eh;
        if (js)
            *(const_cast<justification **>(cls->get_justification_addr())) = js;
        if (save_atoms) {
            for (unsigned i = 0; i < num_lits; i++) {
                expr * atom = bool_var2expr_map[lits[i].var()];
                m.inc_ref(atom);
                const_cast<expr**>(cls->get_atoms_addr())[i] = TAG(expr*, atom, lits[i].sign());
            }
        }

        DEBUG_CODE({
            SASSERT(!cls->is_lemma() || cls->get_activity() == 1);
            SASSERT(cls->get_del_eh() == del_eh);
            SASSERT(cls->get_justification() == js);
            for (unsigned i = 0; i < num_lits; i++) {
                SASSERT((*cls)[i] == lits[i]);
                SASSERT(!save_atoms || cls->get_atom(i) == bool_var2expr_map[lits[i].var()]);
            }});
        return cls;
    }

    void clause::deallocate(ast_manager & m) {
        clause_del_eh * del_eh = get_del_eh();
        if (del_eh)
            (*del_eh)(m, this);
        if (is_lemma() && m_has_justification) {
            justification * js = get_justification();
            if (js) {
                SASSERT(!js->in_region());
                js->del_eh(m);
                dealloc(js);
            }
        }
        unsigned num_atoms = get_num_atoms();
        for (unsigned i = 0; i < num_atoms; i++) {
            SASSERT(m_reinit || get_atom(i) == 0);
            m.dec_ref(get_atom(i));
        }
        m.get_allocator().deallocate(get_obj_size(m_capacity, get_kind(), m_has_atoms, m_has_del_eh, m_has_justification), this);
    }

    void clause::release_atoms(ast_manager & m) {
        unsigned num_atoms = get_num_atoms();
        for (unsigned i = 0; i < num_atoms; i++) {
            m.dec_ref(get_atom(i));
            const_cast<expr**>(get_atoms_addr())[i] = nullptr;
        }
    }

    std::ostream& clause::display(std::ostream & out, ast_manager & m, expr * const * bool_var2expr_map) const {
        out << "(clause";
        for (unsigned i = 0; i < m_num_literals; i++) {
            out << " ";
            m_lits[i].display(out, m, bool_var2expr_map);
        }
        return out << ")";
    }

    std::ostream& clause::display_compact(std::ostream & out, ast_manager & m, expr * const * bool_var2expr_map) const {
        out << "(clause";
        for (unsigned i = 0; i < m_num_literals; i++) {
            out << " ";
            m_lits[i].display_compact(out, bool_var2expr_map);
        }
        return out << ")";
    }

    std::ostream& clause::display_smt2(std::ostream & out, ast_manager & m, expr * const * bool_var2expr_map) const {
        expr_ref_vector args(m);
        for (unsigned i = 0; i < m_num_literals; i++) {
            literal lit = m_lits[i];
            args.push_back(bool_var2expr_map[lit.var()]);
            if (lit.sign()) args[args.size()-1] = m.mk_not(args.back());
        }
        expr_ref disj(m.mk_or(args.size(), args.c_ptr()), m);
        return out << disj;
    }

};
