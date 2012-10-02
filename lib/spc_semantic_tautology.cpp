/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    spc_semantic_tautology.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-11.

Revision History:

--*/
#include"spc_semantic_tautology.h"
#include"ast_pp.h"

namespace spc {

    expr * find(expr2expr & f, expr * n) {
#ifdef _TRACE
        expr * _n = n;
#endif
        ptr_buffer<expr> path;
        expr * next;
        while (f.find(n, next)) {
            path.push_back(n);
            n = next;
        }
        ptr_buffer<expr>::iterator it  = path.begin();
        ptr_buffer<expr>::iterator end = path.end();
        for (; it != end; ++it) {
            expr * prev = *it;
            f.insert(prev, n);
        }
        SASSERT(n);
        TRACE("semantic_tautology_detail", tout << "find(#" << _n->get_id() << ") = #" << n->get_id() << "\n";);
        return n;
    }
    
    semantic_tautology::semantic_tautology(ast_manager & m):
        m_manager(m),
        m_cg_table(DEFAULT_HASHTABLE_INITIAL_CAPACITY, cg_hash(m_manager, m_find), cg_eq(m_find)) {
    }

    unsigned semantic_tautology::cg_hash::operator()(app * n) const { 
        TRACE("semantic_tautology_detail", tout << "hash code of:\n" << mk_pp(n, m_manager) << "\n";);
        unsigned r = get_composite_hash<app *, k_hash, c_hash>(n, n->get_num_args(), m_k_hash, m_c_hash); 
        TRACE("semantic_tautology_detail", tout << "result: " << r << "\n";);
        return r;
    }

    bool semantic_tautology::cg_eq::operator()(app * n1, app * n2) const {
        if (n1->get_decl() != n2->get_decl() || n1->get_num_args() != n2->get_num_args())
            return false;
        unsigned num_args = n1->get_num_args();
        for (unsigned i = 0; i < num_args; i++)
            if (spc::find(m_find, n1->get_arg(i)) != spc::find(m_find, n2->get_arg(i)))
                return false;
        return true;
    }
    
    bool semantic_tautology::is_target(unsigned num_lits, literal * lits) {
        bool has_diseq     = false;
        bool has_non_diseq = false;
        for (unsigned i = 0; i < num_lits; i++) {
            literal const & l = lits[i];
            if (l.sign() && m_manager.is_eq(l.atom())) 
                has_diseq = true;
            else 
                has_non_diseq = true;
        }
        return has_diseq && has_non_diseq;
    }

    void semantic_tautology::reset() {
        m_region.reset();
        m_init_todo.reset();
        m_todo.reset();
        m_already_found.reset();
        m_use_list.reset();
        m_find.reset();
        m_size.reset();
        m_cg_table.reset();
    }

    void semantic_tautology::update_use_list(app * parent, expr * child) {
        list<app*> * use_list = 0;
        m_use_list.find(child, use_list);
        use_list = new (m_region) list<app*>(parent, use_list);
        m_use_list.insert(child, use_list);
    }

    inline void semantic_tautology::push_init_core(expr * n) {
        if (is_app(n) && to_app(n)->get_num_args() > 0)
            m_init_todo.push_back(to_app(n));
    }

    inline void semantic_tautology::push_init(expr * atom) {
        if (m_manager.is_eq(atom)) {
            push_init_core(to_app(atom)->get_arg(0));
            push_init_core(to_app(atom)->get_arg(1));
        }
        else 
            push_init_core(atom);
    }

    void semantic_tautology::init_use_list() {
        while (!m_init_todo.empty()) {
            app * n = m_init_todo.back();
            m_init_todo.pop_back();
            if (!m_already_found.contains(n)) {
                unsigned num_args = n->get_num_args();
                SASSERT(num_args > 0);
                m_cg_table.insert(n);
                m_already_found.insert(n);
                for (unsigned i = 0; i < num_args; i++) {
                    expr * c = n->get_arg(i);
                    update_use_list(n, c);
                    push_init_core(c);
                }
            }
        }
    }

    void semantic_tautology::init(unsigned num_lits, literal * lits) {
        reset();
        for (unsigned i = 0; i < num_lits; i++) {
            literal const & l = lits[i];
            expr * atom = l.atom();
            push_init(atom);
            if (l.sign() && m_manager.is_eq(atom))
                m_todo.push_back(expr_pair(to_app(atom)->get_arg(0), to_app(atom)->get_arg(1)));
        }
        init_use_list();
    }

    void semantic_tautology::remove_parents(expr * n1) {
        list<app*> * use_list = 0;
        m_use_list.find(n1, use_list);
        while (use_list) {
            TRACE("semantic_tautology", tout << "removing parent from cg_table:\n" << mk_pp(use_list->head(), m_manager) << "\n";);
            m_cg_table.erase(use_list->head());
            use_list = use_list->tail();
        }
    }

    void semantic_tautology::restore_parents(expr * n1, expr * n2) {
        list<app*> * use_list = 0;
        m_use_list.find(n1, use_list);
        while (use_list) {
            app * parent = use_list->head();
            app * other  = 0;
            if (m_cg_table.find(parent, other)) {
                TRACE("semantic_tautology", tout << "new congruence:\n" << mk_pp(parent, m_manager) << "\n" << mk_pp(other, m_manager) << "\n";);
                if (parent != other)
                    m_todo.push_back(expr_pair(parent, other));
            }
            else {
                TRACE("semantic_tautology", tout << "restoring parent to cg_table:\n" << mk_pp(parent, m_manager) << "\n";);
                m_cg_table.insert(parent);
                update_use_list(parent, n2);
            }
            use_list = use_list->tail();
        }
    }

    void semantic_tautology::assert_eq(expr * n1, expr * n2) {
        n1 = find(n1);
        n2 = find(n2);
        if (n1 == n2)
            return;
        TRACE("semantic_tautology", tout << "processing equality:\n" << mk_pp(n1, m_manager) << " " << n1->get_id() << "\n" << 
              mk_pp(n2, m_manager) << " " << n2->get_id() << "\n";);
        unsigned sz1 = 1;
        unsigned sz2 = 1;
        m_size.find(n1, sz1);
        m_size.find(n2, sz2);
        if (sz1 > sz2)
            std::swap(n1, n2);
        remove_parents(n1);
        TRACE("semantic_tautology", tout << "merging equivalence classes\n";);
        m_find.insert(n1, n2);
        m_size.insert(n2, sz1 + sz2);
        restore_parents(n1, n2);
    }

    void semantic_tautology::process_eqs() {
        while (!m_todo.empty()) {
            expr_pair const & p = m_todo.back();
            expr * lhs = p.first;
            expr * rhs = p.second;
            m_todo.pop_back();
            assert_eq(lhs, rhs);
        }
    }
    
    bool semantic_tautology::contains_complement(unsigned num_lits, literal * lits, unsigned i, bool sign, expr * atom) {
        atom = find(atom);
        for (unsigned j = i + 1; j < num_lits; j++) {
            literal const & l = lits[j];
            if (l.sign() != sign && find(l.atom()) == atom)
                return true;
        }
        return false;
    }
    
    bool semantic_tautology::is_tautology(unsigned num_lits, literal * lits) {
        for (unsigned i = 0; i < num_lits; i++) {
            literal const & l = lits[i];
            expr * atom       = l.atom();
            if (!l.sign() && m_manager.is_eq(atom) && find(to_app(atom)->get_arg(0)) == find(to_app(atom)->get_arg(1))) 
                return true;
            if (!m_manager.is_eq(atom) && contains_complement(num_lits, lits, i, l.sign(), atom))
                return true;
        }
        return false;
    }
    
    bool semantic_tautology::operator()(unsigned num_lits, literal * lits) {
        if (!is_target(num_lits, lits))
            return false;
        init(num_lits, lits);
        process_eqs();
        bool r = is_tautology(num_lits, lits);
        TRACE("semantic_tautology", display(tout, num_lits, lits, m_manager); tout << "\nis semantic tautology: " << r << "\n";);
        return r;
    }

};
