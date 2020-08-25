/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    euf_egraph.cpp

Abstract:

    E-graph layer

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-23

--*/

#include "ast/euf/euf_egraph.h"
#include "ast/ast_pp.h"

namespace euf {

    void egraph::undo_eq(enode* r1, enode* n1, unsigned r2_num_parents) {
        enode* r2 = r1->get_root();
        r2->dec_class_size(r1->class_size());
        std::swap(r1->m_next, r2->m_next);
        auto begin = r2->begin_parents() + r2_num_parents, end = r2->end_parents();
        for (auto it = begin; it != end; ++it) 
            m_table.erase(*it);
        for (enode* c : enode_class(r1)) 
            c->m_root = r1;
        for (auto it = begin; it != end; ++it) 
            m_table.insert(*it);
        r2->m_parents.shrink(r2_num_parents);
        unmerge_justification(n1);
    }

    enode* egraph::mk_enode(expr* f, unsigned num_args, enode * const* args) {
        enode* n = enode::mk(m_region, f, num_args, args);
        m_nodes.push_back(n);
        m_exprs.push_back(f);
        return n;
    }

    void egraph::reinsert(enode* n) {
        unsigned num_parents = n->m_parents.size();
        for (unsigned i = 0; i < num_parents; ++i) {
            enode* p = n->m_parents[i];
            if (is_equality(p)) {
                reinsert_equality(p);
            }
            else {
                auto rc = m_table.insert(p);
                merge(rc.first, p, justification::congruence(rc.second));
                if (inconsistent())
                    break;
            }
        }
    }

    void egraph::reinsert_equality(enode* p) {
        SASSERT(is_equality(p));
        if (p->get_arg(0)->get_root() == p->get_arg(1)->get_root()) 
            m_new_eqs.push_back(p);
    }

    bool egraph::is_equality(enode* p) const {
        return m.is_eq(p->get_owner());
    }

    void egraph::dedup_equalities() {
        unsigned j = 0;
        for (enode* p : m_new_eqs) {
            if (!p->is_marked1())
                m_new_eqs[j++] = p;
            p->mark1();
        }
        for (enode* p : m_new_eqs)
            p->unmark1();
        m_new_eqs.shrink(j);        
    }

    void egraph::force_push() {
        for (; m_num_scopes > 0; --m_num_scopes) {
            scope s;
            s.m_inconsistent = m_inconsistent;
            s.m_num_eqs = m_eqs.size();
            s.m_num_nodes = m_nodes.size();
            m_scopes.push_back(s);
            m_region.push_scope();
        }
    }

    void egraph::update_children(enode* n) {
        for (enode* child : enode_args(n)) 
            child->get_root()->add_parent(n);
        n->set_update_children();            
    }

    enode* egraph::mk(expr* f, unsigned num_args, enode *const* args) {
        SASSERT(!find(f));
        force_push();
        enode *n = mk_enode(f, num_args, args);
        SASSERT(n->class_size() == 1);
        m_expr2enode.setx(f->get_id(), n, nullptr);
        if (num_args == 0 && m.is_unique_value(f))
            n->mark_interpreted();
        if (num_args == 0) 
            return n;
        if (is_equality(n)) {
            update_children(n);
            return n;
        }
        enode_bool_pair p = m_table.insert(n);
        enode* r = p.first;
        if (r == n) {
            update_children(n);
        }
        else {
            SASSERT(r->get_owner() != n->get_owner());
            merge_justification(n, r, justification::congruence(p.second));
            std::swap(n->m_next, r->m_next);
            n->m_root = r;
            r->inc_class_size(n->class_size());
            push_eq(n, n, r->num_parents());
        }
        return n;
    }

    void egraph::pop(unsigned num_scopes) {
        if (num_scopes <= m_num_scopes) {
            m_num_scopes -= num_scopes;
            return;
        }
        num_scopes -= m_num_scopes;
        unsigned old_lim = m_scopes.size() - num_scopes;
        scope s = m_scopes[old_lim];
        for (unsigned i = m_eqs.size(); i-- > s.m_num_eqs; ) {
            auto const& p = m_eqs[i];
            undo_eq(p.r1, p.n1, p.r2_num_parents);
        }        
        for (unsigned i = m_nodes.size(); i-- > s.m_num_nodes; ) {
            enode* n = m_nodes[i];
            if (n->num_args() > 1)
                m_table.erase(n);
            m_expr2enode[n->get_owner_id()] = nullptr;
            n->~enode();
        }
        m_inconsistent = s.m_inconsistent;
        m_eqs.shrink(s.m_num_eqs);
        m_nodes.shrink(s.m_num_nodes);
        m_exprs.shrink(s.m_num_nodes);
        m_scopes.shrink(old_lim);        
        m_region.pop_scope(num_scopes);  
    }

    void egraph::merge(enode* n1, enode* n2, justification j) {
        SASSERT(m.get_sort(n1->get_owner()) == m.get_sort(n2->get_owner()));
        TRACE("euf", tout << n1->get_owner_id() << " == " << n2->get_owner_id() << "\n";);
        force_push();
        enode* r1 = n1->get_root();
        enode* r2 = n2->get_root();
        if (r1 == r2)
            return;
        if (r1->interpreted() && r2->interpreted()) {
            set_conflict(n1, n2, j);
            return;
        }
        if ((r1->class_size() > r2->class_size() && !r2->interpreted()) || r1->interpreted()) {
            std::swap(r1, r2);
            std::swap(n1, n2);
        }
        if ((m.is_true(r2->get_owner()) || m.is_false(r2->get_owner())) && j.is_congruence())
            m_new_lits.push_back(n1);
        for (enode* p : enode_parents(n1)) 
            m_table.erase(p);            
        for (enode* p : enode_parents(n2)) 
            m_table.erase(p);            
        push_eq(r1, n1, r2->num_parents());
        merge_justification(n1, n2, j);
        for (enode* c : enode_class(n1)) 
            c->m_root = r2;
        std::swap(r1->m_next, r2->m_next);
        r2->inc_class_size(r1->class_size());   
        r2->m_parents.append(r1->m_parents);
        m_worklist.push_back(r2);
    }

    void egraph::propagate() {
        m_new_eqs.reset();
        m_new_lits.reset();
        SASSERT(m_num_scopes == 0 || m_worklist.empty());
        unsigned head = 0, tail = m_worklist.size();
        while (head < tail && m.limit().inc() && !inconsistent()) {
            TRACE("euf", tout << "iterate: " << head << " " << tail << "\n";);
            for (unsigned i = head; i < tail && !inconsistent(); ++i) {
                enode* n = m_worklist[i]->get_root();
                if (!n->is_marked1()) {
                    n->mark1();
                    m_worklist[i] = n;
                    reinsert(n);
                }
            }
            for (unsigned i = head; i < tail; ++i) 
                m_worklist[i]->unmark1();
            head = tail;
            tail = m_worklist.size();
        }
        m_worklist.reset();
        dedup_equalities();
    }

    void egraph::set_conflict(enode* n1, enode* n2, justification j) {
        if (m_inconsistent)
            return;
        m_inconsistent = true;
        m_n1 = n1;
        m_n2 = n2;
        m_justification = j;
    }

    void egraph::merge_justification(enode* n1, enode* n2, justification j) {
        SASSERT(n1->reaches(n1->get_root()));
        n1->reverse_justification();
        n1->m_target = n2;
        n1->m_justification = j;
        SASSERT(n1->get_root()->reaches(n1));
    }

    void egraph::unmerge_justification(enode* n1) {
        // r1 -> ..  -> n1 -> n2 -> ... -> r2
        // where n2 = n1->m_target
        SASSERT(n1->get_root()->reaches(n1));
        n1->m_target        = nullptr;
        n1->m_justification = justification::axiom();
        n1->get_root()->reverse_justification();
        // ---------------
        // n1 -> ... -> r1
        // n2 -> ... -> r2
        SASSERT(n1->reaches(n1->get_root()));
        SASSERT(n1->get_root()->m_target == nullptr);
    }

    /**
       \brief generate an explanation for a congruence.
       Each pair of children under a congruence have the same roots
       and therefore have a least common ancestor. We only need
       explanations up to the least common ancestors.
     */
    void egraph::push_congruence(enode* n1, enode* n2, bool comm) {
        SASSERT(n1->get_decl() == n2->get_decl());
        if (comm && 
            n1->get_arg(0)->get_root() == n2->get_arg(1)->get_root() &&
            n1->get_arg(1)->get_root() == n2->get_arg(0)->get_root()) {
            push_lca(n1->get_arg(0), n2->get_arg(1));
            push_lca(n1->get_arg(1), n2->get_arg(0));
            return;
        }
            
        for (unsigned i = 0; i < n1->num_args(); ++i) 
            push_lca(n1->get_arg(i), n2->get_arg(i));
    }

    void egraph::push_lca(enode* a, enode* b) {
        SASSERT(a->get_root() == b->get_root());
        enode* n = a;
        while (n) {
            n->mark2();
            n = n->m_target;
        }
        n = b;
        while (n) {
            if (n->is_marked2()) 
                n->unmark2();   
            else if (!n->is_marked1()) 
                m_todo.push_back(n);
            n = n->m_target;
        }
        n = a;
        while (n->is_marked2()) {            
            n->unmark2();
            if (!n->is_marked1())
                m_todo.push_back(n);
            n = n->m_target;
        }
    }

    void egraph::push_todo(enode* n) {
        while (n) {
            m_todo.push_back(n);
            n = n->m_target;
        }
    }

    template <typename T>
    void egraph::explain(ptr_vector<T>& justifications) {
        SASSERT(m_inconsistent);
        SASSERT(m_todo.empty());
        push_todo(m_n1);
        push_todo(m_n2);
        explain_eq(justifications, m_n1, m_n2, m_justification);
        explain_todo(justifications);
    }

    template <typename T>
    void egraph::explain_eq(ptr_vector<T>& justifications, enode* a, enode* b, bool comm) {
        SASSERT(m_todo.empty());
        push_congruence(a, b, comm);
        explain_todo(justifications);
    }

    template <typename T>
    void egraph::explain_todo(ptr_vector<T>& justifications) {
        for (unsigned i = 0; i < m_todo.size(); ++i) {
            enode* n = m_todo[i];
            if (n->m_target && !n->is_marked1()) {
                n->mark1();
                explain_eq(justifications, n, n->m_target, n->m_justification);
            }
        }
        for (enode* n : m_todo) 
            n->unmark1();
        m_todo.reset();        
    }

    void egraph::invariant() {
        for (enode* n : m_nodes)
            n->invariant();
    }

    std::ostream& egraph::display(std::ostream& out) const {
        m_table.display(out);
        for (enode* n : m_nodes) {
            out << std::setw(5)
                << n->get_owner_id() << " := ";
            out << n->get_root()->get_owner_id() << " ";
            expr* f = n->get_owner();
            if (is_app(f)) 
                out << to_app(f)->get_decl()->get_name() << " ";
            else if (is_quantifier(f)) 
                out << "q ";
            else 
                out << "v ";
            for (enode* arg : enode_args(n)) 
                out << arg->get_owner_id() << " ";            
            out << std::setw(20) << " parents: ";
            for (enode* p : enode_parents(n)) 
                out << p->get_owner_id() << " ";
            out << "\n";            
        }
        return out;
    }
}

template void euf::egraph::explain(ptr_vector<int>& justifications);
template void euf::egraph::explain_todo(ptr_vector<int>& justifications);
template void euf::egraph::explain_eq(ptr_vector<int>& justifications, enode* a, enode* b, bool comm);

template void euf::egraph::explain(ptr_vector<unsigned>& justifications);
template void euf::egraph::explain_todo(ptr_vector<unsigned>& justifications);
template void euf::egraph::explain_eq(ptr_vector<unsigned>& justifications, enode* a, enode* b, bool comm);

