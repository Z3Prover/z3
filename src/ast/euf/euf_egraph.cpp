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
#include "ast/ast_translation.h"

namespace euf {

    /**
       \brief Trail for add_th_var
    */
    class add_th_var_trail : public trail<egraph> {
        enode *    m_enode;
        theory_id  m_th_id;
    public:
        add_th_var_trail(enode * n, theory_id th_id):
            m_enode(n),
            m_th_id(th_id) {
        }
        
        void undo(egraph & ctx) override {
            theory_var v = m_enode->get_th_var(m_th_id);
            SASSERT(v != null_theory_var);
            m_enode->del_th_var(m_th_id);
            enode * root = m_enode->get_root();
            if (root != m_enode && root->get_th_var(m_th_id) == v) 
                root->del_th_var(m_th_id);
        }
    };

    /**
       \brief Trail for replace_th_var
    */
    class replace_th_var_trail : public trail<egraph> {
        enode *    m_enode;
        unsigned   m_th_id:8;
        unsigned   m_old_th_var:24;
    public:
        replace_th_var_trail(enode * n, theory_id th_id, theory_var old_var):
            m_enode(n),
            m_th_id(th_id),
            m_old_th_var(old_var) {
        }
        
        void undo(egraph & ctx) override {
            SASSERT(m_enode->get_th_var(m_th_id) != null_theory_var);
            m_enode->replace_th_var(m_old_th_var, m_th_id);
        }
    };

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
        if (p->get_arg(0)->get_root() == p->get_arg(1)->get_root()) {
            m_new_lits.push_back(enode_bool_pair(p, true));
            ++m_stats.m_num_eqs;
        }
    }

    bool egraph::is_equality(enode* p) const {
        return m.is_eq(p->get_owner());
    }

    void egraph::force_push() {
        for (; m_num_scopes > 0; --m_num_scopes) {
            scope s;
            s.m_inconsistent = m_inconsistent;
            s.m_num_eqs = m_eqs.size();
            s.m_num_nodes = m_nodes.size();
            s.m_trail_sz  = m_trail.size();
            s.m_new_lits_sz   = m_new_lits.size();
            s.m_new_th_eqs_sz = m_new_th_eqs.size();
            s.m_new_lits_qhead = m_new_lits_qhead;
            s.m_new_th_eqs_qhead = m_new_th_eqs_qhead;
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

    egraph::~egraph() {
        for (enode* n : m_nodes) 
            n->m_parents.finalize();
    }

    void egraph::add_th_var(enode* n, theory_var v, theory_id id) {
        force_push();
        theory_var w = n->get_th_var(id);
        enode* r = n->get_root();

        if (w == null_theory_var) {
            n->add_th_var(v, id, m_region);
            m_trail.push_back(new (m_region) add_th_var_trail(n, id));
            if (r != n) {
                theory_var u = r->get_th_var(id);
                if (u == null_theory_var) 
                    r->add_th_var(v, id, m_region);
                else
                    m_new_th_eqs.push_back(th_eq(id, v, u, n, r));
            }
        }
        else {
            theory_var u = r->get_th_var(id);
            SASSERT(u != v && u != null_theory_var);
            n->replace_th_var(v, id);
            m_trail.push_back(new (m_region) replace_th_var_trail(n, id, u));
            m_new_th_eqs.push_back(th_eq(id, v, u, n, r));
        }
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
        undo_trail_stack<egraph>(*this, m_trail, s.m_trail_sz);
        m_inconsistent = s.m_inconsistent;
        m_new_lits_qhead = s.m_new_lits_qhead;
        m_new_th_eqs_qhead = s.m_new_th_eqs_qhead;
        m_eqs.shrink(s.m_num_eqs);
        m_nodes.shrink(s.m_num_nodes);
        m_exprs.shrink(s.m_num_nodes);
        m_new_lits.shrink(s.m_new_lits_sz);
        m_new_th_eqs.shrink(s.m_new_th_eqs_sz);
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
        ++m_stats.m_num_merge;
        if (r1->interpreted() && r2->interpreted()) {
            set_conflict(n1, n2, j);
            return;
        }
        if ((r1->class_size() > r2->class_size() && !r2->interpreted()) || r1->interpreted()) {
            std::swap(r1, r2);
            std::swap(n1, n2);
        }
        if ((m.is_true(r2->get_owner()) || m.is_false(r2->get_owner())) && j.is_congruence()) {
            m_new_lits.push_back(enode_bool_pair(n1, false));
            ++m_stats.m_num_lits;
        }
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
        merge_th_eq(r1, r2);
        m_worklist.push_back(r2);
    }

    void egraph::merge_th_eq(enode* n, enode* root) {
        SASSERT(n != root);
        for (auto iv : enode_th_vars(n)) {
            theory_id id = iv.get_id();
            theory_var v = root->get_th_var(id);
            if (v == null_theory_var) {
                root->add_th_var(iv.get_var(), id, m_region);                
                m_trail.push_back(new (m_region) add_th_var_trail(root, id));
            }
            else {
                SASSERT(v != iv.get_var());
                m_new_th_eqs.push_back(th_eq(id, v, iv.get_var(), n, root));
            }
        }
    }

    bool egraph::propagate() {
        SASSERT(m_num_scopes == 0 || m_worklist.empty());
        unsigned head = 0, tail = m_worklist.size();
        while (head < tail && m.limit().inc() && !inconsistent()) {
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
        return 
            (m_new_lits_qhead < m_new_lits.size()) || 
            (m_new_th_eqs_qhead < m_new_th_eqs.size()) ||
            inconsistent();
    }

    void egraph::set_conflict(enode* n1, enode* n2, justification j) {
        ++m_stats.m_num_conflicts;
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
        SASSERT(is_app(n1->get_owner()));
        SASSERT(n1->get_decl() == n2->get_decl());
        if (m_used_cc) 
            m_used_cc(to_app(n1->get_owner()), to_app(n2->get_owner()));
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

    enode* egraph::find_lca(enode* a, enode* b) {
        SASSERT(a->get_root() == b->get_root());
        a->mark2_targets<true>();
        while (!b->is_marked2()) 
            b = b->m_target;
        a->mark2_targets<false>();
        return b;
    }
    
    void egraph::push_to_lca(enode* n, enode* lca) {
        while (n != lca) {
            m_todo.push_back(n);
            n = n->m_target;
        }
    }

    void egraph::push_lca(enode* a, enode* b) {
        enode* lca = find_lca(a, b);
        push_to_lca(a, lca);
        push_to_lca(b, lca);
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
    void egraph::explain_eq(ptr_vector<T>& justifications, enode* a, enode* b) {
        SASSERT(m_todo.empty());
        SASSERT(a->get_root() == b->get_root());
        enode* lca = find_lca(a, b);
        push_to_lca(a, lca);
        push_to_lca(b, lca);
        if (m_used_eq)
            m_used_eq(a->get_owner(), b->get_owner(), lca->get_owner());
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

    std::ostream& egraph::display(std::ostream& out, unsigned max_args, enode* n) const {
        out << std::setw(5)
            << n->get_owner_id() << " := ";
        if (!n->is_root()) 
            out << "[" << n->get_root()->get_owner_id() << "] ";
        expr* f = n->get_owner();
        if (is_app(f))
            out << to_app(f)->get_decl()->get_name() << " ";
        else if (is_quantifier(f))
            out << "q ";
        else
            out << "v ";
        for (enode* arg : enode_args(n))
            out << arg->get_owner_id() << " ";
        for (unsigned i = n->num_args(); i < max_args; ++i)
            out << "   ";
        out << "\t";
        for (enode* p : enode_parents(n))
            out << p->get_owner_id() << " ";
        out << "\n";
        return out;
    }

    std::ostream& egraph::display(std::ostream& out) const {
        m_table.display(out);
        unsigned max_args = 0;
        for (enode* n : m_nodes)
            max_args = std::max(max_args, n->num_args());
        for (enode* n : m_nodes) 
            display(out, max_args, n);          
        return out;
    }

    void egraph::collect_statistics(statistics& st) const {
        st.update("euf merge", m_stats.m_num_merge);
        st.update("euf conflicts", m_stats.m_num_conflicts);
        st.update("euf eq prop", m_stats.m_num_eqs);
        st.update("euf lit prop", m_stats.m_num_lits);
    }

    void egraph::copy_from(egraph const& src, std::function<void*(void*)>& copy_justification) {
        SASSERT(m_scopes.empty());
        SASSERT(src.m_scopes.empty());
        SASSERT(m_nodes.empty());
        ptr_vector<enode> old_expr2new_enode, args;
        ast_translation tr(src.m, m);
        for (unsigned i = 0; i < src.m_nodes.size(); ++i) {
            enode* n1 = src.m_nodes[i];
            expr* e1 = src.m_exprs[i];
            SASSERT(!n1->has_th_vars());
            args.reset();
            for (unsigned j = 0; j < n1->num_args(); ++j) 
                args.push_back(old_expr2new_enode[n1->get_arg(j)->get_owner_id()]);
            expr*  e2 = tr(e1);
            enode* n2 = mk(e2, args.size(), args.c_ptr());
            old_expr2new_enode.setx(e1->get_id(), n2, nullptr);
        }
        for (unsigned i = 0; i < src.m_nodes.size(); ++i) {             
            enode* n1 = src.m_nodes[i];
            enode* n1t = n1->m_target;      
            enode* n2 = m_nodes[i];
            enode* n2t = n1t ? old_expr2new_enode[n1->get_owner_id()] : nullptr;
            SASSERT(!n1t || n2t);
            SASSERT(!n1t || src.m.get_sort(n1->get_owner()) == src.m.get_sort(n1t->get_owner()));
            SASSERT(!n1t || m.get_sort(n2->get_owner()) == m.get_sort(n2t->get_owner()));
            if (n1t && n2->get_root() != n2t->get_root()) 
                merge(n2, n2t, n1->m_justification.copy(copy_justification));
        }
        propagate();
    }
}

template void euf::egraph::explain(ptr_vector<int>& justifications);
template void euf::egraph::explain_todo(ptr_vector<int>& justifications);
template void euf::egraph::explain_eq(ptr_vector<int>& justifications, enode* a, enode* b);

template void euf::egraph::explain(ptr_vector<unsigned>& justifications);
template void euf::egraph::explain_todo(ptr_vector<unsigned>& justifications);
template void euf::egraph::explain_eq(ptr_vector<unsigned>& justifications, enode* a, enode* b);

