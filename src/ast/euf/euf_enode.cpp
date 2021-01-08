/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    euf_enode.cpp

Abstract:

    enode layer

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-23

--*/

#include "ast/euf/euf_enode.h"
#include "ast/euf/euf_egraph.h"

namespace euf {

    void enode::invariant(egraph& g) {
        unsigned class_size = 0;
        bool     found_root = false;
        bool     found_this = false;        
        for (enode* c : enode_class(this)) {
            VERIFY(c->m_root == m_root);
            found_root |= c == m_root;
            found_this |= c == this;
            ++class_size;
        }
        VERIFY(found_root);
        VERIFY(found_this);
        VERIFY(this != m_root || class_size == m_class_size);
        if (is_root()) {
            VERIFY(!m_target);
            for (enode* p : enode_parents(this)) {
                if (!p->merge_enabled())
                    continue;
                bool found = false;
                for (enode* arg : enode_args(p)) {
                    found |= arg->get_root() == this;
                }
                CTRACE("euf", !found, tout  << g.bpp(p) << " does not have a child with root: " << g.bpp(this) << "\n";);
                VERIFY(found);
            }
            for (enode* c : enode_class(this)) {
                if (c == this)
                    continue;
                for (enode* p : enode_parents(c)) {
                    if (!p->merge_enabled())
                        continue;
                    bool found = false;
                    for (enode* q : enode_parents(this)) {
                        found |= p->congruent(q);
                    }
                    CTRACE("euf", !found, tout << "parent " << g.bpp(p) << " of " << g.bpp(c) << " is not congruent to a parent of " << g.bpp(this) << "\n";);
                    VERIFY(found);
                }
            }
        }        
    }

    bool enode::congruent(enode* n) const {
        if (get_decl() != n->get_decl()) 
            return false;
        if (num_args() != n->num_args())
            return false;
        SASSERT(!m_commutative || num_args() == 2);
        if (m_commutative &&
            get_arg(0)->get_root() == n->get_arg(1)->get_root() &&
            get_arg(1)->get_root() == n->get_arg(0)->get_root())
            return true;
        for (unsigned i = num_args(); i-- > 0; ) 
            if (get_arg(i)->get_root() != n->get_arg(i)->get_root())
                return false;
        return true;
    }

    /*
     * Find the theory var that that is heuristically 
     * linked with the fewest equality justifications.
     */
    theory_var enode::get_closest_th_var(theory_id id) const {
        enode const* n = this;
        while (n) {
            theory_var v = n->get_th_var(id);
            if (v != null_theory_var)
                return v;
            n = n->m_target;
        }
        return null_theory_var;
    }

    bool enode::acyclic() const {
        enode const* n = this;
        enode const* p = this;
        while (n) {
            n = n->m_target;
            if (n) {
                p = p->m_target;
                n = n->m_target;
            }  
            if (n == p)
                return false;
        }
        return true;
    }

    bool enode::reaches(enode* n) const {
        enode const* r = this;
        SASSERT(acyclic());
        while (r) {
            if (r == n)
                return true;
            r = r->m_target;
        }
        return false;
    }

    void enode::reverse_justification() {
        enode* curr = m_target;
        enode* prev = this;
        justification js = m_justification;
        prev->m_target = nullptr;
        prev->m_justification = justification::axiom();
        while (curr != nullptr) {
            enode* new_curr = curr->m_target;
            justification new_js = curr->m_justification;
            curr->m_target = prev;
            curr->m_justification = js;
            prev = curr;
            js = new_js;
            curr = new_curr;
        }
    }

    bool enode::children_are_roots() const {
        for (auto* child : enode_args(this))
            if (!child->is_root())
                return false;
        return true;
    }

    unsigned enode::class_generation() {
        unsigned gen = m_generation;
        
        for (enode* n : enode_class(this)) 
            gen = std::min(n->generation(), gen);
        return gen;
    }

}
