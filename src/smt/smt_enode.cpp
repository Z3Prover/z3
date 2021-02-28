/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_enode.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-19.

Revision History:

--*/
#include "ast/ast_pp.h"
#include "smt/smt_context.h"
#include "smt/smt_enode.h"

namespace smt {
    
    /**
       \brief Initialize an enode in the given memory position.
    */
    enode * enode::init(ast_manager & m, void * mem, app2enode_t const & app2enode, app * owner, 
                        unsigned generation, bool suppress_args, bool merge_tf, unsigned iscope_lvl,
                        bool cgc_enabled, bool update_children_parent) {
        SASSERT(m.is_bool(owner) || !merge_tf);
        enode * n             = new (mem) enode();
        n->m_owner            = owner;
        n->m_root             = n;
        n->m_next             = n;
        n->m_cg               = nullptr;
        n->m_class_size       = 1;
        n->m_generation       = generation;
        n->m_func_decl_id     = UINT_MAX;
        n->m_mark             = false;
        n->m_mark2            = false;
        n->m_interpreted      = false;
        n->m_suppress_args    = suppress_args;
        n->m_eq               = m.is_eq(owner);
        n->m_commutative      = n->get_num_args() == 2 && owner->get_decl()->is_commutative();
        n->m_bool             = m.is_bool(owner);
        n->m_merge_tf         = merge_tf;
        n->m_cgc_enabled      = cgc_enabled;
        n->m_iscope_lvl       = iscope_lvl;
        n->m_lbl_hash         = -1;
        n->m_proof_is_logged = false;
        unsigned num_args     = n->get_num_args();
        for (unsigned i = 0; i < num_args; i++) {
            enode * arg  = app2enode[owner->get_arg(i)->get_id()];
            n->m_args[i] = arg;
            SASSERT(n->get_arg(i) == arg);
            if (update_children_parent)
                arg->get_root()->m_parents.push_back(n);
        }
        TRACE("mk_enode_detail", tout << "new enode suppress_args: " << n->m_suppress_args << "\n";);
        SASSERT(n->m_suppress_args == suppress_args);
        return n;
    }

    enode * enode::mk(ast_manager & m, region & r, app2enode_t const & app2enode, app * owner, 
                           unsigned generation, bool suppress_args, bool merge_tf, unsigned iscope_lvl,
                           bool cgc_enabled, bool update_children_parent) {
        SASSERT(m.is_bool(owner) || !merge_tf);
        unsigned sz           = get_enode_size(suppress_args ? 0 : owner->get_num_args());
        void * mem            = r.allocate(sz);
        return init(m, mem, app2enode, owner, generation, suppress_args, merge_tf, iscope_lvl, cgc_enabled, update_children_parent);
    }

    enode * enode::mk_dummy(ast_manager & m, app2enode_t const & app2enode, app * owner) {
        unsigned sz           = get_enode_size(owner->get_num_args());
        void * mem            = alloc_svect(char, sz);
        return init(m, mem, app2enode, owner, 0, false, false, 0, true, false);
    }

    void enode::del_eh(ast_manager & m, bool update_children_parent) {
        SASSERT(m_class_size == 1);
        SASSERT(m_root == this);
        SASSERT(m_next == this);
        unsigned num_args = get_num_args();
        for (unsigned i = 0; i < num_args; i++) {
            enode * arg = get_arg(i);
            if (update_children_parent) {
                SASSERT(arg->get_root()->m_parents.back() == this);
                arg->get_root()->m_parents.pop_back();
            }
        }
        this->~enode();
    }
    
    unsigned enode::get_num_th_vars() const {
        return m_th_var_list.size();
    }
    
    /**
       \brief Return the theory var (in theory th_id) associated with
       the enode.
       Return null_theory_var if the enode is not associated
       with a variable of theory th_id
    */
    theory_var enode::get_th_var(theory_id th_id) const {
        return m_th_var_list.find(th_id);
    }
    
    /**
       \brief Add the entry (v, id) to the list of theory variables.
    */
    void enode::add_th_var(theory_var v, theory_id id, region & r) {
        m_th_var_list.add_var(v, id, r);
    }
    
    /**
       \brief Replace the entry (v', id) with the entry (v, id).
       The enode must have an entry (v', id)
    */
    void enode::replace_th_var(theory_var v, theory_id id) {
        m_th_var_list.replace(v, id);
    }

    /**
       \brief Delete theory variable. It assumes the 
       enode is associated with a variable of the given theory.
    */
    void enode::del_th_var(theory_id id) {
        m_th_var_list.del_var(id);
    }

    
    /**
       \brief Push old value of generation on the context trail stack
       and update the generation.       
    */
    void enode::set_generation(context & ctx, unsigned generation) {
        if (m_generation == generation)
            return;
        ctx.push_trail(value_trail<unsigned>(m_generation));
        m_generation = generation;
    }


    void enode::set_lbl_hash(context & ctx) {
        SASSERT(m_lbl_hash == -1);
        // m_lbl_hash should be different from -1, if and only if,
        // there is a pattern that contains the enode. So,
        // I use a trail to restore the value of m_lbl_hash to -1.
        ctx.push_trail(value_trail<signed char>(m_lbl_hash));
        unsigned h = hash_u(get_owner_id());
        m_lbl_hash = h & (APPROX_SET_CAPACITY - 1);
        // propagate modification to the root m_lbls set.
        approx_set & r_lbls = m_root->m_lbls;
        if (!r_lbls.may_contain(m_lbl_hash)) {
            ctx.push_trail(value_trail<approx_set>(r_lbls));
            r_lbls.insert(m_lbl_hash);
        }
    }

    enode * enode::get_eq_enode_with_min_gen() {
        if (m_generation == 0)
            return this;
        enode * r = this;
        enode * curr = this; 
        do {
            if (curr->m_generation < r->m_generation) {
                r = curr;
                if (r->m_generation == 0)
                    return r;
            }
            curr = curr->m_next;
        }
        while (curr != this);
        return r;
    }

#ifdef Z3DEBUG
    bool enode::check_invariant() const {
        unsigned class_size = 0;
        bool     found_root = false;
        bool     found_this = false;
        bool     has_interpreted = false;
        
        // "Equivalence" class structure.
        enode const * curr = this; 
        do {
            SASSERT(curr->m_root == m_root);
            class_size++;
            if (curr == m_root)
                found_root = true;
            if (curr == this)
                found_this = true;
            if (curr->is_interpreted())
                has_interpreted = true;
            curr = curr->m_next;
        }
        while (curr != this);

        SASSERT(found_root);
        SASSERT(found_this);
        SASSERT(this != m_root || class_size == m_class_size);
        SASSERT(!has_interpreted || m_root->is_interpreted());

        // Parent use-list
        if (this == m_root) {
            for (enode* parent : m_parents) {
                unsigned i = 0;
                unsigned num_args = parent->get_num_args();
                SASSERT(num_args > 0);
                for (; i < num_args; i++) {
                    enode * arg = parent->get_arg(i);
                    if (arg->get_root() == m_root)
                        break;
                }
                SASSERT(i < num_args);
            }
        }

        // Proof tree
        // m_root is reachable from "this" by following the transitivity proof
        SASSERT(trans_reaches(m_root));
        SASSERT(check_parent_invariant());
        return true;
    }
    
    /**
       \brief Return true if the node is n or n is reached following the
       m_proof.m_target pointers
    */
    bool enode::trans_reaches(enode * n) const {
        const enode * curr = this;
        while (curr != 0) {
            if (curr == n) {
                return true;
            }
            curr = curr->m_trans.m_target;
        }
        return false;
    }

    bool enode::check_parent_invariant() const {
        if (this != m_root)
            return true;
        enode const * curr = m_root; 
        do {
            if (curr != m_root) {
                for (enode * p : curr->m_parents) {
                    if (!p->is_true_eq() && !m_root->contains_parent_congruent_to(p)) {
                        UNREACHABLE();
                    }
                }
            }
            curr = curr->m_next;
        }
        while (curr != m_root);
        return true;
    }
    
    bool enode::contains_parent_congruent_to(enode * p) const {
        for (enode* curr : m_parents) {
            if (congruent(curr, p))
                return true;
        }
        return false;
    }

#endif

    void enode::display_lbls(std::ostream & out) const {
        out << "#" << get_owner_id() << "  ->  #" << get_root()->get_owner_id() << ", lbls: " << get_lbls() << ", plbls: " << get_plbls() 
            << ", root->lbls: " << get_root()->get_lbls() << ", root->plbls: " << get_root()->get_plbls();
        if (has_lbl_hash())
            out << ", lbl-hash: " << static_cast<int>(get_lbl_hash());
        out << "\n";
    }

    bool congruent(enode * n1, enode * n2, bool & comm) {
        comm          = false;
        if (n1->get_expr()->get_decl() != n2->get_expr()->get_decl())
            return false;
        unsigned num_args = n1->get_num_args();
        if (num_args != n2->get_num_args())
            return false;
        if (n1->is_commutative()) {
            enode * c1_1 = n1->get_arg(0)->get_root();
            enode * c1_2 = n1->get_arg(1)->get_root();
            enode * c2_1 = n2->get_arg(0)->get_root();
            enode * c2_2 = n2->get_arg(1)->get_root();
            if (c1_1 == c2_1 && c1_2 == c2_2) {
                return true;
            }
            if (c1_1 == c2_2 && c1_2 == c2_1) {
                comm = true;
                return true;
            }
            return false;
        }
        else {
            for (unsigned i = 0; i < num_args; i++)
                if (n1->get_arg(i)->get_root() != n2->get_arg(i)->get_root())
                    return false;
            return true;
        }
    }

    unsigned get_max_generation(unsigned num_enodes, enode * const * enodes) {
        unsigned max = 0;
        for (unsigned i = 0; i < num_enodes; i++) {
            unsigned curr = enodes[i]->get_generation();
            if (curr > max)
                max = curr;
        }
        return max;
    }

    void unmark_enodes(unsigned num_enodes, enode * const * enodes) {
        for (unsigned i = 0; i < num_enodes; i++)
            enodes[i]->unset_mark();
    }

    void unmark_enodes2(unsigned num_enodes, enode * const * enodes) {
        for (unsigned i = 0; i < num_enodes; i++)
            enodes[i]->unset_mark2();
    }
    
    tmp_enode::tmp_enode():
        m_app(0),
        m_capacity(0),
        m_enode_data(nullptr) {
        SASSERT(m_app.get_app()->get_decl() == 0);
        set_capacity(5);
    }

    tmp_enode::~tmp_enode() {
        dealloc_svect(m_enode_data);
    }

    void tmp_enode::set_capacity(unsigned new_capacity) {
        SASSERT(new_capacity > m_capacity);
        if (m_enode_data)
            dealloc_svect(m_enode_data);
        m_capacity   = new_capacity;
        unsigned sz  = sizeof(enode) + m_capacity * sizeof(enode*);
        m_enode_data = alloc_svect(char, sz);
        memset(m_enode_data, 0, sz);
        enode * n = get_enode();
        n->m_owner         = m_app.get_app();
        n->m_root          = n;
        n->m_next          = n;
        n->m_class_size    = 1;
        n->m_cgc_enabled   = true;
        n->m_func_decl_id  = UINT_MAX;
    }

    enode * tmp_enode::set(func_decl * f, unsigned num_args, enode * const * args) {
        if (num_args > m_capacity)
            set_capacity(num_args * 2);
        enode * r = get_enode();
        if (m_app.get_app()->get_decl() != f) {
            r->m_func_decl_id = UINT_MAX;
        }
        m_app.set_decl(f);
        m_app.set_num_args(num_args);
        r->m_commutative  = num_args == 2 && f->is_commutative();
        memcpy(get_enode()->m_args, args, sizeof(enode*)*num_args);
        return r;
    }

    void tmp_enode::reset() {
        get_enode()->m_func_decl_id = UINT_MAX;
    }

};

