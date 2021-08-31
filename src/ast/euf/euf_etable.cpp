/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    euf_etable.cpp

Author:

    Leonardo de Moura (leonardo) 2008-02-19.

Revision History:

    Ported from smt_cg_table.cpp

--*/
#include "ast/euf/euf_etable.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"

namespace euf {

    // one table per func_decl implementation
    unsigned etable::cg_hash::operator()(enode * n) const {
        SASSERT(n->get_decl()->is_flat_associative() || n->num_args() >= 3);
        unsigned a, b, c;
        a = b = 0x9e3779b9;
        c = 11;    
        
        unsigned i = n->num_args();
        while (i >= 3) {
            i--;
            a += get_root(n, i)->hash();
            i--;
            b += get_root(n, i)->hash();
            i--;
            c += get_root(n, i)->hash();
            mix(a, b, c);
        }
        
        switch (i) {
        case 2:
            b += get_root(n, 1)->hash();
            Z3_fallthrough;
        case 1:
            c += get_root(n, 0)->hash();
        }
        mix(a, b, c);
        return c;
    }

    bool etable::cg_eq::operator()(enode * n1, enode * n2) const {
        SASSERT(n1->get_decl() == n2->get_decl());
        unsigned num = n1->num_args();
        if (num != n2->num_args()) {
            return false;
        }
        for (unsigned i = 0; i < num; i++) 
            if (get_root(n1, i) != get_root(n2, i))
                return false;
        return true;
    }

    etable::etable(ast_manager & m):
        m_manager(m) {
    }

    etable::~etable() {
        reset();
    }

    void * etable::mk_table_for(unsigned arity, func_decl * d) {
        void * r;
        SASSERT(d->get_arity() >= 1);
        SASSERT(arity >= d->get_arity() || d->is_associative());
        switch (arity) {
        case 1:
            r = TAG(void*, alloc(unary_table), UNARY);
            SASSERT(GET_TAG(r) == UNARY);
            return r;
        case 2:
            if (d->is_commutative()) {
                r = TAG(void*, alloc(comm_table, cg_comm_hash(), cg_comm_eq(m_commutativity)), BINARY_COMM);
                SASSERT(GET_TAG(r) == BINARY_COMM);
            }
            else {
                r = TAG(void*, alloc(binary_table), BINARY);
                SASSERT(GET_TAG(r) == BINARY);
            }
            return r;
        default: 
            r = TAG(void*, alloc(table), NARY);
            SASSERT(GET_TAG(r) == NARY);
            return r;
        }
    }

    unsigned etable::set_table_id(enode * n) {
        func_decl * f = n->get_decl();
        unsigned tid;
        decl_info d(f, n->num_args());
        if (!m_func_decl2id.find(d, tid)) {
            tid = m_tables.size();
            m_func_decl2id.insert(d, tid);
            m_manager.inc_ref(f);
            SASSERT(tid <= m_tables.size());
            m_tables.push_back(mk_table_for(n->num_args(), f));
        }
        SASSERT(tid < m_tables.size());
        n->set_table_id(tid);
        DEBUG_CODE({
            decl_info d(n->get_decl(), n->num_args());
            SASSERT(m_func_decl2id.contains(d));
            SASSERT(m_func_decl2id[d] == tid);
        });
        return tid;
    }
    
    void etable::reset() {
        for (void* t : m_tables) {
            switch (GET_TAG(t)) {
            case UNARY:
                dealloc(UNTAG(unary_table*, t));
                break;
            case BINARY:
                dealloc(UNTAG(binary_table*, t));
                break;
            case BINARY_COMM:
                dealloc(UNTAG(comm_table*, t));
                break;
            case NARY:
                dealloc(UNTAG(table*, t));
                break;
            }
        }
        m_tables.reset();
        for (auto const& kv : m_func_decl2id) {
            m_manager.dec_ref(kv.m_key.first);
        }
        m_func_decl2id.reset();
    }

    void etable::display(std::ostream & out) const {
        for (auto const& kv : m_func_decl2id) {
            void * t = m_tables[kv.m_value];
            out << mk_pp(kv.m_key.first, m_manager) << ": ";
            switch (GET_TAG(t)) {
            case UNARY: 
                display_unary(out, t);
                break;            
            case BINARY: 
                display_binary(out, t);
                break;
            case BINARY_COMM: 
                display_binary_comm(out, t);
                break;            
            case NARY: 
                display_nary(out, t);
                break;
            }
        }        
    }

    void etable::display_binary(std::ostream& out, void* t) const {
        binary_table* tb = UNTAG(binary_table*, t);
        out << "b ";
        for (enode* n : *tb) {
            out << n->get_expr_id() << " ";
        }
        out << "\n";
    }
    
    void etable::display_binary_comm(std::ostream& out, void* t) const {
        comm_table* tb = UNTAG(comm_table*, t);
        out << "bc ";
        for (enode* n : *tb) {
            out << n->get_expr_id() << " ";
        }
        out << "\n";
    }
    
    void etable::display_unary(std::ostream& out, void* t) const {
        unary_table* tb = UNTAG(unary_table*, t);
        out << "un ";
        for (enode* n : *tb) {
            out << n->get_expr_id() << " ";
        }
        out << "\n";
    }
    
    void etable::display_nary(std::ostream& out, void* t) const {
        table* tb = UNTAG(table*, t);
        out << "nary ";
        for (enode* n : *tb) {
            out << n->get_expr_id() << " ";
        }
        out << "\n";
    }


    enode_bool_pair etable::insert(enode * n) {
        // it doesn't make sense to insert a constant.
        SASSERT(n->num_args() > 0);
        SASSERT(!m_manager.is_and(n->get_expr()));
        SASSERT(!m_manager.is_or(n->get_expr()));
        enode * n_prime;
        void * t = get_table(n); 
        switch (static_cast<table_kind>(GET_TAG(t))) {
        case UNARY:
            n_prime = UNTAG(unary_table*, t)->insert_if_not_there(n);
            return enode_bool_pair(n_prime, false);
        case BINARY:
            n_prime = UNTAG(binary_table*, t)->insert_if_not_there(n);
            return enode_bool_pair(n_prime, false);
        case BINARY_COMM:
            m_commutativity = false;
            n_prime = UNTAG(comm_table*, t)->insert_if_not_there(n);
            return enode_bool_pair(n_prime, m_commutativity);
        default:
            n_prime = UNTAG(table*, t)->insert_if_not_there(n);
            return enode_bool_pair(n_prime, false);
        }
    }

    void etable::erase(enode * n) {
        SASSERT(n->num_args() > 0);
        void * t = get_table(n); 
        switch (static_cast<table_kind>(GET_TAG(t))) {
        case UNARY:
            UNTAG(unary_table*, t)->erase(n);
            break;
        case BINARY:
            UNTAG(binary_table*, t)->erase(n);
            break;
        case BINARY_COMM:
            UNTAG(comm_table*, t)->erase(n);
            break;
        default:
            UNTAG(table*, t)->erase(n);
            break;
        }
    }

    bool etable::contains(enode* n) const {
        SASSERT(n->num_args() > 0);
        void* t = const_cast<etable*>(this)->get_table(n);
        switch (static_cast<table_kind>(GET_TAG(t))) {
        case UNARY:
            return UNTAG(unary_table*, t)->contains(n);
        case BINARY:
            return UNTAG(binary_table*, t)->contains(n);
        case BINARY_COMM:
            return UNTAG(comm_table*, t)->contains(n);
        default:
            return UNTAG(table*, t)->contains(n);
        }
    }

    enode* etable::find(enode* n) const {
        SASSERT(n->num_args() > 0);
        enode* r = nullptr;
        void* t = const_cast<etable*>(this)->get_table(n);
        switch (static_cast<table_kind>(GET_TAG(t))) {
        case UNARY:
            return UNTAG(unary_table*, t)->find(n, r) ? r : nullptr;
        case BINARY:
            return UNTAG(binary_table*, t)->find(n, r) ? r : nullptr;
        case BINARY_COMM:
            return UNTAG(comm_table*, t)->find(n, r) ? r : nullptr;
        default:
            return UNTAG(table*, t)->find(n, r) ? r : nullptr;
        }
    }

    bool etable::contains_ptr(enode* n) const {
        return find(n) == n;
    }

};

