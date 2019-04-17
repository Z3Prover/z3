/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_cg_table.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-19.

Revision History:

--*/
#include "smt/smt_cg_table.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"

namespace smt {

    // one table per func_decl implementation
    unsigned cg_table::cg_hash::operator()(enode * n) const {
        SASSERT(n->get_decl()->is_flat_associative() || n->get_num_args() >= 3);
        unsigned a, b, c;
        a = b = 0x9e3779b9;
        c = 11;    
        
        unsigned i = n->get_num_args();
        while (i >= 3) {
            i--;
            a += n->get_arg(i)->get_root()->hash();
            i--;
            b += n->get_arg(i)->get_root()->hash();
            i--;
            c += n->get_arg(i)->get_root()->hash();
            mix(a, b, c);
        }
        
        switch (i) {
        case 2:
            b += n->get_arg(1)->get_root()->hash();
            Z3_fallthrough;
        case 1:
            c += n->get_arg(0)->get_root()->hash();
        }
        mix(a, b, c);
        return c;
    }

    bool cg_table::cg_eq::operator()(enode * n1, enode * n2) const {
        SASSERT(n1->get_decl() == n2->get_decl());
        unsigned num = n1->get_num_args();
        if (num != n2->get_num_args()) {
            return false;
        }
        for (unsigned i = 0; i < num; i++) 
            if (n1->get_arg(i)->get_root() != n2->get_arg(i)->get_root())
                return false;
        return true;
    }

    cg_table::cg_table(ast_manager & m):
        m_manager(m) {
    }

    cg_table::~cg_table() {
        reset();
    }

    void * cg_table::mk_table_for(func_decl * d) {
        void * r;
        SASSERT(d->get_arity() >= 1);
        switch (d->get_arity()) {
        case 1:
            r = TAG(void*, alloc(unary_table), UNARY);
            SASSERT(GET_TAG(r) == UNARY);
            return r;
        case 2:
            if (d->is_flat_associative()) {
                // applications of declarations that are flat-assoc (e.g., +) may have many arguments.
                r = TAG(void*, alloc(table), NARY);
                SASSERT(GET_TAG(r) == NARY);
                return r;
            }
            else if (d->is_commutative()) {
                r = TAG(void*, alloc(comm_table, cg_comm_hash(), cg_comm_eq(m_commutativity)), BINARY_COMM);
                SASSERT(GET_TAG(r) == BINARY_COMM);
                return r;
            }
            else {
                r = TAG(void*, alloc(binary_table), BINARY);
                SASSERT(GET_TAG(r) == BINARY);
                return r;
            }
        default: 
            r = TAG(void*, alloc(table), NARY);
            SASSERT(GET_TAG(r) == NARY);
            return r;
        }
    }

    unsigned cg_table::set_func_decl_id(enode * n) {
        func_decl * f = n->get_decl();
        unsigned tid;
        if (!m_func_decl2id.find(f, tid)) {
            tid = m_tables.size();
            m_func_decl2id.insert(f, tid);
            m_manager.inc_ref(f);
            SASSERT(tid <= m_tables.size());
            m_tables.push_back(mk_table_for(f));
        }
        SASSERT(tid < m_tables.size());
        n->set_func_decl_id(tid);
        DEBUG_CODE({
            unsigned tid_prime;
            SASSERT(m_func_decl2id.find(n->get_decl(), tid_prime) && tid == tid_prime);
        });
        return tid;
    }
    
    void cg_table::reset() {
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
            m_manager.dec_ref(kv.m_key);
        }
        m_func_decl2id.reset();
    }

    void cg_table::display(std::ostream & out) const {
        for (auto const& kv : m_func_decl2id) {
            void * t = m_tables[kv.m_value];
            out << mk_pp(kv.m_key, m_manager) << ": ";
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

    void cg_table::display_binary(std::ostream& out, void* t) const {
        binary_table* tb = UNTAG(binary_table*, t);
        out << "b ";
        for (enode* n : *tb) {
            out << n->get_owner_id() << " " << cg_binary_hash()(n) << " ";
        }
        out << "\n";
    }
    
    void cg_table::display_binary_comm(std::ostream& out, void* t) const {
        comm_table* tb = UNTAG(comm_table*, t);
        out << "bc ";
        for (enode* n : *tb) {
            out << n->get_owner_id() << " ";
        }
        out << "\n";
    }
    
    void cg_table::display_unary(std::ostream& out, void* t) const {
        unary_table* tb = UNTAG(unary_table*, t);
        out << "un ";
        for (enode* n : *tb) {
            out << n->get_owner_id() << " ";
        }
        out << "\n";
    }
    
    void cg_table::display_nary(std::ostream& out, void* t) const {
        table* tb = UNTAG(table*, t);
        out << "nary ";
        for (enode* n : *tb) {
            out << n->get_owner_id() << " ";
        }
        out << "\n";
    }


    enode_bool_pair cg_table::insert(enode * n) {
        // it doesn't make sense to insert a constant.
        SASSERT(n->get_num_args() > 0);
        SASSERT(!m_manager.is_and(n->get_owner()));
        SASSERT(!m_manager.is_or(n->get_owner()));
        enode * n_prime;
        void * t = get_table(n); 
        switch (static_cast<table_kind>(GET_TAG(t))) {
        case UNARY:
            n_prime = UNTAG(unary_table*, t)->insert_if_not_there(n);
            return enode_bool_pair(n_prime, false);
        case BINARY:
            n_prime = UNTAG(binary_table*, t)->insert_if_not_there(n);
            TRACE("cg_table", tout << "insert: " << n->get_owner_id() << " " << cg_binary_hash()(n) << " inserted: " << (n == n_prime) << " " << n_prime->get_owner_id() << "\n";
                  display_binary(tout, t); tout << "contains_ptr: " << contains_ptr(n) << "\n";); 
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

    void cg_table::erase(enode * n) {
        SASSERT(n->get_num_args() > 0);
        void * t = get_table(n); 
        switch (static_cast<table_kind>(GET_TAG(t))) {
        case UNARY:
            UNTAG(unary_table*, t)->erase(n);
            break;
        case BINARY:
            TRACE("cg_table", tout << "erase: " << n->get_owner_id() << " " << cg_binary_hash()(n) << " contains: " << contains_ptr(n) << "\n";);
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


    void cg_table::display_compact(std::ostream & out) const {
    }

    bool cg_table::check_invariant() const {
        return true;
    }

};

