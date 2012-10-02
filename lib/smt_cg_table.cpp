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
#include"smt_cg_table.h"
#include"ast_pp.h"
#include"ast_ll_pp.h"

namespace smt {

#if 0
    unsigned cg_table::cg_hash::operator()(enode * n) const {
        if (n->is_commutative()) {
            return  combine_hash(n->get_decl_id(), 
                                 n->get_arg(0)->get_root()->hash() *
                                 n->get_arg(1)->get_root()->hash());
        }
        else {
            unsigned num = n->get_num_args();
            switch (num) {
            case 0: UNREACHABLE(); return 0;
            case 1: 
                return combine_hash(n->get_decl_id(), n->get_arg(0)->get_root()->hash());
            case 2: {
                unsigned a = n->get_decl_id();
                unsigned b = n->get_arg(0)->get_root()->hash();
                unsigned c = n->get_arg(1)->get_root()->hash();
                mix(a,b,c);
                return c;
            }
            default:
                return get_composite_hash<enode *, cg_khasher, cg_chasher>(n, n->get_num_args(), m_khasher, m_chasher);
            }
        }
    }

    bool cg_table::cg_eq::operator()(enode * n1, enode * n2) const {
#if 0
        static unsigned counter = 0;
        static unsigned failed  = 0;
        bool r = congruent(n1, n2, m_commutativity);
        if (!r) 
            failed++;
        counter++;
        if (counter % 100000 == 0) 
            std::cout << "cg_eq: " << counter << " " << failed << "\n";
        return r;
#else
        return congruent(n1, n2, m_commutativity);
#endif
    }
    
    cg_table::cg_table(ast_manager & m):
        m_manager(m),
        m_table(DEFAULT_HASHTABLE_INITIAL_CAPACITY, cg_hash(), cg_eq(m_commutativity)) {
    }
    
    void cg_table::display(std::ostream & out) const {
        out << "congruence table:\n";
        table::iterator it  = m_table.begin();
        table::iterator end = m_table.end();
        for (; it != end; ++it) {
            enode * n = *it;
            out << mk_pp(n->get_owner(), m_manager) << "\n";
        }
    }

    void cg_table::display_compact(std::ostream & out) const {
        if (!m_table.empty()) {
            out << "congruence table:\n";
            table::iterator it  = m_table.begin();
            table::iterator end = m_table.end();
            for (; it != end; ++it) {
                enode * n = *it;
                out << "#" << n->get_owner()->get_id() << " ";
            }
            out << "\n";
        }
    }

#ifdef Z3DEBUG
    bool cg_table::check_invariant() const {
        table::iterator it  = m_table.begin();
        table::iterator end = m_table.end();
        for (; it != end; ++it) {
            enode * n = *it;
            CTRACE("cg_table", !contains_ptr(n), tout << "#" << n->get_owner_id() << "\n";);
            SASSERT(contains_ptr(n));
        }
        return true;
    }
#endif

#else
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
            __fallthrough;
        case 1:
            c += n->get_arg(0)->get_root()->hash();
        }
        mix(a, b, c);
        return c;
    }

    bool cg_table::cg_eq::operator()(enode * n1, enode * n2) const {
        SASSERT(n1->get_num_args() == n2->get_num_args());
        SASSERT(n1->get_decl() == n2->get_decl());
        unsigned num = n1->get_num_args();
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
        ptr_vector<void>::iterator it  = m_tables.begin();
        ptr_vector<void>::iterator end = m_tables.end();
        for (; it != end; ++it) {
            void * t = *it;
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
        obj_map<func_decl, unsigned>::iterator it2  = m_func_decl2id.begin();
        obj_map<func_decl, unsigned>::iterator end2 = m_func_decl2id.end();
        for (; it2 != end2; ++it2) 
            m_manager.dec_ref(it2->m_key);
        m_func_decl2id.reset();
    }

    void cg_table::display(std::ostream & out) const {
    }

    void cg_table::display_compact(std::ostream & out) const {
    }

#ifdef Z3DEBUG
    bool cg_table::check_invariant() const {
        return true;
    }
#endif

#endif

};

