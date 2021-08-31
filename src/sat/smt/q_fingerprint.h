/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    q_fingerprint.h

Abstract:

    Fingerprint summary of a quantifier instantiation

Author:

    Nikolaj Bjorner (nbjorner) 2021-01-24

--*/
#pragma once

#include "util/hashtable.h"
#include "ast/ast.h"
#include "ast/quantifier_stat.h"
#include "ast/euf/euf_enode.h"
#include "sat/smt/q_clause.h"


namespace q {

    struct fingerprint {
        clause*          c;
        binding*         b;
        unsigned         m_max_generation;
        
        unsigned size() const { return c->num_decls(); }
        euf::enode* const* nodes() const { return b->nodes(); }
        quantifier* q() const { return c->m_q; }
        
        fingerprint(clause& _c, binding& _b, unsigned mg) :
            c(&_c), b(&_b), m_max_generation(mg) {}
        
        bool eq(fingerprint const& other) const {
            if (c->m_q != other.c->m_q)
                return false;
            for (unsigned i = size(); i--> 0; ) 
                if ((*b)[i] != (*other.b)[i])
                    return false;
            return true;
        }
    };

    struct fingerprint_khasher {
        unsigned operator()(fingerprint const * f) const { return f->c->m_q->get_id(); }
    };

    struct fingerprint_chasher {
        unsigned operator()(fingerprint const * f, unsigned idx) const { return f->b->m_nodes[idx]->hash(); }
    };

    struct fingerprint_hash_proc {
        unsigned operator()(fingerprint const * f) const {
            return get_composite_hash<fingerprint *, fingerprint_khasher, fingerprint_chasher>(const_cast<fingerprint*>(f), f->size());
        }
    };
    
    struct fingerprint_eq_proc {
        bool operator()(fingerprint const* a, fingerprint const* b) const { return a->eq(*b); }
    };

    typedef ptr_hashtable<fingerprint, fingerprint_hash_proc, fingerprint_eq_proc> fingerprints;    

    inline std::ostream& operator<<(std::ostream& out, fingerprint const& f) {
        out << "[fp " << f.q()->get_id() << ":";
        for (unsigned i = 0; i < f.size(); ++i)
            out << " " << (*f.b)[i]->get_expr_id();
        return out << "]";
    }

}
