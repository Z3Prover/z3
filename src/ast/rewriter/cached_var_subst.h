/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    cached_var_subst.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2009-01-23.

Revision History:

--*/
#pragma once

#include "ast/rewriter/var_subst.h"
#include "util/map.h"

class cached_var_subst {
    struct key {
        quantifier * m_qa;
        unsigned     m_num_bindings;
        expr *       m_bindings[0];
    };
    struct key_hash_proc {
        unsigned operator()(key * k) const {
            return string_hash(reinterpret_cast<char const *>(k->m_bindings), sizeof(expr *) * k->m_num_bindings, k->m_qa->get_id());
        }
    };
    struct key_eq_proc {
        bool operator()(key * k1, key * k2) const;
    };
    typedef map<key *, expr *, key_hash_proc, key_eq_proc> instances;
    ast_manager&     m;
    var_subst        m_proc;
    expr_ref_vector  m_refs;
    instances        m_instances;
    region           m_region;
    ptr_vector<key>  m_new_keys; // mapping from num_bindings -> next key
    key*             m_key { nullptr };
public:
    cached_var_subst(ast_manager & m);
    expr** operator()(quantifier * qa, unsigned num_bindings);
    expr_ref operator()();
    void reset();
};


