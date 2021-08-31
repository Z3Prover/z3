/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    used_vars.h

Abstract:

    Functor used to collect the set of used variables.

Author:

    Leonardo de Moura (leonardo) 2008-01-14.

Revision History:

--*/
#pragma once

#include "ast/ast.h"
#include "ast/expr_delta_pair.h"

class used_vars {
    ptr_vector<sort> m_found_vars;
    typedef hashtable<expr_delta_pair, obj_hash<expr_delta_pair>, default_eq<expr_delta_pair> > cache;
    cache                    m_cache;
    svector<expr_delta_pair> m_todo;
    unsigned                 m_num_decls{ UINT_MAX };
    unsigned                 m_num_found_vars{ 0 };

    void process(expr * n, unsigned delta);

public:
    
    void operator()(expr * n) {
        reset();
        process(n, 0);
    }

    void reset() {
        m_found_vars.reset();
        m_num_decls = UINT_MAX;
        m_num_found_vars = 0;
    }

    void set_num_decls(unsigned n) {
        m_num_decls = n;
    }

    void process(expr * n) {
        process(n, 0);
    }

    unsigned get_max_found_var_idx_plus_1() const { return m_found_vars.size(); }

    sort * get(unsigned var_idx) const { return m_found_vars[var_idx]; }
    sort * contains(unsigned var_idx) const { return var_idx < m_found_vars.size() ? m_found_vars[var_idx] : 0; }
    
    bool uses_all_vars(unsigned num_decls) const;
    bool uses_a_var(unsigned num_decls) const;
    unsigned get_num_vars() const;
};


