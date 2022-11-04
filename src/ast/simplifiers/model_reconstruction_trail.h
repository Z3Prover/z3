/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    model_reconstruction_trail.h

Abstract:

   Model reconstruction trail
   A model reconstruction trail comprises of a sequence of assignments 
   together with assertions that were removed in favor of the assignments. 
   The assignments satisfy the removed assertions but are not (necessarily) 
   equivalent to the removed assertions. For the case where assignments 
   are equivalent to removed assertions, we squash the removed assertions 
   and don't track them.

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-3.
    
--*/

#pragma once

#include "util/scoped_ptr_vector.h"
#include "ast/rewriter/expr_replacer.h"
#include "ast/simplifiers/dependent_expr.h"
#include "ast/converters/model_converter.h"

class model_reconstruction_trail {

    ast_manager& m;

    struct model_reconstruction_trail_entry {
        scoped_ptr<expr_replacer> m_replace;
        vector<dependent_expr>    m_removed;
        model_reconstruction_trail_entry(expr_replacer* r, vector<dependent_expr> const& rem) :
            m_replace(r), m_removed(rem) {}
    };

    scoped_ptr_vector<model_reconstruction_trail_entry> m_trail;
    unsigned_vector m_limit;

public:

    model_reconstruction_trail(ast_manager& m) : m(m) {}

    /**
    * add a new substitution to the stack
    */
    void push(expr_replacer* r, vector<dependent_expr> const& removed) {
        m_trail.push_back(alloc(model_reconstruction_trail_entry, r, removed));
    }

    /**
    * register a new depedent expression, update the trail 
    * by removing substitutions that are not equivalence preserving.
    */
    void replay(dependent_expr const& d, vector<dependent_expr>& added);

    /**
    * retrieve the current model converter corresponding to chaining substitutions from the trail.
    */
    model_converter_ref get_model_converter();

    /**
    * push a context. Portions of the trail added within a context are removed after a context pop.
    */
    void push() {
        m_limit.push_back(m_trail.size());
    }

    void pop(unsigned n) {
        unsigned old_sz = m_limit[m_limit.size() - n];
        m_trail.resize(old_sz);
        m_limit.shrink(m_limit.size() - n);
    }
};

