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
#include "util/trail.h"
#include "ast/for_each_expr.h"
#include "ast/rewriter/expr_replacer.h"
#include "ast/simplifiers/dependent_expr.h"
#include "ast/converters/model_converter.h"

class model_reconstruction_trail {

    struct entry {
        scoped_ptr<expr_substitution> m_subst;
        vector<dependent_expr>        m_removed;
        func_decl*                    m_hide = nullptr;
        bool                          m_active = true;

        entry(expr_substitution* s, vector<dependent_expr> const& rem) :
            m_subst(s), m_removed(rem) {}

        entry(func_decl* h) : m_hide(h) {}

        bool is_loose() const { return !m_removed.empty(); }

        bool intersects(ast_mark const& free_vars) const {
            for (auto const& [k, v] : m_subst->sub())
                if (free_vars.is_marked(k))
                    return true;
            return false;
        }
    };

    ast_manager&             m;
    trail_stack&             m_trail_stack;
    scoped_ptr_vector<entry> m_trail;

    void add_vars(dependent_expr const& d, ast_mark& free_vars) {
        for (expr* t : subterms::all(expr_ref(d.fml(), d.get_manager())))
            free_vars.mark(t, true);
    }

    bool intersects(ast_mark const& free_vars, dependent_expr const& d) {
        expr_ref term(d.fml(), d.get_manager());
        auto iter = subterms::all(term);
        return any_of(iter, [&](expr* t) { return free_vars.is_marked(t); });
    }

    bool intersects(ast_mark const& free_vars, vector<dependent_expr> const& added) {
        return any_of(added, [&](dependent_expr const& d) { return intersects(free_vars, d); });
    }

public:

    model_reconstruction_trail(ast_manager& m, trail_stack& tr): 
        m(m), m_trail_stack(tr) {}

    /**
    * add a new substitution to the trail
    */
    void push(expr_substitution* s, vector<dependent_expr> const& removed) {
        m_trail.push_back(alloc(entry, s, removed));
        m_trail_stack.push(push_back_vector(m_trail));       
    }

    /**
    * add declaration to hide
    */
    void push(func_decl* f) {
        m_trail.push_back(alloc(entry, f));
        m_trail_stack.push(push_back_vector(m_trail));
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
};

