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
#include "ast/converters/generic_model_converter.h"

class dependent_expr_state;

class model_reconstruction_trail {

    struct entry {
        enum entry_t { loose_subst, loose_constraints, hide, defined};

        entry_t                       m_ty;
        scoped_ptr<expr_substitution> m_subst;
        vector<dependent_expr>        m_removed;
        func_decl_ref                 m_decl;
        vector<std::tuple<func_decl_ref, expr_ref, expr_dependency_ref>> m_defs;
        bool                          m_active = true;

        entry(ast_manager& m, expr_substitution* s, vector<dependent_expr> const& rem, bool replay_constraints) :
            m_ty(replay_constraints ? loose_constraints : loose_subst), m_subst(s), m_removed(rem), m_decl(m) {}

        entry(ast_manager& m, func_decl* h) : m_ty(hide), m_decl(h, m) {}

        entry(ast_manager& m, func_decl* f, expr* def, expr_dependency* dep, vector<dependent_expr> const& rem) :
            m_ty(defined), 
            m_removed(rem),
            m_decl(m){
            m_defs.push_back({ func_decl_ref(f, m), expr_ref(def, m), expr_dependency_ref(dep, m) });
        }

        entry(ast_manager& m, vector<std::tuple<func_decl_ref, expr_ref, expr_dependency_ref>> const& defs, vector<dependent_expr> const& rem) :
            m_ty(defined), 
            m_removed(rem),
            m_decl(m),
            m_defs(defs) {
        }

        bool is_loose() const { return !m_removed.empty(); }
        bool is_loose_subst() const { return m_ty == loose_subst; }
        bool is_loose_constraint() const { return m_ty == loose_constraints; }

        bool intersects(ast_mark const& free_vars) const {
            if (is_hide())
                return false;
            for (auto const& [f, def, dep] : m_defs)
                if (free_vars.is_marked(f))
                    return true;
            if (m_subst) {
                for (auto const& [k, v] : m_subst->sub())
                    if (free_vars.is_marked(to_app(k)->get_decl()))
                        return true;
            }
            return false;
        }

        bool is_hide() const { return m_decl && m_defs.empty(); }
        bool is_def() const { return !m_defs.empty(); }
        bool is_subst() const { return m_subst && !m_subst->empty(); }
    };

    ast_manager&             m;
    trail_stack&             m_trail_stack;
    scoped_ptr_vector<entry> m_trail;
    func_decl_ref_vector     m_model_vars_trail;
    ast_mark                 m_model_vars;
    bool                     m_intersects_with_model = false;

    struct undo_model_var : public trail {
        model_reconstruction_trail& s;
        undo_model_var(model_reconstruction_trail& s) : s(s) {}
        void undo() override {
            s.m_model_vars.mark(s.m_model_vars_trail.back(), false);
            s.m_model_vars_trail.pop_back();
        }
    };

    /**
    * register that f occurs in the model reconstruction trail.
    */
    void add_model_var(func_decl* f) {
        if (!m_model_vars.is_marked(f)) {
            m_model_vars_trail.push_back(f);
            m_model_vars.mark(f, true);
            m_trail_stack.push(undo_model_var(*this));
        }
    }

    /**
    * walk the free functions of 'e' and add them to 'free_vars'.
    * record if there is an intersection with the model_vars that are
    * registered when updates are added to the trail.
    */
    void add_vars(expr* e, ast_mark& free_vars);
    
    void add_vars(dependent_expr const& d, ast_mark& free_vars) {
        add_vars(d.fml(), free_vars);
    }

    bool intersects(ast_mark const& free_vars, dependent_expr const& d) {
        expr_ref term(d.fml(), m);
        auto iter = subterms::all(term);
        return any_of(iter, [&](expr* t) { return is_app(t) && free_vars.is_marked(to_app(t)->get_decl()); });
    }

    bool intersects(ast_mark const& free_vars, vector<dependent_expr> const& added) {
        return any_of(added, [&](dependent_expr const& d) { return intersects(free_vars, d); });
    }

    /**
    * Append new updates to model converter.
    */
    void append(generic_model_converter& mc);

public:

    model_reconstruction_trail(ast_manager& m, trail_stack& tr): 
        m(m), m_trail_stack(tr), m_model_vars_trail(m) {}

    /**
    * add a new substitution to the trail
    */
    void push(expr_substitution* s, vector<dependent_expr> const& removed, bool replay_constraints) {
        m_trail.push_back(alloc(entry, m, s, removed, replay_constraints));
        m_trail_stack.push(push_back_vector(m_trail));     
        for (auto& [k, v] : s->sub())
            add_model_var(to_app(k)->get_decl());
    }

    /**
    * add declaration to hide
    */
    void hide(func_decl* f) {
        m_trail.push_back(alloc(entry, m, f));
        m_trail_stack.push(push_back_vector(m_trail));
    }

    /**
     * add definition
     */
    void push(func_decl* f, expr* def, expr_dependency* dep, vector<dependent_expr> const& removed) {
        m_trail.push_back(alloc(entry, m, f, def, dep, removed));
        m_trail_stack.push(push_back_vector(m_trail));
        add_model_var(f);
    }

    /**
     * add definitions
     */
    void push(vector<std::tuple<func_decl_ref, expr_ref, expr_dependency_ref>> const& defs, vector<dependent_expr> const& removed) {
        m_trail.push_back(alloc(entry, m, defs, removed));
        m_trail_stack.push(push_back_vector(m_trail));
        for (auto const& [f, def, dep] : defs)
            add_model_var(f);
    }

    /**
    * register a new depedent expression, update the trail 
    * by removing substitutions that are not equivalence preserving.
    */
    void replay(unsigned qhead, expr_ref_vector& assumptions, dependent_expr_state& fmls);
    

    /**
     * retrieve the current model converter corresponding to chaining substitutions from the trail.
     */
    model_converter_ref get_model_converter();

    std::ostream& display(std::ostream& out) const;
};

