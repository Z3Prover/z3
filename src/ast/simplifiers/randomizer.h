
/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    randomizer.h

Abstract:

    Simplifier that randomizes formulas by renaming uninterpreted functions and permuting arguments of associative and commutative functions.

Author:

    Nikolaj Bjorner nbjorner 20-05-2025

--*/

#pragma once

#include "ast/ast.h"
#include "ast/ast_pp.h"
#include "ast/simplifiers/dependent_expr_state.h"
#include "util/obj_hashtable.h"
#include "params/tactic_params.hpp"
#include <algorithm>

class randomizer_simplifier : public dependent_expr_simplifier {
    ast_manager& m;
    obj_map<func_decl, func_decl*> m_rename;
    ast_ref_vector   m_ast_trail;    
    expr_ref_vector  m_new_exprs;
    ptr_vector<expr> m_todo, m_args;
    random_gen       m_rand;

    func_decl* get_random_func_decl(func_decl* f) {
        func_decl* r = nullptr;
        if (m_rename.find(f, r))
            return r;
        // Create a new random name
        std::string rand_name = f->get_name().str() + "_rand_" + std::to_string(m_rand());
        symbol new_sym(rand_name.c_str());
        r = m.mk_func_decl(new_sym, f->get_arity(), f->get_domain(), f->get_range());
        m_ast_trail.push_back(r);
        m_ast_trail.push_back(f);
        m_rename.insert(f, r);

        m_trail.push(push_back_vector(m_ast_trail));
        m_trail.push(push_back_vector(m_ast_trail));
        m_trail.push(insert_obj_map(m_rename, f));


        m_args.reset();
        for (unsigned i = 0; i < f->get_arity(); ++i)
            m_args.push_back(m.mk_var(i, f->get_domain(i)));
        m_fmls.model_trail().hide(r);
	    m_fmls.model_trail().push(f, m.mk_app(r, m_args), nullptr, {});
        return r;        
    }

    void push_new_expr(expr* e, expr* new_e) {
        m_new_exprs.setx(e->get_id(), new_e);
        m_ast_trail.push_back(e);
        m_trail.push(push_back_vector(m_ast_trail));
        m_trail.push(set_vector_idx_trail(m_new_exprs, e->get_id()));
        m_todo.pop_back();
    }

    expr* get_new_expr(expr* e) {
        return m_new_exprs.get(e->get_id(), nullptr);
    }

    void randomize(expr* e) {
        m_todo.push_back(e);
        while (!m_todo.empty()) {
            e = m_todo.back();
            if (get_new_expr(e)) 
                m_todo.pop_back();            
            else if (is_app(e)) {
                auto f = to_app(e)->get_decl();
                // If uninterpreted function, rename
                if (is_uninterp(f)) 
                    f = get_random_func_decl(f);
                m_args.reset();
                auto arity = to_app(e)->get_num_args();
                for (expr* arg : *to_app(e)) {
                    expr* new_arg = get_new_expr(arg);
                    if (new_arg)
                        m_args.push_back(new_arg);
                    else
                        m_todo.push_back(arg);
                }
                if (m_args.size() < arity)
                    continue;
                if (f->is_associative() && f->is_commutative() && arity > 1) 
                    shuffle(m_args.size(), m_args.data(), m_rand);
                 expr_ref new_e(m.mk_app(f, m_args.size(), m_args.data()), m);
                 push_new_expr(e, new_e);
            }        
            else if (is_quantifier(e)) {
                quantifier* q = to_quantifier(e);
                expr* body = q->get_expr();
                expr* new_body = get_new_expr(body);
                if (new_body) {
                    expr_ref new_e(m.update_quantifier(q, new_body), m);
                    push_new_expr(e, new_e);
                }
                else
                    m_todo.push_back(body);
            } 
            else 
                push_new_expr(e, e);                        
        }
    }

public:
    randomizer_simplifier(ast_manager& m, params_ref const & p, dependent_expr_state& fmls)
        : dependent_expr_simplifier(m, fmls), m(m), m_ast_trail(m), m_new_exprs(m) {
        tactic_params tp(p);
        m_rand.set_seed(tp.randomizer_seed()); // set random seed from parameter
        }

    char const* name() const override { return "randomizer"; }

    void reduce() override {
        for (unsigned idx : indices()) {
            auto d = m_fmls[idx];
            randomize(d.fml());
            m_fmls.update(idx, dependent_expr(m, get_new_expr(d.fml()), d.pr(), d.dep()));
        }
        unsigned num_fmls = qtail() - qhead();
        for (unsigned i = qhead(); i < qtail(); ++i) {
            unsigned j = qhead() + m_rand(num_fmls);
            if (i == j)
                continue;
            auto d1 = m_fmls[i];
            auto d2 = m_fmls[j];
            m_fmls.update(i, d2);
            m_fmls.update(j, d1);
        }
    }

    bool supports_proofs() const override { return false; }
};

/*
  ADD_SIMPLIFIER("randomizer", "shuffle assertions and rename uninterpreted functions.", "alloc(randomizer_simplifier, m, p, s)")
*/