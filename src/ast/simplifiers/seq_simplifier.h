/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    seq_simplifier.h

Abstract:

    create a simplifier from a sequence of simplifiers

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-24

--*/

#pragma once

#include "ast/simplifiers/dependent_expr_state.h"


class seq_simplifier : public dependent_expr_simplifier {
    scoped_ptr_vector<dependent_expr_simplifier> m_simplifiers;

public:
    seq_simplifier(ast_manager& m, params_ref const& p, dependent_expr_state& fmls):
        dependent_expr_simplifier(m, fmls) {
    }
    
    void add_simplifier(dependent_expr_simplifier* s) {
        m_simplifiers.push_back(s);
    }
        
    void reduce() override {
        for (auto* s : m_simplifiers) {
            if (m_fmls.inconsistent())
                break;
            s->reduce();
        }
    }
    
    void collect_statistics(statistics& st) const override {
        for (auto* s : m_simplifiers)
            s->collect_statistics(st);
    }
    
    void reset_statistics() override {
        for (auto* s : m_simplifiers)
            s->reset_statistics(st);
    }
    
    void updt_params(params_ref const& p) override {
        for (auto* s : m_simplifiers)
            s->updt_params(p);        
    }
    
    void collect_param_descrs(param_descrs& r) override {
        for (auto* s : m_simplifiers)
            s->collect_param_descrs(r);
    }
    
    void push() override {
        for (auto* s : m_simplifiers)
            s->push();       
    }
    
    void pop(unsigned n) override {
        for (auto* s : m_simplifiers)
            s->pop(n);     
    }
};
