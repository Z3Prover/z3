/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    dependent_expr_state.h

Abstract:

    abstraction for simplification of depenent expression states.
    A dependent_expr_state is an interface to a set of dependent expressions.
    Dependent expressions are formulas together with a set of dependencies that are coarse grained 
    proof hints or justifications for them. Input assumptions can be self-justified.

    The dependent_expr_simplifier implements main services:
    - push, pop - that scope the local state
    - reduce - to process formulas in a dependent_expr_state between the current value of m_qhead and the size() 
      of the depdenent_expr_state

    A dependent expr_simplifier can be used to:
    - to build a tactic
    - for incremental pre-processing

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-2.
    
--*/

#pragma once

#include "util/trail.h"
#include "util/statistics.h"
#include "util/params.h"
#include "ast/simplifiers/dependent_expr.h"
#include "ast/converters/model_converter.h"

/**
   abstract interface to state updated by simplifiers.
 */
class dependent_expr_state {
public:
    virtual ~dependent_expr_state() {}
    virtual unsigned size() const = 0;
    virtual dependent_expr const& operator[](unsigned i) = 0;
    virtual void update(unsigned i, dependent_expr const& j) = 0;
    virtual bool inconsistent() = 0;
};

/**
   Shared interface of simplifiers. 
 */
class dependent_expr_simplifier {
protected:
    ast_manager&          m;
    dependent_expr_state& m_fmls;
    unsigned       m_qhead = 0;          // pointer into last processed formula in m_fmls
    unsigned       m_num_scopes = 0;
    trail_stack    m_trail;    
    void advance_qhead(unsigned sz) { if (m_num_scopes > 0) m_trail.push(value_trail(m_qhead)); m_qhead = sz; }
public:
    dependent_expr_simplifier(ast_manager& m, dependent_expr_state& s) : m(m), m_fmls(s) {}
    virtual ~dependent_expr_simplifier() {}
    virtual void push() { m_num_scopes++; m_trail.push_scope(); }
    virtual void pop(unsigned n) { m_num_scopes -= n; m_trail.pop_scope(n); }
    virtual void reduce() = 0;
    virtual void collect_statistics(statistics& st) const {}
    virtual void reset_statistics() {}
    virtual void updt_params(params_ref const& p) {}
    virtual model_converter_ref get_model_converter() { return model_converter_ref(); }
};

/**
   Factory interface for creating simplifiers. 
   The use of a factory allows delaying the creation of the dependent_expr_state
   argument until the point where the expression simplifier is created.
   This is used in tactics where the dependent_expr_state is a reference to the
   new tactic. 

   Alternatively have a clone method on dependent_expr_simplifier.
 */
class dependent_expr_simplifier_factory {
    unsigned m_ref = 0;
public:
    virtual dependent_expr_simplifier* mk(ast_manager& m, params_ref const& p, dependent_expr_state& s) = 0;
    virtual ~dependent_expr_simplifier_factory() {}
    void inc_ref() { ++m_ref; }
    void dec_ref() { if (--m_ref == 0) dealloc(this); }
};
