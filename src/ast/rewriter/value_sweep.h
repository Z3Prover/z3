/*++
  Copyright (c) 2020 Microsoft Corporation

  Module Name:

   value_sweep.h

  Abstract:
   
    Evaluate terms using different random initial assignments.
    Return the assignments.

  Author:

    Nikolaj Bjorner 2020-04-27
  
--*/

#pragma once

#include "ast/value_generator.h"
#include "ast/recfun_decl_plugin.h"
#include "ast/datatype_decl_plugin.h"
#include "ast/rewriter/th_rewriter.h"

class value_sweep {
    typedef vector<ptr_vector<app>> parents_t;

    ast_manager&     m;
    value_generator  m_gen;
    recfun::util     m_rec;
    datatype::util   m_dt;
    th_rewriter      m_rewrite;
    expr_ref_vector  m_values;
    expr_ref_vector  m_args;
    expr_ref_vector  m_pinned;
    unsigned         m_rounds;
    unsigned         m_range;
    random_gen       m_rand;
    
    parents_t        m_parents;
    ptr_vector<expr> m_queue;
    ptr_vector<expr> m_vars;
    unsigned         m_qhead;
    unsigned         m_vhead;
   
    void init(expr_ref_vector const& terms);

    void set_value_core(expr* e, expr* v);

    expr* get_value(expr* e) const;

    void unassign(unsigned qhead);

    void propagate_values();

    bool assign_next_value();

    bool is_reducible(expr* e) const;

    bool all_args_have_values(app* p) const;
    

 public:
    value_sweep(ast_manager& m);
    void set_rounds(unsigned r) { m_rounds = r; }
    void set_range(unsigned r) { m_range = r; }
    void set_value(expr* e, expr* v);
    void reset_values();

    void operator()(expr_ref_vector const& terms,
                    vector<expr_ref_vector>& values);
};
