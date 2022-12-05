/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    demodulator_simplifier.h

Author:

    Nikolaj Bjorner (nbjorner) 2022-12-4

--*/

#pragma once

#include "ast/substitution/demodulator_rewriter.h"
#include "ast/simplifiers/dependent_expr_state.h"
#include "util/uint_set.h"

class demodulator_index {
    ast_manager& m;
    obj_map<func_decl, uint_set*> m_fwd_index, m_bwd_index; 
    void add(func_decl* f, unsigned i, obj_map<func_decl, uint_set*>& map);
    void del(func_decl* f, unsigned i, obj_map<func_decl, uint_set*>& map);
 public:
    demodulator_index(ast_manager& m): m(m) {}
    ~demodulator_index();
    void reset();
    void insert_fwd(func_decl* f, unsigned i) { add(f, i, m_fwd_index); }
    void remove_fwd(func_decl* f, unsigned i) { del(f, i, m_fwd_index); }
    void insert_bwd(expr* e, unsigned i);
    void remove_bwd(expr* e, unsigned i);
    bool find_fwd(func_decl* f, uint_set*& s) { return m_fwd_index.find(f, s); }
    bool find_bwd(func_decl* f, uint_set*& s) { return m_bwd_index.find(f, s); }
    bool empty() const { return m_fwd_index.empty(); }
    std::ostream& display(std::ostream& out) const;
};

class demodulator_simplifier : public dependent_expr_simplifier {
    typedef std::pair<app*, expr*> app_expr_pair;
    demodulator_index         m_index;
    demodulator_util          m_util;
    demodulator_match_subst   m_match_subst;
    demodulator_rewriter_util m_rewriter;
    u_map<app_expr_pair>      m_rewrites;
    uint_set                  m_processed, m_dependencies;
    unsigned_vector           m_todo;
    expr_ref_vector           m_pinned;

    void rewrite(unsigned i);
    bool rewrite1(func_decl* f, expr_ref_vector const& args, expr_ref& np);
    expr* fml(unsigned i) { return m_fmls[i].fml(); }
    expr_dependency* dep(unsigned i) { return m_fmls[i].dep(); }
    void reschedule_processed(func_decl* f);
    void reschedule_demodulators(func_decl* f, expr* lhs);
    void reset();

 public:
     demodulator_simplifier(ast_manager& m, params_ref const& p, dependent_expr_state& st);

     void reduce() override;    

     char const* name() const override { return "demodulator"; }
};
