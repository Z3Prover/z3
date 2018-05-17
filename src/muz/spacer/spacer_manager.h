/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    spacer_manager.h

Abstract:

    A manager class for SPACER, taking care of creating of AST
    objects and conversions between them.

Author:

    Krystof Hoder (t-khoder) 2011-8-25.

Revision History:

--*/

#ifndef _SPACER_MANAGER_H_
#define _SPACER_MANAGER_H_

#include <utility>
#include <map>
#include <vector>

#include "ast/rewriter/bool_rewriter.h"
#include "ast/rewriter/expr_replacer.h"
#include "ast/expr_substitution.h"
#include "util/map.h"
#include "util/ref_vector.h"
#include "smt/smt_kernel.h"
#include "muz/spacer/spacer_util.h"
#include "muz/spacer/spacer_sym_mux.h"
#include "muz/spacer/spacer_farkas_learner.h"
#include "muz/spacer/spacer_smt_context_manager.h"
#include "muz/base/dl_rule.h"

namespace smt {class context;}

namespace spacer {

struct relation_info {
    func_decl_ref         m_pred;
    func_decl_ref_vector  m_vars;
    expr_ref              m_body;
    relation_info(ast_manager& m, func_decl* pred, ptr_vector<func_decl> const& vars, expr* b):
        m_pred(pred, m), m_vars(m, vars.size(), vars.c_ptr()), m_body(b, m) {}
    relation_info(relation_info const& other): m_pred(other.m_pred), m_vars(other.m_vars), m_body(other.m_body) {}
};

class unknown_exception {};

class inductive_property {
    ast_manager&             m;
    model_converter_ref      m_mc;
    vector<relation_info>    m_relation_info;
    expr_ref fixup_clauses(expr* property) const;
    expr_ref fixup_clause(expr* clause) const;
public:
    inductive_property(ast_manager& m, model_converter_ref& mc, vector<relation_info> const& relations):
        m(m),
        m_mc(mc),
        m_relation_info(relations) {}

    std::string to_string() const;
    expr_ref to_expr() const;
    void to_model(model_ref& md) const;
    void display(datalog::rule_manager& rm,
                 ptr_vector<datalog::rule> const& rules,
                 std::ostream& out) const;
};

class manager {
    ast_manager&      m;

    // manager of multiplexed names
    sym_mux               m_mux;

    // three solver pools for different queries
    spacer::smt_context_manager   m_contexts;
    spacer::smt_context_manager   m_contexts2;
    spacer::smt_context_manager   m_contexts3;

    unsigned n_index() const { return 0; }
    unsigned o_index(unsigned i) const { return i + 1; }

    void add_new_state(func_decl * s);

public:
    manager(unsigned max_num_contexts, ast_manager & manager);

    ast_manager& get_manager() const { return m; }

    // management of mux names

    //"o" predicates stand for the old states and "n" for the new states
    func_decl * get_o_pred(func_decl * s, unsigned idx);
    func_decl * get_n_pred(func_decl * s);

    void get_o_index(func_decl* p, unsigned& idx) const {
        m_mux.try_get_index(p, idx);
        SASSERT(idx != n_index());
        idx--;  // m_mux has indices starting at 1
    }

    bool is_o(func_decl * p, unsigned idx) const
    {return m_mux.has_index(p, o_index(idx));}
    bool is_o(func_decl * p) const {
        unsigned idx;
        return m_mux.try_get_index(p, idx) && idx != n_index();
    }
    bool is_o(expr* e) const
    {return is_app(e) && is_o(to_app(e)->get_decl());}
    bool is_o(expr* e, unsigned idx) const
    {return is_app(e) && is_o(to_app(e)->get_decl(), idx);}
    bool is_n(func_decl * p) const
    {return m_mux.has_index(p, n_index());}
    bool is_n(expr* e) const
    {return is_app(e) && is_n(to_app(e)->get_decl());}


    /** true if f doesn't contain any n predicates */
    bool is_o_formula(expr * f) const
    {return !m_mux.contains(f, n_index());}
    /** true if f contains only o state preds of index o_idx */
    bool is_o_formula(expr * f, unsigned o_idx) const
    {return m_mux.is_homogenous_formula(f, o_index(o_idx));}
    /** true if f doesn't contain any o predicates */
    bool is_n_formula(expr * f) const
    {return m_mux.is_homogenous_formula(f, n_index());}

    func_decl * o2n(func_decl * p, unsigned o_idx) const
    {return m_mux.conv(p, o_index(o_idx), n_index());}
    func_decl * o2o(func_decl * p, unsigned src_idx, unsigned tgt_idx) const
    {return m_mux.conv(p, o_index(src_idx), o_index(tgt_idx));}
    func_decl * n2o(func_decl * p, unsigned o_idx) const
    {return m_mux.conv(p, n_index(), o_index(o_idx));}

    void formula_o2n(expr * f, expr_ref & result, unsigned o_idx, bool homogenous = true) const
    {m_mux.conv_formula(f, o_index(o_idx), n_index(), result, homogenous);}

    void formula_n2o(expr * f, expr_ref & result, unsigned o_idx, bool homogenous = true) const
    {m_mux.conv_formula(f, n_index(), o_index(o_idx), result, homogenous);}

    void formula_n2o(unsigned o_idx, bool homogenous, expr_ref & result) const
    {m_mux.conv_formula(result.get(), n_index(), o_index(o_idx), result, homogenous);}

    void formula_o2o(expr * src, expr_ref & tgt, unsigned src_idx,
                     unsigned tgt_idx, bool homogenous = true) const
    {m_mux.conv_formula(src, o_index(src_idx), o_index(tgt_idx), tgt, homogenous);}


    // three different solvers with three different sets of parameters
    // different solvers are used for different types of queries in spacer
    solver* mk_fresh() {return m_contexts.mk_fresh();}
    smt_params& fparams() { return m_contexts.fparams(); }
    solver* mk_fresh2() {return m_contexts2.mk_fresh();}
    smt_params &fparams2() { return m_contexts2.fparams(); }
    solver* mk_fresh3() {return m_contexts3.mk_fresh();}
    smt_params &fparams3() {return m_contexts3.fparams();}



    void collect_statistics(statistics& st) const {
        m_contexts.collect_statistics(st);
        m_contexts2.collect_statistics(st);
        m_contexts3.collect_statistics(st);
    }

    void reset_statistics() {
        m_contexts.reset_statistics();
        m_contexts2.reset_statistics();
        m_contexts3.reset_statistics();
    }
};

/** Skolem constants for quantified spacer */
app* mk_zk_const (ast_manager &m, unsigned idx, sort *s);
int find_zk_const(expr* e, app_ref_vector &out);
inline int find_zk_const(expr_ref_vector const &v, app_ref_vector &out)
{return find_zk_const (mk_and(v), out);}

bool has_zk_const(expr* e);
bool is_zk_const (const app *a, int &n);

struct sk_lt_proc {bool operator()(const app* a1, const app* a2);};

}

#endif
