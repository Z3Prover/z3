/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    spacer_manager.h

Abstract:

    A manager class for SPACER, taking care of creating of AST
    objects and conversions between them.

Author:

    Krystof Hoder (t-khoder) 2011-8-25.
    Arie Gurfinkel

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
#include "muz/base/dl_rule.h"
#include "solver/solver.h"
#include "solver/solver_pool.h"
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


    unsigned n_index() const { return 0; }
    unsigned o_index(unsigned i) const { return i + 1; }

public:
    manager(ast_manager & manager);

    ast_manager& get_manager() const { return m; }

    // management of mux names

    //"o" predicates stand for the old states and "n" for the new states
    func_decl * get_o_pred(func_decl * s, unsigned idx);
    func_decl * get_n_pred(func_decl * s);

    bool is_n_formula(expr * f) const
    {return m_mux.is_homogenous_formula(f, n_index());}

    func_decl * o2n(func_decl * p, unsigned o_idx) const
    {return m_mux.shift_decl(p, o_index(o_idx), n_index());}
    func_decl * o2o(func_decl * p, unsigned src_idx, unsigned tgt_idx) const
    {return m_mux.shift_decl(p, o_index(src_idx), o_index(tgt_idx));}
    func_decl * n2o(func_decl * p, unsigned o_idx) const
    {return m_mux.shift_decl(p, n_index(), o_index(o_idx));}

    void formula_o2n(expr * f, expr_ref & result, unsigned o_idx,
                     bool homogenous = true) const
    {m_mux.shift_expr(f, o_index(o_idx), n_index(), result, homogenous);}

    void formula_n2o(expr * f, expr_ref & result, unsigned o_idx,
                     bool homogenous = true) const
    {m_mux.shift_expr(f, n_index(), o_index(o_idx), result, homogenous);}

    void formula_n2o(unsigned o_idx, bool homogenous, expr_ref & result) const
    {m_mux.shift_expr(result.get(), n_index(), o_index(o_idx),
                        result, homogenous);}

    void formula_o2o(expr * src, expr_ref & tgt, unsigned src_idx,
                     unsigned tgt_idx, bool homogenous = true) const
    {m_mux.shift_expr(src, o_index(src_idx), o_index(tgt_idx),
                        tgt, homogenous);}

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
