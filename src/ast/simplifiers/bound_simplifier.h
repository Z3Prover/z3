/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    bound_simplifier.h

Author:

    Nikolaj Bjorner (nbjorner) 2023-01-22

Description:

    Collects bounds of sub-expressions and uses them to simplify modulus
    expressions. 
    propagate_ineqs_tactic handles other propagations with bounds.

--*/

#pragma once

#include "ast/arith_decl_plugin.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/simplifiers/dependent_expr_state.h"
#include "ast/simplifiers/bound_propagator.h"
#include "math/interval/interval.h"


class bound_simplifier : public dependent_expr_simplifier {
    typedef interval_manager<im_default_config> _interval_manager;
    typedef _interval_manager::interval interval;
    typedef _scoped_interval<_interval_manager> scoped_interval;

    arith_util              a;
    th_rewriter             m_rewriter;
    unsynch_mpq_manager     nm;
    small_object_allocator  m_alloc;
    bound_propagator        bp;
    im_default_config       i_cfg;
    _interval_manager       i_manager;
    unsigned                m_num_vars = 0;
    ptr_vector<expr>        m_var2expr;
    unsigned_vector         m_expr2var;
    bool                    m_updated = false;

    struct rw_cfg;
    struct rw;
   
    bool insert_bound(dependent_expr const& de);
    void tighten_bound(dependent_expr const& de);

    void reset();

    expr* to_expr(unsigned v) const { 
        return m_var2expr.get(v, nullptr); 
    }

    bool is_var(expr* e) const {
        return UINT_MAX != m_expr2var.get(e->get_id(), UINT_MAX);
    }

    unsigned to_var(expr* e) { 
        unsigned v = m_expr2var.get(e->get_id(), UINT_MAX); 
        if (v == UINT_MAX) {
            v = m_num_vars++;
            bp.mk_var(v, a.is_int(e));
            m_expr2var.setx(e->get_id(), v, UINT_MAX);
            m_var2expr.setx(v, e, nullptr);
        }
        return v;
    }

    void assert_lower(expr* x, rational const& n, bool strict);
    void assert_upper(expr* x, rational const& n, bool strict);

    bool has_upper(expr* x, rational& n, bool& strict);
    bool has_lower(expr* x, rational& n, bool& strict);
    void get_bounds(expr* x, scoped_interval&);

    // e = x + offset
    bool is_offset(expr* e, expr* x, rational& offset);

public:

    bound_simplifier(ast_manager& m, params_ref const& p, dependent_expr_state& fmls):
        dependent_expr_simplifier(m, fmls),
        a(m),
        m_rewriter(m),
        bp(nm, m_alloc, p),
        i_cfg(nm),
        i_manager(m.limit(), im_default_config(nm)) {
    }

    char const* name() const override { return "bounds-simplifier"; }
      
    bool supports_proofs() const override { return false; }

    void reduce() override;
};

