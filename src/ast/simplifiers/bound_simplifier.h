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
#include "math/interval/dep_intervals.h"


class bound_simplifier : public dependent_expr_simplifier {
    typedef bound_propagator::var a_var;
    typedef numeral_buffer<mpq, unsynch_mpq_manager> mpq_buffer;
    typedef svector<a_var> var_buffer;

    arith_util              a;
    params_ref              m_params;
    th_rewriter             m_rewriter;
    unsynch_mpq_manager     nm;
    small_object_allocator  m_alloc;
    bound_propagator        bp;
    u_dependency_manager    m_dep_manager;
    dep_intervals           m_interval;
    ptr_vector<expr>        m_var2expr;
    unsigned_vector         m_expr2var;
    expr_ref_vector         m_trail;
    mpq_buffer              m_num_buffer;
    var_buffer              m_var_buffer;
    unsigned                m_num_reduced = 0;

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
            v = m_var2expr.size();
            expr* core_e = e;
            a.is_to_real(e, core_e);
            bp.mk_var(v, a.is_int(core_e));
            m_expr2var.setx(e->get_id(), v, UINT_MAX);
            if (e != core_e)
                m_expr2var.setx(core_e->get_id(), v, UINT_MAX);
            m_var2expr.push_back(core_e);
            m_trail.push_back(e);
        }
        return v;
    }

    bool reduce_arg(expr* arg, expr_ref& result);

    br_status reduce_app(func_decl* f, unsigned num_args, expr* const* args, expr_ref& result, proof_ref& pr);

    

    void assert_lower(expr* x, rational const& n, bool strict);
    void assert_upper(expr* x, rational const& n, bool strict);

    bool has_upper(expr* x, rational& n, bool& strict);
    bool has_lower(expr* x, rational& n, bool& strict);
    void get_bounds(expr* x, scoped_dep_interval&);

    void expr2linear_pol(expr* t, mpq_buffer& as, var_buffer& xs);
    bool lower_subsumed(expr* p, mpq const& k, bool strict);
    bool upper_subsumed(expr* p, mpq const& k, bool strict);
    void restore_bounds();

    // e = x + offset
    bool is_offset(expr* e, expr* x, rational& offset);

public:

    bound_simplifier(ast_manager& m, params_ref const& p, dependent_expr_state& fmls):
        dependent_expr_simplifier(m, fmls),
        a(m),
        m_rewriter(m),
        bp(nm, m_alloc, p),
        m_interval(m_dep_manager, m.limit()),
        m_trail(m),
        m_num_buffer(nm) {
        updt_params(p);
    }

    char const* name() const override { return "propagate-ineqs"; }
      
    bool supports_proofs() const override { return false; }

    void reduce() override;

    void updt_params(params_ref const& p) override {
        m_params.append(p);
        bp.updt_params(m_params);
    }

    void collect_param_descrs(param_descrs & r) override {
        bound_propagator::get_param_descrs(r);
    }

    void collect_statistics(statistics& st) const override {
        st.update("bound-propagations", bp.get_num_propagations());
        st.update("bound-false-alarms", bp.get_num_false_alarms());
        st.update("bound-simplifications", m_num_reduced);
    }

    void reset_statistics() override {
        m_num_reduced = 0;
        bp.reset_statistics();
    }
};

