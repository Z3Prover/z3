/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    bv2int_rewriter.h

Abstract:

    Basic rewriting rules for bv2int propagation.

Author:

    Nikolaj (nbjorner) 2011-05-05

Notes:

--*/
#pragma once

#include "ast/ast.h"
#include "ast/rewriter/rewriter.h"
#include "ast/bv_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "util/params.h"
#include "tactic/goal.h"

class bv2int_rewriter_ctx {
    unsigned                 m_max_size;
    expr_ref_vector          m_side_conditions;
    obj_map<expr, expr*>     m_power2;
    expr_ref_vector          m_trail;
    
public:
    bv2int_rewriter_ctx(ast_manager& m, params_ref const& p, unsigned max_size) : 
		m_max_size(max_size), m_side_conditions(m), m_trail(m) {
		update_params(p); 
	}

    void reset() { m_side_conditions.reset(); m_trail.reset(); m_power2.reset(); }
    void add_side_condition(expr* e) { m_side_conditions.push_back(e); }
    unsigned num_side_conditions() const { return m_side_conditions.size(); }
    expr* const* side_conditions() const { return m_side_conditions.data(); }
    unsigned get_max_num_bits() const { return m_max_size; }
    
    void collect_power2(goal const & s);
    bool is_power2(expr* x, expr*& log_x);
    obj_map<expr, expr*> const& power2() const { return m_power2; }

private:
    void update_params(params_ref const& p); 
};

class bv2int_rewriter {
    ast_manager &            m_manager;
    bv2int_rewriter_ctx&     m_ctx;
    bv_util                  m_bv;
    arith_util               m_arith;

public:
    bv2int_rewriter(ast_manager & m, bv2int_rewriter_ctx& ctx);
    ast_manager & m() const { return m_manager; }

    br_status mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result);
    void mk_app(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
        if (mk_app_core(f, num_args, args, result) == BR_FAILED)
            result = m().mk_app(f, num_args, args);
    }
private:
    br_status mk_eq(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_ite(expr* c, expr* s, expr* t, expr_ref& result);
    br_status mk_le(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_lt(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_ge(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_gt(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_idiv(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_mod(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_rem(expr * arg1, expr * arg2, expr_ref & result);   
    br_status mk_add(unsigned num_args, expr * const * args, expr_ref & result);     
    br_status mk_mul(unsigned num_args, expr * const * args, expr_ref & result); 
    br_status mk_sub(unsigned num_args, expr * const * args, expr_ref & result); 
    br_status mk_add(expr* s, expr* t, expr_ref& result);
    br_status mk_mul(expr* s, expr* t, expr_ref& result);
    br_status mk_sub(expr* s, expr* t, expr_ref& result);
    br_status mk_uminus(expr* e, expr_ref & result); 

    bool      is_bv2int(expr* e, expr_ref& s);
    bool      is_sbv2int(expr* e, expr_ref& s);
    bool      is_bv2int_diff(expr* e, expr_ref& s, expr_ref& t);
    bool      is_zero(expr* e);
    bool      is_shl1(expr* e, expr_ref& s);

    expr*     mk_bv_add(expr* s, expr* t, bool is_signed);
    expr*     mk_bv_mul(expr* s, expr* t, bool is_signed);
    expr*     mk_sbv2int(expr* s);
    expr*     mk_extend(unsigned sz, expr* b, bool is_signed);

    void      align_sizes(expr_ref& s, expr_ref& t, bool is_signed);

};

struct bv2int_rewriter_cfg : public default_rewriter_cfg {
    bv2int_rewriter m_r;
    bool rewrite_patterns() const { return false; }
    bool flat_assoc(func_decl * f) const { return false; }
    br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
        result_pr = nullptr;
        return m_r.mk_app_core(f, num, args, result);
    }
    bv2int_rewriter_cfg(ast_manager & m, bv2int_rewriter_ctx& ctx):m_r(m, ctx) {}
};

class bv2int_rewriter_star : public rewriter_tpl<bv2int_rewriter_cfg> {
    bv2int_rewriter_cfg m_cfg;
public:
    bv2int_rewriter_star(ast_manager & m, bv2int_rewriter_ctx& ctx):
        rewriter_tpl<bv2int_rewriter_cfg>(m, false, m_cfg),
        m_cfg(m, ctx) {}
};

