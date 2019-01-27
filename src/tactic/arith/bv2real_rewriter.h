/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    bv2real_rewriter.h

Abstract:

    Basic rewriting rules for bv2real propagation.

Author:

    Nikolaj (nbjorner) 2011-08-05

Notes:

--*/
#ifndef BV2REAL_REWRITER_H_
#define BV2REAL_REWRITER_H_

#include "ast/ast.h"
#include "ast/rewriter/rewriter.h"
#include "ast/bv_decl_plugin.h"
#include "ast/arith_decl_plugin.h"

//
// bv2real[d,r](n,m) has interpretation: 
// sbv2int(n)/d + sbv2int(m)/d*sqrt(r)
// where
// sbv2int is signed bit-vector 2 integer.
// 
class bv2real_util {
    struct bvr_sig { 
        unsigned m_msz, m_nsz;
        rational m_d, m_r; 
    };

    struct bvr_eq {
        bool operator()(bvr_sig const& x, bvr_sig const& y) const {
            return 
                x.m_msz == y.m_msz && 
                x.m_nsz == y.m_nsz && 
                x.m_d   == y.m_d && 
                x.m_r   == y.m_r;
        }
    };

    struct bvr_hash {
        unsigned operator()(bvr_sig const& x) const {
            unsigned a[3] = { x.m_msz, x.m_nsz, x.m_d.hash() };            
            return string_hash((char const*)a, 12, x.m_r.hash());
        }
    };

    ast_manager& m_manager;
    arith_util   m_arith;
    bv_util      m_bv;
    func_decl_ref_vector m_decls;
    func_decl_ref m_pos_le;
    func_decl_ref m_pos_lt;
    expr_ref_vector m_side_conditions;
    map<bvr_sig, func_decl*, bvr_hash, bvr_eq> m_sig2decl;
    obj_map<func_decl, bvr_sig>                m_decl2sig;
    rational m_default_root;
    rational m_default_divisor;
    rational m_max_divisor;
    unsigned m_max_num_bits;

    class contains_bv2real_proc;

public:
    bv2real_util(ast_manager& m, rational const& default_root, rational const& default_divisor, unsigned max_num_bits);

    void reset() { m_side_conditions.reset(); }

    bool is_bv2real(func_decl* f) const;
    bool is_bv2real(func_decl* f, unsigned num_args, expr* const* args, 
                    expr*& m, expr*& n, rational& d, rational& r) const;
    bool is_bv2real(expr* e, expr*& n, expr*& m, rational& d, rational& r) const;
    bool is_bv2real(expr* e, expr*& n, expr*& m, rational& d);    

    bool contains_bv2real(expr* e) const;

    bool mk_bv2real(expr* s, expr* t, rational& d, rational& r, expr_ref& result);
    expr* mk_bv2real_c(expr* s, expr* t, rational const& d, rational const& r);
    expr* mk_bv2real(expr* n, expr* m) { return mk_bv2real_c(n, m, default_divisor(), default_root()); }

    void mk_bv2real_reduced(expr* s, expr* t, expr_ref & result) { mk_bv2real_reduced(s, t, default_divisor(), default_root(), result); }
    void mk_bv2real_reduced(expr* s, expr* t, rational const& d, rational const& r, expr_ref & result);


    //
    // Positive polarity comparison operators.
    // Translation of positive polarity comparison requires fewer clauses.
    //
    bool is_pos_ltf(func_decl* f) const { return f == m_pos_lt; }
    bool is_pos_lef(func_decl* f) const { return f == m_pos_le; }
    bool is_pos_lt(expr const* e) const { return is_app(e) && is_pos_ltf(to_app(e)->get_decl()); }
    bool is_pos_le(expr const* e) const { return is_app(e) && is_pos_lef(to_app(e)->get_decl()); }
    MATCH_BINARY(is_pos_lt);
    MATCH_BINARY(is_pos_le);
    expr* mk_pos_lt(expr* s, expr* t) { return m().mk_app(m_pos_lt, s, t); }
    expr* mk_pos_le(expr* s, expr* t) { return m().mk_app(m_pos_le, s, t); }

    rational const& default_root() const { return m_default_root; }
    rational const& default_divisor() const { return m_default_divisor; }
    rational const& max_divisor() const { return m_max_divisor; }

    unsigned get_max_num_bits() const { return m_max_num_bits; }

    void add_side_condition(expr* e) { m_side_conditions.push_back(e); }
    unsigned num_side_conditions() const { return m_side_conditions.size(); }
    expr* const* side_conditions() const { return m_side_conditions.c_ptr(); }

    bool      is_zero(expr* e);

    expr*     mk_bv_add(expr* s, expr* t);
    expr*     mk_bv_sub(expr* s, expr* t);
    expr*     mk_bv_mul(expr* s, expr* t);
    expr*     mk_bv_mul(rational const& n, expr* t);
    expr*     mk_extend(unsigned sz, expr* b);
    expr*     mk_sbv(rational const& n); 

    void      align_sizes(expr_ref& s, expr_ref& t);
    void      align_divisors(expr_ref& s1, expr_ref& s2, expr_ref& t1, expr_ref& t2, rational& d1, rational& d2);

    bool      is_bv2real(expr* n, expr_ref& s, expr_ref& t, rational& d, rational& r);
    bool      align_divisor(expr_ref& s, expr_ref& t, rational& d);

    bool       mk_is_divisible_by(expr_ref& s, rational const& _overflow);

    void       add_aux_decl(func_decl* f) { m_decls.push_back(f); }
    unsigned   num_aux_decls() const { return m_decls.size(); }
    func_decl* get_aux_decl(unsigned i) const { return m_decls[i]; }

private:
    ast_manager & m() const { return m_manager; }
    arith_util & a() { return m_arith; }
    void mk_div(expr* e, rational const& d, expr_ref& result);
    void mk_sbv2real(expr* e, expr_ref& result);
};


class bv2real_rewriter {
    ast_manager &            m_manager;
    bv2real_util&            m_util;
    bv_util                  m_bv;
    arith_util               m_arith;

public:
    bv2real_rewriter(ast_manager & m, bv2real_util& util);

    br_status mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result);

private:
    ast_manager & m() const { return m_manager; }
    arith_util & a() { return m_arith; }
    bv2real_util& u() { return m_util; }
    br_status mk_eq(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_ite(expr* c, expr* s, expr* t, expr_ref& result);
    bool      mk_le(expr* s, expr* t, bool is_pos, bool is_neg, expr_ref& result);
    br_status mk_le(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_lt(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_le_pos(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_lt_pos(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_ge(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_gt(expr * arg1, expr * arg2, expr_ref & result);
    br_status mk_add(unsigned num_args, expr * const * args, expr_ref & result);     
    br_status mk_mul(unsigned num_args, expr * const * args, expr_ref & result); 
    br_status mk_sub(unsigned num_args, expr * const * args, expr_ref & result); 
    br_status mk_div(expr* s, expr* t, expr_ref& result);
    br_status mk_add(expr* s, expr* t, expr_ref& result);
    br_status mk_mul(expr* s, expr* t, expr_ref& result);
    br_status mk_sub(expr* s, expr* t, expr_ref& result);
    br_status mk_uminus(expr* e, expr_ref & result); 
};

struct bv2real_rewriter_cfg : public default_rewriter_cfg {
    bv2real_rewriter m_r;
    bool rewrite_patterns() const { return false; }
    bool flat_assoc(func_decl * f) const { return false; }
    br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
        result_pr = nullptr;
        return m_r.mk_app_core(f, num, args, result);
    }
    bv2real_rewriter_cfg(ast_manager & m, bv2real_util& u):m_r(m, u) {}
};

class bv2real_rewriter_star : public rewriter_tpl<bv2real_rewriter_cfg> {
    bv2real_rewriter_cfg m_cfg;
public:
    bv2real_rewriter_star(ast_manager & m, bv2real_util& u):
        rewriter_tpl<bv2real_rewriter_cfg>(m, false, m_cfg),
        m_cfg(m, u) {}
};




/**
   \brief replace le(bv2real(a),bv2real(b)) by under-approximation.
*/

class bv2real_elim_rewriter {
    bv2real_util&            m_util;
public:
    bv2real_elim_rewriter(bv2real_util& util) : m_util(util) {}

    br_status mk_app_core(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result);
};


struct bv2real_elim_rewriter_cfg : public default_rewriter_cfg {
    bv2real_elim_rewriter m_r;
    bool rewrite_patterns() const { return false; }
    bool flat_assoc(func_decl * f) const { return false; }
    br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
        result_pr = nullptr;
        return m_r.mk_app_core(f, num, args, result);
    }
    bv2real_elim_rewriter_cfg(bv2real_util& u):m_r(u) {}
};

class bv2real_elim_rewriter_star : public rewriter_tpl<bv2real_elim_rewriter_cfg> {
    bv2real_elim_rewriter_cfg m_cfg;
public:
    bv2real_elim_rewriter_star(ast_manager & m, bv2real_util& u):
        rewriter_tpl<bv2real_elim_rewriter_cfg>(m, false, m_cfg),
        m_cfg(u) {}
};

#endif
