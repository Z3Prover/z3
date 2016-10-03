/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    card2bv_tactic.cpp

Abstract:

    Tactic for converting Pseudo-Boolean constraints to BV

Author:

    Nikolaj Bjorner (nbjorner) 2014-03-20

Notes:

--*/
#ifndef CARD2BV_TACTIC_H_
#define CARD2BV_TACTIC_H_

#include"params.h"
#include"pb_decl_plugin.h"
#include"th_rewriter.h"
#include"rewriter.h"
#include<typeinfo>
#include"sorting_network.h"


class ast_manager;
class tactic;

namespace pb {

    class card2bv_rewriter {
    public:
        typedef expr* literal;
        typedef ptr_vector<expr> literal_vector;
    private:
        ast_manager& m;
        arith_util   au;
        pb_util      pb;
        bv_util      bv;
        psort_nw<card2bv_rewriter> m_sort;
        expr_ref_vector m_lemmas;
        expr_ref_vector m_trail;

        unsigned get_num_bits(func_decl* f);
        void mk_bv(func_decl * f, unsigned sz, expr * const* args, expr_ref & result);
        br_status mk_shannon(func_decl * f, unsigned sz, expr * const* args, expr_ref & result);
        expr* negate(expr* e);
        expr* mk_ite(expr* c, expr* hi, expr* lo);
        bool is_or(func_decl* f);
        bool is_and(func_decl* f);
        bool is_atmost1(func_decl* f, unsigned sz, expr * const* args, expr_ref& result);
        expr_ref mk_atmost1(unsigned sz, expr * const* args);

    public:
        card2bv_rewriter(ast_manager& m);
        br_status mk_app_core(func_decl * f, unsigned sz, expr * const* args, expr_ref & result);
        void mk_assert(func_decl * f, unsigned sz, expr * const* args, expr_ref & result, expr_ref_vector& lemmas);

        // definitions used for sorting network
        literal mk_false() { return m.mk_false(); }
        literal mk_true() { return m.mk_true(); }
        literal mk_max(literal a, literal b) { return trail(m.mk_or(a, b)); }
        literal mk_min(literal a, literal b) { return trail(m.mk_and(a, b)); }
        literal mk_not(literal a) { if (m.is_not(a,a)) return a; return trail(m.mk_not(a)); }
        std::ostream& pp(std::ostream& out, literal lit);
        literal fresh();
        literal trail(literal l);
        void mk_clause(unsigned n, literal const* lits);
        
    };

    struct card2bv_rewriter_cfg : public default_rewriter_cfg {
        card2bv_rewriter m_r;
        bool rewrite_patterns() const { return false; }
        bool flat_assoc(func_decl * f) const { return false; }
        br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
            result_pr = 0;
            return m_r.mk_app_core(f, num, args, result);
        }
        card2bv_rewriter_cfg(ast_manager & m):m_r(m) {}
    };
    
    class card_pb_rewriter : public rewriter_tpl<card2bv_rewriter_cfg> {
        card2bv_rewriter_cfg m_cfg;
        pb_util         pb;
        expr_ref_vector m_lemmas;
    public:
        card_pb_rewriter(ast_manager & m):
            rewriter_tpl<card2bv_rewriter_cfg>(m, false, m_cfg),
            m_cfg(m),
            pb(m),
            m_lemmas(m) {}
        
        void rewrite(expr* e, expr_ref& result);

        expr_ref_vector& lemmas() { return m_lemmas; }
    };
};

tactic * mk_card2bv_tactic(ast_manager & m, params_ref const & p = params_ref());
/*
  ADD_TACTIC("card2bv", "convert pseudo-boolean constraints to bit-vectors.", "mk_card2bv_tactic(m, p)")
*/


#endif
