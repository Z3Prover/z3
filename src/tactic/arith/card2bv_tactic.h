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
#ifndef _CARD2BV_TACTIC_
#define _CARD2BV_TACTIC_

#include"params.h"
#include"pb_decl_plugin.h"
#include"th_rewriter.h"
#include"rewriter.h"

class ast_manager;
class tactic;

namespace pb {

    class card2bv_rewriter {
        ast_manager& m;
        arith_util   au;
        pb_util      pb;
        bv_util      bv;
        unsigned get_num_bits(func_decl* f);
    public:
        card2bv_rewriter(ast_manager& m);
        br_status mk_app_core(func_decl * f, unsigned sz, expr * const* args, expr_ref & result);
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
    public:
    card_pb_rewriter(ast_manager & m):
        rewriter_tpl<card2bv_rewriter_cfg>(m, false, m_cfg),
            m_cfg(m) {}
    };
};

tactic * mk_card2bv_tactic(ast_manager & m, params_ref const & p = params_ref());
/*
  ADD_TACTIC("card2bv", "convert pseudo-boolean constraints to bit-vectors.", "mk_card2bv_tactic(m, p)")
*/


#endif
