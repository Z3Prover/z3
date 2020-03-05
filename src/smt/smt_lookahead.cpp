/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_lookahead.cpp

Abstract:

    Lookahead cuber for SMT

Author:

    nbjorner 2019-05-27.

Revision History:

--*/

#include <cmath>
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "smt/smt_lookahead.h"
#include "smt/smt_context.h"

namespace smt {

    lookahead::lookahead(context& ctx): 
        ctx(ctx), m(ctx.get_manager()) {}

    double lookahead::get_score() {
        double score = 0;
        for (clause* cp : ctx.m_aux_clauses) {
            unsigned nf = 0, nu = 0;
            bool is_taut = false;
            for (literal lit : *cp) {
                switch (ctx.get_assignment(lit)) {
                case l_false:
                    if (ctx.get_assign_level(lit) > 0) {
                        ++nf;
                    }
                    break;
                case l_true:
                    is_taut = true;
                    break;
                default:
                    ++nu;
                    break;
                }
            }
            if (!is_taut && nf > 0) {
                score += pow(0.5, nu);
            }
        }
        return score;
    }

    struct lookahead::compare {
        context& ctx;
        compare(context& ctx): ctx(ctx) {}

        bool operator()(bool_var v1, bool_var v2) const {
            return ctx.get_activity(v1) > ctx.get_activity(v2);
        }
    };
    
    expr_ref lookahead::choose() {
        ctx.pop_to_base_lvl();
        unsigned sz = ctx.m_bool_var2expr.size();
        bool_var best_v = null_bool_var;
        double best_score = -1;
        svector<bool_var> vars;
        for (bool_var v = 0; v < static_cast<bool_var>(sz); ++v) {
            expr* b = ctx.bool_var2expr(v);
            if (b && ctx.get_assignment(v) == l_undef) {
                vars.push_back(v);
            }
        }
        compare comp(ctx);
        std::sort(vars.begin(), vars.end(), comp);
        
        unsigned nf = 0, nc = 0, ns = 0, bound = 2000, n = 0;
        for (bool_var v : vars) {
            if (!ctx.bool_var2expr(v)) continue;
            literal lit(v, false);	
            ctx.push_scope();
            ctx.assign(lit, b_justification::mk_axiom(), true);
            ctx.propagate();
            bool inconsistent = ctx.inconsistent();
            double score1 = get_score();
            ctx.pop_scope(1);
            if (inconsistent) {
                ctx.assign(~lit, b_justification::mk_axiom(), false);
                ctx.propagate();           
                ++nf;
                continue;
            }

            ctx.push_scope();
            ctx.assign(~lit, b_justification::mk_axiom(), true);
            ctx.propagate();
            inconsistent = ctx.inconsistent();
            double score2 = get_score();
            ctx.pop_scope(1);
            if (inconsistent) {
                ctx.assign(lit, b_justification::mk_axiom(), false);
                ctx.propagate(); 
                ++nf;
                continue;
            }
            double score = score1 + score2 + 1024*score1*score2;

            if (score > best_score || (score == best_score && ctx.get_random_value() % (++n) == 0)) {
                if (score > best_score) n = 0;
                best_score = score;
                best_v = v;
                bound += ns;
                ns = 0;
            }
            ++nc;
            ++ns;
            if (ns > bound) {
                break;
            }
        }
        expr_ref result(m);
        if (ctx.inconsistent()) {
            result = m.mk_false();
        }
        else if (best_v != null_bool_var) {
            result = ctx.bool_var2expr(best_v);
        }
        else {
            result = m.mk_true();
        }
        return result;
    }
}
