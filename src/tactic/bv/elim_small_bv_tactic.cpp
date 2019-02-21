/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

    elim_small_bv.h

Abstract:

    Tactic that eliminates small, quantified bit-vectors.

Author:

    Christoph (cwinter) 2015-11-09

Revision History:

--*/
#include "tactic/tactical.h"
#include "ast/rewriter/rewriter_def.h"
#include "tactic/generic_model_converter.h"
#include "util/cooperate.h"
#include "ast/bv_decl_plugin.h"
#include "ast/used_vars.h"
#include "ast/well_sorted.h"
#include "ast/rewriter/var_subst.h"
#include "ast/rewriter/th_rewriter.h"

#include "tactic/bv/elim_small_bv_tactic.h"

namespace {
class elim_small_bv_tactic : public tactic {

    struct rw_cfg : public default_rewriter_cfg {
        ast_manager               & m;
        params_ref                  m_params;
        bv_util                     m_util;
        th_rewriter                 m_simp;
        ref<generic_model_converter> m_mc;
        unsigned                    m_max_bits;
        unsigned long long          m_max_steps;
        unsigned long long          m_max_memory; // in bytes
        bool                        m_produce_models;
        sort_ref_vector             m_bindings;
        unsigned long               m_num_eliminated;

        rw_cfg(ast_manager & _m, params_ref const & p) :
            m(_m),
            m_params(p),
            m_util(_m),
            m_simp(_m),
            m_bindings(_m),
            m_num_eliminated(0) {
            updt_params(p);
            m_max_steps = UINT_MAX;
        }

        bool max_steps_exceeded(unsigned long long num_steps) const {
            cooperate("elim-small-bv");
            if (num_steps > m_max_steps)
                return true;
            if (memory::get_allocation_size() > m_max_memory)
                throw tactic_exception(TACTIC_MAX_MEMORY_MSG);
            return false;
        }

        bool is_small_bv(sort * s) {
            return m_util.is_bv_sort(s) && m_util.get_bv_size(s) <= m_max_bits;
        }

        expr_ref replace_var(used_vars & uv,
            unsigned num_decls, unsigned max_var_idx_p1,
            unsigned idx, sort * s, expr * e, expr * replacement) {
            TRACE("elim_small_bv", tout << "replace idx " << idx << " with " << mk_ismt2_pp(replacement, m) <<
                " in " << mk_ismt2_pp(e, m) << std::endl;);
            expr_ref res(m);
            ptr_vector<expr> substitution;

            substitution.resize(num_decls, nullptr);
            substitution[num_decls - idx - 1] = replacement;

            // (VAR 0) is in the first position of substitution; (VAR num_decls-1) is in the last position.

            for (unsigned i = 0; i < max_var_idx_p1; i++)
                substitution.push_back(nullptr);

            // (VAR num_decls) ... (VAR num_decls+sz-1); are in positions num_decls .. num_decls+sz-1

            std::reverse(substitution.c_ptr(), substitution.c_ptr() + substitution.size());

            // (VAR 0) should be in the last position of substitution.

            TRACE("elim_small_bv", tout << "substitution: " << std::endl;
                                    for (unsigned k = 0; k < substitution.size(); k++) {
                                        expr * se = substitution[k];
                                        tout << k << " = ";
                                        if (se == 0) tout << "0";
                                        else tout << mk_ismt2_pp(se, m);
                                        tout << std::endl;
                                    });

            var_subst vsbst(m);
            res = vsbst(e, substitution.size(), substitution.c_ptr());
            SASSERT(is_well_sorted(m, res));

            proof_ref pr(m);
            m_simp(res, res, pr);
            TRACE("elim_small_bv", tout << "replace done: " << mk_ismt2_pp(res, m) << std::endl;);

            return res;
        }

        br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
            TRACE("elim_small_bv_app", expr_ref tmp(m.mk_app(f, num, args), m); tout << "reduce " << tmp << std::endl; );
            return BR_FAILED;
        }

        bool reduce_quantifier(
            quantifier * q,
            expr * old_body,
            expr * const * new_patterns,
            expr * const * new_no_patterns,
            expr_ref & result,
            proof_ref & result_pr) {
            if (is_lambda(q)) {
                return false;
            }
            TRACE("elim_small_bv", tout << "reduce_quantifier " << mk_ismt2_pp(q, m) << std::endl; );
            unsigned long long num_steps = 0;
            unsigned curr_sz = m_bindings.size();
            SASSERT(q->get_num_decls() <= curr_sz);
            unsigned num_decls = q->get_num_decls();
            unsigned old_sz = curr_sz - num_decls;

            used_vars uv;
            uv(q);
            SASSERT(is_well_sorted(m, q));
            unsigned max_var_idx_p1 = uv.get_max_found_var_idx_plus_1();

            expr_ref body(old_body, m);
            for (unsigned i = num_decls-1; i != ((unsigned)-1) && !max_steps_exceeded(num_steps); i--) {
                sort * s = q->get_decl_sort(i);
                unsigned bv_sz = m_util.get_bv_size(s);

                if (is_small_bv(s) && !max_steps_exceeded(num_steps)) {
                    TRACE("elim_small_bv", tout << "eliminating " << q->get_decl_name(i) <<
                        "; sort = " << mk_ismt2_pp(s, m) <<
                        "; body = " << mk_ismt2_pp(body, m) << std::endl;);

                    expr_ref_vector new_bodies(m);
                    for (unsigned j = 0; j < bv_sz && !max_steps_exceeded(num_steps); j ++) {
                        expr_ref n(m_util.mk_numeral(j, bv_sz), m);
                        new_bodies.push_back(replace_var(uv, num_decls, max_var_idx_p1, i, s, body, n));
                        num_steps++;
                    }

                    TRACE("elim_small_bv", tout << "new bodies: " << std::endl;
                                           for (unsigned k = 0; k < new_bodies.size(); k++)
                                               tout << mk_ismt2_pp(new_bodies[k].get(), m) << std::endl; );

                    body = is_forall(q) ? m.mk_and(new_bodies.size(), new_bodies.c_ptr()) :
                                          m.mk_or(new_bodies.size(), new_bodies.c_ptr());
                    SASSERT(is_well_sorted(m, body));

                    proof_ref pr(m);
                    m_simp(body, body, pr);
                    m_num_eliminated++;
                }
            }

            quantifier_ref new_q(m);
            new_q = m.update_quantifier(q, body);
            unused_vars_eliminator el(m, m_params);
            result = el(new_q);

            TRACE("elim_small_bv", tout << "elimination result: " << mk_ismt2_pp(result, m) << std::endl; );

            result_pr = nullptr; // proofs NIY
            m_bindings.shrink(old_sz);
            return true;
        }

        bool pre_visit(expr * t) {
            TRACE("elim_small_bv_pre", tout << "pre_visit: " << mk_ismt2_pp(t, m) << std::endl;);
            if (is_quantifier(t)) {
                quantifier * q = to_quantifier(t);
                TRACE("elim_small_bv", tout << "pre_visit quantifier [" << q->get_id() << "]: " << mk_ismt2_pp(q->get_expr(), m) << std::endl;);
                sort_ref_vector new_bindings(m);
                for (unsigned i = 0; i < q->get_num_decls(); i++)
                    new_bindings.push_back(q->get_decl_sort(i));
                SASSERT(new_bindings.size() == q->get_num_decls());
                m_bindings.append(new_bindings);
            }
            return true;
        }

        void updt_params(params_ref const & p) {
            m_params = p;
            m_max_memory = megabytes_to_bytes(p.get_uint("max_memory", UINT_MAX));
            m_max_steps = p.get_uint("max_steps", UINT_MAX);
            m_max_bits = p.get_uint("max_bits", 4);
        }
    };

    struct rw : public rewriter_tpl<rw_cfg> {
        rw_cfg m_cfg;

        rw(ast_manager & m, params_ref const & p) :
            rewriter_tpl<rw_cfg>(m, m.proofs_enabled(), m_cfg),
            m_cfg(m, p) {
        }
    };

    ast_manager & m;
    rw            m_rw;
    params_ref    m_params;

public:
    elim_small_bv_tactic(ast_manager & m, params_ref const & p) :
        m(m),
        m_rw(m, p),
        m_params(p) {
    }

    tactic * translate(ast_manager & m) override {
        return alloc(elim_small_bv_tactic, m, m_params);
    }

    void updt_params(params_ref const & p) override {
        m_params = p;
        m_rw.cfg().updt_params(p);
    }

    void collect_param_descrs(param_descrs & r) override {
        insert_max_memory(r);
        insert_max_steps(r);
        r.insert("max_bits", CPK_UINT, "(default: 4) maximum bit-vector size of quantified bit-vectors to be eliminated.");
    }

    void operator()(goal_ref const & g,
                    goal_ref_buffer & result) override {
        SASSERT(g->is_well_sorted());
        tactic_report report("elim-small-bv", *g);
        bool produce_proofs = g->proofs_enabled();
        fail_if_proof_generation("elim-small-bv", g);
        fail_if_unsat_core_generation("elim-small-bv", g);
        m_rw.cfg().m_produce_models = g->models_enabled();

        expr_ref   new_curr(m);
        proof_ref  new_pr(m);
        unsigned   size = g->size();
        for (unsigned idx = 0; idx < size; idx++) {
            expr * curr = g->form(idx);
            m_rw(curr, new_curr, new_pr);
            if (produce_proofs) {
                proof * pr = g->pr(idx);
                new_pr = m.mk_modus_ponens(pr, new_pr);
            }
            g->update(idx, new_curr, new_pr, g->dep(idx));
        }
        g->add(m_rw.m_cfg.m_mc.get());

        report_tactic_progress(":elim-small-bv-num-eliminated", m_rw.m_cfg.m_num_eliminated);
        g->inc_depth();
        result.push_back(g.get());
        TRACE("elim-small-bv", g->display(tout););
        SASSERT(g->is_well_sorted());
    }

    void cleanup() override {
        m_rw.~rw();
        new (&m_rw) rw(m, m_params);
    }

};
}

tactic * mk_elim_small_bv_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(elim_small_bv_tactic, m, p));
}

