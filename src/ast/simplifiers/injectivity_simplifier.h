/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    injectivity_simplifier.h

Abstract:

    Dependent expression simplifier for injectivity rewriting.

    - Discover axioms of the form `forall x. (= (g (f x)) x)`
      Mark `f` as injective

    - Rewrite (sub)terms of the form `(= (f x) (f y))` to `(= x y)` whenever `f` is injective.

Author:

    Nicolas Braud-Santoni (t-nibrau) 2017-08-10
    Ported to simplifier by Nikolaj Bjorner (nbjorner) 2023

Notes:
    * does not support cores nor proofs

--*/

#pragma once

#include "ast/simplifiers/dependent_expr_state.h"
#include "ast/rewriter/rewriter_def.h"

class injectivity_simplifier : public dependent_expr_simplifier {

    struct inj_map : public obj_map<func_decl, obj_hashtable<func_decl>*> {
        ast_manager& m;

        inj_map(ast_manager& m) : m(m) {}

        ~inj_map() {
            for (auto& kv : *this) {
                for (func_decl* f : *kv.get_value())
                    m.dec_ref(f);
                m.dec_ref(kv.m_key);
                dealloc(kv.m_value);
            }
        }

        void insert(func_decl* f, func_decl* g) {
            obj_hashtable<func_decl>* inverses;
            if (!obj_map::find(f, inverses)) {
                m.inc_ref(f);
                inverses = alloc(obj_hashtable<func_decl>);
                obj_map::insert(f, inverses);
            }
            if (!inverses->contains(g)) {
                m.inc_ref(g);
                inverses->insert(g);
            }
        }
    };

    struct rw_cfg : public default_rewriter_cfg {
        ast_manager&  m;
        inj_map&      m_map;

        rw_cfg(ast_manager& m, inj_map& map) : m(m), m_map(map) {}

        br_status reduce_app(func_decl* f, unsigned num, expr* const* args,
                             expr_ref& result, proof_ref& result_pr) {
            if (num != 2 || !m.is_eq(f))
                return BR_FAILED;

            if (!is_app(args[0]) || !is_app(args[1]))
                return BR_FAILED;

            app* a = to_app(args[0]);
            app* b = to_app(args[1]);

            if (a->get_decl() != b->get_decl())
                return BR_FAILED;

            if (a->get_num_args() != 1 || b->get_num_args() != 1)
                return BR_FAILED;

            if (!m_map.contains(a->get_decl()))
                return BR_FAILED;

            SASSERT(a->get_arg(0)->get_sort() == b->get_arg(0)->get_sort());
            result = m.mk_eq(a->get_arg(0), b->get_arg(0));
            result_pr = nullptr;
            return BR_DONE;
        }
    };

    struct rw : public rewriter_tpl<rw_cfg> {
        rw_cfg m_cfg;

        rw(ast_manager& m, inj_map& map) :
            rewriter_tpl<rw_cfg>(m, false, m_cfg),
            m_cfg(m, map) {}
    };

    inj_map m_map;
    rw      m_rw;

    bool is_axiom(expr* n, func_decl*& f, func_decl*& g) {
        if (!is_forall(n))
            return false;

        quantifier* q = to_quantifier(n);
        if (q->get_num_decls() != 1)
            return false;

        expr* body = q->get_expr();
        if (!m.is_eq(body))
            return false;

        app* body_a = to_app(body);
        if (body_a->get_num_args() != 2)
            return false;

        expr* a = body_a->get_arg(0);
        expr* b = body_a->get_arg(1);

        if (is_app(a) && is_var(b)) {
            // keep a, b as-is
        }
        else if (is_app(b) && is_var(a)) {
            std::swap(a, b);
        }
        else
            return false;

        app* a_app = to_app(a);
        var* b_var = to_var(b);

        if (b_var->get_idx() != 0)
            return false;

        if (a_app->get_num_args() != 1)
            return false;

        g = a_app->get_decl();
        expr* a_body = a_app->get_arg(0);

        if (!is_app(a_body))
            return false;

        app* a_body_app = to_app(a_body);
        if (a_body_app->get_num_args() != 1)
            return false;

        f = a_body_app->get_decl();
        expr* a_body_body = a_body_app->get_arg(0);

        if (a_body_body != b_var)
            return false;

        return true;
    }

public:
    injectivity_simplifier(ast_manager& m, params_ref const& p, dependent_expr_state& s) :
        dependent_expr_simplifier(m, s), m_map(m), m_rw(m, m_map) {}

    char const* name() const override { return "injectivity"; }

    void reduce() override {
        // Phase 1: Scan for injectivity axioms
        for (unsigned idx : indices()) {
            auto const& d = m_fmls[idx];
            func_decl* fn = nullptr;
            func_decl* inv = nullptr;
            if (is_axiom(d.fml(), fn, inv)) {
                TRACE(injectivity, tout << "Marking " << fn->get_name() << " as injective\n";);
                m_map.insert(fn, inv);
            }
        }

        // Phase 2: Rewrite using injectivity
        expr_ref new_fml(m);
        proof_ref new_pr(m);
        for (unsigned idx : indices()) {
            auto const& d = m_fmls[idx];
            m_rw(d.fml(), new_fml, new_pr);
            if (new_fml != d.fml())
                m_fmls.update(idx, dependent_expr(m, new_fml, nullptr, d.dep()));
        }
    }
};
