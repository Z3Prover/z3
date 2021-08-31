/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

  injectivity_tactic.cpp

Abstract:

  Injectivity tactics
  - Discover axioms of the form `forall x. (= (g (f x)) x`
    Mark `f` as injective
  - Rewrite (sub)terms of the form `(= (f x) (f y))` to `(= x y)` whenever `f` is injective.

Author:

  Nicolas Braud-Santoni (t-nibrau) 2017-08-10

Notes:

--*/
#include <algorithm>
#include <utility>
#include "tactic/tactical.h"
#include "ast/rewriter/rewriter_def.h"
#include "tactic/core/injectivity_tactic.h"
#include "util/dec_ref_util.h"


class injectivity_tactic : public tactic {

    struct InjHelper : public obj_map<func_decl, obj_hashtable<func_decl>*> {
        ast_manager & m_manager;

        void insert(func_decl* const f, func_decl* const g) {
            obj_hashtable<func_decl> *m;
            if (! obj_map::find(f, m)) {
                m_manager.inc_ref(f);
                m = alloc(obj_hashtable<func_decl>); // TODO: Check we don't leak memory
                obj_map::insert(f, m);
            }
            if (!m->contains(g)) {
                m_manager.inc_ref(g);
                m->insert(g);
            }
        }

        bool find(func_decl* const f, func_decl* const g) const {
            obj_hashtable<func_decl> *m;
            if(! obj_map::find(f, m))
                return false;

            return m->contains(g);
        }

        InjHelper(ast_manager& m) : obj_map<func_decl, obj_hashtable<func_decl>*>(), m_manager(m) {}
        ~InjHelper() {
            for(auto m : *this) {
                for (func_decl* f : *m.get_value())
                    m_manager.dec_ref(f);

                m_manager.dec_ref(m.m_key);
                dealloc(m.m_value);
            }
        }

    };

    struct finder {
        ast_manager & m_manager;
        InjHelper   & inj_map;

        finder(ast_manager & m, InjHelper & map, params_ref const & p) :
            m_manager(m),
            inj_map(map) {
            updt_params(p);
        }

        ast_manager & m() const { return m_manager; }

        bool is_axiom(expr* n, func_decl* &f, func_decl* &g) {
            if (!is_forall(n))
                return false;

            quantifier* const q = to_quantifier(n);
            if (q->get_num_decls() != 1)
                return false;

            const expr * const body = q->get_expr();

            // n ~= forall x. body

            if (!m().is_eq(body))
                return false;

            const app * const body_a = to_app(body);
            if (body_a->get_num_args() != 2)
                return false;

            const expr* a = body_a->get_arg(0);
            const expr* b = body_a->get_arg(1);

            // n ~= forall x. (= a b)

            if (is_app(a) && is_var(b)) {
                // Do nothing
            }
            else if (is_app(b) && is_var(a)) {
                std::swap(a, b);
            }
            else
                return false;

            const app* const a_app = to_app(a);
            const var* const b_var = to_var(b);

            if (b_var->get_idx() != 0) // idx is the De Bruijn's index
                return false;

            if (a_app->get_num_args() != 1)
                return false;

            g = a_app->get_decl();
            const expr* const a_body = a_app->get_arg(0);

            // n ~= forall x. (= (g a_body) x)

            if (!is_app(a_body))
                return false;
            const app* const a_body_app = to_app(a_body);
            if (a_body_app->get_num_args() != 1) // Maybe TODO: support multi-argument functions
                return false;

            f = a_body_app->get_decl();
            const expr* const a_body_body = a_body_app->get_arg(0);

            // n ~= forall x. (= (g (f a_body_body)) x)
            if (a_body_body != b_var)
                return false;

            // n ~= forall x. (= (g (f x)) x)

            return true;
        }

        void operator()(goal_ref const & goal,
                        goal_ref_buffer & result) {
            tactic_report report("injectivity", *goal);
            fail_if_unsat_core_generation("injectivity", goal); // TODO: Support UNSAT cores
            fail_if_proof_generation("injectivity", goal);

            for (unsigned i = 0; i < goal->size(); ++i) {
                func_decl *f, *g;
                if (!is_axiom(goal->form(i), f, g)) continue;
                TRACE("injectivity", tout << "Marking " << f->get_name() << " as injective" << std::endl;);
                inj_map.insert(f, g);
                // TODO: Record that g is f's pseudoinverse
            }
        }

        void updt_params(params_ref const & p) {}
    };

    struct rewriter_eq_cfg : public default_rewriter_cfg {
        ast_manager              & m_manager;
        InjHelper                & inj_map;
//        expr_ref_vector            m_out;
//        sort_ref_vector            m_bindings;

        ast_manager & m() const { return m_manager; }

        rewriter_eq_cfg(ast_manager & m, InjHelper & map, params_ref const & p) : m_manager(m), inj_map(map) {
        }

        ~rewriter_eq_cfg() {
        }

        void cleanup_buffers() {
//            m_out.finalize();
        }

        void reset() {
        }

        br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
            if(num != 2)
                return BR_FAILED;

            if (!m().is_eq(f))
                return BR_FAILED;

            // We are rewriting (= a b)
            if (!is_app(args[0]) || !is_app(args[1]))
                return BR_FAILED;

            const app* const a = to_app(args[0]);
            const app* const b = to_app(args[1]);

            // a and b are applications of the same function
            if (a->get_decl() != b->get_decl())
                return BR_FAILED;

            // Maybe TODO: Generalize to multi-parameter functions ?
            if (a->get_num_args() != 1 || b->get_num_args() != 1)
                return BR_FAILED;

            if (!inj_map.contains(a->get_decl()))
                return BR_FAILED;

            SASSERT(a->get_arg(0)->get_sort() == b->get_arg(0)->get_sort());
            TRACE("injectivity", tout << "Rewriting (= " << mk_ismt2_pp(args[0], m()) <<
                                              " " << mk_ismt2_pp(args[1], m()) << ")" << std::endl;);
            result = m().mk_eq(a->get_arg(0), b->get_arg(0));
            result_pr = nullptr;
            return BR_DONE;
        }

    };

    struct rewriter_eq : public rewriter_tpl<rewriter_eq_cfg> {
        rewriter_eq_cfg m_cfg;
        rewriter_eq(ast_manager & m, InjHelper & map, params_ref const & p) :
            rewriter_tpl<rewriter_eq_cfg>(m, m.proofs_enabled(), m_cfg),
            m_cfg(m, map, p) {
        }
    };

    struct rewriter_inverse { };

    finder *           m_finder;
    rewriter_eq *      m_eq;
    InjHelper *        m_map;
//    rewriter_inverse * m_inverse;

    params_ref         m_params;
    ast_manager &      m_manager;

public:
    injectivity_tactic(ast_manager & m, params_ref const & p):
        m_params(p),
        m_manager(m) {
        TRACE("injectivity", tout << "constructed new tactic" << std::endl;);
        m_map = alloc(InjHelper, m);
        m_finder = alloc(finder, m, *m_map, p);
        m_eq = alloc(rewriter_eq, m, *m_map, p);
    }

    tactic * translate(ast_manager & m) override {
        return alloc(injectivity_tactic, m, m_params);
    }

    ~injectivity_tactic() override {
        dealloc(m_finder);
        dealloc(m_eq);
        dealloc(m_map);
    }

    void updt_params(params_ref const & p) override {
        m_params = p;
        m_finder->updt_params(p);
    }

    void collect_param_descrs(param_descrs & r) override {
        insert_max_memory(r);
        insert_produce_models(r);
    }

    void operator()(goal_ref const & g,
                    goal_ref_buffer & result) override {
        (*m_finder)(g, result);

        for (unsigned i = 0; i < g->size(); ++i) {
            expr*     curr = g->form(i);
            expr_ref  rw(m_manager);
            proof_ref pr(m_manager);
            (*m_eq)(curr, rw, pr);
            g->update(i, rw, pr, g->dep(i));
        }
        result.push_back(g.get());
    }

    void cleanup() override {
        InjHelper * m = alloc(InjHelper, m_manager);
        finder * f = alloc(finder, m_manager, *m, m_params);
        rewriter_eq * r = alloc(rewriter_eq, m_manager, *m, m_params);
        std::swap(m, m_map), std::swap(f, m_finder), std::swap(r, m_eq);
        dealloc(m), dealloc(f), dealloc(r);
    }


};

tactic * mk_injectivity_tactic(ast_manager & m, params_ref const & p) {
    return alloc(injectivity_tactic, m, p);
}
