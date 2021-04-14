/*++
Copyright (c) 2018 Arie Gurfinkel

Module Name:

    dl_mk_elim_term_ite.h

Abstract:

   Remove term-ite expressions from the rules

Author:

    Arie Gurfinkel (agurfinkel)

Revision History:

--*/

#include "ast/ast_util.h"
#include "ast/expr_abstract.h"
#include "tactic/core/blast_term_ite_tactic.h"
#include "tactic/tactic.h"
#include "tactic/core/elim_term_ite_tactic.h"
#include "muz/transforms/dl_mk_elim_term_ite.h"

namespace {
    /**
     * collect uninterpreted constants that are contained in ground
     */
    struct uninterp_const_collector {
        app_ref_vector&         m_consts;
        expr_ref_vector const&  m_ground;
        uninterp_const_collector(app_ref_vector &v, expr_ref_vector const& g) : m_consts(v), m_ground(g) {}
        void operator()(var *v) {}
        void operator()(quantifier *n) {}
        void operator()(expr *a){}
        void operator()(app *a){
            if (is_uninterp_const(a) && m_ground.contains(a)) 
                m_consts.push_back(a);
        }
    };

    void collect_uninterp_consts(expr *e, app_ref_vector &v, expr_ref_vector const& g) {
        uninterp_const_collector c(v, g);
        quick_for_each_expr(c, e);
    }

    struct term_ite_proc {
        class found{};
        ast_manager &m;
        term_ite_proc(ast_manager &m) : m(m) {}
        void operator()(var *v) {}
        void operator()(quantifier *n) {}
        void operator()(expr *a) {
            if (m.is_term_ite(a)) 
                throw found();
        }
    };

    bool has_term_ite(expr *e, ast_manager& m) {
        term_ite_proc f(m);
        try {
            quick_for_each_expr(f, e);
        } 
        catch (const term_ite_proc::found &) {
            return true;
        }
        return false;
    }

    bool has_term_ite(expr_ref &e) { return has_term_ite(e, e.m());}
}

namespace datalog {
    mk_elim_term_ite::mk_elim_term_ite(context & ctx, unsigned priority) :
        rule_transformer::plugin(priority, false),
        m_ctx(ctx),
        m(ctx.get_manager()),
        rm(ctx.get_rule_manager()),
        m_ground(m) {}

    mk_elim_term_ite::~mk_elim_term_ite() {}

    /**
       \brief map free variables in e to ground, fresh, constants
       m_ground is reset on every new rule so it is safe to assume
       that the sorts in m_ground are consistent.       
     */
    expr_ref mk_elim_term_ite::ground(expr* e) {
        expr_free_vars fv(e);
        m_ground.reserve(fv.size());
        for (unsigned i = 0, sz = fv.size(); i < sz; ++i) {
            if (!fv[i])
                continue;
            if (!m_ground.get(i))
                m_ground[i] = m.mk_fresh_const("c", fv[i]);
            SASSERT(m_ground[i]->get_sort() == fv[i]);
        }
        var_subst vsub(m, false);
        return vsub(e, m_ground);
    }

    bool mk_elim_term_ite::elim(rule &r, rule_set &new_rules){
        m_ground.reset();

        th_rewriter rw(m);
        unsigned utsz = r.get_uninterpreted_tail_size();
        unsigned tsz = r.get_tail_size();
        expr_ref_vector new_conjs(m);

        for (unsigned i = utsz; i < tsz; ++i)
            new_conjs.push_back(r.get_tail(i));
        flatten_and(new_conjs);

        expr_ref fml1(m), fml2(m), body(m);

        // blast ite
        body = mk_and(new_conjs);
        if (!has_term_ite(body)) {
            new_rules.add_rule(&r);
            return false;
        }
        new_conjs.reset();
        blast_term_ite(body, m_ctx.blast_term_ite_inflation());
        // simplify body
        rw(body);

        if (!has_term_ite(body)) {
            app_ref_vector tail(m);
            flatten_and(body, new_conjs);
            for (unsigned i = 0; i < utsz; ++i) {
                tail.push_back(r.get_tail(i));
            }
            for (expr* e : new_conjs) {
                tail.push_back(rm.ensure_app(e));
            }
            rule_ref new_rule(rm.mk(r.get_head(), tail.size(), tail.data(), nullptr, r.name(), false), rm);           
            rm.mk_rule_rewrite_proof(r, *new_rule.get());
            new_rules.add_rule(new_rule);
            TRACE("dl", tout << "No term-ite after blast_term_ite\n";);
            return true;
        }

        TRACE("dl", tout << "Rule has term-ite after blasting, starting elimination\n";);
        body = ground(body);
        // elim ite
        tactic_ref elim_term_ite = mk_elim_term_ite_tactic(m);
        goal_ref g = alloc(goal, m);
        goal_ref_buffer result;
        flatten_and(body, new_conjs);
        for (auto *e : new_conjs) {
            g->assert_expr(e);
        }
        unsigned sz = g->num_exprs();
        (*elim_term_ite)(g, result);
        if (result.size() == 1) {
            // NSB code review: fragile test for effect
            goal_ref new_goal = result[0];
            if (new_goal->num_exprs() != sz) {
                new_conjs.reset();
                new_goal->get_formulas(new_conjs);
                flatten_and(new_conjs);
            }
        }

        for (unsigned i = 0; i < utsz; ++i) {
            new_conjs.push_back(ground(r.get_tail(i)));
        }

        body = mk_and(new_conjs);
        rw(body);

        fml2 = m.mk_implies(body, ground(r.get_head()));
        CTRACE("dl", has_term_ite(fml2), tout << "Rule has term-ite after elimination. Giving up\n";);
        if (has_term_ite(fml2))
            return false;
        app_ref_vector consts(m);
        collect_uninterp_consts(fml2, consts, m_ground);
        
        fml2 = mk_forall(m, consts.size(), consts.data(), fml2);
        proof_ref p(m);
        rm.mk_rule(fml2, p, new_rules, r.name()); 

        // NSB code review: breaks abstraction barrier: mk_rule could convert a single formula
        // into multiple rules
        rm.mk_rule_rewrite_proof(r, *new_rules.last());
        TRACE("dl", tout << "New rule: " << fml2 << "\n";);
        return true;
    }



    rule_set * mk_elim_term_ite::operator()(rule_set const & source) {
        if (!m_ctx.elim_term_ite ()) 
            return nullptr;

        scoped_ptr<rule_set> rules = alloc(rule_set, m_ctx);
        rules->inherit_predicates(source);
        bool change = false;
        for (auto *rule : source) {
            if (m_ctx.canceled()) {
                return nullptr;
            }
            change |= elim(*rule, *rules);
        }
        if (!change) {
            rules = nullptr;
        }
        return rules.detach();
    }


}
