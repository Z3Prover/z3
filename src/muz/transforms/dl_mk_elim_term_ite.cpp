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

#include "muz/transforms/dl_mk_elim_term_ite.h"
#include "tactic/core/blast_term_ite_tactic.h"
#include "ast/ast_util.h"
#include "ast/expr_abstract.h"
#include "tactic/tactic.h"
#include "tactic/core/elim_term_ite_tactic.h"

namespace {
    struct uninterp_const_collector {
        app_ref_vector &m_consts;
        uninterp_const_collector(app_ref_vector &v) : m_consts(v) {}
        void operator()(var *v) {}
        void operator()(quantifier *n) {}
        void operator()(expr *a){}
        void operator()(app *a){
            if (is_uninterp_const(a)) {m_consts.push_back(a);};
        }
    };

    void collect_uninterp_consts(expr *e, app_ref_vector &v) {
        uninterp_const_collector c(v);
        quick_for_each_expr(c, e);
    }

    struct term_ite_proc {
        class found{};
        ast_manager &m;
        term_ite_proc(ast_manager &m) : m(m) {}
        void operator()(var *v) {}
        void operator()(quantifier *n) {}
        void operator()(expr *a){}
        void operator()(app *a){
            if (m.is_term_ite(a)) throw found();
        }
    };

    bool has_term_ite(expr *e, ast_manager& m) {
        term_ite_proc f(m);
        try {
            quick_for_each_expr(f, e);
        } catch (term_ite_proc::found) {
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

    expr_ref mk_elim_term_ite::ground(expr_ref &e) {
        expr_free_vars fv;
        fv(e);
        if (m_ground.size() < fv.size())
            m_ground.resize(fv.size());
        for (unsigned i = 0, sz = fv.size(); i < sz; ++i) {
            if (fv[i] && !m_ground.get(i))
                m_ground[i] = m.mk_fresh_const("c", fv[i]);
        }

        var_subst vsub(m, false);
        return vsub(e, m_ground.size(), m_ground.c_ptr());
    }

    bool mk_elim_term_ite::elim(rule &r, rule_set &new_rules){
        m_ground.reset();

        th_rewriter rw(m);
        unsigned utsz = r.get_uninterpreted_tail_size();
        unsigned tsz = r.get_tail_size();
        expr_ref_vector new_conjs(m);
        expr_ref tmp(m);


        for (unsigned i = utsz; i < tsz; ++i)
            new_conjs.push_back(r.get_tail(i));
        flatten_and(new_conjs);

        expr_ref fml1(m), fml2(m), body(m), head(m);

        // blast ite
        body = m.mk_and(new_conjs.size(), new_conjs.c_ptr());
        if (!has_term_ite(body)) {
            TRACE("dl_term_ite", tout << "No term-ite, skipping a rule\n";);
            new_rules.add_rule(&r);
            return false;
        }
        new_conjs.reset();
        blast_term_ite(body, m_ctx.blast_term_ite_inflation());
        // simplify body
        rw(body);

        if (!has_term_ite(body)) {
            head = r.get_head();

            fml2 = m.mk_implies(body, head);
            proof_ref p(m);
            rm.mk_rule(fml2, p, new_rules, r.name());
            rm.mk_rule_rewrite_proof(r, *new_rules.last());
            TRACE("dl_term_ite", tout << "No term-ite after blast_term_ite\n";);
            return true;
        }

        TRACE("dl_term_ite",
              tout << "Rule has term-ite after blasting, starting elimination\n";);
        body = ground(body);
        // elim ite
        tactic_ref elim_term_ite = mk_elim_term_ite_tactic(m);
        goal_ref goal = alloc(class goal, m);
        goal_ref_buffer result;
        flatten_and(body, new_conjs);
        for (auto *e : new_conjs) {
            goal->assert_expr(e);
        }
        unsigned sz = goal->num_exprs();
        (*elim_term_ite)(goal, result);
        if (result.size() == 1) {
            goal_ref new_goal = result[0];
            if (new_goal->num_exprs() != sz) {
                new_conjs.reset();
                new_goal->get_formulas(new_conjs);
                flatten_and(new_conjs);
            }
        }

        expr_ref_vector conjs(m);
        for (unsigned i = 0; i < utsz; ++i) {
            tmp = r.get_tail(i);
            tmp = ground(tmp);
            conjs.push_back(tmp);
        }
        conjs.append(new_conjs);

        body = mk_and(conjs);
        rw(body);

        head = r.get_head();
        head = ground(head);

        fml2 = m.mk_implies(body, head);
        SASSERT(!has_term_ite(fml2));
        app_ref_vector consts(m);
        collect_uninterp_consts(fml2, consts);
        fml2 = mk_forall(m, consts.size(), consts.c_ptr(), fml2);
        proof_ref p(m);
        rm.mk_rule(fml2, p, new_rules, r.name());
        rm.mk_rule_rewrite_proof(r, *new_rules.last());
        TRACE("dl_term_ite", tout << "New rule: " << fml2 << "\n";);

        return true;
    }



    rule_set * mk_elim_term_ite::operator()(rule_set const & source) {
        if (!m_ctx.elim_term_ite ()) {return nullptr;}

        rule_set* rules = alloc(rule_set, m_ctx);
        rules->inherit_predicates(source);
        bool change = false;
        for (auto *rule : source) {
            if (m_ctx.canceled()) {
                change = false;
                break;
            }
            change |= elim(*rule, *rules);
        }
        if (!change) {
            dealloc(rules);
            rules = nullptr;
        }
        return rules;
    }


}
