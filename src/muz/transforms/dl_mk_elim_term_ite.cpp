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
#include "tactic/tactic.h"
#include "tactic/core/elim_term_ite_tactic.h"

namespace datalog {
    mk_elim_term_ite::mk_elim_term_ite(context & ctx, unsigned priority) :
        rule_transformer::plugin(priority, false),
        m_ctx(ctx),
        m(ctx.get_manager()),
        rm(ctx.get_rule_manager()) {}

    mk_elim_term_ite::~mk_elim_term_ite() {}

    bool mk_elim_term_ite::elim(rule &r, rule_set &new_rules){
        unsigned utsz = r.get_uninterpreted_tail_size();
        unsigned tsz = r.get_tail_size();
        expr_ref_vector new_conjs(m);
        expr_ref tmp(m);

        bool change = false;

        for (unsigned i = utsz; i < tsz; ++i)
            new_conjs.push_back(r.get_tail(i));
        flatten_and(new_conjs);

        expr_ref fml1(m), fml2(m), old_body(m), body(m), head(m);

        // blast ite
        old_body = m.mk_and(new_conjs.size(), new_conjs.c_ptr());
        body = old_body;
        blast_term_ite(body, 2);
        change = old_body != body;
        if (!change) {
            new_rules.add_rule(&r);
            return false;
        }
        new_conjs.reset();

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
            }
        }


        expr_ref_vector conjs(m);
        for (unsigned i = 0; i < utsz; ++i)
            conjs.push_back(r.get_tail(i));
        conjs.append(new_conjs);

        body = mk_and(conjs);
        head = r.get_head();

        fml2 = m.mk_implies(body, head);
        proof_ref p(m);
        rm.mk_rule(fml2, p, new_rules, r.name());

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
