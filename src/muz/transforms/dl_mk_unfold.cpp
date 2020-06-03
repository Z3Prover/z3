/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    dl_mk_unfold.cpp

Abstract:

    Unfold rules once, return the unfolded set of rules.

Author:

    Nikolaj Bjorner (nbjorner) 2012-10-15

Revision History:

--*/
#include "muz/transforms/dl_mk_unfold.h"

namespace datalog {

    mk_unfold::mk_unfold(context& ctx):
        rule_transformer::plugin(100, false),
        m_ctx(ctx),
        m(ctx.get_manager()),
        rm(ctx.get_rule_manager()),
        m_unify(ctx)
    {}

    void mk_unfold::expand_tail(rule& r, unsigned tail_idx, rule_set const& src, rule_set& dst) {
        SASSERT(tail_idx <= r.get_uninterpreted_tail_size());
        if (tail_idx == r.get_uninterpreted_tail_size()) {
            dst.add_rule(&r);
        }
        else {
            func_decl* p = r.get_decl(tail_idx);
            rule_vector const& p_rules = src.get_predicate_rules(p);
            rule_ref new_rule(rm);
            for (unsigned i = 0; i < p_rules.size(); ++i) {
                rule const& r2 = *p_rules[i];
                if (m_unify.unify_rules(r, tail_idx, r2) &&
                    m_unify.apply(r, tail_idx, r2, new_rule)) {
                    expr_ref_vector s1 = m_unify.get_rule_subst(r, true);
                    expr_ref_vector s2 = m_unify.get_rule_subst(r2, false);                    
                    resolve_rule(rm, r, r2, tail_idx, s1, s2, *new_rule.get());
                    expand_tail(*new_rule.get(), tail_idx+r2.get_uninterpreted_tail_size(), src, dst);
                }
            }
        }
    }
        
    rule_set * mk_unfold::operator()(rule_set const & source) {
        scoped_ptr<rule_set> rules = alloc(rule_set, m_ctx);
        for (rule* r : source) {
            expand_tail(*r, 0, source, *rules);
        }
        rules->inherit_predicates(source);
        return rules.detach();
    }

};

