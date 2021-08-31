/*++

Module Name:

    dl_mk_array_eq_rewrite.h

Abstract:
    Selects a representative for array equivalence classes.

Author:

    Julien Braine

Revision History:

--*/

#include "ast/pattern/pattern_inference.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "ast/expr_abstract.h"
#include "muz/base/dl_context.h"
#include "muz/base/dl_context.h"
#include "muz/base/fp_params.hpp"
#include "muz/transforms/dl_mk_array_eq_rewrite.h"
#include "ast/rewriter/factor_equivs.h"

namespace datalog {

    mk_array_eq_rewrite::mk_array_eq_rewrite(
        context & ctx, unsigned priority):
        plugin(priority),
        m(ctx.get_manager()),
        m_ctx(ctx),
        m_a(m)
    {
    }

    rule_set * mk_array_eq_rewrite::operator()(rule_set const & source)
    {
        m_src_set = &source;
        scoped_ptr<rule_set> result = alloc(rule_set, m_ctx);
        result->inherit_predicates(source);
        m_dst = result.get();
        m_src_manager = &source.get_rule_manager();
        for (rule * rp : source) {
            instantiate_rule(*rp, *result);
        }
        return result.detach();
    }

    void mk_array_eq_rewrite::instantiate_rule(const rule& r, rule_set & dest)
    {
        //Reset everything
        m_cnt = m_src_manager->get_counter().get_max_rule_var(r)+1;


        expr_ref_vector new_tail(m);
        unsigned nb_predicates = r.get_uninterpreted_tail_size();
        unsigned tail_size = r.get_tail_size();
        for (unsigned i = 0; i < nb_predicates; i++) {
            new_tail.push_back(r.get_tail(i));
        }

        expr_equiv_class array_eq_classes(m);
        for(unsigned i = nb_predicates; i < tail_size; i++) {
            expr* cond = r.get_tail(i);
            expr* e1, *e2;
            if (m.is_eq(cond, e1, e2) && m_a.is_array(e1->get_sort())) {
                array_eq_classes.merge(e1, e2);
            }
            else {
                new_tail.push_back(cond);
            }
        }

        for (auto c_eq : array_eq_classes) {
            expr* representative = *(c_eq.begin());
            for (expr * v : c_eq) {
                if (!is_var(v)) {
                    representative = v;
                    break;
                }
            }
            for (expr * v : c_eq) {
                for (unsigned i = 0; i < new_tail.size(); i++)
                    new_tail[i] = replace(new_tail[i].get(), representative, v);
            }
            for (expr * v : c_eq) {
                new_tail.push_back(m.mk_eq(v, representative));
            }
        }
        params_ref select_over_store;
        select_over_store.set_bool("expand_select_store", true);
        th_rewriter t(m, select_over_store);
        expr_ref_vector res_conjs(m);
        for (expr* e : new_tail) {
            expr_ref tmp(m);
            t(e, tmp);
            res_conjs.push_back(tmp);
        }
        proof_ref pr(m);
        m_src_manager->mk_rule(m.mk_implies(m.mk_and(res_conjs.size(), res_conjs.data()), r.get_head()), pr, dest, r.name());
    }

    // NSB Code review: use substitution facility, such as expr_safe_replace or expr_replacer.
    expr* mk_array_eq_rewrite::replace(expr* e, expr* new_val, expr* old_val)
    {
        if (e == old_val)
            return new_val;
        else if (!is_app(e)) {
            return e;
        }
        app* f = to_app(e);
        ptr_vector<expr> n_args;
        for (expr * arg : *f) {
            n_args.push_back(replace(arg, new_val, old_val));
        }
        return m.mk_app(f->get_decl(), n_args.size(), n_args.data());
    }

}
