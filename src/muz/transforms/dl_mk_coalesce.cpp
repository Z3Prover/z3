/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    dl_mk_coalesce.cpp

Abstract:

    Coalesce rules with shared bodies.

Author:

    Nikolaj Bjorner (nbjorner) 2012-10-15

Revision History:


Notes:

 Implements proof rule of the form:

    a(x) & q(x) -> p(x),       b(y) & q(y) -> p(y)
    ----------------------------------------------
           (a(z) \/ b(z)) & q(z) -> p(z)

 
--*/
#include "muz/transforms/dl_mk_coalesce.h"
#include "ast/rewriter/bool_rewriter.h"

namespace datalog {

    mk_coalesce::mk_coalesce(context& ctx):
        rule_transformer::plugin(50, false),
        m_ctx(ctx),
        m(ctx.get_manager()),
        rm(ctx.get_rule_manager()),
        m_sub1(m),
        m_sub2(m),
        m_idx(0)
    {}

    void mk_coalesce::mk_pred(app_ref& pred, app* p1, app* p2) {
        SASSERT(p1->get_decl() == p2->get_decl());
        unsigned sz = p1->get_num_args();
        expr_ref_vector args(m);
        for (unsigned i = 0; i < sz; ++i) {
            expr* a = p1->get_arg(i);
            expr* b = p2->get_arg(i);
            SASSERT(m.get_sort(a) == m.get_sort(b));
            m_sub1.push_back(a);
            m_sub2.push_back(b);
            args.push_back(m.mk_var(m_idx++, m.get_sort(a)));
        }
        pred = m.mk_app(p1->get_decl(), args.size(), args.c_ptr());
    }

    void mk_coalesce::extract_conjs(expr_ref_vector const& sub, rule const& rl, expr_ref& result) {
        obj_map<expr, unsigned> indices;
        bool_rewriter bwr(m);
        rule_ref r(const_cast<rule*>(&rl), rm);
        ptr_vector<sort> sorts;
        expr_ref_vector revsub(m), conjs(m);
        rl.get_vars(m, sorts);
        revsub.resize(sorts.size());  
        svector<bool> valid(sorts.size(), true);
        for (unsigned i = 0; i < sub.size(); ++i) {
            expr* e = sub[i];
            sort* s = m.get_sort(e);
            expr_ref w(m.mk_var(i, s), m);
            if (is_var(e)) {
                unsigned v = to_var(e)->get_idx();
                SASSERT(v < valid.size());
                if (sorts[v]) {
                    SASSERT(s == sorts[v]);
                    if (valid[v]) {
                        revsub[v] = w;
                        valid[v] = false;
                    }
                    else {
                        SASSERT(revsub[v].get());
                        SASSERT(m.get_sort(revsub[v].get()) == s);
                        conjs.push_back(m.mk_eq(revsub[v].get(), w));    
                    }
                }
            }
            else {
                SASSERT(m.is_value(e));
                SASSERT(m.get_sort(e) == m.get_sort(w));
                conjs.push_back(m.mk_eq(e, w));
            }
        }
        for (unsigned i = 0; i < sorts.size(); ++i) {
            if (valid[i] && sorts[i] && !revsub[i].get()) {
                revsub[i] = m.mk_var(m_idx++, sorts[i]);
            }
        }
        var_subst vs(m, false);
        for (unsigned i = r->get_uninterpreted_tail_size(); i < r->get_tail_size(); ++i) {
            result = vs(r->get_tail(i), revsub.size(), revsub.c_ptr());
            conjs.push_back(result);
        }
        bwr.mk_and(conjs.size(), conjs.c_ptr(), result);
    }

    void mk_coalesce::merge_rules(rule_ref& tgt, rule const& src) {
        SASSERT(same_body(*tgt.get(), src));
        m_sub1.reset();
        m_sub2.reset();
        m_idx = 0;
        app_ref pred(m), head(m);
        expr_ref fml1(m), fml2(m), fml(m);
        app_ref_vector tail(m);
        ptr_vector<sort> sorts1, sorts2;
        expr_ref_vector conjs1(m), conjs(m);
        rule_ref res(rm);
        bool_rewriter bwr(m);
        svector<bool> is_neg;
        tgt->get_vars(m, sorts1);
        src.get_vars(m, sorts2);

        mk_pred(head, src.get_head(), tgt->get_head()); 
        for (unsigned i = 0; i < src.get_uninterpreted_tail_size(); ++i) {
            mk_pred(pred, src.get_tail(i), tgt->get_tail(i));
            tail.push_back(pred);
            is_neg.push_back(src.is_neg_tail(i));
        }           
        extract_conjs(m_sub1, src, fml1);
        extract_conjs(m_sub2, *tgt.get(),  fml2);
        bwr.mk_or(fml1, fml2, fml);
        SASSERT(is_app(fml));
        tail.push_back(to_app(fml));
        is_neg.push_back(false);
        res = rm.mk(head, tail.size(), tail.c_ptr(), is_neg.c_ptr(), tgt->name());
        if (m_ctx.generate_proof_trace()) {
            rm.to_formula(src, fml1);
            rm.to_formula(*tgt.get(),fml2);
            rm.to_formula(*res.get(),fml);
#if 0
            sort* ps = m.mk_proof_sort();
            sort* domain[3] = { ps, ps, m.mk_bool_sort() };
            func_decl* merge = m.mk_func_decl(symbol("merge-clauses"), 3, domain, ps);  // TBD: ad-hoc proof rule
            expr* args[3] = { m.mk_asserted(fml1), m.mk_asserted(fml2), fml };
            // ...m_pc->insert(m.mk_app(merge, 3, args));
#else
            svector<std::pair<unsigned, unsigned> > pos;
            vector<expr_ref_vector> substs;
            proof* p = src.get_proof();
            p = m.mk_hyper_resolve(1, &p, fml, pos, substs);
            res->set_proof(m, p);
#endif
        }
        tgt = res;
    }

    bool mk_coalesce::same_body(rule const& r1, rule const& r2) const {
        SASSERT(r1.get_decl() == r2.get_decl());
        unsigned sz = r1.get_uninterpreted_tail_size();
        if (sz != r2.get_uninterpreted_tail_size()) {
            return false;
        }
        for (unsigned i = 0; i < sz; ++i) {
            if (r1.get_decl(i) != r2.get_decl(i)) {
                return false;
            }
            if (r1.is_neg_tail(i) != r2.is_neg_tail(i)) {
                return false;
            }
        }
        return true;
    }    
        
    rule_set * mk_coalesce::operator()(rule_set const & source) {
        rule_set* rules = alloc(rule_set, m_ctx);
        rules->inherit_predicates(source);
        rule_set::decl2rules::iterator it = source.begin_grouped_rules(), end = source.end_grouped_rules();
        for (; it != end; ++it) {
            rule_ref_vector d_rules(rm);
            d_rules.append(it->m_value->size(), it->m_value->c_ptr());
            for (unsigned i = 0; i < d_rules.size(); ++i) {
                rule_ref r1(d_rules[i].get(), rm);
                for (unsigned j = i + 1; j < d_rules.size(); ++j) {
                    if (same_body(*r1.get(), *d_rules[j].get())) {
                        merge_rules(r1, *d_rules[j].get());
                        d_rules[j] = d_rules.back();
                        d_rules.pop_back();
                        --j;
                    }
                }
                rules->add_rule(r1.get());
            }
        }
        return rules;
    }

};


