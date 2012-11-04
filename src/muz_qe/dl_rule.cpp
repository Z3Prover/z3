/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_rule.cpp

Abstract:

    <abstract>

Author:

    Krystof Hoder (t-khoder) 2011-10-19.

Revision History:

    Nikolaj Bjorner (nbjorner) 2012-10-31.
      Check for enabledness of fix_unbound_vars inside call.
      This function gets called from many rule tansformers.

--*/

#include<algorithm>
#include<sstream>

#include"ast_pp.h"
#include"dl_context.h"
#include"map.h"
#include"recurse_expr_def.h"
#include"dl_rule.h"
#include"qe.h"
#include"for_each_expr.h"
#include"used_vars.h"
#include"var_subst.h"
#include"expr_abstract.h"
#include"rewriter_def.h"
#include"th_rewriter.h"
#include"ast_smt2_pp.h"
#include"used_symbols.h"
#include"quant_hoist.h"
#include"expr_replacer.h"
#include"bool_rewriter.h"
#include"qe_lite.h"

namespace datalog {

    rule_manager::rule_manager(context& ctx) 
        : m(ctx.get_manager()),
        m_ctx(ctx),
        m_refs(ctx.get_manager()) {}

    bool rule_manager::is_predicate(func_decl * f) const {
        return m_ctx.is_predicate(f);
    }

    void rule_manager::inc_ref(rule * r) {
        if (r) {
            SASSERT(r->m_ref_cnt!=UINT_MAX);
            r->m_ref_cnt++;
        }
    }

    void rule_manager::dec_ref(rule * r) {
        if (r) {
            SASSERT(r->m_ref_cnt>0);
            r->m_ref_cnt--;
            if (r->m_ref_cnt==0) {
                r->deallocate(m);
            }
        }
    }

    class remove_label_cfg : public default_rewriter_cfg {
        family_id m_label_fid;
    public:        
        remove_label_cfg(ast_manager& m): m_label_fid(m.get_family_id("label")) {}
        virtual ~remove_label_cfg() {}

        br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, 
            proof_ref & result_pr)
        {
            if (is_decl_of(f, m_label_fid, OP_LABEL)) {
                SASSERT(num == 1);
                result = args[0];
                return BR_DONE;
            }
            return BR_FAILED;
        }
    };

    void rule_manager::remove_labels(expr_ref& fml) {
        expr_ref tmp(m);
        remove_label_cfg r_cfg(m);
        rewriter_tpl<remove_label_cfg> rwr(m, false, r_cfg);
        rwr(fml, tmp);
        fml = tmp;
    }


    void rule_manager::mk_rule(expr* fml, rule_ref_vector& rules, symbol const& name) {              
        expr_ref fml1(m);
        m_memoize_disj.reset();
        m_refs.reset();
        bind_variables(fml, true, fml1);
        remove_labels(fml1);
        mk_rule_core(fml1, rules, name);
    }

    // 
    // Hoist quantifier from rule (universal) or query (existential)
    // 
    unsigned rule_manager::hoist_quantifier(bool is_forall, expr_ref& fml, svector<symbol>* names) {   

        unsigned index = var_counter().get_next_var(fml);
        while (is_quantifier(fml) && (is_forall == to_quantifier(fml)->is_forall())) {
            quantifier* q = to_quantifier(fml);
            index += q->get_num_decls();
            if (names) {
                names->append(q->get_num_decls(), q->get_decl_names());
            }
            fml = q->get_expr();
        }
        if (!has_quantifiers(fml)) {
            return index;
        }
        app_ref_vector vars(m);
        quantifier_hoister qh(m);
        qh.pull_quantifier(is_forall, fml, vars);
        if (vars.empty()) {
            return index;
        }
        // replace vars by de-bruijn indices
        expr_substitution sub(m);
        for (unsigned i = 0; i < vars.size(); ++i) {
            app* v = vars[i].get();
            if (names) {
                names->push_back(v->get_decl()->get_name());
            }                
            sub.insert(v, m.mk_var(index++,m.get_sort(v)));
        }
        scoped_ptr<expr_replacer> rep = mk_default_expr_replacer(m); 
        rep->set_substitution(&sub);
        (*rep)(fml);
        return index;
    }

    void rule_manager::mk_rule_core(expr* _fml, rule_ref_vector& rules, symbol const& name) {
        app_ref_vector body(m);
        app_ref head(m);
        expr_ref e(m), fml(_fml, m);
        svector<bool> is_negated;
        TRACE("dl_rule", tout << mk_pp(fml, m) << "\n";);
        unsigned index = hoist_quantifier(true, fml, 0); 
        check_app(fml);
        head = to_app(fml);
        
        while (m.is_implies(head)) {
            e = head->get_arg(0);
            th_rewriter th_rwr(m);
            th_rwr(e);
            body.push_back(ensure_app(e));
            e = to_app(head)->get_arg(1);
            check_app(e);
            head = to_app(e.get());
        }
        symbol head_name = (name == symbol::null)?head->get_decl()->get_name():name;
        flatten_body(body);
        if (body.size() == 1 && m.is_or(body[0].get()) && contains_predicate(body[0].get())) {
            app* _or = to_app(body[0].get());
            for (unsigned i = 0; i < _or->get_num_args(); ++i) {
                e = m.mk_implies(_or->get_arg(i), head);
                mk_rule_core(e, rules, head_name);
            } 
            return;
        }

        eliminate_disjunctions(body, rules, head_name);
        eliminate_quantifier_body(body, rules, head_name);
        hoist_compound(index, head, body);
        unsigned sz = body.size();
        for (unsigned i = 0; i < sz; ++i) {
            app_ref b(body[i].get(), m);
            hoist_compound(index, b, body);
            body[i] = b;
        }
        TRACE("dl_rule",
              tout << mk_pp(head, m) << " :- ";
              for (unsigned i = 0; i < body.size(); ++i) {
                  tout << mk_pp(body[i].get(), m) << " ";
              }
              tout << "\n";);

        for (unsigned i = 0; i < body.size(); ++i) {
            expr* e = body[i].get(), *e1;
            if (m.is_not(e, e1) && is_predicate(e1)) {
                check_app(e1);
                body[i] = to_app(e1);
                is_negated.push_back(true);
            }
            else {
                is_negated.push_back(false);
            }
        }
        check_valid_rule(head, body.size(), body.c_ptr());

        rules.push_back(mk(head.get(), body.size(), body.c_ptr(), is_negated.c_ptr(), name));
        
        if (m_ctx.fix_unbound_vars()) {
            unsigned rule_cnt = rules.size();
            for (unsigned i=0; i<rule_cnt; ++i) {
                rule_ref r(rules[i].get(), *this);
                fix_unbound_vars(r, true);
                if (r.get()!=rules[i].get()) {
                    rules[i] = r;
                }
            }
        }
    }

    void rule_manager::mk_query(expr* query, func_decl_ref& qpred, rule_ref_vector& query_rules, rule_ref& query_rule) {
        ptr_vector<sort> vars;
        svector<symbol> names;
        app_ref_vector body(m);
        expr_ref q(m);
        
        // Add implicit variables.
        // Remove existential prefix.
        bind_variables(query, false, q);
        hoist_quantifier(false, q, &names);
        // retrieve free variables.
        get_free_vars(q, vars);
        if (vars.contains(static_cast<sort*>(0))) {
            var_subst sub(m, false);  
            expr_ref_vector args(m);
            // [s0, 0, s2, ..]
            // [0 -> 0, 1 -> x, 2 -> 1, ..]
            for (unsigned i = 0, j = 0; i < vars.size(); ++i) {
                if (vars[i]) {
                    args.push_back(m.mk_var(j, vars[i]));
                    ++j;
                }
                else {
                    args.push_back(m.mk_var(0, m.mk_bool_sort()));
                }
            }
            sub(q, args.size(), args.c_ptr(), q);
            vars.reset();
            get_free_vars(q, vars);
        }
        SASSERT(!vars.contains(static_cast<sort*>(0)) && "Unused variables have been eliminated");


        // flatten body and extract query predicate.
        if (!is_app(q)) {
            throw default_exception("Query body is not well-formed");
        }
        body.push_back(to_app(q));
        flatten_body(body);
        func_decl* body_pred = 0;
        for (unsigned i = 0; i < body.size(); i++) {
            if (is_uninterp(body[i].get())) {
                body_pred = body[i]->get_decl();
                break;
            }
        }

        // we want outermost declared variable first to 
        // follow order of quantified variables so we reverse vars.
        while (vars.size() > names.size()) {
            names.push_back(symbol(names.size()));
        }
        vars.reverse();
        names.reverse();
        qpred = m_ctx.mk_fresh_head_predicate(symbol("query"), symbol(), vars.size(), vars.c_ptr(), body_pred);

        expr_ref_vector qhead_args(m);
        for (unsigned i = 0; i < vars.size(); i++) {
            qhead_args.push_back(m.mk_var(vars.size()-i-1, vars[i]));
        }
        app_ref qhead(m.mk_app(qpred, qhead_args.c_ptr()), m);
        app_ref impl(m.mk_implies(q, qhead), m);
        expr_ref rule_expr(impl.get(), m);
        if (!vars.empty()) {
            rule_expr = m.mk_forall(vars.size(), vars.c_ptr(), names.c_ptr(), impl);
        }

        mk_rule(rule_expr, query_rules);
        SASSERT(query_rules.size() >= 1);
        query_rule = query_rules.back();
    }

    void rule_manager::bind_variables(expr* fml, bool is_forall, expr_ref& result) {
        app_ref_vector const& vars = m_ctx.get_variables();
        if (vars.empty()) {
            result = fml;
        }
        else {
            ptr_vector<sort> sorts;
            expr_abstract(m, 0, vars.size(), reinterpret_cast<expr*const*>(vars.c_ptr()), fml, result);
            get_free_vars(result, sorts);
            if (sorts.empty()) {
                result = fml;
            }
            else {
                svector<symbol> names;
                for (unsigned i = 0; i < sorts.size(); ++i) {
                    if (!sorts[i]) {
                        sorts[i] = m.mk_bool_sort();
                    }
                    names.push_back(symbol(i));
                }
                quantifier_ref q(m);
                q = m.mk_quantifier(is_forall, sorts.size(), sorts.c_ptr(), names.c_ptr(), result); 
                elim_unused_vars(m, q, result);
            }
        }
    }

    void rule_manager::flatten_body(app_ref_vector& body) {

        expr_ref_vector r(m);
        for (unsigned i = 0; i < body.size(); ++i) {
            r.push_back(body[i].get());
        }
        flatten_and(r);
        body.reset();
        for (unsigned i = 0; i < r.size(); ++i) {
            body.push_back(ensure_app(r[i].get()));
        }
    }                

    void rule_manager::hoist_compound(unsigned& num_bound, app_ref& fml, app_ref_vector& body) {

        expr_ref e(m);
        expr* not_fml;
        if (m.is_not(fml, not_fml)) {
            fml = ensure_app(not_fml);
            hoist_compound(num_bound, fml, body);
            fml = m.mk_not(fml);
            return;
        }
        expr_ref_vector args(m);
        if (!is_predicate(fml)) {
            return;
        }
        for (unsigned i = 0; i < fml->get_num_args(); ++i) {
            e = fml->get_arg(i);
            if (!is_app(e)) {
                args.push_back(e);
                continue;
            }
            app* b = to_app(e);

            if (m.is_value(b)) {
                args.push_back(e);
            }
            else {
                var* v = m.mk_var(num_bound++, m.get_sort(b));
                args.push_back(v);
                body.push_back(m.mk_eq(v, b));
            }
        }
        fml = m.mk_app(fml->get_decl(), args.size(), args.c_ptr());
        TRACE("dl_rule", tout << mk_pp(fml.get(), m) << "\n";);
    }

    class contains_predicate_proc {
        rule_manager const& m;
    public:
        struct found {};
        contains_predicate_proc(rule_manager const& m): m(m) {}
        void operator()(var * n) {}
        void operator()(quantifier * n) {}
        void operator()(app* n) {
            if (m.is_predicate(n)) throw found();
        }
    };

    bool rule_manager::contains_predicate(expr* fml) const {
        contains_predicate_proc proc(*this);
        try {
            quick_for_each_expr(proc, fml);
        }
        catch (contains_predicate_proc::found) {
            return true;
        }
        return false;
    }

    void rule_manager::eliminate_disjunctions(app_ref_vector::element_ref& body, rule_ref_vector& rules, symbol const& name) {

        app* b = body.get(); 
        expr* e1;
        bool negate_args = false;
        bool is_disj = false;
        unsigned num_disj = 0;
        expr* const* disjs = 0;
        if (!contains_predicate(b)) {
            return;
        }
        TRACE("dl_rule", tout << mk_ismt2_pp(b, m) << "\n";);
        if (m.is_or(b)) {
            is_disj = true;
            negate_args = false;
            num_disj = b->get_num_args();
            disjs = b->get_args();
        }
        if (m.is_not(b, e1) && m.is_and(e1)) {
            is_disj = true;
            negate_args = true;
            num_disj = to_app(e1)->get_num_args();
            disjs = to_app(e1)->get_args();
        }
        if (is_disj) {
            ptr_vector<sort> sorts0, sorts1;
            get_free_vars(b, sorts0);
            expr_ref_vector args(m);
            for (unsigned i = 0; i < sorts0.size(); ++i) {
                if (sorts0[i]) {
                    args.push_back(m.mk_var(i,sorts0[i]));
                    sorts1.push_back(sorts0[i]);
                }
            }
            app* old_head = 0;
            if (m_memoize_disj.find(b, old_head)) {
                body = old_head;
            }
            else {
                app_ref head(m);
                func_decl_ref f(m);
                f = m.mk_fresh_func_decl(name.str().c_str(),"", sorts1.size(), sorts1.c_ptr(), m.mk_bool_sort());
                m_ctx.register_predicate(f);
                head = m.mk_app(f, args.size(), args.c_ptr());
                
                for (unsigned i = 0; i < num_disj; ++i) {
                    expr_ref fml(m);
                    expr* e = disjs[i];
                    if (negate_args) e = m.mk_not(e);
                    fml = m.mk_implies(e,head);
                    mk_rule_core(fml, rules, name);
                }
                m_memoize_disj.insert(b, head);
                m_refs.push_back(b);
                m_refs.push_back(head);
                // update the body to be the newly introduced head relation
                body = head;
            }
        }
    }

    void rule_manager::eliminate_disjunctions(app_ref_vector& body, rule_ref_vector& rules, symbol const& name) {
        for (unsigned i = 0; i < body.size(); ++i) {
            app_ref_vector::element_ref t = body[i];
            eliminate_disjunctions(t, rules, name);
        }
    }

    bool rule_manager::is_forall(ast_manager& m, expr* e, quantifier*& q) {
        expr* e1, *e2;
        if (m.is_iff(e, e1, e2)) {
            if (m.is_true(e2)) {
                e = e1;
            }
            else if (m.is_true(e1)) {
                e = e2;
            }
        }
        if (is_quantifier(e)) {
            q = to_quantifier(e);
            return q->is_forall();
        }    
        return false;
    }

    void rule_manager::eliminate_quantifier_body(app_ref_vector::element_ref& body, rule_ref_vector& rules, symbol const& name) {
        quantifier* q;
        if (is_forall(m, body.get(), q) && contains_predicate(q)) {
            expr* e = q->get_expr();
            if (!is_predicate(e)) {
                ptr_vector<sort> sorts0, sorts1;
                get_free_vars(e, sorts0);
                expr_ref_vector args(m);
                for (unsigned i = 0; i < sorts0.size(); ++i) {
                    if (sorts0[i]) {
                        args.push_back(m.mk_var(i,sorts0[i]));
                        sorts1.push_back(sorts0[i]);
                    }
                }
                app_ref head(m), fml(m);
                func_decl_ref f(m);
                f = m.mk_fresh_func_decl(name.str().c_str(),"", sorts1.size(), sorts1.c_ptr(), m.mk_bool_sort());
                m_ctx.register_predicate(f);
                head = m.mk_app(f, args.size(), args.c_ptr());
                fml = m.mk_implies(e, head);
                mk_rule_core(fml, rules, name);
                // update the body to be the newly introduced head relation
                body = m.mk_eq(m.mk_true(), m.update_quantifier(q, head));                
            }
        }
    }

    void rule_manager::eliminate_quantifier_body(app_ref_vector& body, rule_ref_vector& rules, symbol const& name) {
        for (unsigned i = 0; i < body.size(); ++i) {
            app_ref_vector::element_ref t = body[i];
            eliminate_quantifier_body(t, rules, name);
        }
    }


    app_ref rule_manager::ensure_app(expr* e) {
        SASSERT(m.is_bool(e));
        if (is_app(e)) {
            return app_ref(to_app(e), m);
        }
        else {
            return app_ref(m.mk_eq(e, m.mk_true()), m);
        }
    }
   
    void rule_manager::check_app(expr* e) {
        if (!is_app(e)) {
            std::ostringstream out;
            out << "expected application, got " << mk_pp(e, m);
            throw default_exception(out.str());
        }
    }

    rule * rule_manager::mk(app * head, unsigned n, app * const * tail, bool const * is_negated, symbol const& name) {
        DEBUG_CODE(check_valid_rule(head, n, tail););
        unsigned sz     = rule::get_obj_size(n);
        void * mem      = m.get_allocator().allocate(sz);
        rule * r        = new (mem) rule();
        r->m_head       = head;
        r->m_name       = name;
        r->m_tail_size  = n;
        m.inc_ref(r->m_head);

        app * * uninterp_tail = r->m_tail; //grows upwards
        app * * interp_tail = r->m_tail+n; //grows downwards

        bool has_neg = false;

        for (unsigned i = 0; i < n; i++) {
            bool  is_neg = (is_negated != 0 && is_negated[i]); 
            app * curr = tail[i];

            if (is_neg && !is_predicate(curr)) {
                curr = m.mk_not(curr);
                is_neg = false;
            }
            if (is_neg) {
                has_neg = true;
            }
            app * tail_entry = TAG(app *, curr, is_neg);
            if (is_predicate(curr)) {
                *uninterp_tail=tail_entry;
                uninterp_tail++;
            }
            else {
                interp_tail--;
                *interp_tail=tail_entry;
            }
            m.inc_ref(curr);
        }
        SASSERT(uninterp_tail==interp_tail);

        r->m_uninterp_cnt = static_cast<unsigned>(uninterp_tail - r->m_tail);

        if (has_neg) {
            //put negative predicates between positive and interpreted
            app * * it = r->m_tail;
            app * * end = r->m_tail + r->m_uninterp_cnt;
            while(it!=end) {
                bool  is_neg = GET_TAG(*it)!=0;
                if (is_neg) {
                    --end;
                    std::swap(*it, *end);
                }
                else {
                    ++it;
                }
            }
            r->m_positive_cnt = static_cast<unsigned>(it - r->m_tail);
            SASSERT(r->m_positive_cnt < r->m_uninterp_cnt);
        }
        else {
            r->m_positive_cnt = r->m_uninterp_cnt;
        }

        r->norm_vars(*this);
        return r;
    }

    rule * rule_manager::mk(rule const * source, symbol const& name) {
        return mk(source, source->get_head(), name);
    }

    rule * rule_manager::mk(rule const * source, app * new_head, symbol const& name) {
        unsigned n        = source->get_tail_size();
        unsigned sz       = rule::get_obj_size(n);
        void * mem        = m.get_allocator().allocate(sz);
        rule * r          = new (mem) rule();
        r->m_head         = new_head;
        r->m_name         = name;
        r->m_tail_size    = n;
        r->m_positive_cnt = source->m_positive_cnt;
        r->m_uninterp_cnt = source->m_uninterp_cnt;
        m.inc_ref(r->m_head);
        for (unsigned i = 0; i < n; i++) {
            r->m_tail[i] = source->m_tail[i];
            m.inc_ref(r->get_tail(i));
        }
        return r;
    }

    void rule_manager::reduce_unbound_vars(rule_ref& r) {
        unsigned ut_len = r->get_uninterpreted_tail_size();
        unsigned t_len = r->get_tail_size();
        ptr_vector<sort> vars;
        uint_set index_set;
        qe_lite qe(m);
        expr_ref_vector conjs(m);

        if (ut_len == t_len) {
            return;
        }

        get_free_vars(r->get_head(), vars);
        for (unsigned i = 0; i < ut_len; ++i) {
            get_free_vars(r->get_tail(i), vars);
        }
        for (unsigned i = ut_len; i < t_len; ++i) {
            conjs.push_back(r->get_tail(i));
        }

        for (unsigned i = 0; i < vars.size(); ++i) {
            if (vars[i]) {
                index_set.insert(i);
            }
        }
        qe(index_set, false, conjs);
        bool change = conjs.size() != t_len - ut_len;
        for (unsigned i = 0; !change && i < conjs.size(); ++i) {
            change = r->get_tail(ut_len+i) != conjs[i].get();
        }
        if (change) {
            app_ref_vector tail(m);
            svector<bool> tail_neg;
            for (unsigned i = 0; i < ut_len; ++i) {
                tail.push_back(r->get_tail(i));
                tail_neg.push_back(r->is_neg_tail(i));
            }
            for (unsigned i = 0; i < conjs.size(); ++i) {
                tail.push_back(ensure_app(conjs[i].get()));
            }
            tail_neg.resize(tail.size(), false);
            r = mk(r->get_head(), tail.size(), tail.c_ptr(), tail_neg.c_ptr());
            TRACE("dl", r->display(m_ctx, tout << "reduced rule\n"););
        }
    }

    void rule_manager::fix_unbound_vars(rule_ref& r, bool try_quantifier_elimination) {

        reduce_unbound_vars(r);

        if (!m_ctx.fix_unbound_vars()) {
            return;
        }

        unsigned ut_len = r->get_uninterpreted_tail_size();
        unsigned t_len = r->get_tail_size();

        if (ut_len == t_len) {
            // no interpreted tail to fix
            return;
        }

        ptr_vector<sort> free_rule_vars;
        var_counter vctr;
        app_ref_vector tail(m);
        svector<bool> tail_neg;
        app_ref head(r->get_head(), m);

        get_free_vars(r, free_rule_vars);
        vctr.count_vars(m, head);


        for (unsigned i = 0; i < ut_len; i++) {
            app * t = r->get_tail(i);
            vctr.count_vars(m, t);
            tail.push_back(t);
            tail_neg.push_back(r->is_neg_tail(i));
        }

        ptr_vector<sort> interp_vars;
        var_idx_set unbound_vars;
        expr_ref_vector tails_with_unbound(m);

        for (unsigned i = ut_len; i < t_len; i++) {
            app * t = r->get_tail(i);
            interp_vars.reset();
            ::get_free_vars(t, interp_vars);
            bool has_unbound = false;
            unsigned iv_size = interp_vars.size();
            for (unsigned i=0; i<iv_size; i++) {
                if (!interp_vars[i]) { continue; }
                if (vctr.get(i)==0) {
                    has_unbound = true;
                    unbound_vars.insert(i);
                }
            }

            if (has_unbound) {
                tails_with_unbound.push_back(t);
            }
            else {
                tail.push_back(t);
                tail_neg.push_back(false);
            }
        }

        if (tails_with_unbound.empty()) {
            //there are no unbound interpreted tail variables
            return;
        }
        expr_ref unbound_tail(m);
        bool_rewriter(m).mk_and(tails_with_unbound.size(), tails_with_unbound.c_ptr(), unbound_tail);

        unsigned q_var_cnt = unbound_vars.num_elems();
        unsigned max_var = m_var_counter.get_max_var(*r);

        expr_ref_vector subst(m);

        ptr_vector<sort> qsorts;
        qsorts.resize(q_var_cnt);

        unsigned q_idx = 0;
        for (unsigned v = 0; v <= max_var; ++v) {
            sort * v_sort = free_rule_vars[v];
            if (!v_sort) {
                //this variable index is not used
                continue;
            }

            unsigned new_idx;
            if (unbound_vars.contains(v)) {
                new_idx = q_idx++;
                qsorts.push_back(v_sort);
            }
            else {
                new_idx = v + q_var_cnt;
            }
            subst.push_back(m.mk_var(new_idx, v_sort));
        }
        SASSERT(q_idx == q_var_cnt);

        svector<symbol> qnames;
        for (unsigned i = 0; i < q_var_cnt; i++) {
            qnames.push_back(symbol(i));
        }
        //quantifiers take this reversed
        qsorts.reverse();
        qnames.reverse();

        expr_ref unbound_tail_pre_quant(m), fixed_tail(m), quant_tail(m);

        var_subst vs(m, false);
        vs(unbound_tail, subst.size(), subst.c_ptr(), unbound_tail_pre_quant);

        quant_tail = m.mk_exists(q_var_cnt, qsorts.c_ptr(), qnames.c_ptr(), unbound_tail_pre_quant);

        if (try_quantifier_elimination) {
            TRACE("dl_rule_unbound_fix_pre_qe", 
                tout<<"rule: ";
                r->display(m_ctx, tout);
                tout<<"tail with unbound vars: "<<mk_pp(unbound_tail, m)<<"\n";
                tout<<"quantified tail: "<<mk_pp(quant_tail, m)<<"\n";
            );

            proof_ref pr(m);
            qe::expr_quant_elim_star1 simpl(m, m_ctx.get_fparams());
            simpl(quant_tail, fixed_tail, pr);
        }
        else {
            fixed_tail = quant_tail;
        }

        TRACE("dl_rule_unbound_fix", 
            tout<<"rule: ";
            r->display(m_ctx, tout);
            tout<<"tail with unbound vars: "<<mk_pp(unbound_tail, m)<<"\n";
            tout<<"quantified tail: "<<mk_pp(quant_tail, m)<<"\n";
            tout<<"fixed tail: "<<mk_pp(fixed_tail, m)<<"\n";
        );

        if (is_var(fixed_tail) || ::is_quantifier(fixed_tail)) {
            fixed_tail = m.mk_eq(fixed_tail, m.mk_true());
        }
        SASSERT(is_app(fixed_tail));

        if (!m.is_true(fixed_tail.get())) {
            tail.push_back(to_app(fixed_tail.get()));
            tail_neg.push_back(false);
        }

        SASSERT(tail.size()==tail_neg.size());
        rule_ref old_r = r;
        r = mk(head, tail.size(), tail.c_ptr(), tail_neg.c_ptr());
        r->set_accounting_parent_object(m_ctx, old_r);
    }

    void rule_manager::substitute(rule_ref& r, unsigned sz, expr*const* es) {
        expr_ref tmp(m);
        app_ref  new_head(m);
        app_ref_vector new_tail(m);
        svector<bool> tail_neg;
        var_subst vs(m, false);
        vs(r->get_head(), sz, es, tmp);
        new_head = to_app(tmp);
        for (unsigned i = 0; i < r->get_tail_size(); ++i) {
            vs(r->get_tail(i), sz, es, tmp);
            new_tail.push_back(to_app(tmp));
            tail_neg.push_back(r->is_neg_tail(i));
        }
        r = mk(new_head.get(), new_tail.size(), new_tail.c_ptr(), tail_neg.c_ptr(), r->name());

        // keep old variable indices around so we can compose with substitutions. 
        // r->norm_vars(*this);
    }


    void rule_manager::check_valid_rule(app * head, unsigned n, app * const * tail) const {
        check_valid_head(head);
    }

    void rule_manager::check_valid_head(expr * head) const {
        SASSERT(head);
        
        if (!is_predicate(head)) {
            std::ostringstream out;
            out << "Illegal head. The head predicate needs to be uninterpreted and registered (as recursive) " << mk_pp(head, m);
            throw default_exception(out.str());
        }
        unsigned num_args = to_app(head)->get_num_args();
        for (unsigned i = 0; i < num_args; i++) {
            expr * arg = to_app(head)->get_arg(i);
            if (!is_var(arg) && !m.is_value(arg)) {
                std::ostringstream out;
                out << "Illegal argument to predicate in head " << mk_pp(arg, m);
                throw default_exception(out.str());
            }
        }
    }

    bool rule_manager::is_fact(app * head) const {
        unsigned num_args = head->get_num_args();
        for (unsigned i = 0; i < num_args; i++) {
            if (!m.is_value(head->get_arg(i)))
                return false;
        }
        return true;
    }

    void rule::deallocate(ast_manager & m) {
        m.dec_ref(m_head);
        unsigned n = get_tail_size();
        for (unsigned i = 0; i < n; i++) {
            m.dec_ref(get_tail(i));
        }
        this->~rule();
        m.get_allocator().deallocate(get_obj_size(n), this);
    }

    bool rule::is_in_tail(const func_decl * p, bool only_positive) const {
        unsigned len = only_positive ? get_positive_tail_size() : get_uninterpreted_tail_size();
        for (unsigned i = 0; i < len; i++) {
            if (get_tail(i)->get_decl()==p) {
                return true;
            }
        }
        return false;
    }

    struct uninterpreted_function_finder_proc {
        bool m_found;
        func_decl* m_func;
        uninterpreted_function_finder_proc() : m_found(false), m_func(0) {}
        void operator()(var * n) { }
        void operator()(quantifier * n) { }
        void operator()(app * n) {
            if (is_uninterp(n)) {
                m_found = true;
                m_func = n->get_decl();
            }
        }

        bool found(func_decl*& f) const { f = m_func; return m_found; }
    };

    //
    // non-predicates may appear only in the interpreted tail, it is therefore 
    // sufficient only to check the tail.
    //
    bool rule::has_uninterpreted_non_predicates(func_decl*& f) const {
        unsigned sz = get_tail_size();
        uninterpreted_function_finder_proc proc;
        expr_mark visited;
        for (unsigned i = get_uninterpreted_tail_size(); i < sz && !proc.found(f); ++i) {
            for_each_expr(proc, visited, get_tail(i));
        }
        return proc.found(f);
    }

    struct quantifier_finder_proc {
        bool m_exist;
        bool m_univ;
        quantifier_finder_proc() : m_exist(false), m_univ(false) {}
        void operator()(var * n) { }
        void operator()(quantifier * n) {
            if (n->is_forall()) {
                m_univ = true;
            }
            else {
                SASSERT(n->is_exists());
                m_exist = true;
            }
        }
        void operator()(app * n) { }
    };

    //
    // Quantifiers may appear only in the interpreted tail, it is therefore 
    // sufficient only to check the interpreted tail.
    //
    void rule::has_quantifiers(bool& existential, bool& universal) const {
        unsigned sz = get_tail_size();
        quantifier_finder_proc proc;
        expr_mark visited;
        for (unsigned i = get_uninterpreted_tail_size(); i < sz; ++i) {
            for_each_expr(proc, visited, get_tail(i));
        }
        existential = proc.m_exist;
        universal = proc.m_univ;
    }

    bool rule::has_quantifiers() const {
        bool exist, univ;
        has_quantifiers(exist, univ);
        return exist || univ;
    }

    void rule::get_used_vars(used_vars& used) const {
        used.process(get_head());
        unsigned sz = get_tail_size();
        for (unsigned i = 0; i < sz; ++i) {
            used.process(get_tail(i));
        }        
    }

    void rule::get_vars(sort_ref_vector& sorts) const {
        sorts.reset();
        used_vars used;
        get_used_vars(used);
        unsigned sz = used.get_max_found_var_idx_plus_1();
        for (unsigned i = 0; i < sz; ++i) {
            sorts.push_back(used.get(i));
        }
    }

    void rule::norm_vars(rule_manager & rm) {
        used_vars used;
        get_used_vars(used);

        unsigned first_unsused = used.get_max_found_var_idx_plus_1();
        if (used.uses_all_vars(first_unsused)) {
            return;
        }
        ast_manager& m = rm.get_manager();

        unsigned next_fresh_var = 0;
        expr_ref_vector subst_vals(m);
        for (unsigned i=0; i<first_unsused; ++i) {
            sort* var_srt = used.contains(i);
            if (var_srt) {
                subst_vals.push_back(m.mk_var(next_fresh_var++, var_srt));
            }
            else {
                subst_vals.push_back(0);
            }
        }

        var_subst vs(m, false);

        expr_ref new_head_e(m);
        vs(m_head, subst_vals.size(), subst_vals.c_ptr(), new_head_e);

        m.inc_ref(new_head_e);
        m.dec_ref(m_head);
        m_head = to_app(new_head_e);

        for (unsigned i = 0; i < m_tail_size; i++) {
            app * old_tail = get_tail(i);
            expr_ref new_tail_e(m);
            vs(old_tail, subst_vals.size(), subst_vals.c_ptr(), new_tail_e);
            bool  sign     = is_neg_tail(i); 
            m.inc_ref(new_tail_e);
            m.dec_ref(old_tail);
            m_tail[i] = TAG(app *, to_app(new_tail_e), sign);
        }
    }
  
    void rule::display(context & ctx, std::ostream & out) const {
        ast_manager & m = ctx.get_manager();
        //out << mk_pp(m_head, m);
        output_predicate(ctx, m_head, out);
        if (m_tail_size == 0) {
            out << ".\n";
            return;
        }
        out << " :- ";
        for (unsigned i = 0; i < m_tail_size; i++) {
            if (i > 0)
                out << ",";
            out << "\n ";
            if (is_neg_tail(i))
                out << "not ";
            app * t = get_tail(i);
            if (ctx.get_rule_manager().is_predicate(t)) {
                output_predicate(ctx, t, out);
            }
            else {
                out << mk_pp(t, m);
            }
        }
        out << '.';
        if (ctx.output_profile()) {
            out << " {";
            output_profile(ctx, out);
            out << '}';
        }
        out << '\n';
    }

    void rule::to_formula(expr_ref& fml) const {
        ast_manager & m = fml.get_manager();
        expr_ref_vector body(m);
        for (unsigned i = 0; i < m_tail_size; i++) {
            body.push_back(get_tail(i));
            if (is_neg_tail(i)) {
                body[body.size()-1] = m.mk_not(body.back());
            }
        }
        switch(body.size()) {
        case 0:  fml = m_head; break;
        case 1:  fml = m.mk_implies(body[0].get(), m_head); break;
        default: fml = m.mk_implies(m.mk_and(body.size(), body.c_ptr()), m_head); break;
        }
 
        ptr_vector<sort> sorts;
        get_free_vars(fml, sorts);        
        if (sorts.empty()) {
            return;
        }
        svector<symbol> names;
        used_symbols<> us;
        
        us(fml);
        sorts.reverse();
        
        for (unsigned i = 0; i < sorts.size(); ) {
            if (!sorts[i]) {
                sorts[i] = m.mk_bool_sort();
            }
            for (unsigned j = 0; i < sorts.size(); ++j) {
                for (char c = 'A'; i < sorts.size() && c <= 'Z'; ++c) {
                    func_decl_ref f(m);
                    std::stringstream _name;
                    _name << c;
                    if (j > 0) _name << j;
                    symbol name(_name.str().c_str());
                    if (!us.contains(name)) {
                        names.push_back(name);
                        ++i;
                    }
                }
            }
        }
        fml = m.mk_forall(sorts.size(), sorts.c_ptr(), names.c_ptr(), fml); 
    }

    std::ostream& rule::display_smt2(ast_manager& m, std::ostream & out) const {
        expr_ref fml(m);
        to_formula(fml);
        return out << mk_ismt2_pp(fml, m);
    }

    bool rule_eq_proc::operator()(const rule * r1, const rule * r2) const {
        if (r1->get_head()!=r2->get_head()) { return false; }
        unsigned tail_len = r1->get_tail_size();
        if (r2->get_tail_size()!=tail_len) {
            return false;
        }
        for (unsigned i=0; i<tail_len; ++i) {
            if (r1->get_tail(i)!=r2->get_tail(i)) {
                return false;
            }
            if (r1->is_neg_tail(i)!=r2->is_neg_tail(i)) {
                return false;
            }
        }
        return true;
    }

    unsigned rule::hash() const {
        unsigned res = get_head()->hash();
        unsigned tail_len = get_tail_size();
        for (unsigned i=0; i<tail_len; ++i) {
            res = combine_hash(res, combine_hash(get_tail(i)->hash(), is_neg_tail(i)));
        }
        return res;
    }

    unsigned rule_hash_proc::operator()(const rule * r) const {
        return r->hash();
    }



};
