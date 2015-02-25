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
#include"rewriter_def.h"
#include"th_rewriter.h"
#include"ast_smt2_pp.h"
#include"used_symbols.h"
#include"quant_hoist.h"
#include"expr_replacer.h"
#include"bool_rewriter.h"
#include"expr_safe_replace.h"
#include"filter_model_converter.h"
#include"scoped_proof.h"
#include"datatype_decl_plugin.h"

namespace datalog {

    rule_manager::rule_manager(context& ctx) 
        : m(ctx.get_manager()),
          m_ctx(ctx),
          m_body(m),
          m_head(m),
          m_args(m),
          m_hnf(m),
          m_qe(m),
          m_cfg(m),
          m_rwr(m, false, m_cfg) {}

    void rule_manager::inc_ref(rule * r) {
        if (r) {
            SASSERT(r->m_ref_cnt != UINT_MAX);
            r->m_ref_cnt++;
        }
    }

    void rule_manager::dec_ref(rule * r) {
        if (r) {
            SASSERT(r->m_ref_cnt > 0);
            r->m_ref_cnt--;
            if (r->m_ref_cnt == 0) {
                r->deallocate(m);
            }
        }
    }

    rule_manager::remove_label_cfg::~remove_label_cfg() {}

    br_status rule_manager::remove_label_cfg::reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, 
                                                         proof_ref & result_pr)
    {
        if (is_decl_of(f, m_label_fid, OP_LABEL)) {
            SASSERT(num == 1);
            result = args[0];
            return BR_DONE;
        }
        return BR_FAILED;
    }


    void rule_manager::remove_labels(expr_ref& fml, proof_ref& pr) {
        expr_ref tmp(m);
        m_rwr(fml, tmp);
        if (pr && fml != tmp) {
            
            pr = m.mk_modus_ponens(pr, m.mk_rewrite(fml, tmp));
        }
        fml = tmp;
    }

    var_idx_set& rule_manager::collect_vars(expr* e) {
        return collect_vars(e, 0);
    }

    var_idx_set& rule_manager::collect_vars(expr* e1, expr* e2) {
        reset_collect_vars();
        if (e1) accumulate_vars(e1);
        if (e2) accumulate_vars(e2);
        return finalize_collect_vars();
    }

    void rule_manager::reset_collect_vars() {
        m_vars.reset();
        m_var_idx.reset();
        m_todo.reset();
        m_mark.reset();
    }

    var_idx_set& rule_manager::finalize_collect_vars() {
        unsigned sz = m_vars.size();
        for (unsigned i=0; i<sz; ++i) {
            if (m_vars[i]) m_var_idx.insert(i); 
        }
        return m_var_idx;
    }

    var_idx_set& rule_manager::collect_tail_vars(rule * r) {
        reset_collect_vars();
        unsigned n = r->get_tail_size();
        for (unsigned i=0;i<n;i++) {
            accumulate_vars(r->get_tail(i));
        }
        return finalize_collect_vars();
    }

    var_idx_set& rule_manager::collect_rule_vars_ex(rule * r, app* t) {
        reset_collect_vars();
        unsigned n = r->get_tail_size();
        accumulate_vars(r->get_head());
        for (unsigned i=0;i<n;i++) {
            if (r->get_tail(i) != t) {
                accumulate_vars(r->get_tail(i));
            }
        }
        return finalize_collect_vars();
    }

    var_idx_set& rule_manager::collect_rule_vars(rule * r) {
        reset_collect_vars();
        unsigned n = r->get_tail_size();
        accumulate_vars(r->get_head());
        for (unsigned i=0;i<n;i++) {
            accumulate_vars(r->get_tail(i));
        }
        return finalize_collect_vars();
    }

    void rule_manager::accumulate_vars(expr* e) {
        ::get_free_vars(m_mark, m_todo, e, m_vars);
    }


    void rule_manager::mk_rule(expr* fml, proof* p, rule_set& rules, symbol const& name) {              
        scoped_proof_mode _sc(m, m_ctx.generate_proof_trace()?PGM_FINE:PGM_DISABLED);
        proof_ref pr(p, m);
        expr_ref fml1(m);
        bind_variables(fml, true, fml1);
        if (fml1 != fml && pr) {
            pr = m.mk_asserted(fml1);
        }
        remove_labels(fml1, pr);        
        mk_rule_core(fml1, pr, rules, name);
    }

    void rule_manager::mk_negations(app_ref_vector& body, svector<bool>& is_negated) {
        for (unsigned i = 0; i < body.size(); ++i) {
            expr* e = body[i].get(), *e1;
            if (m.is_not(e, e1) && m_ctx.is_predicate(e1)) {
                check_app(e1);
                body[i] = to_app(e1);
                is_negated.push_back(true);
            }
            else {
                is_negated.push_back(false);
            }
        }        
    }

    void rule_manager::mk_rule_core(expr* fml, proof* p, rule_set& rules, symbol const& name) {
        DEBUG_CODE(ptr_vector<sort> sorts; 
                   ::get_free_vars(fml, sorts); );
        expr_ref_vector fmls(m);
        proof_ref_vector prs(m);
        m_hnf.reset();
        m_hnf.set_name(name);
        
        m_hnf(fml, p, fmls, prs);
        for (unsigned i = 0; i < m_hnf.get_fresh_predicates().size(); ++i) {
            m_ctx.register_predicate(m_hnf.get_fresh_predicates()[i], false);
        }
        for (unsigned i = 0; i < fmls.size(); ++i) {
            DEBUG_CODE(ptr_vector<sort> sorts; 
                       ::get_free_vars(fmls[i].get(), sorts); );
            mk_horn_rule(fmls[i].get(), prs[i].get(), rules, name);
        }
    }

    void rule_manager::mk_horn_rule(expr* fml, proof* p, rule_set& rules, symbol const& name) {
        
        m_body.reset();
        m_neg.reset();
        unsigned index = extract_horn(fml, m_body, m_head);
        hoist_compound_predicates(index, m_head, m_body);
        TRACE("dl_rule",
              tout << mk_pp(m_head, m) << " :- ";
              for (unsigned i = 0; i < m_body.size(); ++i) {
                  tout << mk_pp(m_body[i].get(), m) << " ";
              }
              tout << "\n";);


        mk_negations(m_body, m_neg);
        check_valid_rule(m_head, m_body.size(), m_body.c_ptr());

        rule_ref r(*this);
        r = mk(m_head.get(), m_body.size(), m_body.c_ptr(), m_neg.c_ptr(), name);

        expr_ref fml1(m);
        if (p) {
            r->to_formula(fml1);
            if (fml1 == fml) {
                // no-op.
            }
            else if (is_quantifier(fml1)) {
                p = m.mk_modus_ponens(p, m.mk_symmetry(m.mk_der(to_quantifier(fml1), fml)));
            }            
            else {
                p = m.mk_modus_ponens(p, m.mk_rewrite(fml, fml1));
            }
        }

        if (m_ctx.fix_unbound_vars()) {            
            fix_unbound_vars(r, true);
        }

        if (p) {
            expr_ref fml2(m);
            r->to_formula(fml2);
            if (fml1 != fml2) {
                p = m.mk_modus_ponens(p, m.mk_rewrite(fml1, fml2));
            }
            r->set_proof(m, p);
        }
        rules.add_rule(r);
    }

    unsigned rule_manager::extract_horn(expr* fml, app_ref_vector& body, app_ref& head) {
        expr* e1, *e2;
        unsigned index = m_counter.get_next_var(fml);
        if (::is_forall(fml)) {
            index += to_quantifier(fml)->get_num_decls();
            fml = to_quantifier(fml)->get_expr();
        }
        if (m.is_implies(fml, e1, e2)) {
            expr_ref_vector es(m);
            head = ensure_app(e2);
            qe::flatten_and(e1, es);
            for (unsigned i = 0; i < es.size(); ++i) {
                body.push_back(ensure_app(es[i].get()));
            }
        } 
        else {
            head = ensure_app(fml);
        }        
        return index;
    }

    void rule_manager::hoist_compound_predicates(unsigned index, app_ref& head, app_ref_vector& body) {
        unsigned sz = body.size();
        hoist_compound(index, head, body);
        for (unsigned i = 0; i < sz; ++i) {
            app_ref b(body[i].get(), m);
            hoist_compound(index, b, body);
            body[i] = b;
        }
    }


    func_decl* rule_manager::mk_query(expr* query, rule_set& rules) {
        ptr_vector<sort> vars;
        svector<symbol> names;
        app_ref_vector body(m);
        expr_ref q(m);
        
        // Add implicit variables.
        // Remove existential prefix.
        bind_variables(query, false, q);
        quantifier_hoister qh(m);
        qh.pull_quantifier(false, q, 0, &names);
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
        func_decl* qpred = m_ctx.mk_fresh_head_predicate(symbol("query"), symbol(), vars.size(), vars.c_ptr(), body_pred);
        m_ctx.register_predicate(qpred, false);        
        rules.set_output_predicate(qpred);
        
        if (m_ctx.get_model_converter()) {
            filter_model_converter* mc = alloc(filter_model_converter, m);
            mc->insert(qpred);
            m_ctx.add_model_converter(mc);
        }

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

        scoped_proof_mode _sc(m, m_ctx.generate_proof_trace()?PGM_FINE:PGM_DISABLED);
        proof_ref pr(m);
        if (m_ctx.generate_proof_trace()) {
            pr = m.mk_asserted(rule_expr);
        }
        mk_rule(rule_expr, pr, rules);
        return qpred;
    }

    void rule_manager::bind_variables(expr* fml, bool is_forall, expr_ref& result) {
        result = m_ctx.bind_variables(fml, is_forall);
    }

    void rule_manager::flatten_body(app_ref_vector& body) {

        expr_ref_vector r(m);
        for (unsigned i = 0; i < body.size(); ++i) {
            r.push_back(body[i].get());
        }
        qe::flatten_and(r);
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
        if (!m_ctx.is_predicate(fml)) {
            return;
        }
        m_args.reset();
        for (unsigned i = 0; i < fml->get_num_args(); ++i) {
            e = fml->get_arg(i);
            if (!is_app(e)) {
                m_args.push_back(e);
                continue;
            }
            app* b = to_app(e);

            if (m.is_value(b)) {
                m_args.push_back(e);
            }
            else {
                var* v = m.mk_var(num_bound++, m.get_sort(b));
                m_args.push_back(v);
                body.push_back(m.mk_eq(v, b));
            }
        }
        fml = m.mk_app(fml->get_decl(), m_args.size(), m_args.c_ptr());
        TRACE("dl_rule", tout << mk_pp(fml.get(), m) << "\n";);
    }

    class contains_predicate_proc {
        context const& ctx;
    public:
        struct found {};
        contains_predicate_proc(context const& ctx): ctx(ctx) {}
        void operator()(var * n) {}
        void operator()(quantifier * n) {}
        void operator()(app* n) {
            if (ctx.is_predicate(n)) throw found();
        }
    };

    bool rule_manager::contains_predicate(expr* fml) const {
        contains_predicate_proc proc(m_ctx);
        try {
            quick_for_each_expr(proc, fml);
        }
        catch (contains_predicate_proc::found) {
            return true;
        }
        return false;
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

    rule * rule_manager::mk(app * head, unsigned n, app * const * tail, bool const * is_negated, symbol const& name, bool normalize) {
        DEBUG_CODE(check_valid_rule(head, n, tail););
        unsigned sz     = rule::get_obj_size(n);
        void * mem      = m.get_allocator().allocate(sz);
        rule * r        = new (mem) rule();
        r->m_head       = head;
        r->m_name       = name;
        r->m_tail_size  = n;
        r->m_proof      = 0;
        m.inc_ref(r->m_head);

        app * * uninterp_tail = r->m_tail; //grows upwards
        app * * interp_tail = r->m_tail+n; //grows downwards

        DEBUG_CODE(ptr_vector<sort> sorts; 
                   ::get_free_vars(head, sorts);
                   for (unsigned i = 0; i < n; ++i) {
                       ::get_free_vars(tail[i], sorts);
                   });

        bool has_neg = false;

        for (unsigned i = 0; i < n; i++) {
            bool  is_neg = (is_negated != 0 && is_negated[i]); 
            app * curr = tail[i];

            if (is_neg && !m_ctx.is_predicate(curr)) {
                curr = m.mk_not(curr);
                is_neg = false;
            }
            if (is_neg) {
                has_neg = true;
            }
            app * tail_entry = TAG(app *, curr, is_neg);
            if (m_ctx.is_predicate(curr)) {
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

        if (normalize) {
            r->norm_vars(*this);
        }
        DEBUG_CODE(ptr_vector<sort> sorts; 
                   ::get_free_vars(head, sorts);
                   for (unsigned i = 0; i < n; ++i) {
                       ::get_free_vars(tail[i], sorts);
                   });
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
        r->m_proof        = 0;
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
        expr_ref_vector conjs(m);

        if (ut_len == t_len) {
            return;
        }

        reset_collect_vars();
        accumulate_vars(r->get_head());
        for (unsigned i = 0; i < ut_len; ++i) {
            accumulate_vars(r->get_tail(i));
        }
        var_idx_set& index_set = finalize_collect_vars();
        for (unsigned i = ut_len; i < t_len; ++i) {
            conjs.push_back(r->get_tail(i));
        }
        m_qe(index_set, false, conjs);
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

        var_counter vctr;
        app_ref_vector tail(m);
        svector<bool> tail_neg;
        app_ref head(r->get_head(), m);

        collect_rule_vars(r);
        vctr.count_vars(m, head);
        ptr_vector<sort>& free_rule_vars = m_vars;

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
        unsigned max_var = m_counter.get_max_rule_var(*r);

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

    void rule_manager::mk_rule_rewrite_proof(rule& old_rule, rule& new_rule) {
        if (&old_rule != &new_rule &&
            !new_rule.get_proof() &&
            old_rule.get_proof()) {
            expr_ref fml(m);
            new_rule.to_formula(fml);
            scoped_proof _sc(m);
            proof* p = m.mk_rewrite(m.get_fact(old_rule.get_proof()), fml);
            new_rule.set_proof(m, m.mk_modus_ponens(old_rule.get_proof(), p)); 
        }
    }

    void rule_manager::mk_rule_asserted_proof(rule& r) {
        if (m_ctx.generate_proof_trace()) {
            scoped_proof _scp(m);
            expr_ref fml(m);
            r.to_formula(fml);
            r.set_proof(m, m.mk_asserted(fml));
        }
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
        r = mk(new_head.get(), new_tail.size(), new_tail.c_ptr(), tail_neg.c_ptr(), r->name(), false);

        // keep old variable indices around so we can compose with substitutions. 
        // r->norm_vars(*this);
    }


    void rule_manager::check_valid_rule(app * head, unsigned n, app * const * tail) const {
        check_valid_head(head);
    }

    void rule_manager::check_valid_head(expr * head) const {
        SASSERT(head);
        
        if (!m_ctx.is_predicate(head)) {
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
        if (m_proof) {
            m.dec_ref(m_proof);
        }
        this->~rule();
        m.get_allocator().deallocate(get_obj_size(n), this);
    }

    void rule::set_proof(ast_manager& m, proof* p) { 
        if (p) {
            m.inc_ref(p); 
        }
        if (m_proof) {
            m.dec_ref(m_proof); 
        }
        m_proof = p; 
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
        ast_manager& m;
        datatype_util m_dt;
        dl_decl_util  m_dl;
        bool m_found;
        func_decl* m_func;
        uninterpreted_function_finder_proc(ast_manager& m): 
            m(m), m_dt(m), m_dl(m), m_found(false), m_func(0) {}
        void operator()(var * n) { }
        void operator()(quantifier * n) { }
        void operator()(app * n) {
            if (is_uninterp(n) && !m_dl.is_rule_sort(n->get_decl()->get_range())) {
                m_found = true;
                m_func = n->get_decl();
            }
            else if (m_dt.is_accessor(n)) {
                sort* s = m.get_sort(n->get_arg(0));
                SASSERT(m_dt.is_datatype(s));
                if (m_dt.get_datatype_constructors(s)->size() > 1) {
                    m_found = true;
                    m_func = n->get_decl();
                }
            }
        }

        bool found(func_decl*& f) const { f = m_func; return m_found; }
    };

    //
    // non-predicates may appear only in the interpreted tail, it is therefore 
    // sufficient only to check the tail.
    //
    bool rule::has_uninterpreted_non_predicates(ast_manager& m, func_decl*& f) const {
        unsigned sz = get_tail_size();
        uninterpreted_function_finder_proc proc(m);
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

    bool rule::has_negation() const {
        for (unsigned i = 0; i < get_uninterpreted_tail_size(); ++i) {
            if (is_neg_tail(i)) {
                return true;
            }
        }
        return false;
    }

    void rule::get_used_vars(used_vars& used) const {
        used.process(get_head());
        unsigned sz = get_tail_size();
        for (unsigned i = 0; i < sz; ++i) {
            used.process(get_tail(i));
        }        
    }

    void rule::get_vars(ast_manager& m, ptr_vector<sort>& sorts) const {
        sorts.reset();
        used_vars used;
        get_used_vars(used);
        unsigned sz = used.get_max_found_var_idx_plus_1();
        for (unsigned i = 0; i < sz; ++i) {
            sort* s = used.get(i);
            sorts.push_back(s?s:m.mk_bool_sort());
        }
    }

    void rule::norm_vars(rule_manager & rm) {
        used_vars& used = rm.reset_used();
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
            if (ctx.is_predicate(t)) {
                output_predicate(ctx, t, out);
            }
            else {
                out << mk_pp(t, m);
            }
        }
        out << '.';
        if (ctx.output_profile()) {
            out << " {";
            output_profile(out);
            out << '}';
        }
        out << '\n';
        if (m_proof) {
            out << mk_pp(m_proof, m) << '\n';
        }
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
        for (unsigned i = 0; i < sorts.size(); ++i) {
            if (!sorts[i]) {
                sorts[i] = m.mk_bool_sort();
            }
        }
               
        us(fml);
        sorts.reverse();
        for (unsigned j = 0, i = 0; i < sorts.size(); ++j) {
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

template class rewriter_tpl<datalog::rule_manager::remove_label_cfg>;

