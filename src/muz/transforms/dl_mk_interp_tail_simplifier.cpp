/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_mk_interp_tail_simplifier.cpp

Abstract:

    Rule transformer which simplifies interpreted tails

Author:

    Krystof Hoder (t-khoder) 2011-10-01.

Revision History:

--*/


#include <sstream>
#include"ast_pp.h"
#include"bool_rewriter.h"
#include"rewriter.h"
#include"rewriter_def.h"
#include"dl_mk_rule_inliner.h"
#include"dl_mk_interp_tail_simplifier.h"
#include"ast_util.h"

namespace datalog {

    // -----------------------------------
    //
    // mk_interp_tail_simplifier::rule_substitution
    //
    // -----------------------------------

    void mk_interp_tail_simplifier::rule_substitution::reset(rule * r) {
        unsigned var_cnt = m_context.get_rule_manager().get_counter().get_max_rule_var(*r)+1;
        m_subst.reset();
        m_subst.reserve(1, var_cnt);
        m_rule = r;
    }

    bool mk_interp_tail_simplifier::rule_substitution::unify(expr * e1, expr * e2) {
        SASSERT(m_rule);

        //we need to apply the current substitution in order to ensure the unifier 
        //works in an incremental way
        expr_ref e1_s(m);
        expr_ref e2_s(m);
        m_subst.apply(e1,e1_s);
        m_subst.apply(e2,e2_s);
        //and we need to reset the cache as we're going to modify the substitution
        m_subst.reset_cache();

        return m_unif (e1_s, e2_s, m_subst, false);
    }

    void mk_interp_tail_simplifier::rule_substitution::apply(app * a, app_ref& res) {
        SASSERT(m_rule);
        expr_ref res_e(m);
        m_subst.apply(a, res_e);
        SASSERT(is_app(res_e.get()));
        res = to_app(res_e.get());
    }

    void mk_interp_tail_simplifier::rule_substitution::get_result(rule_ref & res) {
        SASSERT(m_rule);

        apply(m_rule->get_head(), m_head);

        m_tail.reset();
        m_neg.reset();

        unsigned tail_len = m_rule->get_tail_size();
        for (unsigned i=0; i<tail_len; i++) {
            app_ref new_tail_el(m);
            apply(m_rule->get_tail(i), new_tail_el);
            m_tail.push_back(new_tail_el);
            m_neg.push_back(m_rule->is_neg_tail(i));
        }

        mk_rule_inliner::remove_duplicate_tails(m_tail, m_neg);

        SASSERT(m_tail.size() == m_neg.size());
        res = m_context.get_rule_manager().mk(m_head, m_tail.size(), m_tail.c_ptr(), m_neg.c_ptr());
        res->set_accounting_parent_object(m_context, m_rule);
        res->norm_vars(res.get_manager());
    }


    // -----------------------------------
    //
    // mk_interp_tail_simplifier
    //
    // -----------------------------------


    class mk_interp_tail_simplifier::normalizer_cfg : public default_rewriter_cfg
    {
        struct expr_cmp
        {
            ast_manager& m;

            expr_cmp(ast_manager& m) : m(m) {}

            bool operator()(expr * ae, expr * be) {
                return cmp_expr(ae, be, 4) == -1;
            }

            template<typename T>
            static int cmp(T a, T b) { return (a>b) ? 1 : ((a == b) ? 0 : -1); }

            int cmp_expr(expr * ae, expr * be, int depth) {
                if (ae == be) { return 0; }

                //remove negations
                bool a_neg = m.is_not(ae, ae);
                bool b_neg = m.is_not(be, be);

                if (ae==be) { return cmp(a_neg, b_neg); }

                if (!is_app(ae) && !is_app(be)) { return cmp(ae->get_id(), be->get_id()); }
                if (!is_app(ae)) { return -1; }
                if (!is_app(be)) { return 1; }
                app * a = to_app(ae);
                app * b = to_app(be);
                if (a->get_decl()!=b->get_decl()) {
                    return cmp(a->get_decl()->get_id(), b->get_decl()->get_id());
                }

                if (a->get_num_args()!=b->get_num_args()) {
                    return cmp(a->get_num_args(), b->get_num_args());
                }

                if (depth==0) {
                    return cmp(a->get_id(),b->get_id());
                }
                unsigned arg_cnt = a->get_num_args();

                unsigned neg_comparison = 0;

                for (unsigned i=0; i<arg_cnt; i++) {
                    expr * arg_a = a->get_arg(i);
                    expr * arg_b = b->get_arg(i);

                    //we normalize away negations
                    bool a_is_neg = m.is_not(arg_a, arg_a);
                    bool b_is_neg = m.is_not(arg_b, arg_b);

                    if (neg_comparison==0 && a_is_neg!=b_is_neg) {
                        neg_comparison = a_is_neg ? -1 : 1;
                    }

                    int res = cmp_expr(arg_a, arg_b, depth-1);
                    if (res!=0) {
                        return res;
                    }
                }
                if (neg_comparison!=0) {
                    return neg_comparison;
                }
                //by normalizing away negation we may have put non-equal terms to be equal, so here we check
                return cmp(a->get_id(),b->get_id());
            }
        };

        ast_manager& m;
        bool_rewriter m_brwr;

        //instead of a local variable
        expr_ref_vector m_app_args;

        expr_cmp m_expr_cmp;

    public:
        normalizer_cfg(ast_manager& m)
            : m(m), m_brwr(m), m_app_args(m), m_expr_cmp(m)
        {
        }

        static void remove_duplicates(expr_ref_vector& v)
        {
            expr * a = v[0].get();
            unsigned read_idx = 1;
            unsigned write_idx = 1;
            for (;;) {
                while(read_idx<v.size() && a==v[read_idx].get()) {
                    read_idx++;
                }
                if (read_idx==v.size()) {
                    break;
                }

                a = v[read_idx].get();
                if (write_idx!=read_idx) {
                    v[write_idx] = a;
                }
                write_idx++;
                read_idx++;
            }
            v.shrink(write_idx);
        }

        typedef std::pair<expr *,expr *> arg_pair;

        bool match_arg_pair(expr * e, arg_pair& pair, bool seek_conjunction)
        {
            if (seek_conjunction) {
                return m.is_and(e, pair.first, pair.second);
            }
            else {
                return m.is_or(e, pair.first, pair.second);
            }
        }

        /**
        If inside_disjunction is false, we're inside a conjunction (and arg pairs
        represent disjunctions).
        */
        app * detect_equivalence(const arg_pair& p1, const arg_pair& p2, bool inside_disjunction)
        {
            if (m.is_not(p1.first)==m.is_not(p2.first)) { return 0; }
            if (m.is_not(p1.second)==m.is_not(p2.second)) { return 0; }

            expr * first_bare = 0;
            if (m.is_not(p1.first, first_bare) && p2.first!=first_bare) { return 0; }
            if (m.is_not(p2.first, first_bare) && p1.first!=first_bare) { return 0; }
            SASSERT(first_bare);

            expr * second_bare = 0;
            if (m.is_not(p1.second, second_bare) && p2.second!=second_bare) { return 0; }
            if (m.is_not(p2.second, second_bare) && p1.second!=second_bare) { return 0; }
            SASSERT(second_bare);

            if (!m.is_bool(first_bare) || !m.is_bool(second_bare)) { return 0; }

            //both negations are in the same pair
            bool negs_together = m.is_not(p1.first)==m.is_not(p1.second);

            if (negs_together==inside_disjunction) {
                return m.mk_eq(first_bare, second_bare);
            }
            else {
                return m.mk_eq(first_bare, m.mk_not(second_bare));
            }
        }

        bool detect_equivalences(expr_ref_vector& v, bool inside_disjunction)
        {
            bool have_pair = false;
            unsigned prev_pair_idx;
            arg_pair ap;

            unsigned read_idx = 0;
            unsigned write_idx = 0;
            while(read_idx<v.size()) {
                expr * e = v[read_idx].get();

                arg_pair new_ap;
                if (match_arg_pair(e, new_ap, inside_disjunction)) {
                    app * neq = 0;
                    if (have_pair) {
                        neq = detect_equivalence(ap, new_ap, inside_disjunction);
                    }
                    if (neq) {
                        have_pair = false;
                        v[prev_pair_idx] = neq;
                        
                        read_idx++;
                        continue;
                    }
                    else {
                        have_pair = true;
                        prev_pair_idx = write_idx;
                        ap = new_ap;
                    }
                }
                else {
                    have_pair = false;
                }

                if (write_idx!=read_idx) {
                    v[write_idx] = e;
                }
                read_idx++;
                write_idx++;
            }
            v.shrink(write_idx);
            return read_idx!=write_idx;
        }

        //bool detect_same_variable_conj_pairs

        br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, 
            proof_ref & result_pr)
        {

            if (m.is_not(f) && (m.is_and(args[0]) || m.is_or(args[0]))) {
                SASSERT(num==1);
                expr_ref tmp(m);
                app* a = to_app(args[0]);
                m_app_args.reset();
                for (unsigned i = 0; i < a->get_num_args(); ++i) {
                    m_brwr.mk_not(a->get_arg(i), tmp);
                    m_app_args.push_back(tmp);
                }
                if (m.is_and(args[0])) {
                    result = m.mk_or(m_app_args.size(), m_app_args.c_ptr());
                }
                else {
                    result = m.mk_and(m_app_args.size(), m_app_args.c_ptr());
                }
                return BR_REWRITE2;
            }
            if (!m.is_and(f) && !m.is_or(f)) { 
                return BR_FAILED; 
            }
            if (num == 0) {
                if (m.is_and(f)) {
                    result = m.mk_true();
                }
                else {
                    result = m.mk_false();
                }
                return BR_DONE;
            }
            if (num == 1) {
                result = args[0];
                return BR_DONE;
            }

            m_app_args.reset();
            m_app_args.append(num, args);

            std::sort(m_app_args.c_ptr(), m_app_args.c_ptr()+m_app_args.size(), m_expr_cmp);

            remove_duplicates(m_app_args);

            bool have_rewritten_args = false;

            have_rewritten_args = detect_equivalences(m_app_args, m.is_or(f));

            if (m_app_args.size()==1) {
                result = m_app_args[0].get();
            }
            else {
                if (m.is_and(f)) {
                    result = m.mk_and(m_app_args.size(), m_app_args.c_ptr());
                }
                else {
                    SASSERT(m.is_or(f));
                    result = m.mk_or(m_app_args.size(), m_app_args.c_ptr());
                }
            }

            if (have_rewritten_args) {
                return BR_REWRITE1;
            }
            return BR_DONE;
        }
    };

    class mk_interp_tail_simplifier::normalizer_rw : public rewriter_tpl<normalizer_cfg> {
    public:
        normalizer_rw(ast_manager& m, normalizer_cfg& cfg): rewriter_tpl<normalizer_cfg>(m, false, cfg) {}
    };


    mk_interp_tail_simplifier::mk_interp_tail_simplifier(context & ctx, unsigned priority)
            : plugin(priority),
              m(ctx.get_manager()),
              m_context(ctx),
              m_simp(ctx.get_rewriter()),
              a(m),
              m_rule_subst(ctx),
              m_tail(m), 
              m_itail_members(m),
              m_conj(m) {
        m_cfg = alloc(normalizer_cfg, m);
        m_rw = alloc(normalizer_rw, m, *m_cfg);
    }

    mk_interp_tail_simplifier::~mk_interp_tail_simplifier() {
        dealloc(m_rw);
        dealloc(m_cfg);
    }
    

    void mk_interp_tail_simplifier::simplify_expr(app * a, expr_ref& res)
    {
        expr_ref simp1_res(m);
        m_simp(a, simp1_res);
        (*m_rw)(simp1_res.get(), res);

        m_simp(res.get(), res);
    }

    bool mk_interp_tail_simplifier::propagate_variable_equivalences(rule * r, rule_ref& res) {
        unsigned u_len = r->get_uninterpreted_tail_size();
        unsigned len = r->get_tail_size();
        if (u_len == len) {
            return false;
        }

        m_todo.reset();
        m_leqs.reset();
        for (unsigned i = u_len; i < len; i++) {
            m_todo.push_back(r->get_tail(i));
            SASSERT(!r->is_neg_tail(i));
        }

        m_rule_subst.reset(r);

        expr_ref_vector trail(m);
        expr_ref tmp1(m), tmp2(m);
        bool found_something = false;

#define TRY_UNIFY(_x,_y) if (m_rule_subst.unify(_x,_y)) { found_something = true; }
#define IS_FLEX(_x) (is_var(_x) || m.is_value(_x))

        while (!m_todo.empty()) {
            expr * arg1, *arg2;
            expr * t0 = m_todo.back();
            m_todo.pop_back();
            expr* t = t0;
            bool neg = m.is_not(t, t);
            if (is_var(t)) {
                TRY_UNIFY(t, neg ? m.mk_false() : m.mk_true());
            }
            else if (!neg && m.is_and(t)) {
                app* a = to_app(t);
                m_todo.append(a->get_num_args(), a->get_args());
            }
            else if (!neg && m.is_eq(t, arg1, arg2) && IS_FLEX(arg1) && IS_FLEX(arg2)) {
                TRY_UNIFY(arg1, arg2);
            }
            else if (m.is_iff(t, arg1, arg2)) {
                //determine the polarity of the equivalence and remove the negations
                while (m.is_not(arg1, arg1)) neg = !neg;
                while (m.is_not(arg2, arg2)) neg = !neg;
                if (!is_var(arg1)) {
                    std::swap(arg1, arg2);
                }
                if (!IS_FLEX(arg1) || !IS_FLEX(arg2)) {
                    // no-op
                }
                else if (is_var(arg1) && !neg) {
                    TRY_UNIFY(arg1, arg2);
                }
                else if (is_var(arg1) && neg && m.is_true(arg2)) {
                    TRY_UNIFY(arg1, m.mk_false());
                }
                else if (is_var(arg1) && neg && m.is_false(arg2)) {
                    TRY_UNIFY(arg1, m.mk_true());
                }
            }
            else if (!neg && (a.is_le(t, arg1, arg2) || a.is_ge(t, arg2, arg1))) {
                tmp1 = a.mk_sub(arg1, arg2);
                tmp2 = a.mk_sub(arg2, arg1);
                if (false && m_leqs.contains(tmp2) && IS_FLEX(arg1) && IS_FLEX(arg2)) {
                    TRY_UNIFY(arg1, arg2);
                }
                else {
                    trail.push_back(tmp1);
                    m_leqs.insert(tmp1);
                }
            }
        }

        if (!found_something) {
            return false;
        }
        TRACE("dl_interp_tail_simplifier_propagation_pre",
                tout << "will propagate rule:\n";
                r->display(m_context, tout);
            );
        m_rule_subst.get_result(res);
        TRACE("dl_interp_tail_simplifier_propagation",
                tout << "propagated equivalences of:\n";
                r->display(m_context, tout);
                tout << "into:\n";
                res->display(m_context, tout);
            );
        return true;
    }

    bool mk_interp_tail_simplifier::transform_rule(rule * r0, rule_ref & res)
    {
        rule_manager& rm = m_context.get_rule_manager();
        rule_ref r(r0, rm);

        if (rm.has_quantifiers(*r)) {
            res = r;
            return true;
        }

    start:
        unsigned u_len = r->get_uninterpreted_tail_size();
        unsigned len = r->get_tail_size();
        if (u_len == len) {
            res = r;
            return true;
        }
        app_ref head(r->get_head(), m);

        m_tail.reset();
        m_tail_neg.reset();

        for (unsigned i=0; i<u_len; i++) {
            m_tail.push_back(r->get_tail(i));
            m_tail_neg.push_back(r->is_neg_tail(i));
        }

        bool modified = false;
        app_ref itail(m);

        if (u_len+1==len) {
            //we have only one interpreted tail
            itail = r->get_tail(u_len);
            SASSERT(!r->is_neg_tail(u_len));
        }
        else {
            m_itail_members.reset();
            for (unsigned i=u_len; i<len; i++) {
                m_itail_members.push_back(r->get_tail(i));
                SASSERT(!r->is_neg_tail(i));
            }
            itail = m.mk_and(m_itail_members.size(), m_itail_members.c_ptr());
            modified = true;
        }

        expr_ref simp_res(m);
        simplify_expr(itail.get(), simp_res);

        modified |= itail.get() != simp_res.get();
        
        if (m.is_false(simp_res)) {
            TRACE("dl", r->display(m_context, tout << "rule is infeasible\n"););
            return false;
        }
        SASSERT(m.is_bool(simp_res));

        if (modified) {
            m_conj.reset();
            flatten_and(simp_res, m_conj);
            for (unsigned i = 0; i < m_conj.size(); ++i) {
                expr* e = m_conj[i].get();
                if (is_app(e)) {
                    m_tail.push_back(to_app(e));
                }
                else {
                    m_tail.push_back(m.mk_eq(e, m.mk_true()));
                }
                m_tail_neg.push_back(false);
            }

            SASSERT(m_tail.size() == m_tail_neg.size());
            res = m_context.get_rule_manager().mk(head, m_tail.size(), m_tail.c_ptr(), m_tail_neg.c_ptr());
            res->set_accounting_parent_object(m_context, r);
        }
        else {
            res = r;
        }

        rule_ref pro_var_eq_result(m_context.get_rule_manager());
        if (propagate_variable_equivalences(res, pro_var_eq_result)) {
            SASSERT(rule_counter().get_max_rule_var(*r.get())==0 || 
                    rule_counter().get_max_rule_var(*r.get()) > rule_counter().get_max_rule_var(*pro_var_eq_result.get()));
            r = pro_var_eq_result;
            goto start;
        }

        CTRACE("dl", (res != r0), r0->display(m_context, tout << "old:\n"); res->display(m_context, tout << "new:\n"););

        return true;
    }

    bool mk_interp_tail_simplifier::transform_rules(const rule_set & orig, rule_set & tgt) {
        bool modified = false;
        rule_manager& rm = m_context.get_rule_manager();
        rule_set::iterator rit = orig.begin();
        rule_set::iterator rend = orig.end();
        for (; rit!=rend; ++rit) {
            rule_ref new_rule(rm);
            if (transform_rule(*rit, new_rule)) {
                rm.mk_rule_rewrite_proof(**rit, *new_rule.get());
                bool is_modified = *rit != new_rule;
                modified |= is_modified;
                tgt.add_rule(new_rule);
            }
            else {
                modified = true;
            }
        }
        return modified;
    }

    rule_set * mk_interp_tail_simplifier::operator()(rule_set const & source) {
        if (source.get_num_rules() == 0) {
            return 0;
        }

        rule_set * res = alloc(rule_set, m_context);
        if (transform_rules(source, *res)) {
            res->inherit_predicates(source);
        } else {
            dealloc(res);
            res = 0;
        }
        return res;
    }
  
};

