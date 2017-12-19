/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    rewriter_def.h

Abstract:

    Lean and mean rewriter

Author:

    Leonardo (leonardo) 2011-03-31

Notes:

--*/
#include "ast/rewriter/rewriter.h"
#include "ast/ast_smt2_pp.h"
#include "ast/ast_ll_pp.h"

template<typename Config>
template<bool ProofGen>
void rewriter_tpl<Config>::process_var(var * v) {
    if (m_cfg.reduce_var(v, m_r, m_pr)) {
        result_stack().push_back(m_r);
        SASSERT(v->get_sort() == m().get_sort(m_r));
        if (ProofGen) {
            result_pr_stack().push_back(m_pr);
            m_pr = 0;
        }
        set_new_child_flag(v);
        TRACE("rewriter", tout << mk_ismt2_pp(v, m()) << " -> " << m_r << "\n";);
        m_r = 0;
        return;
    }
    if (!ProofGen) {
        // bindings are only used when Proof Generation is not enabled.
        unsigned idx = v->get_idx();
        if (idx < m_bindings.size()) {
            unsigned index = m_bindings.size() - idx - 1;
            var * r = (var*)(m_bindings[index]);
            if (r != 0) {
                CTRACE("rewriter", v->get_sort() != m().get_sort(r),
                       tout << expr_ref(v, m()) << ":" << sort_ref(v->get_sort(), m()) << " != " << expr_ref(r, m()) << ":" << sort_ref(m().get_sort(r), m());
                       tout << "index " << index << " bindings " << m_bindings.size() << "\n";
                       display_bindings(tout););
                SASSERT(v->get_sort() == m().get_sort(r));
                if (!is_ground(r) && m_shifts[index] != m_bindings.size()) {

                    unsigned shift_amount = m_bindings.size() - m_shifts[index];
                    expr_ref tmp(m());
                    m_shifter(r, shift_amount, tmp);
                    result_stack().push_back(tmp);
                    TRACE("rewriter", tout << "shift: " << shift_amount << " idx: " << idx << " --> " << tmp << "\n";
                          display_bindings(tout););
                }
                else {
                    result_stack().push_back(r);
                    TRACE("rewriter", tout << idx << " " << mk_ismt2_pp(r, m()) << "\n";);
                }
                set_new_child_flag(v);
                return;
            }
        }
    }
    result_stack().push_back(v);
    if (ProofGen)
        result_pr_stack().push_back(0); // implicit reflexivity
}

template<typename Config>
template<bool ProofGen>
void rewriter_tpl<Config>::process_const(app * t) {
    SASSERT(t->get_num_args() == 0);
    br_status st = m_cfg.reduce_app(t->get_decl(), 0, 0, m_r, m_pr);
    SASSERT(st != BR_DONE || m().get_sort(m_r) == m().get_sort(t));
    SASSERT(st == BR_FAILED || st == BR_DONE);
    if (st == BR_DONE) {
        result_stack().push_back(m_r.get());
        if (ProofGen) {
            if (m_pr)
                result_pr_stack().push_back(m_pr);
            else
                result_pr_stack().push_back(m().mk_rewrite(t, m_r));
            m_pr = 0;
        }
        m_r = 0;
        set_new_child_flag(t);
    }
    else {
        result_stack().push_back(t);
        if (ProofGen)
            result_pr_stack().push_back(0); // implicit reflexivity
    }
}

/**
   \brief visit expression t. Return true if t was rewritten and the result is on the top m_result_stack.
   We may skip t if:
      - pre_visit(t) returns false
      - max_depth == 0
      - t is already in the cache
   Otherwise, return false and add a new frame stack for t with the updated max_depth.
*/
template<typename Config>
template<bool ProofGen>
bool rewriter_tpl<Config>::visit(expr * t, unsigned max_depth) {
    TRACE("rewriter_visit", tout << "visiting\n" << mk_ismt2_pp(t, m()) << "\n";);
    expr *  new_t = 0;
    proof * new_t_pr = 0;
    if (m_cfg.get_subst(t, new_t, new_t_pr)) {
        TRACE("rewriter_subst", tout << "subst\n" << mk_ismt2_pp(t, m()) << "\n---->\n" << mk_ismt2_pp(new_t, m()) << "\n";);
        SASSERT(m().get_sort(t) == m().get_sort(new_t));
        result_stack().push_back(new_t);
        set_new_child_flag(t, new_t);
        if (ProofGen)
            result_pr_stack().push_back(new_t_pr);
        return true;
    }
    if (max_depth == 0) {
        result_stack().push_back(t);
        if (ProofGen)
            result_pr_stack().push_back(0); // implicit reflexivity
        return true; // t is not going to be processed
    }
    SASSERT(max_depth > 0);
    SASSERT(max_depth <= RW_UNBOUNDED_DEPTH);
    bool c = must_cache(t);
    if (c) {
#if 0
        static unsigned checked_cache = 0;
        checked_cache ++;
        if (checked_cache % 100000 == 0)
            std::cerr << "[rewriter] num-cache-checks: " << checked_cache << std::endl;
#endif
        expr * r = get_cached(t);
        if (r) {
            SASSERT(m().get_sort(r) == m().get_sort(t));
            result_stack().push_back(r);
            set_new_child_flag(t, r);
            if (ProofGen) {
                proof * pr = get_cached_pr(t);
                result_pr_stack().push_back(pr);
            }
            return true;
        }
    }
    if (!pre_visit(t)) {
        result_stack().push_back(t);
        if (ProofGen)
            result_pr_stack().push_back(0); // implicit reflexivity
        return true; // t is not going to be processed
    }
    switch (t->get_kind()) {
    case AST_APP:
        if (to_app(t)->get_num_args() == 0) {
            process_const<ProofGen>(to_app(t));
            return true;
        }
        else {
            if (max_depth != RW_UNBOUNDED_DEPTH)
                max_depth--;
            push_frame(t, c, max_depth);
            return false;
        }
    case AST_VAR:
        process_var<ProofGen>(to_var(t));
        return true;
    case AST_QUANTIFIER:
        if (max_depth != RW_UNBOUNDED_DEPTH)
            max_depth--;
        push_frame(t, c, max_depth);
        return false;
    default:
        UNREACHABLE();
        return true;
    }
}

template<typename Config>
bool rewriter_tpl<Config>::constant_fold(app * t, frame & fr) {
    if (fr.m_i == 1 && m().is_ite(t)) {
        expr * cond = result_stack()[fr.m_spos].get();
        expr* arg = 0;
        if (m().is_true(cond)) {
            arg = t->get_arg(1);
        }
        else if (m().is_false(cond)) {
            arg = t->get_arg(2);
        }
        if (arg) {
            result_stack().shrink(fr.m_spos);
            result_stack().push_back(arg);
            fr.m_state = REWRITE_BUILTIN;
            if (visit<false>(arg, fr.m_max_depth)) {
                m_r = result_stack().back();
                result_stack().pop_back();
                result_stack().pop_back();
                result_stack().push_back(m_r);
                cache_result<false>(t, m_r, m_pr, fr.m_cache_result);
                frame_stack().pop_back();
                set_new_child_flag(t);
            }
            m_r = 0;
            return true;
        }
    }
    return false;
}

template<typename Config>
template<bool ProofGen>
void rewriter_tpl<Config>::process_app(app * t, frame & fr) {
    SASSERT(t->get_num_args() > 0);
    SASSERT(!frame_stack().empty());
    switch (fr.m_state) {
    case PROCESS_CHILDREN: {
        unsigned num_args = t->get_num_args();
        while (fr.m_i < num_args) {
            if (!ProofGen && constant_fold(t, fr)) {
                return;
            }
            expr * arg = t->get_arg(fr.m_i);
            fr.m_i++;
            if (!visit<ProofGen>(arg, fr.m_max_depth))
                return;


        }
        func_decl * f = t->get_decl();

        // If AC flattening is enabled, f is associative, t is not shared, and there is a previous frame on the stack.
        if (!ProofGen) {
            // this optimization is only used when Proof generation is disabled.
            if (f->is_associative() && t->get_ref_count() <= 1 && frame_stack().size() > 1) {
                frame & prev_fr = frame_stack()[frame_stack().size() - 2];
                if (is_app(prev_fr.m_curr) &&
                    to_app(prev_fr.m_curr)->get_decl() == f &&
                    prev_fr.m_state == PROCESS_CHILDREN &&
                    flat_assoc(f)) {
                    frame_stack().pop_back();
                    set_new_child_flag(t);
                    return;
                }
            }
        }

        unsigned new_num_args   = result_stack().size() - fr.m_spos;
        expr * const * new_args = result_stack().c_ptr() + fr.m_spos;
        app * new_t;
        if (ProofGen) {
            elim_reflex_prs(fr.m_spos);
            unsigned num_prs    = result_pr_stack().size() - fr.m_spos;
            if (num_prs == 0) {
                new_t = t;
                m_pr  = 0;
            }
            else {
                new_t = m().mk_app(f, new_num_args, new_args);
                m_pr  = m().mk_congruence(t, new_t, num_prs, result_pr_stack().c_ptr() + fr.m_spos);
            }
        }
        br_status st = m_cfg.reduce_app(f, new_num_args, new_args, m_r, m_pr2);
        SASSERT(st != BR_DONE || m().get_sort(m_r) == m().get_sort(t));
        CTRACE("reduce_app", st != BR_FAILED,
              tout << mk_bounded_pp(t, m()) << "\n";
              tout << "st: " << st;
              if (m_r) tout << " --->\n" << mk_bounded_pp(m_r, m());
              tout << "\n";);
        if (st != BR_FAILED) {
            result_stack().shrink(fr.m_spos);
            SASSERT(m().get_sort(m_r) == m().get_sort(t));
            result_stack().push_back(m_r);
            if (ProofGen) {
                result_pr_stack().shrink(fr.m_spos);
                if (!m_pr2)
                    m_pr2 = m().mk_rewrite(new_t, m_r);
                m_pr  = m().mk_transitivity(m_pr, m_pr2);
                m_pr2 = 0;
                result_pr_stack().push_back(m_pr);
            }
            if (st == BR_DONE) {
                cache_result<ProofGen>(t, m_r, m_pr, fr.m_cache_result);
                frame_stack().pop_back();
                set_new_child_flag(t);
                m_r = 0;
                if (ProofGen)
                    m_pr = 0;
                return;
            }
            else {
                fr.m_state = REWRITE_BUILTIN;
                SASSERT(st == BR_REWRITE1 || st == BR_REWRITE2 || st == BR_REWRITE3 || st == BR_REWRITE_FULL);
                unsigned max_depth = static_cast<unsigned>(st);
                SASSERT(0 <= max_depth && max_depth <= RW_UNBOUNDED_DEPTH);
                SASSERT((st == BR_REWRITE1) == (max_depth == 0));
                SASSERT((st == BR_REWRITE2) == (max_depth == 1));
                SASSERT((st == BR_REWRITE3) == (max_depth == 2));
                SASSERT((st == BR_REWRITE_FULL) == (max_depth == RW_UNBOUNDED_DEPTH));
                if (max_depth != RW_UNBOUNDED_DEPTH)
                    max_depth++;
                if (visit<ProofGen>(m_r, max_depth)) {
                    if (ProofGen) {
                        proof_ref pr2(m()), pr1(m());
                        pr2 = result_pr_stack().back();
                        result_pr_stack().pop_back();
                        pr1 = result_pr_stack().back();
                        result_pr_stack().pop_back();
                        m_pr = m().mk_transitivity(pr1, pr2);
                        result_pr_stack().push_back(m_pr);
                    }
                    m_r = result_stack().back();
                    result_stack().pop_back();
                    result_stack().pop_back();
                    result_stack().push_back(m_r);
                    cache_result<ProofGen>(t, m_r, m_pr, fr.m_cache_result);
                    frame_stack().pop_back();
                    set_new_child_flag(t);
                    m_r = 0;
                    if (ProofGen)
                        m_pr = 0;
                    return;
                }
                else {
                    // frame was created for processing m_r
                    m_r = 0;
                    if (ProofGen)
                        m_pr = 0;
                    return;
                }
            }
            UNREACHABLE();
        }
        // TODO: add rewrite rules support
        expr * def;
        proof * def_pr;
        quantifier * def_q;
        // When get_macro succeeds, then
        // we know that:
        // forall X. f(X) = def[X]
        // and def_pr is a proof for this quantifier.
        //
        // Remark: def_q is only used for proof generation.
        // It is the quantifier forall X. f(X) = def[X]
        if (get_macro(f, def, def_q, def_pr)) {
            SASSERT(!f->is_associative() || !flat_assoc(f));
            SASSERT(new_num_args == t->get_num_args());
            SASSERT(m().get_sort(def) == m().get_sort(t));
            if (is_ground(def)) {
                m_r = def;
                if (ProofGen) {
                    m_pr = m().mk_transitivity(m_pr, def_pr);
                }
            }
            else {
                if (ProofGen) {
                    NOT_IMPLEMENTED_YET();
                    // We do not support the use of bindings in proof generation mode.
                    // Thus we have to apply the subsitution here, and
                    // beta_reducer subst(m());
                    // subst.set_bindings(new_num_args, new_args);
                    // expr_ref r2(m());
                    // subst(def, r2);
                }
                else {
                    fr.m_state = EXPAND_DEF;
                    TRACE("get_macro", tout << "f: " << f->get_name() << ", def: \n" << mk_ismt2_pp(def, m()) << "\n";
                          tout << "Args num: " << num_args << "\n";
                          for (unsigned i = 0; i < num_args; i++) tout << mk_ismt2_pp(new_args[i], m()) << "\n";);
                    unsigned sz = m_bindings.size();
                    unsigned i = num_args;
                    while (i > 0) {
                        --i;
                        m_bindings.push_back(new_args[i]); // num_args - i - 1]);
                        m_shifts.push_back(sz);
                    }
                    result_stack().push_back(def);
                    TRACE("get_macro", display_bindings(tout););
                    begin_scope();
                    m_num_qvars += num_args;
                    //m_num_qvars = 0;
                    m_root      = def;
                    push_frame(def, false, RW_UNBOUNDED_DEPTH);
                    return;
                }
            }
        }
        else {
            if (ProofGen) {
                m_r = new_t;
            }
            else {
                if (fr.m_new_child) {
                    m_r = m().mk_app(f, new_num_args, new_args);
                }
                else {
                    TRACE("rewriter_reuse", tout << "reusing:\n" << mk_ismt2_pp(t, m()) << "\n";);
                    m_r = t;
                }
            }
        }
        result_stack().shrink(fr.m_spos);
        result_stack().push_back(m_r);
        cache_result<ProofGen>(t, m_r, m_pr, fr.m_cache_result);
        if (ProofGen) {
            result_pr_stack().shrink(fr.m_spos);
            result_pr_stack().push_back(m_pr);
            m_pr = 0;
        }
        frame_stack().pop_back();
        set_new_child_flag(t, m_r);
        m_r = 0;
        return;
    }
    case REWRITE_BUILTIN:
        SASSERT(fr.m_spos + 2 == result_stack().size());
        if (ProofGen) {
            proof_ref pr2(m()), pr1(m());
            pr2 = result_pr_stack().back();
            result_pr_stack().pop_back();
            pr1 = result_pr_stack().back();
            result_pr_stack().pop_back();
            m_pr = m().mk_transitivity(pr1, pr2);
            result_pr_stack().push_back(m_pr);
        }
        m_r = result_stack().back();
        result_stack().pop_back();
        result_stack().pop_back();
        result_stack().push_back(m_r);
        cache_result<ProofGen>(t, m_r, m_pr, fr.m_cache_result);
        frame_stack().pop_back();
        set_new_child_flag(t);
        return;
    case EXPAND_DEF:
        SASSERT(fr.m_spos + t->get_num_args() + 2 == result_stack().size());
        SASSERT(t->get_num_args() <= m_bindings.size());
        if (!ProofGen) {
            expr_ref tmp(m());
            unsigned num_args = t->get_num_args();
            m_bindings.shrink(m_bindings.size() - num_args);
            m_shifts.shrink(m_shifts.size() - num_args);
            m_num_qvars -= num_args;
            end_scope();
            m_r = result_stack().back();
            if (!is_ground(m_r)) {
                m_inv_shifter(m_r, num_args, tmp);
                m_r = tmp;
            }
            result_stack().shrink(fr.m_spos);
            result_stack().push_back(m_r);
            cache_result<ProofGen>(t, m_r, m_pr, fr.m_cache_result);
            frame_stack().pop_back();
            set_new_child_flag(t);
        }
        else {
            // TODO
            NOT_IMPLEMENTED_YET();
        }
        return;
    case REWRITE_RULE:
        // support for rewriting rules was not implemented yet.
        NOT_IMPLEMENTED_YET();
        break;
    default:
        UNREACHABLE();
        break;
    }
}

template<typename Config>
template<bool ProofGen>
void rewriter_tpl<Config>::process_quantifier(quantifier * q, frame & fr) {
    SASSERT(fr.m_state == PROCESS_CHILDREN);
    unsigned num_decls = q->get_num_decls();
    if (fr.m_i == 0) {
        if (!ProofGen) {
            begin_scope();
            m_root       = q->get_expr();
            unsigned sz = m_bindings.size();
            for (unsigned i = 0; i < num_decls; i++) {
                m_bindings.push_back(0);
                m_shifts.push_back(sz);
            }
        }
        m_num_qvars += num_decls;
    }
    unsigned num_children = rewrite_patterns() ? q->get_num_children() : 1;
    while (fr.m_i < num_children) {
        expr * child = q->get_child(fr.m_i);
        fr.m_i++;
        if (!visit<ProofGen>(child, fr.m_max_depth)) {
            return;
        }
    }
    SASSERT(fr.m_spos + num_children == result_stack().size());
    expr * const * it = result_stack().c_ptr() + fr.m_spos;
    expr * new_body   = *it;
    expr * const * new_pats;
    expr * const * new_no_pats;
    if (rewrite_patterns()) {
        TRACE("reduce_quantifier_bug", tout << "rewrite patterns\n";);
        new_pats    = it + 1;
        new_no_pats = new_pats + q->get_num_patterns();
    }
    else {
        new_pats    = q->get_patterns();
        new_no_pats = q->get_no_patterns();
    }
    if (ProofGen) {
        quantifier_ref new_q(m().update_quantifier(q, q->get_num_patterns(), new_pats, q->get_num_no_patterns(), new_no_pats, new_body), m());
        m_pr = q == new_q ? 0 : m().mk_quant_intro(q, new_q, result_pr_stack().get(fr.m_spos));
        m_r = new_q;
        proof_ref pr2(m());
        if (m_cfg.reduce_quantifier(new_q, new_body, new_pats, new_no_pats, m_r, pr2)) {
            m_pr = m().mk_transitivity(m_pr, pr2);
        }
        TRACE("reduce_quantifier_bug", tout << "m_pr is_null: " << (m_pr.get() == 0) << "\n";
              if (m_pr) tout << mk_ismt2_pp(m_pr, m()) << "\n";);
        result_pr_stack().shrink(fr.m_spos);
        result_pr_stack().push_back(m_pr);
    }
    else {
        expr_ref tmp(m());
        TRACE("reduce_quantifier_bug", tout << mk_ismt2_pp(q, m()) << " " << mk_ismt2_pp(new_body, m()) << "\n";);
        if (!m_cfg.reduce_quantifier(q, new_body, new_pats, new_no_pats, m_r, m_pr)) {
            if (fr.m_new_child) {
                m_r = m().update_quantifier(q, q->get_num_patterns(), new_pats, q->get_num_no_patterns(), new_no_pats, new_body);
            }
            else {
                TRACE("rewriter_reuse", tout << "reusing:\n" << mk_ismt2_pp(q, m()) << "\n";);
                m_r = q;
            }
        }
    }
    result_stack().shrink(fr.m_spos);
    result_stack().push_back(m_r.get());
    SASSERT(m().is_bool(m_r));
    if (!ProofGen) {
        SASSERT(num_decls <= m_bindings.size());
        m_bindings.shrink(m_bindings.size() - num_decls);
        m_shifts.shrink(m_shifts.size() - num_decls);
        end_scope();
        cache_result<ProofGen>(q, m_r, m_pr, fr.m_cache_result);
    }
    else {
        cache_result<ProofGen>(q, m_r, m_pr, fr.m_cache_result);
        m_pr = 0;
    }
    m_r = 0;
    frame_stack().pop_back();
    set_new_child_flag(q, m_r);
}

template<typename Config>
bool rewriter_tpl<Config>::not_rewriting() const {
    SASSERT(frame_stack().empty());
    SASSERT(m_cache == m_cache_stack[0]);
    return true;
}

template<typename Config>
rewriter_tpl<Config>::rewriter_tpl(ast_manager & m, bool proof_gen, Config & cfg):
    rewriter_core(m, proof_gen),
    m_cfg(cfg),
    m_num_steps(0),
    m_shifter(m),
    m_inv_shifter(m),
    m_r(m),
    m_pr(m),
    m_pr2(m) {
}

template<typename Config>
rewriter_tpl<Config>::~rewriter_tpl() {
}

template<typename Config>
void rewriter_tpl<Config>::reset() {
    m_cfg.reset();
    rewriter_core::reset();
    m_bindings.reset();
    m_shifts.reset();
    m_shifter.reset();
    m_inv_shifter.reset();
}

template<typename Config>
void rewriter_tpl<Config>::cleanup() {
    m_cfg.cleanup();
    rewriter_core::cleanup();
    m_bindings.finalize();
    m_shifter.cleanup();
    m_shifts.finalize();
    m_inv_shifter.cleanup();
}

template<typename Config>
void rewriter_tpl<Config>::display_bindings(std::ostream& out) {
    out << "bindings:\n";
    for (unsigned i = 0; i < m_bindings.size(); i++) {
        if (m_bindings[i])
            out << i << ": " << mk_ismt2_pp(m_bindings[i], m()) << "\n";
    }
}

template<typename Config>
void rewriter_tpl<Config>::set_bindings(unsigned num_bindings, expr * const * bindings) {
    SASSERT(!m_proof_gen);
    SASSERT(not_rewriting());
    m_bindings.reset();
    m_shifts.reset();
    unsigned i = num_bindings;
    while (i > 0) {
        --i;
        m_bindings.push_back(bindings[i]);
        m_shifts.push_back(num_bindings);
    }
    TRACE("rewriter", display_bindings(tout););
}

template<typename Config>
void rewriter_tpl<Config>::set_inv_bindings(unsigned num_bindings, expr * const * bindings) {
    SASSERT(!m_proof_gen);
    SASSERT(not_rewriting());
    m_bindings.reset();
    m_shifts.reset();
    for (unsigned i = 0; i < num_bindings; i++) {
        m_bindings.push_back(bindings[i]);
        m_shifts.push_back(num_bindings);
    }
    TRACE("rewriter", display_bindings(tout););
}

template<typename Config>
template<bool ProofGen>
void rewriter_tpl<Config>::main_loop(expr * t, expr_ref & result, proof_ref & result_pr) {
    if (m_cancel_check && m().canceled()) {
        reset();
        throw rewriter_exception(m().limit().get_cancel_msg());
    }
    SASSERT(!ProofGen || result_stack().size() == result_pr_stack().size());
    SASSERT(not_rewriting());
    m_root      = t;
    m_num_qvars = 0;
    m_num_steps = 0;
    if (visit<ProofGen>(t, RW_UNBOUNDED_DEPTH)) {
        result = result_stack().back();
        result_stack().pop_back();
        SASSERT(result_stack().empty());
        if (ProofGen) {
            result_pr = result_pr_stack().back();
            result_pr_stack().pop_back();
            if (result_pr.get() == 0)
                result_pr = m().mk_reflexivity(t);
            SASSERT(result_pr_stack().empty());
        }
    }
    else {
        resume_core<ProofGen>(result, result_pr);
    }
    TRACE("rewriter", tout << mk_ismt2_pp(t, m()) << "\n=>\n" << result << "\n";;);
}

/**
   \brief Resume the execution when it was interrupted by cancel() or check_max_steps().
*/
template<typename Config>
template<bool ProofGen>
void rewriter_tpl<Config>::resume_core(expr_ref & result, proof_ref & result_pr) {
    SASSERT(!frame_stack().empty());
    while (!frame_stack().empty()) {
        if (m_cancel_check && m().canceled()) {
            reset();
            throw rewriter_exception(m().limit().get_cancel_msg());
        }
        SASSERT(!ProofGen || result_stack().size() == result_pr_stack().size());
        frame & fr = frame_stack().back();
        expr * t   = fr.m_curr;
        TRACE("rewriter_step", tout << "step\n" << mk_ismt2_pp(t, m()) << "\n";);
        m_num_steps++;
        check_max_steps();
        if (first_visit(fr) && fr.m_cache_result) {
            expr * r = get_cached(t);
            if (r) {
                SASSERT(m().get_sort(r) == m().get_sort(t));
                result_stack().push_back(r);
                if (ProofGen) {
                    proof * pr = get_cached_pr(t);
                    result_pr_stack().push_back(pr);
                }
                frame_stack().pop_back();
                set_new_child_flag(t, r);
                continue;
            }
        }
        switch (t->get_kind()) {
        case AST_APP:
            process_app<ProofGen>(to_app(t), fr);
            break;
        case AST_QUANTIFIER:
            process_quantifier<ProofGen>(to_quantifier(t), fr);
            break;
        case AST_VAR:
            frame_stack().pop_back();
            process_var<ProofGen>(to_var(t));
            break;
        default:
            UNREACHABLE();
            break;
        }
    }
    result = result_stack().back();
    result_stack().pop_back();
    SASSERT(result_stack().empty());
    if (ProofGen) {
        result_pr = result_pr_stack().back();
        result_pr_stack().pop_back();
        if (result_pr.get() == 0)
            result_pr = m().mk_reflexivity(m_root);
        SASSERT(result_pr_stack().empty());
    }
}

template<typename Config>
void rewriter_tpl<Config>::operator()(expr * t, expr_ref & result, proof_ref & result_pr) {
    if (m_proof_gen)
        main_loop<true>(t, result, result_pr);
    else
        main_loop<false>(t, result, result_pr);
}

template<typename Config>
void rewriter_tpl<Config>::resume(expr_ref & result, proof_ref & result_pr) {
    if (m_proof_gen)
        resume_core<true>(result, result_pr);
    else
        resume_core<false>(result, result_pr);
}
