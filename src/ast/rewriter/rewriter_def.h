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
#include "ast/ast_pp.h"

template<typename Config>
template<bool ProofGen>
void rewriter_tpl<Config>::process_var(var * v) {
    if (m_cfg.reduce_var(v, m_r, m_pr)) {
        result_stack().push_back(m_r);
        SASSERT(v->get_sort() == m_r->get_sort());
        if (ProofGen) {
            result_pr_stack().push_back(m_pr);
            m_pr = nullptr;
        }
        set_new_child_flag(v);
        TRACE("rewriter", tout << mk_ismt2_pp(v, m()) << " -> " << m_r << "\n";);
        m_r = nullptr;
        return;
    }
    unsigned idx = v->get_idx();
    if (ProofGen) {
        result_pr_stack().push_back(nullptr); // implicit reflexivity
    }
    unsigned index = 0;
    expr * r;
    if (idx < m_bindings.size() && (index = m_bindings.size() - idx - 1, r = m_bindings[index])) {
        CTRACE("rewriter", v->get_sort() != r->get_sort(),
               tout << expr_ref(v, m()) << ":" << sort_ref(v->get_sort(), m()) << " != " << expr_ref(r, m()) << ":" << sort_ref(r->get_sort(), m());
               tout << "index " << index << " bindings " << m_bindings.size() << "\n";
               display_bindings(tout););
        SASSERT(v->get_sort() == r->get_sort());
        if (!is_ground(r) && m_shifts[index] != m_bindings.size()) {            
            unsigned shift_amount = m_bindings.size() - m_shifts[index];
            expr* c = get_cached(r, shift_amount);
            if (c) {
                result_stack().push_back(c);
            }
            else {
                expr_ref tmp(m());
                m_shifter(r, shift_amount, tmp);
                result_stack().push_back(tmp);
                TRACE("rewriter", display_bindings(tout << "shift: " << shift_amount << " idx: " << idx << " --> " << tmp << "\n"););
                cache_shifted_result(r, shift_amount, tmp);                    
            }
        }
        else {
            result_stack().push_back(r);
            TRACE("rewriter", tout << idx << " " << mk_ismt2_pp(r, m()) << "\n";);
        }
        set_new_child_flag(v);
    }
    else {
        result_stack().push_back(v);
    }
}

template<typename Config>
template<bool ProofGen>
bool rewriter_tpl<Config>::process_const(app * t0) {
    app_ref t(t0, m());
    bool retried = false;
 retry:
    SASSERT(t->get_num_args() == 0);
    br_status st = m_cfg.reduce_app(t->get_decl(), 0, nullptr, m_r, m_pr);
    TRACE("reduce_app",
          tout << "t0:" << mk_bounded_pp(t0, m()) << "\n";
          if (t != t0) tout << "t: " << mk_bounded_pp(t, m()) << "\n";
          tout << "st: " << st;
          if (m_r) tout << " --->\n" << mk_bounded_pp(m_r, m());
          tout << "\n";
          if (m_pr) tout << mk_bounded_pp(m_pr, m()) << "\n";
          );
    CTRACE("reduce_app", 
           st != BR_FAILED && m_r->get_sort() != t->get_sort(),
           tout << mk_pp(t->get_sort(), m()) << ": " << mk_pp(t, m()) << "\n";
           tout << m_r->get_id() << " " << mk_pp(m_r->get_sort(), m()) << ": " << m_r << "\n";);
    SASSERT(st != BR_DONE || m_r->get_sort() == t->get_sort());
    switch (st) {
    case BR_FAILED:
        if (!retried) {
            result_stack().push_back(t);
            if (ProofGen)
                result_pr_stack().push_back(nullptr); // implicit reflexivity
            return true;
        }
        m_r = t;
        // fall through
    case BR_DONE:
        result_stack().push_back(m_r.get());
        if (ProofGen) {
            SASSERT(rewrites_from(t0, m_pr));
            SASSERT(rewrites_to(m_r, m_pr));
            if (m_pr)
                result_pr_stack().push_back(m_pr);
            else
                result_pr_stack().push_back(m().mk_rewrite(t0, m_r));
            m_pr = nullptr;
        }
        m_r = nullptr;
        set_new_child_flag(t0);
        return true;
    default: 
        if (is_app(m_r) && to_app(m_r)->get_num_args() == 0) {
            t = to_app(m_r);
            retried = true;
            goto retry;
        }
        return false;
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
    expr *  new_t = nullptr;
    proof * new_t_pr = nullptr;
    if (m_cfg.get_subst(t, new_t, new_t_pr)) {
        TRACE("rewriter_subst", tout << "subst\n" << mk_ismt2_pp(t, m()) << "\n---->\n" << mk_ismt2_pp(new_t, m()) << "\n";);
        SASSERT(t->get_sort() == new_t->get_sort());
        result_stack().push_back(new_t);
        set_new_child_flag(t, new_t);
        SASSERT(rewrites_from(t, new_t_pr));
        SASSERT(rewrites_to(new_t, new_t_pr));
        if (ProofGen)
            result_pr_stack().push_back(new_t_pr);
        return true;
    }
    if (max_depth == 0) {
        result_stack().push_back(t);
        if (ProofGen)
            result_pr_stack().push_back(nullptr); // implicit reflexivity
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
            SASSERT(r->get_sort() == t->get_sort());
            result_stack().push_back(r);
            set_new_child_flag(t, r);
            if (ProofGen) {
                proof * pr = get_cached_pr(t);
                result_pr_stack().push_back(pr);
                SASSERT(rewrites_from(t, pr));
                SASSERT(rewrites_to(r, pr));
            }
            return true;
        }
    }
    if (!pre_visit(t)) {
        result_stack().push_back(t);
        if (ProofGen)
            result_pr_stack().push_back(nullptr); // implicit reflexivity
        return true; // t is not going to be processed
    }
    switch (t->get_kind()) {
    case AST_APP:
        if (to_app(t)->get_num_args() == 0) {
            if (process_const<ProofGen>(to_app(t))) 
                return true; 
            TRACE("rewriter", tout << "process const: " << mk_bounded_pp(t, m()) << " -> " << mk_bounded_pp(m_r,m()) << "\n";);
            t = m_r;
        }
        if (max_depth != RW_UNBOUNDED_DEPTH)
            max_depth--;
        push_frame(t, c, max_depth);
        return false;        
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
        expr* arg = nullptr;
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
            TRACE("rewriter_step", tout << "step\n" << mk_ismt2_pp(t, m()) << "\n";);
            if (visit<false>(arg, fr.m_max_depth)) {
                m_r = result_stack().back();
                result_stack().pop_back();
                result_stack().pop_back();
                result_stack().push_back(m_r);
                cache_result<false>(t, m_r, m_pr, fr.m_cache_result);
                TRACE("rewriter_step", tout << "step 1\n" << mk_ismt2_pp(m_r, m()) << "\n";);
                frame_stack().pop_back();
                set_new_child_flag(t);
            }
            m_r = nullptr;
            return true;
        }
    }
    return false;
}


template<typename Config>
template<bool ProofGen>
void rewriter_tpl<Config>::process_app(app * t, frame & fr) {
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
        expr * const * new_args = result_stack().data() + fr.m_spos;
        app_ref new_t(m());
        if (ProofGen) {
            elim_reflex_prs(fr.m_spos);
            unsigned num_prs    = result_pr_stack().size() - fr.m_spos;
            if (num_prs == 0) {
                new_t = t;
                m_pr  = nullptr;
            }
            else {
                new_t = m().mk_app(f, new_num_args, new_args);
                m_pr  = m().mk_congruence(t, new_t, num_prs, result_pr_stack().data() + fr.m_spos);
                SASSERT(rewrites_from(t, m_pr));
                SASSERT(rewrites_to(new_t, m_pr));
            }
        }
        br_status st = m_cfg.reduce_app(f, new_num_args, new_args, m_r, m_pr2);       
        
        CTRACE("reduce_app", true || st != BR_FAILED || new_t,
               tout << mk_bounded_pp(t, m()) << "\n";
               tout << "st: " << st;
               if (m_r) tout << " --->\n" << mk_bounded_pp(m_r, m());
               tout << "\n";
               if (m_pr2) tout << mk_bounded_pp(m_pr2, m()) << "\n";
               if (new_t) tout << new_t << "\n";
              );
        SASSERT(st == BR_FAILED || rewrites_to(m_r, m_pr2));
        SASSERT(st == BR_FAILED || rewrites_from(new_t, m_pr2));
        SASSERT(st != BR_DONE || m_r->get_sort() == t->get_sort());
        if (st != BR_FAILED) {
            result_stack().shrink(fr.m_spos);
            SASSERT(m_r->get_sort() == t->get_sort());
            result_stack().push_back(m_r);
            if (ProofGen) {
                result_pr_stack().shrink(fr.m_spos);
                if (!m_pr2) {
                    m_pr2 = m().mk_rewrite(new_t, m_r);
                }
                m_pr  = m().mk_transitivity(m_pr, m_pr2);
                result_pr_stack().push_back(m_pr);
                SASSERT(rewrites_to(m_r, m_pr));
                SASSERT(rewrites_from(t, m_pr));
                m_pr2 = nullptr;
            }
            if (st == BR_DONE) {
                cache_result<ProofGen>(t, m_r, m_pr, fr.m_cache_result);
                frame_stack().pop_back();
                set_new_child_flag(t);
                m_r = nullptr;
                if (ProofGen)
                    m_pr = nullptr;
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
                        SASSERT(rewrites_from(t, pr1));
                        SASSERT(rewrites_to(result_stack().back(), pr2));
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
                    m_r = nullptr;
                    if (ProofGen)
                        m_pr = nullptr;
                    return;
                }
                else {
                    // frame was created for processing m_r
                    m_r = nullptr;
                    if (ProofGen)
                        m_pr = nullptr;
                    return;
                }
            }
            UNREACHABLE();
        }
        // TODO: add rewrite rules support
        expr * def = nullptr;
        proof * def_pr = nullptr;
        // When get_macro succeeds, then
        // we know that:
        // forall X. f(X) = def[X]
        // and def_pr is a proof for this quantifier.
        //
        if (get_macro(f, def, def_pr)) {
            SASSERT(!f->is_associative() || !flat_assoc(f));
            SASSERT(new_num_args == t->get_num_args());
            SASSERT(def->get_sort() == t->get_sort());
            if (is_ground(def) && !m_cfg.reduce_macro()) {
                m_r = def;
                if (ProofGen) {
                    m_pr = m().mk_transitivity(m_pr, def_pr);
                }
            }
            else {
                if (ProofGen) {
                    NOT_IMPLEMENTED_YET();
                    // We do not support the use of bindings in proof generation mode.
                    // Thus we have to apply the substitution here, and
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
                    m_root      = def;
                    push_frame(def, false, RW_UNBOUNDED_DEPTH);
                    return;
                }
            }
        }
        else {
            if (fr.m_new_child) {
                m_r = m().mk_app(f, new_num_args, new_args);
                if (ProofGen) {
                    m_pr = m().mk_rewrite(t, m_r);
                }
            }
            else {
                TRACE("rewriter_reuse", tout << "reusing:\n" << mk_ismt2_pp(t, m()) << "\n";);
                m_r = t;
            }
        }
        result_stack().shrink(fr.m_spos);
        result_stack().push_back(m_r);
        cache_result<ProofGen>(t, m_r, m_pr, fr.m_cache_result);
        if (ProofGen) {
            result_pr_stack().shrink(fr.m_spos);
            result_pr_stack().push_back(m_pr);
            m_pr = nullptr;
        }
        frame_stack().pop_back();
        set_new_child_flag(t, m_r);
        m_r = nullptr;
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
                m_r = std::move(tmp);
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
        begin_scope();
        m_root       = q->get_expr();
        unsigned sz = m_bindings.size();
        for (unsigned i = 0; i < num_decls; i++) {
            m_bindings.push_back(nullptr);
            m_shifts.push_back(sz);
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
    expr * const * it = result_stack().data() + fr.m_spos;
    expr * new_body   = *it;
    unsigned num_pats = q->get_num_patterns();
    unsigned num_no_pats = q->get_num_no_patterns();
    expr_ref_vector new_pats(m_manager, num_pats, q->get_patterns());
    expr_ref_vector new_no_pats(m_manager, num_no_pats, q->get_no_patterns());
    if (rewrite_patterns()) {
        TRACE("reduce_quantifier_bug", tout << "rewrite patterns\n";);
        expr * const * np  = it + 1;
        expr * const * nnp = np + num_pats;
        unsigned j = 0;
        for (unsigned i = 0; i < num_pats; i++)
            if (m_manager.is_pattern(np[i]))
                new_pats[j++] = np[i];
        new_pats.shrink(j);
        num_pats = j;
        j = 0;
        for (unsigned i = 0; i < num_no_pats; i++)
            if (m_manager.is_pattern(nnp[i]))
                new_no_pats[j++] = nnp[i];
        new_no_pats.shrink(j);
        num_no_pats = j;
    }
    if (ProofGen) {
        quantifier_ref new_q(m().update_quantifier(q, num_pats, new_pats.data(), num_no_pats, new_no_pats.data(), new_body), m());
        m_pr = nullptr;
        if (q != new_q) {
            m_pr = result_pr_stack().get(fr.m_spos);
            if (m_pr) {
                m_pr = m().mk_bind_proof(q, m_pr);
                m_pr = m().mk_quant_intro(q, new_q, m_pr);
            }
            else {
                m_pr = m().mk_rewrite(q, new_q);
            }
        }
        m_r = new_q;
        proof_ref pr2(m());
        if (m_cfg.reduce_quantifier(new_q, new_body, new_pats.data(), new_no_pats.data(), m_r, pr2)) {
            m_pr = m().mk_transitivity(m_pr, pr2);
        }
        TRACE("reduce_quantifier_bug",if (m_pr) tout << mk_ismt2_pp(m_pr, m()) << "\n"; else tout << "m_pr is_null\n";);
        result_pr_stack().shrink(fr.m_spos);
        result_pr_stack().push_back(m_pr);
    }
    else {
        TRACE("reduce_quantifier_bug", tout << mk_ismt2_pp(q, m()) << " " << mk_ismt2_pp(new_body, m()) << "\n";);
        if (!m_cfg.reduce_quantifier(q, new_body, new_pats.data(), new_no_pats.data(), m_r, m_pr)) {
            if (fr.m_new_child) {
                m_r = m().update_quantifier(q, num_pats, new_pats.data(), num_no_pats, new_no_pats.data(), new_body);
            }
            else {
                TRACE("rewriter_reuse", tout << "reusing:\n" << mk_ismt2_pp(q, m()) << "\n";);
                m_r = q;
            }
        }
    }
    result_stack().shrink(fr.m_spos);
    result_stack().push_back(m_r.get());
    SASSERT(q->get_sort() == m_r->get_sort());
    SASSERT(num_decls <= m_bindings.size());
    m_bindings.shrink(m_bindings.size() - num_decls);
    m_shifts.shrink(m_shifts.size() - num_decls);
    end_scope();
    cache_result<ProofGen>(q, m_r, m_pr, fr.m_cache_result);
    m_r = nullptr;
    m_pr = nullptr;
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
    for (unsigned i = 0; i < m_bindings.size(); i++) {
        if (m_bindings[i])
            out << i << ": " << mk_ismt2_pp(m_bindings[i], m()) << ";\n";
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
    SCTRACE("bindings", is_trace_enabled("coming_from_quant"), display_bindings(tout););
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
    SCTRACE("bindings", is_trace_enabled("coming_from_quant"), display_bindings(tout););
}

template<typename Config>
void rewriter_tpl<Config>::update_inv_binding_at(unsigned i, expr* binding) {
    m_bindings[i] = binding;
}

template<typename Config>
void rewriter_tpl<Config>::update_binding_at(unsigned i, expr* binding) {
    m_bindings[m_bindings.size() - i - 1] = binding;
}


template<typename Config>
template<bool ProofGen>
void rewriter_tpl<Config>::main_loop(expr * t, expr_ref & result, proof_ref & result_pr) {
    result_pr = nullptr;
    if (!m().inc()) {
        if (m_cancel_check) {
            reset();
            throw rewriter_exception(m().limit().get_cancel_msg());
        }
        result = t;
        return;
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
            if (result_pr.get() == nullptr)
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
        if (!m().inc()) {
            if (m_cancel_check) {
                reset();
                throw rewriter_exception(m().limit().get_cancel_msg());
            }
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
                SASSERT(r->get_sort() == t->get_sort());
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
        if (result_pr.get() == nullptr)
            result_pr = m().mk_reflexivity(m_root);
        SASSERT(result_pr_stack().empty());
    }
}

template<typename Config>
void rewriter_tpl<Config>::operator()(expr * t, expr_ref & result, proof_ref & result_pr) {
    if (!frame_stack().empty() || m_cache != m_cache_stack[0]) {
        frame_stack().reset();
        result_stack().reset();
        result_pr_stack().reset();
        m_scopes.reset();
        reset_cache();
    }

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
