/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    rewriter.cpp

Abstract:

    Lean and mean rewriter

Author:

    Leonardo (leonardo) 2011-03-31

Notes:

--*/
#include "ast/rewriter/rewriter_def.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_smt2_pp.h"

void rewriter_core::init_cache_stack() {
    SASSERT(m_cache_stack.empty());
    m_cache = alloc(cache, m());
    m_cache_stack.push_back(m_cache);
    if (m_proof_gen) {
        SASSERT(m_cache_pr_stack.empty());
        m_cache_pr = alloc(cache, m());
        m_cache_pr_stack.push_back(m_cache_pr);
    }
}

void rewriter_core::del_cache_stack() {
    std::for_each(m_cache_stack.begin(), m_cache_stack.end(), delete_proc<cache>());
    m_cache_stack.finalize();
    m_cache = nullptr;
    if (m_proof_gen) {
        std::for_each(m_cache_pr_stack.begin(), m_cache_pr_stack.end(), delete_proc<cache>());
        m_cache_pr_stack.finalize();
        m_cache_pr = nullptr;
    }
}

void rewriter_core::cache_result(expr * k, expr * v) {
#if 0
    // trace for tracking cache usage
    verbose_stream() << "1 " << k->get_id() << std::endl;
#endif
    SASSERT(!m_proof_gen);
    
    TRACE("rewriter_cache_result", tout << mk_ismt2_pp(k, m()) << "\n--->\n" << mk_ismt2_pp(v, m()) << "\n";);

    SASSERT(m().get_sort(k) == m().get_sort(v));

    m_cache->insert(k, v);
#if 0
    static unsigned num_cached = 0;
    num_cached ++;
    if (num_cached % 100000 == 0)
        verbose_stream() << "[rewriter] :num-cached " << num_cached << " :capacity " << m_cache->capacity() << " :size " << m_cache->size() 
                  << " :frame-stack-size " << m_frame_stack.size() << std::endl;
#endif
}

void rewriter_core::cache_result(expr * k, expr * v, proof * pr) {
    m_cache->insert(k, v);
    SASSERT(m_proof_gen);
    m_cache_pr->insert(k, pr);
}

unsigned rewriter_core::get_cache_size() const {
    return m_cache->size();
}

void rewriter_core::reset_cache() {
    m_cache = m_cache_stack[0];
    m_cache->reset();
    if (m_proof_gen) {
        m_cache_pr = m_cache_pr_stack[0];
        m_cache_pr->reset();
    }
}

// free memory allocated by the rewriter
void rewriter_core::free_memory() {
    del_cache_stack();
    m_frame_stack.finalize();
    m_result_stack.finalize();
    m_scopes.finalize();
}

void rewriter_core::begin_scope() {
    m_scopes.push_back(scope(m_root, m_num_qvars));
    unsigned lvl = m_scopes.size();
    SASSERT(lvl <= m_cache_stack.size());
    SASSERT(!m_proof_gen || m_cache_pr_stack.size() == m_cache_stack.size());
    if (lvl == m_cache_stack.size()) {
        m_cache_stack.push_back(alloc(cache, m()));
        if (m_proof_gen)
            m_cache_pr_stack.push_back(alloc(cache, m()));
    }
    m_cache = m_cache_stack[lvl];
    m_cache->reset();
    SASSERT(m_cache->empty());
    if (m_proof_gen) {
        m_cache_pr = m_cache_pr_stack[lvl];
        m_cache_pr->reset();
        SASSERT(m_cache_pr->empty());
    }
}

void rewriter_core::end_scope() {
    m_cache->reset();
    if (m_proof_gen)
        m_cache_pr->reset();
    scope & s        = m_scopes.back();
    m_root           = s.m_old_root;
    m_num_qvars      = s.m_old_num_qvars;
    m_scopes.pop_back();
    unsigned new_lvl = m_scopes.size();
    m_cache          = m_cache_stack[new_lvl];
    if (m_proof_gen)
        m_cache_pr   = m_cache_pr_stack[new_lvl];
}

bool rewriter_core::is_child_of_top_frame(expr * t) const {
    if (m_frame_stack.empty())
        return true;
    frame const & fr = m_frame_stack.back();
    expr * parent = fr.m_curr;
    unsigned num;
    switch (parent->get_kind()) {
    case AST_APP:
        num = to_app(parent)->get_num_args();
        for (unsigned i = 0; i < num; i++) {
            if (to_app(parent)->get_arg(i) == t)
                return true;
        }
        return false;
    case AST_QUANTIFIER:
        num = to_quantifier(parent)->get_num_children();
        for (unsigned i = 0; i < num; i++) {
            if (to_quantifier(parent)->get_child(i) == t)
                return true;
        }
        return false;
    default:
        return false;
    }
}

/**
   \brief Eliminate (implicit) reflexivity proofs from m_result_pr_stack starting at position spos.
   The implicit reflexivity proof is 0.
*/
void rewriter_core::elim_reflex_prs(unsigned spos) {
    SASSERT(m_proof_gen);
    unsigned sz = m_result_pr_stack.size();
    SASSERT(spos <= sz);
    unsigned j = spos;
    for (unsigned i = spos; i < sz; i++) {
        proof * pr = m_result_pr_stack.get(i);
        if (pr != nullptr) {
            if (i != j)
                m_result_pr_stack.set(j, pr);
            j++;
        }
    }
    m_result_pr_stack.shrink(j);
}

rewriter_core::rewriter_core(ast_manager & m, bool proof_gen):
    m_manager(m),
    m_proof_gen(proof_gen),
    m_cancel_check(true),
    m_result_stack(m),
    m_result_pr_stack(m),
    m_num_qvars(0) {
    init_cache_stack();
}

rewriter_core::~rewriter_core() {
    del_cache_stack();
}

// reset rewriter (macro definitions are not erased)
void rewriter_core::reset() {
    SASSERT(!m_cache_stack.empty());
    reset_cache();
    m_frame_stack.reset();
    m_result_stack.reset();
    if (m_proof_gen)
        m_result_pr_stack.reset();
    m_root = nullptr;
    m_num_qvars = 0;
    m_scopes.reset();
}

// free memory & reset (macro definitions are not erased)
void rewriter_core::cleanup() {
    free_memory();
    init_cache_stack();
    m_root       = nullptr;
    m_num_qvars  = 0;
}


#ifdef _TRACE
void rewriter_core::display_stack(std::ostream & out, unsigned pp_depth) {
    svector<frame>::iterator it  = m_frame_stack.begin();
    svector<frame>::iterator end = m_frame_stack.end();
    for (; it != end; ++it) {
        out << mk_bounded_pp(it->m_curr, m(), pp_depth) << "\n";
        out << "state: " << it->m_state << "\n";
        out << "cache: " << it->m_cache_result << ", new_child: " << it->m_new_child << ", max-depth: " << it->m_max_depth << ", i: " << it->m_i << "\n";
        out << "------------------\n";
    }
}
#endif

bool var_shifter_core::visit(expr * t) {
    if (is_ground(t)) {
        m_result_stack.push_back(t);
        return true;
    }
    bool c = must_cache(t);
    if (c) {
        expr * r = get_cached(t);
        if (r) {
            m_result_stack.push_back(r);
            set_new_child_flag(t, r);
            return true;
        }
    }
    switch (t->get_kind()) {
    case AST_APP:
        SASSERT(to_app(t)->get_num_args() > 0);
        push_frame(t, c);
        return false;
    case AST_VAR:
        process_var(to_var(t));
        return true;
    case AST_QUANTIFIER:
        push_frame(t, c);
        return false;
    default:
        UNREACHABLE();
        return true;
    }
}

void var_shifter_core::process_app(app * t, frame & fr) {
    unsigned num_args = t->get_num_args();
    while (fr.m_i < num_args) {
        expr * arg = t->get_arg(fr.m_i);
        fr.m_i++;
        if (!visit(arg))
            return;
    }
    SASSERT(fr.m_spos + num_args == m_result_stack.size());
    expr * new_t;
    if (fr.m_new_child) {
        expr * const * new_args = m_result_stack.c_ptr() + fr.m_spos;
        new_t = m().mk_app(t->get_decl(), num_args, new_args);
    }
    else {
        new_t = t;
    }
    m_result_stack.shrink(fr.m_spos);
    m_result_stack.push_back(new_t);
    m_frame_stack.pop_back();
    set_new_child_flag(t, new_t);
    if (fr.m_cache_result)
        cache_result(t, new_t);
}

void var_shifter_core::process_quantifier(quantifier * q, frame & fr) {
    if (fr.m_i == 0) {
        begin_scope();
        m_num_qvars += q->get_num_decls();
        m_root       = q->get_expr();
    }
    unsigned num_children = q->get_num_children();
    while (fr.m_i < num_children) {
        expr * child = q->get_child(fr.m_i);
        fr.m_i++;
        if (!visit(child))
            return;
    }
    SASSERT(fr.m_spos + num_children == m_result_stack.size());
    expr * new_q;
    if (fr.m_new_child) {
        expr * const * it = m_result_stack.c_ptr() + fr.m_spos;
        expr * new_expr = *it;
        ++it;
        expr * const * new_pats    = it;
        expr * const * new_no_pats = new_pats + q->get_num_patterns();
        new_q = m().update_quantifier(q, q->get_num_patterns(), new_pats, q->get_num_no_patterns(), new_no_pats, new_expr);
    }
    else {
        new_q = q;
    }
    m_result_stack.shrink(fr.m_spos);
    m_result_stack.push_back(new_q);
    m_frame_stack.pop_back();
    set_new_child_flag(q, new_q);
    end_scope();
    if (fr.m_cache_result)
        cache_result(q, new_q);
}

void var_shifter_core::main_loop(expr * t, expr_ref & r) {
    SASSERT(m_cache == m_cache_stack[0]);
    SASSERT(m_frame_stack.empty());
    SASSERT(m_result_stack.empty());
    m_root      = t;

    if (visit(t)) {
        r = m_result_stack.back();
        m_result_stack.pop_back();
        SASSERT(m_result_stack.empty());
        return;
    }
    SASSERT(!m_frame_stack.empty());
    while (!m_frame_stack.empty()) {
        frame & fr = m_frame_stack.back();
        expr * t   = fr.m_curr;
        if (fr.m_i == 0 && fr.m_cache_result) {
            expr * r = get_cached(t);
            if (r) {
                m_result_stack.push_back(r);
                m_frame_stack.pop_back();
                set_new_child_flag(t, r);
                continue;
            }
        }
        switch (t->get_kind()) {
        case AST_APP:
            process_app(to_app(t), fr);
            break;
        case AST_QUANTIFIER:
            process_quantifier(to_quantifier(t), fr);
            break;
        default:
            UNREACHABLE();
        }
    }
    r = m_result_stack.back();
    m_result_stack.pop_back();
    SASSERT(m_result_stack.empty());
}

void var_shifter::operator()(expr * t, unsigned bound, unsigned shift1, unsigned shift2, expr_ref & r) {
    if (is_ground(t)) {
        r = t;
        return;
    }
    reset_cache();
    m_bound     = bound;
    m_shift1    = shift1;
    m_shift2    = shift2;
    main_loop(t, r);
}

void var_shifter::process_var(var * v) {
    unsigned vidx = v->get_idx();
    if (vidx < m_num_qvars) {
        m_result_stack.push_back(v);
    }
    else {
        unsigned nvidx = vidx - m_num_qvars;
        if (nvidx >= m_bound)
            vidx += m_shift1;
        else
            vidx += m_shift2;
        m_result_stack.push_back(m().mk_var(vidx, v->get_sort()));
        set_new_child_flag(v);
    }
}

void inv_var_shifter::operator()(expr * t, unsigned shift, expr_ref & r) {
    if (is_ground(t)) {
        r = t;
        return;
    }
    reset_cache();
    m_shift     = shift;
    main_loop(t, r);
}

void inv_var_shifter::process_var(var * v) {
    unsigned vidx = v->get_idx();
    if (vidx < m_num_qvars) {
        m_result_stack.push_back(v);
    }
    else {
        SASSERT(vidx >= m_num_qvars + m_shift); 
        vidx -= m_shift;
        m_result_stack.push_back(m().mk_var(vidx, v->get_sort()));
        set_new_child_flag(v);
    }
}
    
template class rewriter_tpl<beta_reducer_cfg>;
