/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    rewriter.h

Abstract:

    Lean and mean rewriter

Author:

    Leonardo (leonardo) 2011-03-31

Notes:

--*/
#ifndef REWRITER_H_
#define REWRITER_H_

#include"ast.h"
#include"rewriter_types.h"
#include"act_cache.h"

/**
   \brief Common infrastructure for AST rewriters.
*/
class rewriter_core {
protected:
    struct frame {
        expr *   m_curr;
        unsigned m_cache_result:1; // true if the result of rewriting m_expr must be cached.
        unsigned m_new_child:1;
        unsigned m_state:2;
        unsigned m_max_depth:2;     // bounded rewrite... if m_max_depth == 0, then children are not rewritten.
        unsigned m_i:26;
        unsigned m_spos;           // top of the result stack, when the frame was created.
        frame(expr * n, bool cache_res, unsigned st, unsigned max_depth, unsigned spos):
            m_curr(n), 
            m_cache_result(cache_res),
            m_new_child(false),
            m_state(st),
            m_max_depth(max_depth),
            m_i(0),
            m_spos(spos) {
        }
    };
    ast_manager &              m_manager;
    bool                       m_proof_gen; 
    bool                       m_cancel_check;
    typedef act_cache          cache;
    ptr_vector<cache>          m_cache_stack;
    cache *                    m_cache; // current cache.
    svector<frame>             m_frame_stack;
    expr_ref_vector            m_result_stack;

    // proof generation goodness ----
    ptr_vector<cache>          m_cache_pr_stack; 
    cache *                    m_cache_pr;
    proof_ref_vector           m_result_pr_stack;
    // --------------------------

    expr *                     m_root;
    unsigned                   m_num_qvars;
    struct scope {
        expr *   m_old_root;
        unsigned m_old_num_qvars;
        scope(expr * r, unsigned n):m_old_root(r), m_old_num_qvars(n) {}
    };
    svector<scope>             m_scopes;

    // Return true if the rewriting result of the given expression must be cached.
    bool must_cache(expr * t) const {
        return 
            t->get_ref_count() > 1 &&  // t must be a shared expression
            t != m_root && // t must not be the root expression
            ((is_app(t) && to_app(t)->get_num_args() > 0) || is_quantifier(t)); // t is a (non-constant) application or a quantifier.
    }

    void push_frame_core(expr * t, bool cache_res, unsigned st = 0, unsigned max_depth = RW_UNBOUNDED_DEPTH) {
        SASSERT(!m_proof_gen || m_result_stack.size() == m_result_pr_stack.size());
        m_frame_stack.push_back(frame(t, cache_res, st, max_depth, m_result_stack.size()));
    }

    void push_frame(expr * t, unsigned st = 0) {
        push_frame_core(t, must_cache(t), st);
    } 

    void init_cache_stack();
    void del_cache_stack();
    void reset_cache();
    void cache_result(expr * k, expr * v);
    expr * get_cached(expr * k) const { return m_cache->find(k); } 

    void cache_result(expr * k, expr * v, proof * pr);
    proof * get_cached_pr(expr * k) const { return static_cast<proof*>(m_cache_pr->find(k)); } 

    void free_memory();
    void begin_scope();
    void end_scope();
    bool is_child_of_top_frame(expr * t) const;
    void set_new_child_flag(expr * old_t) {
        CTRACE("rewriter_bug", !is_child_of_top_frame(old_t), display_stack(tout, 3););
        SASSERT(is_child_of_top_frame(old_t));
        if (!m_frame_stack.empty())
            m_frame_stack.back().m_new_child = true;
    }
    void set_new_child_flag(expr * old_t, expr * new_t) { if (old_t != new_t) set_new_child_flag(old_t); }
    
    void elim_reflex_prs(unsigned spos);
public:
    rewriter_core(ast_manager & m, bool proof_gen);
    ~rewriter_core();
    ast_manager & m() const { return m_manager; }
    void reset();
    void cleanup();
    void set_cancel_check(bool f) { m_cancel_check = f; }
#ifdef _TRACE
    void display_stack(std::ostream & out, unsigned pp_depth);
#endif
    unsigned get_cache_size() const;
};

class var_shifter_core : public rewriter_core {
protected:
    bool visit(expr * t);
    void process_app(app * t, frame & fr);
    virtual void process_var(var * v) = 0;
    void process_quantifier(quantifier * q, frame & fr);
    void main_loop(expr * t, expr_ref & r);
public:
    var_shifter_core(ast_manager & m):rewriter_core(m, false) {}
};

/**
   \brief Functor used to shift the free variables of an AST by a given amount.
   This functor is used by the var_subst functor.

   This functor implements the following functions:
   1) shift(n, s) will return a new AST where all free variables (VAR i) in n,
   are replaced by (VAR (+ i s)).

   2) shift(n, b, s1, s2) is a variant of the previous function such that 
   for a each free variable (VAR i) is shifted to:
       - (VAR i + s1) if i >= b
       - (VAR i + s2) if i < b 
*/
class var_shifter : public var_shifter_core {
    unsigned  m_bound;
    unsigned  m_shift1;
    unsigned  m_shift2;
    virtual void process_var(var * v);
public:
    var_shifter(ast_manager & m):var_shifter_core(m) {}
    void operator()(expr * t, unsigned bound, unsigned shift1, unsigned shift2, expr_ref & r);
    void operator()(expr * t, unsigned s, expr_ref & r) {
        operator()(t, 0, s, 0, r);
    }
};

/**
   \brief Functor used to shift the free variables of an AST by a negative amount.

   Abstract implementation:

   inv_shift(f(c_1, ..., c_n), d, s) =
     f(inv_shift(c_1, d, s), ..., inv_shift(c_n, d, s))
   inv_shift(var(i), d, s) =
     if (i < d) 
       var(i)
     else
       assert(i - s >= d)
       var(i-s)
  inv_shift((forall (x) P), d, s) =
    (forall (x) inv_shift(P, d+1, s))
   
  This functor assumes that if we are shifting an expression F by N, then F
  does not contain free variables #0, ... #N-1 

  See assertion above.
*/
class inv_var_shifter : public var_shifter_core {
protected:
    unsigned m_shift;
    virtual void process_var(var * v);
public:
    inv_var_shifter(ast_manager & m):var_shifter_core(m) {}
    void operator()(expr * t, unsigned shift, expr_ref & r);
};

template<typename Config> 
class rewriter_tpl : public rewriter_core {
protected:
    // Rewriter maintains a stack of frames.
    // Each frame represents an expression that is being rewritten.
    // The resultant expressions are store on the Result stack.
    // Each frame is in a particular state.
    // Let f(t_0,...,t_n) be the expression is the frame Fr. Then Fr can be is one of the 
    // following states:
    //    PROCESS_CHILDREN(i) the children t_0, ..., t_{i-1} have already been rewritten, and the result is on the Result stack.
    //    REWRITE_BUILTIN All t_0, ..., t_n have been rewritten to t_0',...,t_n', and the builtin rewriter (or plugin) produced a new term t
    //                    that can be further rewritten.
    //    EXPAND_DEF      All t_0, ..., t_n have been rewritten to t_0',...,t_n'.
    //                    The function symbol f is a macro, and the body of the macro needs to be rewritten using the t_0',...,t_n' as bindings.
    //    REWRITE_RULE    All t_0, ..., t_n have been rewritten to t_0',...,t_n'.
    //                    There is rewrite rule lhs -> rhs s.t. f(t_0', ..., t_n') matches lhs with substitution delta.
    //                    rhs is then rewritten using delta.
    enum state {
        PROCESS_CHILDREN,
        REWRITE_BUILTIN,
        EXPAND_DEF,
        REWRITE_RULE
    };
    Config &                   m_cfg;
    unsigned                   m_num_steps;
    ptr_vector<expr>           m_bindings;
    var_shifter                m_shifter;
    inv_var_shifter            m_inv_shifter;
    expr_ref                   m_r;
    proof_ref                  m_pr;
    proof_ref                  m_pr2;
    unsigned_vector            m_shifts;

    svector<frame> & frame_stack() { return this->m_frame_stack; }
    svector<frame> const & frame_stack() const { return this->m_frame_stack; }
    expr_ref_vector & result_stack() { return this->m_result_stack; }
    expr_ref_vector const & result_stack() const { return this->m_result_stack; }
    proof_ref_vector & result_pr_stack() { return this->m_result_pr_stack; }
    proof_ref_vector const & result_pr_stack() const { return this->m_result_pr_stack; }

    void display_bindings(std::ostream& out);

    void set_new_child_flag(expr * old_t) {
        SASSERT(frame_stack().empty() || frame_stack().back().m_state != PROCESS_CHILDREN || this->is_child_of_top_frame(old_t));
        if (!frame_stack().empty())
            frame_stack().back().m_new_child = true;
    }
    void set_new_child_flag(expr * old_t, expr * new_t) { if (old_t != new_t) set_new_child_flag(old_t); }

    // cache the result of shared non atomic expressions.
    bool cache_results() const { return m_cfg.cache_results(); }
    // cache all results share and non shared expressions non atomic expressions.
    bool cache_all_results() const { return m_cfg.cache_all_results(); }
    // flat non shared AC terms
    bool flat_assoc(func_decl * f) const { return m_cfg.flat_assoc(f); }
    // rewrite patterns
    bool rewrite_patterns() const { return m_cfg.rewrite_patterns(); }
   
    // check maximum number of scopes
    void check_max_scopes() const { 
        if (m_cfg.max_scopes_exceeded(this->m_scopes.size()))
            throw rewriter_exception(Z3_MAX_SCOPES_MSG);
    }
    // check maximum size of the frame stack
    void check_max_frames() const { 
        if (m_cfg.max_frames_exceeded(frame_stack().size()))
            throw rewriter_exception(Z3_MAX_FRAMES_MSG);
    }
    // check maximum number of rewriting steps
    void check_max_steps() const { 
        if (m_cfg.max_steps_exceeded(m_num_steps))
            throw rewriter_exception(Z3_MAX_STEPS_MSG);
    }

    // If pre_visit returns false, then t children are not visited/rewritten.
    // This should be used with care, since it may produce incorrect results
    // when the rewriter is used to apply variable substitution.
    bool pre_visit(expr * t) {
        return m_cfg.pre_visit(t);
    }

    // Return true if the rewriting result of the given expression must be cached.
    bool must_cache(expr * t) const {
        if (cache_all_results())
            return t != this->m_root && ((is_app(t) && to_app(t)->get_num_args() > 0) || is_quantifier(t));
        if (cache_results())
            return rewriter_core::must_cache(t); 
        return false;
    }

    bool get_macro(func_decl * f, expr * & def, quantifier * & q, proof * & def_pr) {
        return m_cfg.get_macro(f, def, q, def_pr);
    }

    void push_frame(expr * t, bool mcache, unsigned max_depth) {
        check_max_frames();
        push_frame_core(t, mcache, PROCESS_CHILDREN, max_depth);
    }

    void begin_scope() {
        check_max_scopes();
        rewriter_core::begin_scope();
    }
    
    template<bool ProofGen>
    void process_var(var * v);

    template<bool ProofGen>
    void process_const(app * t);

    template<bool ProofGen>
    bool visit(expr * t, unsigned max_depth);

    template<bool ProofGen>
    void cache_result(expr * t, expr * new_t, proof * pr, bool c) {
        if (c) {
            if (!ProofGen)
                rewriter_core::cache_result(t, new_t);
            else
                rewriter_core::cache_result(t, new_t, pr);
        }
    }

    template<bool ProofGen>
    void process_app(app * t, frame & fr);

    template<bool ProofGen>
    void process_quantifier(quantifier * q, frame & fr);

    bool first_visit(frame & fr) const {
        return fr.m_state == PROCESS_CHILDREN && fr.m_i == 0;
    }

    bool not_rewriting() const;

    template<bool ProofGen>
    void main_loop(expr * t, expr_ref & result, proof_ref & result_pr);

    template<bool ProofGen>
    void resume_core(expr_ref & result, proof_ref & result_pr);

public:
    rewriter_tpl(ast_manager & m, bool proof_gen, Config & cfg);

    ast_manager & m() const { return this->m_manager; }
    Config & cfg() { return m_cfg; }
    Config const & cfg() const { return m_cfg; }

    ~rewriter_tpl();
    
    void reset();
    void cleanup();
    
    void set_bindings(unsigned num_bindings, expr * const * bindings);
    void set_inv_bindings(unsigned num_bindings, expr * const * bindings);
    void operator()(expr * t, expr_ref & result, proof_ref & result_pr);
    void operator()(expr * t, expr_ref & result) { operator()(t, result, m_pr); }
    void operator()(expr * n, unsigned num_bindings, expr * const * bindings, expr_ref & result) {
        SASSERT(!m_proof_gen);
        reset();
        set_inv_bindings(num_bindings, bindings);
        operator()(n, result);
    }

    void resume(expr_ref & result, proof_ref & result_pr);
    void resume(expr_ref & result) { resume(result, m_pr); }

    // Return the number of steps performed by the rewriter in the last call to operator().
    unsigned get_num_steps() const { return m_num_steps; }
};

struct default_rewriter_cfg {
    bool cache_all_results() const { return false; }
    bool cache_results() const { return true; }
    bool flat_assoc(func_decl * f) const { return false; }
    bool rewrite_patterns() const { return true; }
    bool max_scopes_exceeded(unsigned num_scopes) const { return false; }
    bool max_frames_exceeded(unsigned num_frames) const { return false; }
    bool max_steps_exceeded(unsigned num_steps) const { return false; }
    bool pre_visit(expr * t) { return true; }
    br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) { return BR_FAILED; }
    bool reduce_quantifier(quantifier * old_q, 
                           expr * new_body, 
                           expr * const * new_patterns, 
                           expr * const * new_no_patterns,
                           expr_ref & result,
                           proof_ref & result_pr) {
        return false;
    }
    bool reduce_var(var * t, expr_ref & result, proof_ref & result_pr) { return false; }
    bool get_macro(func_decl * d, expr * & def, quantifier * & q, proof * & def_pr) { return false; }
    bool get_subst(expr * s, expr * & t, proof * & t_pr) { return false; }
    void reset() {}
    void cleanup() {}
};

struct beta_reducer_cfg : public default_rewriter_cfg {
    bool pre_visit(expr * t) { return !is_ground(t); }
};

class beta_reducer : public rewriter_tpl<beta_reducer_cfg>  {
    beta_reducer_cfg m_cfg;
public:
    beta_reducer(ast_manager & m):
        rewriter_tpl<beta_reducer_cfg>(m, false, m_cfg) {}
};

#endif
