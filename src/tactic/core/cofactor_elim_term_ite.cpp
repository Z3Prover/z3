/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    cofactor_elim_term_ite.cpp

Abstract:

    Eliminate term if-then-else's using cofactors.

Author:

    Leonardo de Moura (leonardo) 2011-06-05.

Revision History:

--*/
#include "tactic/core/cofactor_elim_term_ite.h"
#include "ast/rewriter/mk_simplified_app.h"
#include "ast/rewriter/rewriter_def.h"
#include "util/cooperate.h"
#include "ast/for_each_expr.h"
#include "ast/ast_smt2_pp.h"
#include "ast/ast_ll_pp.h"
#include "tactic/tactic.h"

struct cofactor_elim_term_ite::imp {
    ast_manager &      m;
    params_ref         m_params;
    unsigned long long m_max_memory;
    bool               m_cofactor_equalities;

    void checkpoint() { 
        cooperate("cofactor ite");
        if (memory::get_allocation_size() > m_max_memory)
            throw tactic_exception(TACTIC_MAX_MEMORY_MSG);
        if (m.canceled())
            throw tactic_exception(m.limit().get_cancel_msg());
    }

    // Collect atoms that contain term if-then-else
    struct analyzer {
        struct frame {
            expr *   m_t;
            unsigned m_first:1;
            unsigned m_form_ctx:1;
            frame(expr * t, bool form_ctx):m_t(t), m_first(true), m_form_ctx(form_ctx) {}
        };
        
        ast_manager &       m;
        imp &               m_owner;
        obj_hashtable<expr> m_candidates;
        expr_fast_mark1     m_processed;
        expr_fast_mark2     m_has_term_ite;
        svector<frame>      m_frame_stack;

        analyzer(ast_manager & _m, imp & owner):m(_m), m_owner(owner) {}
        
        void push_frame(expr * t, bool form_ctx) {
            m_frame_stack.push_back(frame(t, form_ctx && m.is_bool(t)));
        }
        
        void visit(expr * t, bool form_ctx, bool & visited) {
            if (!m_processed.is_marked(t)) {
                visited = false;
                push_frame(t, form_ctx);
            }
        }
        
        void save_candidate(expr * t, bool form_ctx) {
            if (!form_ctx)
                return;
            if (!m.is_bool(t))
                return;
            if (!m_has_term_ite.is_marked(t))
                return;
            if (!is_app(t))
                return;
            if (to_app(t)->get_family_id() == m.get_basic_family_id()) {
                switch (to_app(t)->get_decl_kind()) {
                case OP_OR:
                case OP_AND:
                case OP_NOT:
                case OP_XOR:
                case OP_IMPLIES:
                case OP_TRUE:
                case OP_FALSE:
                case OP_ITE:
                    return;
                case OP_EQ:
                case OP_DISTINCT:
                    if (m.is_bool(to_app(t)->get_arg(0)))
                        return;
                    break;
                default:
                    break;
                }
            }
            // it is an atom in a formula context (i.e., it is not nested inside a term),
            // and it contains a term if-then-else.
            m_candidates.insert(t);
        }
        
        void operator()(expr * t) {
            SASSERT(m.is_bool(t));
            push_frame(t, true);
            SASSERT(!m_frame_stack.empty());
            while (!m_frame_stack.empty()) {
                frame & fr    = m_frame_stack.back();
                expr * t      = fr.m_t;
                bool form_ctx = fr.m_form_ctx;
                TRACE("cofactor", tout << "processing, form_ctx: " << form_ctx << "\n" << mk_bounded_pp(t, m) << "\n";);

                m_owner.checkpoint();
                
                if (m_processed.is_marked(t)) {
                    save_candidate(t, form_ctx);
                    m_frame_stack.pop_back();
                    continue;
                }

                if (m.is_term_ite(t)) {
                    m_has_term_ite.mark(t);
                    m_processed.mark(t);
                    m_frame_stack.pop_back();
                    continue;
                }
                
                if (fr.m_first) {
                    fr.m_first   = false;
                    bool visited = true;
                    if (is_app(t)) {
                        unsigned num_args = to_app(t)->get_num_args();
                        for (unsigned i = 0; i < num_args; i++)
                            visit(to_app(t)->get_arg(i), form_ctx, visited);
                    }
                    // ignoring quantifiers
                    if (!visited)
                        continue;
                }
                
                if (is_app(t)) {
                    unsigned num_args = to_app(t)->get_num_args();
                    unsigned i;
                    for (i = 0; i < num_args; i++) {
                        if (m_has_term_ite.is_marked(to_app(t)->get_arg(i)))
                            break;
                    }
                    if (i < num_args) {
                        m_has_term_ite.mark(t);
                        TRACE("cofactor", tout << "saving candidate: " << form_ctx << "\n" << mk_bounded_pp(t, m) << "\n";);
                        save_candidate(t, form_ctx);
                    }
                }
                else {
                    SASSERT(is_quantifier(t) || is_var(t));
                    // ignoring quantifiers... they are treated as black boxes.
                }
                m_processed.mark(t);
                m_frame_stack.pop_back();
            }
            m_processed.reset();
            m_has_term_ite.reset();
        }
    };

    expr * get_first(expr * t) { 
        TRACE("cofactor", tout << mk_ismt2_pp(t, m) << "\n";);
        typedef std::pair<expr *, unsigned> frame;
        expr_fast_mark1         visited;            
        sbuffer<frame>          stack;    
        stack.push_back(frame(t, 0));
        while (!stack.empty()) {
        start:
            checkpoint();
            frame & fr  = stack.back();
            expr * curr = fr.first;
            if (m.is_term_ite(curr)) 
                return to_app(curr)->get_arg(0);
            switch (curr->get_kind()) {
            case AST_VAR:
            case AST_QUANTIFIER:
                // ignore quantifiers
                stack.pop_back();
                break;
            case AST_APP: {
                unsigned num_args = to_app(curr)->get_num_args();
                while (fr.second < num_args) {
                    expr * arg = to_app(curr)->get_arg(fr.second);
                    fr.second++;
                    if (arg->get_ref_count() > 1) {
                        if (visited.is_marked(arg))
                            continue;
                        visited.mark(arg);
                    }
                    switch (arg->get_kind()) {
                    case AST_VAR:
                    case AST_QUANTIFIER:
                        // ignore quantifiers
                        break;
                    case AST_APP:
                        if (to_app(arg)->get_num_args() > 0) {
                            stack.push_back(frame(arg, 0));
                            goto start;
                        }
                        break;
                    default:
                        UNREACHABLE();
                        break;
                    }
                }
                stack.pop_back();
                break;
            }
            default:
                UNREACHABLE();
                break;
            }
        }
        return nullptr;
    }

    /**
       \brief Fuctor for selecting the term if-then-else condition with the most number of occurrences.
    */
    expr * get_best(expr * t) {
        TRACE("cofactor", tout << mk_ismt2_pp(t, m) << "\n";);
        typedef std::pair<expr *, unsigned> frame;
        obj_map<expr, unsigned> occs;
        expr_fast_mark1         visited;            
        sbuffer<frame>          stack;    
        
        stack.push_back(frame(t, 0));
        while (!stack.empty()) {
        start:
            checkpoint();
            frame & fr  = stack.back();
            expr * curr = fr.first;
            switch (curr->get_kind()) {
            case AST_VAR:
            case AST_QUANTIFIER:
                // ignore quantifiers
                stack.pop_back();
                break;
            case AST_APP: {
                unsigned num_args = to_app(curr)->get_num_args();
                bool is_term_ite = m.is_term_ite(curr);
                while (fr.second < num_args) {
                    expr * arg = to_app(curr)->get_arg(fr.second);
                    if (fr.second == 0 && is_term_ite) {
                        unsigned num = 0;
                        if (occs.find(arg, num))
                            occs.insert(arg, num+1);
                        else
                            occs.insert(arg, 1);
                    }
                    fr.second++;
                    if (arg->get_ref_count() > 1) {
                        if (visited.is_marked(arg))
                            continue;
                        visited.mark(arg);
                    }
                    switch (arg->get_kind()) {
                    case AST_VAR:
                    case AST_QUANTIFIER:
                        // ignore quantifiers
                        break;
                    case AST_APP:
                        if (to_app(arg)->get_num_args() > 0) {
                            stack.push_back(frame(arg, 0));
                            goto start;
                        }
                        break;
                    default:
                        UNREACHABLE();
                        break;
                    }
                }
                stack.pop_back();
                break;
            }
            default:
                UNREACHABLE();
                break;
            }
        }
        expr * best = nullptr;
        unsigned best_occs = 0;
        obj_map<expr, unsigned>::iterator it  = occs.begin();
        obj_map<expr, unsigned>::iterator end = occs.end();
        for (; it != end; ++it) {
            if ((!best) ||
                (get_depth(it->m_key) < get_depth(best))  ||
                (get_depth(it->m_key) == get_depth(best) && it->m_value > best_occs) ||
                // break ties by giving preference to equalities
                (get_depth(it->m_key) == get_depth(best) && it->m_value == best_occs && m.is_eq(it->m_key) && !m.is_eq(best))) {
                best = it->m_key;
                best_occs = it->m_value;
            }
        }
        visited.reset();
        CTRACE("cofactor", best != 0, tout << "best num-occs: " << best_occs << "\n" << mk_ismt2_pp(best, m) << "\n";);
        return best;
    }

    void updt_params(params_ref const & p) {
        m_max_memory     = megabytes_to_bytes(p.get_uint("max_memory", UINT_MAX));
        m_cofactor_equalities = p.get_bool("cofactor_equalities", true);
    }

    void collect_param_descrs(param_descrs & r) {
        r.insert("cofactor_equalities", CPK_BOOL, "(default: true) use equalities to rewrite bodies of ite-expressions. This is potentially expensive.");
    }


    struct cofactor_rw_cfg : public default_rewriter_cfg {
        ast_manager &         m;
        imp &                 m_owner;
        obj_hashtable<expr> * m_has_term_ite;
        mk_simplified_app     m_mk_app;
        expr *                m_atom;
        bool                  m_sign;
        expr *                m_term;
        app *                 m_value;
        bool                  m_strict_lower;
        app *                 m_lower;
        bool                  m_strict_upper;
        app *                 m_upper;

        cofactor_rw_cfg(ast_manager & _m, imp & owner, obj_hashtable<expr> * has_term_ite = nullptr):
            m(_m),
            m_owner(owner),
            m_has_term_ite(has_term_ite),
            m_mk_app(m, owner.m_params) {
        }

        bool max_steps_exceeded(unsigned num_steps) const { 
            m_owner.checkpoint();
            return false;
        }
        
        bool pre_visit(expr * t) {
            return true;
        }

        void set_cofactor_atom(expr * t) {
            if (m.is_not(t)) {
                m_atom = to_app(t)->get_arg(0);
                m_sign = true;
                m_term = nullptr;
                // TODO: bounds
            }
            else {
                m_atom = t;
                m_sign = false;
                m_term = nullptr;
                expr * lhs;
                expr * rhs;
                if (m_owner.m_cofactor_equalities && m.is_eq(t, lhs, rhs)) {
                    if (m.is_unique_value(lhs)) {
                        m_term  = rhs;
                        m_value = to_app(lhs); 
                        TRACE("cofactor", tout << "term:\n" << mk_ismt2_pp(m_term, m) << "\nvalue: " << mk_ismt2_pp(m_value, m) << "\n";);
                    }
                    else if (m.is_unique_value(rhs)) {
                        m_term  = lhs;
                        m_value = to_app(rhs);
                        TRACE("cofactor", tout << "term:\n" << mk_ismt2_pp(m_term, m) << "\nvalue: " << mk_ismt2_pp(m_value, m) << "\n";);
                    }
                }
                // TODO: bounds
            }
        }
        
        bool rewrite_patterns() const { return false; }
        
        br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
            result_pr = nullptr;
            return m_mk_app.mk_core(f, num, args, result);
        }

        bool get_subst(expr * s, expr * & t, proof * & pr) {
            pr = nullptr;
            
            if (s == m_atom) {
                t = m_sign ? m.mk_false() : m.mk_true();
                return true;
            }
            
            if (s == m_term && m_value != nullptr) {
                t = m_value;
                return true;
            }
            
            // TODO: handle simple bounds
            // Example: s is of the form (<= s 10) and m_term == s, and m_upper is 9
            // then rewrite to true.
            
            return false;
        }
    
    };

    struct cofactor_rw : rewriter_tpl<cofactor_rw_cfg> {
        cofactor_rw_cfg m_cfg;
    public:
        cofactor_rw(ast_manager & m, imp & owner, obj_hashtable<expr> * has_term_ite = nullptr):
            rewriter_tpl<cofactor_rw_cfg>(m, false, m_cfg),
            m_cfg(m, owner, has_term_ite) {
        }

        void set_cofactor_atom(expr * t) {
            m_cfg.set_cofactor_atom(t);
            reset();
        }
    };
    
    struct main_rw_cfg : public default_rewriter_cfg {
        ast_manager &               m;
        imp &                       m_owner;
        cofactor_rw                 m_cofactor;
        obj_hashtable<expr> const & m_candidates;
        obj_map<expr, expr*>        m_cache;
        expr_ref_vector             m_cache_domain;

        main_rw_cfg(ast_manager & _m, imp & owner, obj_hashtable<expr> & candidates):
            m(_m),
            m_owner(owner),
            m_cofactor(m, m_owner),
            m_candidates(candidates),
            m_cache_domain(_m) {
        }

        bool max_steps_exceeded(unsigned num_steps) const { 
            m_owner.checkpoint();
            return false;
        }
        
        bool pre_visit(expr * t) { 
            return m.is_bool(t) && !is_quantifier(t);
        }
        
        bool get_subst(expr * s, expr * & t, proof * & t_pr) { 
            if (m_candidates.contains(s)) {
                t_pr = nullptr;

                if (m_cache.find(s, t))
                    return true;
                unsigned step = 0;
                TRACE("cofactor_ite", tout << "cofactor target:\n" << mk_ismt2_pp(s, m) << "\n";);
                expr_ref curr(m);
                curr = s;
                while (true) {
                    // expr * c = m_owner.get_best(curr);
                    expr * c = m_owner.get_first(curr);
                    if (c == nullptr) {
                        m_cache.insert(s, curr);
                        m_cache_domain.push_back(curr);
                        t = curr.get();
                        return true;
                    }
                    step++;
                    expr_ref pos_cofactor(m);
                    expr_ref neg_cofactor(m);
                    m_cofactor.set_cofactor_atom(c);
                    m_cofactor(curr, pos_cofactor);
                    expr_ref neg_c(m);
                    neg_c = m.is_not(c) ? to_app(c)->get_arg(0) : m.mk_not(c);                    
                    m_cofactor.set_cofactor_atom(neg_c);
                    m_cofactor(curr, neg_cofactor);
                    curr = m.mk_ite(c, pos_cofactor, neg_cofactor);
                    TRACE("cofactor", tout << "cofactor_ite step: " << step << "\n" << mk_ismt2_pp(curr, m) << "\n";);
                }
            }
            return false;
        }
    };

    struct main_rw : rewriter_tpl<main_rw_cfg> {
        main_rw_cfg m_cfg;
    public:
        main_rw(ast_manager & m, imp & owner, obj_hashtable<expr> & candidates):
            rewriter_tpl<main_rw_cfg>(m, false, m_cfg),
            m_cfg(m, owner, candidates) {
        }
    };

    struct bottom_up_elim {
        typedef std::pair<expr*, bool> frame;
        ast_manager &        m;
        imp &                m_owner;
        obj_map<expr, expr*> m_cache;
        expr_ref_vector      m_cache_domain;
        obj_hashtable<expr>  m_has_term_ite;
        svector<frame>       m_frames;
        cofactor_rw          m_cofactor;
        
        bottom_up_elim(ast_manager & _m, imp & owner):
            m(_m),
            m_owner(owner),
            m_cache_domain(m),
            m_cofactor(m, owner, &m_has_term_ite) {
        }

        bool is_atom(expr * t) const {
            if (!m.is_bool(t))
                return false;
            if (!is_app(t))
                return false;
            if (to_app(t)->get_family_id() == m.get_basic_family_id()) {
                switch (to_app(t)->get_decl_kind()) {
                case OP_EQ:
                case OP_DISTINCT:
                    if (m.is_bool(to_app(t)->get_arg(0)))
                        return false;
                    else 
                        return true;
                default:
                    return false;
                }
            }
            return true;
        }
        
        void cofactor(expr * t, expr_ref & r) {
            unsigned step = 0;
            TRACE("cofactor", tout << "cofactor target:\n" << mk_ismt2_pp(t, m) << "\n";);
            expr_ref curr(m);
            curr = t;
            while (true) {
                expr * c = m_owner.get_best(curr);
                // expr * c = m_owner.get_first(curr);
                if (c == nullptr) {
                    r = curr.get();
                    return;
                }
                step++;
                expr_ref pos_cofactor(m);
                expr_ref neg_cofactor(m);
                m_cofactor.set_cofactor_atom(c);
                m_cofactor(curr, pos_cofactor);
                expr_ref neg_c(m);
                neg_c = m.is_not(c) ? to_app(c)->get_arg(0) : m.mk_not(c);                    
                m_cofactor.set_cofactor_atom(neg_c);
                m_cofactor(curr, neg_cofactor);
                if (pos_cofactor == neg_cofactor) {
                    curr = pos_cofactor;
                }
                else if (m.is_true(pos_cofactor) && m.is_false(neg_cofactor)) {
                    curr = c;
                }
                else if (m.is_false(pos_cofactor) && m.is_true(neg_cofactor)) {
                    curr = neg_c;
                }
                else {
                    curr = m.mk_ite(c, pos_cofactor, neg_cofactor);
                }
                TRACE("cofactor", 
                      tout << "cofactor_ite step: " << step << "\n";
                      tout << "cofactor: " << mk_ismt2_pp(c, m) << "\n";
                      tout << mk_ismt2_pp(curr, m) << "\n";);
            }
        }

        void visit(expr * t, bool & visited) {
            if (!m_cache.contains(t)) {
                m_frames.push_back(frame(t, true));
                visited = false;
            }
        }
        
        void operator()(expr * t, expr_ref & r) {
            ptr_vector<expr> new_args;
            SASSERT(m_frames.empty());
            m_frames.push_back(frame(t, true));
            while (!m_frames.empty()) {
                m_owner.checkpoint();
                frame & fr = m_frames.back();
                expr * t   = fr.first;
                TRACE("cofactor_bug", tout << "processing: " << t->get_id() << " :first " << fr.second << "\n";);
                if (!is_app(t)) {
                    m_cache.insert(t, t);
                    m_frames.pop_back();
                    continue;
                }
                if (m_cache.contains(t)) {
                    m_frames.pop_back();
                    continue;
                }
                if (fr.second) {
                    fr.second    = false;
                    bool visited = true;
                    unsigned i = to_app(t)->get_num_args();
                    while (i > 0) {
                        --i;
                        expr * arg = to_app(t)->get_arg(i);
                        visit(arg, visited);
                    }
                    if (!visited)
                        continue;
                }
                new_args.reset();
                bool has_new_args = false;
                bool has_term_ite = false;
                unsigned num = to_app(t)->get_num_args();
                for (unsigned i = 0; i < num; i++) {
                    expr * arg = to_app(t)->get_arg(i);
                    expr * new_arg = nullptr;
                    TRACE("cofactor_bug", tout << "collecting child: " << arg->get_id() << "\n";);
                    m_cache.find(arg, new_arg);
                    SASSERT(new_arg != 0);
                    if (new_arg != arg)
                        has_new_args = true;
                    if (m_has_term_ite.contains(new_arg))
                        has_term_ite = true;
                    new_args.push_back(new_arg);
                }
                if (m.is_term_ite(t))
                    has_term_ite = true;
                expr_ref new_t(m);
                if (has_new_args)
                    new_t = m.mk_app(to_app(t)->get_decl(), num, new_args.c_ptr());
                else
                    new_t = t;
                if (has_term_ite && is_atom(new_t)) {
                    // update new_t
                    expr_ref new_new_t(m);
                    m_has_term_ite.insert(new_t);
                    cofactor(new_t, new_new_t);
                    m_has_term_ite.erase(new_t);
                    new_t = new_new_t;
                    has_term_ite = false;
                }
                if (has_term_ite)
                    m_has_term_ite.insert(new_t);
                SASSERT(new_t.get() != 0);
                TRACE("cofactor_bug", tout << "caching: " << t->get_id() << "\n";);
#if 0
                counter ++;
                verbose_stream() << counter << "\n";
#endif
                m_cache.insert(t, new_t);
                m_cache_domain.push_back(new_t);
                m_frames.pop_back();
            }
            expr * result = nullptr;
            m_cache.find(t, result);
            r = result;
        }
    };

    imp(ast_manager & _m, params_ref const & p):
        m(_m),
        m_params(p),
        m_cofactor_equalities(true) {
        updt_params(p);
    }

    void operator()(expr * t, expr_ref & r) {
#if 0
        analyzer proc(m, *this);
        proc(t); 
        main_rw rw(m, *this, proc.m_candidates);
        rw(t, r);
#else
        bottom_up_elim proc(m, *this);
        proc(t, r);
#endif
    }
};


cofactor_elim_term_ite::cofactor_elim_term_ite(ast_manager & m, params_ref const & p):
    m_imp(alloc(imp, m, p)),
    m_params(p) {
}

cofactor_elim_term_ite::~cofactor_elim_term_ite() {
    dealloc(m_imp);
}

void cofactor_elim_term_ite::updt_params(params_ref const & p) {
    m_imp->updt_params(p);
}

void cofactor_elim_term_ite::collect_param_descrs(param_descrs & r) {
    m_imp->collect_param_descrs(r);
}

void cofactor_elim_term_ite::operator()(expr * t, expr_ref & r) {
    m_imp->operator()(t, r);
}
    

void cofactor_elim_term_ite::cleanup() {
    ast_manager & m = m_imp->m;    
    imp * d = alloc(imp, m, m_params);
    std::swap(d, m_imp);    
    dealloc(d);
}

