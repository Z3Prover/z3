/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    tseitin_cnf_tactic.cpp

Abstract:

    Puts an assertion set in CNF.
    Auxiliary variables are used to avoid blowup.

    Features:
    
    - Efficient encoding is used for commonly used patterns such as:
       (iff a (iff b c))
       (or (not (or a b)) (not (or a c)) (not (or b c)))

    - Efficient encoding is used for chains of if-then-elses 

    - Distributivity is applied to non-shared nodes if the blowup is acceptable.
    
    - The features above can be disabled/enabled using parameters.

    - The assertion-set is only modified if the resultant set of clauses
    is "acceptable".

    Notes: 
    
    - Term-if-then-else expressions are not handled by this strategy.
    This kind of expression should be processed by other strategies.

    - Quantifiers are treated as "theory" atoms. They are viewed
    as propositional variables by this strategy.
    
    - The assertion set may contain free variables. 

    - This strategy assumes the assertion_set_rewriter was
    used before invoking it.
    In particular, it is more effective when "and" operators
    were eliminated.

    TODO: add proof production

Author:

    Leonardo (leonardo) 2011-12-29

Notes:

--*/
#include "tactic/tactical.h"
#include "tactic/goal_shared_occs.h"
#include "tactic/generic_model_converter.h"
#include "ast/rewriter/bool_rewriter.h"
#include "tactic/core/simplify_tactic.h"
#include "util/cooperate.h"

static void swap_if_gt(expr * & n1, expr * & n2) {
    if (n1->get_id() > n2->get_id())
        std::swap(n1, n2);
}

/**
   \brief Return true if n is of the form (= a b)
*/
static bool is_iff(ast_manager & m, expr * n, expr * & a, expr * & b) {
    if (m.is_iff(n, a, b))
        return true;
    if (m.is_eq(n, a, b) && m.is_bool(a))
        return true;
    return false;
}

class tseitin_cnf_tactic : public tactic {
    struct imp {
        struct frame {
            app *     m_t;
            bool      m_first;
            frame(app * n):m_t(n), m_first(true) {}
        };
        
        typedef generic_model_converter mc;
        
        ast_manager &              m;
        svector<frame>             m_frame_stack;
        obj_map<app, app*>         m_cache;
        expr_ref_vector            m_cache_domain;
        goal_shared_occs           m_occs;
        expr_ref_vector            m_fresh_vars;
        ref<mc>                    m_mc;
        expr_ref_vector            m_clauses;
        expr_dependency_ref_vector m_deps;
        bool_rewriter              m_rw;
        expr_dependency *          m_curr_dep;
        bool                       m_produce_models;
        bool                       m_produce_unsat_cores;

        // parameters
        bool                 m_common_patterns;
        bool                 m_distributivity;
        unsigned             m_distributivity_blowup;
        bool                 m_ite_chains;
        bool                 m_ite_extra;
        unsigned long long   m_max_memory;

        unsigned             m_num_aux_vars;

        imp(ast_manager & _m, params_ref const & p):
            m(_m),
            m_cache_domain(_m),
            m_occs(m, false /* don't track atoms */, false /* do not visit quantifiers */),
            m_fresh_vars(_m),
            m_clauses(_m),
            m_deps(_m),
            m_rw(_m),
            m_num_aux_vars(0) {
            updt_params(p);
            m_rw.set_flat(false);
        }
        
        void updt_params(params_ref const & p) {
            m_common_patterns = p.get_bool("common_patterns", true);
            m_distributivity  = p.get_bool("distributivity",  true);
            m_distributivity_blowup = p.get_uint("distributivity_blowup", 32);
            m_ite_chains      = p.get_bool("ite_chains", true);
            m_ite_extra       = p.get_bool("ite_extra", true);
            m_max_memory      = megabytes_to_bytes(p.get_uint("max_memory", UINT_MAX));
        }
        
        void push_frame(app * n) { m_frame_stack.push_back(frame(n)); }
        
        void throw_op_not_handled() {
            throw tactic_exception("operator not supported, apply simplifier before invoking this strategy");
        }
        
        void inv(expr * n, expr_ref & r) {
            if (m.is_true(n)) {
                r = m.mk_false();
                return;
            }
            if (m.is_false(n)) {
                r = m.mk_true();
                return; 
            }
            if (m.is_not(n)) {
                r = to_app(n)->get_arg(0);
                return;
            }
            r = m.mk_not(n);
        }

        void mk_lit(expr * n, bool sign, expr_ref & r) {
            if (sign)
                r = m.mk_not(n);
            else
                r = n;
        }
        
        void get_lit(expr * n, bool sign, expr_ref & r) {
        start:
            if (!is_app(n) ||
                to_app(n)->get_num_args() == 0) {
                mk_lit(n, sign, r);
                return;
            }
            func_decl * f = to_app(n)->get_decl();
            if (f->get_family_id() != m.get_basic_family_id()) {
                mk_lit(n, sign, r);
                return;
            }
            app * l;
            switch (f->get_decl_kind()) {
            case OP_NOT:
                n    = to_app(n)->get_arg(0);
                sign = !sign;
                goto start;
            case OP_OR:
                l = nullptr;
                m_cache.find(to_app(n), l);
                SASSERT(l != 0);
                mk_lit(l, sign, r);
                return;
            case OP_ITE:
            case OP_EQ:
                if (m.is_bool(to_app(n)->get_arg(1))) {
                    l = nullptr;
                    m_cache.find(to_app(n), l);
                    SASSERT(l != 0);
                    mk_lit(l, sign, r);
                    return;
                }
                mk_lit(n, sign, r);
                return;
            default:
                TRACE("tseitin_cnf_bug", tout << f->get_name() << "\n";);
                UNREACHABLE();
                return;
            }
        }
        
        void visit(expr * n, bool & visited, bool root = false) {
        start:
            if (!is_app(n))
                return;
            if (m_cache.contains(to_app(n)))
                return;
            if (to_app(n)->get_num_args() == 0)
                return;
            func_decl * f = to_app(n)->get_decl();
            if (f->get_family_id() != m.get_basic_family_id())
                return;
            switch (f->get_decl_kind()) {
            case OP_NOT:
                if (root) {
                    visited = false;
                    push_frame(to_app(n));
                    return;
                }
                else {
                    n = to_app(n)->get_arg(0);
                    goto start;
                }
            case OP_OR:
                visited = false;
                push_frame(to_app(n));
                return;
            case OP_ITE:
            case OP_EQ:
                if (m.is_bool(to_app(n)->get_arg(1))) {
                    visited = false;
                    push_frame(to_app(n));
                }
                return;
            case OP_AND:
            case OP_XOR:
            case OP_IMPLIES:
            case OP_DISTINCT:
                throw_op_not_handled();
            default:
                return;
            }
        }
        
        bool is_shared(expr * t) {
            return m_occs.is_shared(t);
        }
        
        /**
           \brief Return true if n is of the form
           
           (or (not (or a b)) (not (or a c)) (not (or b c)))
           
           \remark This pattern is found in the following "circuits":
           - carry
           - less-than (signed and unsigned)
        */
        bool is_or_3and(expr * n, expr * & a, expr * & b, expr * & c) {
            expr * a1, * a2, * b1, * b2, * c1, * c2;
            if (!m.is_or(n, a1, b1, c1) ||
                !m.is_not(a1, a1) || 
                is_shared(a1) ||
                !m.is_not(b1, b1) || 
                is_shared(b1) ||
                !m.is_not(c1, c1) ||
                is_shared(c1) ||
                !m.is_or(a1, a1, a2) ||
                !m.is_or(b1, b1, b2) ||
                !m.is_or(c1, c1, c2))
                return false;
            
            swap_if_gt(a1, a2);
            swap_if_gt(b1, b2);
            swap_if_gt(c1, c2);
            
            if ((a1 == b1 && a2 == c1 && b2 == c2) ||
                (a1 == b1 && a2 == c2 && b2 == c1) ||
                (a1 == c1 && a2 == b1 && b2 == c2)) {
                a = a1; b = a2; c = b2;
                return true;
            }
            
            if ((a1 == b2 && a2 == c2 && b1 == c1) ||
                (a1 == c1 && a2 == b2 && b1 == c2) ||
                (a1 == c2 && a2 == b2 && b1 == c1)) {
                a = a1; b = a2; c = b1;
                return true;
            }
            
            return false;
        }
        
        
        /**
           \brief Return true if n is of the form
           (iff a (iff b c))
        */
        bool is_iff3(expr * n, expr * & a, expr * & b, expr * & c) {
            expr * l1, * l2;
            if (!is_iff(m, n, l1, l2))
                return false;
            if (!is_shared(l1) && is_iff(m, l1, a, b)) {
                c = l2;
                return true;
            }
            if (!is_shared(l2) && is_iff(m, l2, b, c)) {
                a = l1;
                return true;
            }
            return false;
        }
        
        void mk_clause(unsigned num, expr * const * ls) {
            expr_ref cls(m);
            m_rw.mk_or(num, ls, cls);
            m_clauses.push_back(cls);
            if (m_produce_unsat_cores)
                m_deps.push_back(m_curr_dep);
        }
        
        void mk_clause(expr * l1) {
            return mk_clause(1, &l1);
        }
        
        void mk_clause(expr * l1, expr * l2) {
            expr * ls[2] = { l1, l2 };
            mk_clause(2, ls);
        }
        
        void mk_clause(expr * l1, expr * l2, expr * l3) {
            expr * ls[3] = { l1, l2, l3 };
            mk_clause(3, ls);
        }
        
        void mk_clause(expr * l1, expr * l2, expr * l3, expr * l4) {
            expr * ls[4] = { l1, l2, l3, l4 };
            mk_clause(4, ls);
        }
        
        app * mk_fresh() {
            m_num_aux_vars++;
            app * v = m.mk_fresh_const(nullptr, m.mk_bool_sort());
            m_fresh_vars.push_back(v);
            if (m_mc)
                m_mc->hide(v->get_decl());
            return v;
        }
        
        void cache_result(app * t, app * r) {
            m_cache.insert(t, r);
            m_cache_domain.push_back(t);
        }
        
        enum mres {
            NO,    // did not match
            CONT,  // matched but the children need to be processed
            DONE   // matched 
        };

        mres match_not(app * t, bool first, bool root) {
            expr * a;
            if (m.is_not(t, a)) {
                if (first) {
                    bool visited = true;
                    visit(a, visited);
                    if (!visited)
                        return CONT;
                }
                expr_ref nla(m);
                get_lit(a, true, nla);
                if (root) {
                    mk_clause(nla);
                }
                // Remark: don't need to do anything if it is not a root.
                return DONE;
            }
            return NO;
        }
        
        mres match_or_3and(app * t, bool first, bool root) {
            if (!m_common_patterns)
                return NO;
            expr * a, * b, * c;
            if (is_or_3and(t, a, b, c)) {
                if (first) {
                    bool visited = true;
                    visit(a, visited);
                    visit(b, visited);
                    visit(c, visited);
                    if (!visited)
                        return CONT;
                }
                expr_ref nla(m), nlb(m), nlc(m);
                get_lit(a, true, nla);
                get_lit(b, true, nlb);
                get_lit(c, true, nlc);
                if (root) {
                    mk_clause(nla, nlb);
                    mk_clause(nla, nlc);
                    mk_clause(nlb, nlc);
                }
                else {
                    app_ref k(m), nk(m);
                    k  = mk_fresh();
                    nk = m.mk_not(k);
                    mk_clause(nk, nla, nlb);
                    mk_clause(nk, nla, nlc);
                    mk_clause(nk, nlb, nlc);
                    expr_ref la(m), lb(m), lc(m);
                    inv(nla, la);
                    inv(nlb, lb);
                    inv(nlc, lc);
                    mk_clause(k,  la,  lb);
                    mk_clause(k,  la,  lc);
                    mk_clause(k,  lb,  lc);
                    cache_result(t, k);
                }
                return DONE;
            }
            return NO;
        }

        mres match_iff3(app * t, bool first, bool root) {
            if (!m_common_patterns)
                return NO;
            expr * a, * b, * c;
            if (is_iff3(t, a, b, c)) {
                if (first) {
                    bool visited = true;
                    visit(a, visited);
                    visit(b, visited);
                    visit(c, visited);
                    if (!visited)
                        return CONT;
                }
                expr_ref la(m), lb(m), lc(m);
                expr_ref nla(m), nlb(m), nlc(m);
                get_lit(a, false, la);
                get_lit(b, false, lb);
                get_lit(c, false, lc);
                inv(la, nla);
                inv(lb, nlb);
                inv(lc, nlc);
                if (root) {
                    mk_clause(la,   lb,  lc);
                    mk_clause(la,  nlb, nlc);
                    mk_clause(nla,  lb, nlc);
                    mk_clause(nla, nlb,  lc); 
                }
                else {
                    app_ref k(m), nk(m);
                    k  = mk_fresh();
                    nk = m.mk_not(k);
                    mk_clause(nk, la,   lb,  lc);
                    mk_clause(nk, la,  nlb, nlc);
                    mk_clause(nk, nla,  lb, nlc);
                    mk_clause(nk, nla, nlb,  lc); 
                    
                    mk_clause(k, nla, nlb, nlc);
                    mk_clause(k, nla,  lb,  lc);
                    mk_clause(k,  la, nlb,  lc);
                    mk_clause(k,  la,  lb, nlc); 
                    cache_result(t, k);
                }
                return DONE;
            }
            return NO;
        }

        mres match_iff_or(app * t, bool first, bool root) {
            expr * a = nullptr, * _b = nullptr;
            if (!root) return NO;
            if (!is_iff(m, t, a, _b)) return NO;
            bool sign = m.is_not(_b, _b);
            if (!m.is_or(_b)) return NO;
            app* b = to_app(_b);
            if (first) {
                bool visited = true;
                visit(a, visited);
                for (expr* arg : *b) {
                    visit(arg, visited);
                }
                if (!visited)
                    return CONT;
            }
            expr_ref la(m), nla(m), nlb(m), lb(m);
            get_lit(a, sign, la);
            inv(la, nla);
            expr_ref_buffer lits(m); 
            lits.push_back(nla);
            for (expr* arg : *b) {
                get_lit(arg, false, lb);
                lits.push_back(lb);
                inv(lb, nlb);
                mk_clause(la, nlb);
            }
            mk_clause(lits.size(), lits.c_ptr());
            return DONE;
        }
        
        mres match_iff(app * t, bool first, bool root) {
            expr * a, * b;
            if (is_iff(m, t, a, b)) {
                if (first) {
                    bool visited = true;
                    visit(a, visited);
                    visit(b, visited);
                    if (!visited)
                        return CONT;
                }
                expr_ref la(m), lb(m);
                expr_ref nla(m), nlb(m);
                get_lit(a, false, la);
                get_lit(b, false, lb);
                inv(la, nla);
                inv(lb, nlb);
                if (root) {
                    mk_clause(la,  nlb);
                    mk_clause(nla,  lb);
                }
                else {
                    app_ref k(m), nk(m);
                    k  = mk_fresh();
                    nk = m.mk_not(k);
                    
                    mk_clause(nk, la,  nlb);
                    mk_clause(nk, nla,  lb);
                    
                    mk_clause(k, nla, nlb);
                    mk_clause(k,  la,  lb);
                    cache_result(t, k);
                }
                return DONE;
            }
            return NO;
        }
        
        mres match_ite(app * t, bool first, bool root) {
            if (!m.is_ite(t))
                return NO;
            if (first) {
                bool visited = true;
                app * ite = t;
                while (true) {
                    visit(ite->get_arg(0), visited);
                    if (m_ite_chains && m.is_ite(ite->get_arg(1)) && !is_shared(ite->get_arg(1))) {
                        visit(ite->get_arg(2), visited);
                        ite = to_app(ite->get_arg(1));
                        continue;
                    }
                    if (m_ite_chains && m.is_ite(ite->get_arg(2)) && !is_shared(ite->get_arg(2))) {
                        visit(ite->get_arg(1), visited);
                        ite = to_app(ite->get_arg(2));
                        continue;
                    }
                    visit(ite->get_arg(1), visited);
                    visit(ite->get_arg(2), visited);
                    break;
                }
                if (!visited)
                    return CONT;
            }
            expr_ref_buffer ctx(m);
            expr_ref_buffer ex_pos_ctx(m); // for extra ite clauses
            expr_ref_buffer ex_neg_ctx(m); // for extra ite clauses
            expr_ref la(m),   lb(m), lc(m);
            expr_ref nla(m), nlb(m), nlc(m);
            app_ref k(m), nk(m);
            if (!root) {
                k = mk_fresh();
                nk = m.mk_not(k);
                cache_result(t, k);
            }
            
#define MK_ITE_ROOT_CLS(L1, L2) {               \
    ctx.push_back(L1); ctx.push_back(L2);       \
    mk_clause(ctx.size(), ctx.c_ptr());         \
    ctx.pop_back(); ctx.pop_back();             \
}
            
#define MK_ITE_CLS(L1, L2, L3) {                                \
    ctx.push_back(L1); ctx.push_back(L2); ctx.push_back(L3);    \
    mk_clause(ctx.size(), ctx.c_ptr());                         \
    ctx.pop_back(); ctx.pop_back(); ctx.pop_back();             \
}
            
            app * ite = t;
            while (true) {
                get_lit(ite->get_arg(0), false, la);
                inv(la, nla);
                if (m_ite_chains && m.is_ite(ite->get_arg(1)) && !is_shared(ite->get_arg(1))) {
                    get_lit(ite->get_arg(2), false, lc);
                    if (root) {
                        MK_ITE_ROOT_CLS(la, lc);
                    }
                    else {
                        inv(lc, nlc);
                        MK_ITE_CLS(la, lc, nk);
                        MK_ITE_CLS(la, nlc, k);
                        if (m_ite_extra) {
                            ex_neg_ctx.push_back(lc);
                            ex_pos_ctx.push_back(nlc);
                        }
                    }
                    ctx.push_back(nla);
                    ite = to_app(ite->get_arg(1));
                    continue;
                }
                if (m_ite_chains && m.is_ite(ite->get_arg(2)) && !is_shared(ite->get_arg(2))) {
                    get_lit(ite->get_arg(1), false, lb);
                    if (root) {
                        MK_ITE_ROOT_CLS(nla, lb);
                    }
                    else {
                        inv(lb, nlb);
                        MK_ITE_CLS(nla, lb, nk);
                        MK_ITE_CLS(nla, nlb, k);
                        if (m_ite_extra) {
                            ex_neg_ctx.push_back(lb);
                            ex_pos_ctx.push_back(nlb);
                        }
                    }
                    ctx.push_back(la);
                    ite = to_app(ite->get_arg(2));
                    continue;
                }
                get_lit(ite->get_arg(1), false, lb);
                get_lit(ite->get_arg(2), false, lc);
                if (root) {
                    MK_ITE_ROOT_CLS(nla, lb);
                    MK_ITE_ROOT_CLS(la,  lc);
                }
                else {
                    inv(lb, nlb);
                    inv(lc, nlc);
                    MK_ITE_CLS(nla, lb, nk);
                    MK_ITE_CLS(la,  lc, nk);
                    MK_ITE_CLS(nla, nlb, k);
                    MK_ITE_CLS(la,  nlc, k);
                    if (m_ite_extra) {
                        MK_ITE_CLS(lb,   lc, nk);
                        MK_ITE_CLS(nlb, nlc, k);
                        
                        ex_neg_ctx.push_back(lb); ex_neg_ctx.push_back(lc); ex_neg_ctx.push_back(nk);
                        mk_clause(ex_neg_ctx.size(), ex_neg_ctx.c_ptr());
                        ex_pos_ctx.push_back(nlb); ex_pos_ctx.push_back(nlc); ex_pos_ctx.push_back(k);
                        mk_clause(ex_pos_ctx.size(), ex_pos_ctx.c_ptr());
                    }
                }
                break;
            }
            return DONE;
        }
        
        mres match_or(app * t, bool first, bool root) {
            if (!m.is_or(t))
                return NO;
            if (first) {
                bool visited = true;
                unsigned num = t->get_num_args();
                unsigned blowup = 1;
                for (unsigned i = 0; i < num; i++) {
                    expr * a = t->get_arg(i);
                    expr * a0;
                    if (m_distributivity && m.is_not(a, a0) && m.is_or(a0) && !is_shared(a0)) {
                        unsigned num2 = to_app(a0)->get_num_args();
                        if (num2 < m_distributivity_blowup && blowup * num2 < m_distributivity_blowup && blowup < blowup * num2) { 
                            blowup *= num2;
                            for (unsigned j = 0; j < num2; j++)
                                visit(to_app(a0)->get_arg(j), visited);
                            continue;
                        }
                    }
                    visit(a, visited);
                }
                if (!visited)
                    return CONT;
            }
            
            app_ref k(m), nk(m);
            if (!root) {
                k = mk_fresh();
                nk = m.mk_not(k);
                cache_result(t, k);
            }
            
            unsigned num = t->get_num_args();
            bool distributivity = false;
            if (m_distributivity) {
                // check if need to apply distributivity
                for (unsigned i = 0; i < num; i++) {
                    expr * a = t->get_arg(i);
                    expr * a0;
                    if (m.is_not(a, a0) && m.is_or(a0) && !is_shared(a0) && to_app(a0)->get_num_args() < m_distributivity_blowup) {
                        distributivity = true;
                        break;
                    }
                }
            }
            
            if (!distributivity) {
                // easy case
                expr_ref_buffer lits(m); expr_ref l(m);
                for (unsigned i = 0; i < num; i++) {
                    get_lit(t->get_arg(i), false, l);
                    lits.push_back(l);
                }
                if (root) {
                    mk_clause(lits.size(), lits.c_ptr());
                }
                else {
                    for (unsigned i = 0; i < num; i++) {
                        inv(lits[i], l);
                        mk_clause(l, k);
                    }
                    lits.push_back(nk);
                    mk_clause(lits.size(), lits.c_ptr());
                }
            }
            else {
                expr_ref_buffer buffer(m); expr_ref l(m), nl(m);
                sbuffer<unsigned> szs;
                sbuffer<unsigned> it;
                sbuffer<unsigned> offsets;
                unsigned blowup = 1;
                for (unsigned i = 0; i < num; i++) {
                    it.push_back(0);
                    offsets.push_back(buffer.size());
                    expr * a = t->get_arg(i);
                    expr * a0;
                    if (m.is_not(a, a0) && m.is_or(a0) && !is_shared(a0)) {
                        unsigned num2 = to_app(a0)->get_num_args();
                        if (num2 < m_distributivity_blowup && blowup * num2 < m_distributivity_blowup && blowup < blowup * num2) { 
                            szs.push_back(num2);
                            blowup *= num2;
                            expr_ref_buffer lits(m);
                            for (unsigned j = 0; j < num2; j++) {
                                get_lit(to_app(a0)->get_arg(j), true, nl);
                                buffer.push_back(nl);
                                if (!root) {
                                    inv(nl, l);
                                    lits.push_back(l);
                                }
                            }
                            if (!root) {
                                lits.push_back(k);
                                mk_clause(lits.size(), lits.c_ptr());
                            }
                            continue;
                        }
                    }
                    szs.push_back(1);
                    get_lit(a, false, l);
                    buffer.push_back(l);
                    if (!root) {
                        inv(l, nl);
                        mk_clause(nl, k); 
                    }
                }
                SASSERT(offsets.size() == num);
                sbuffer<expr**> arg_lits;
                ptr_buffer<expr> lits;
                expr ** buffer_ptr = buffer.c_ptr();
                for (unsigned i = 0; i < num; i++) {
                    arg_lits.push_back(buffer_ptr + offsets[i]);
                }
                do {
                    lits.reset();
                    for (unsigned i = 0; i < num; i++) {
                        lits.push_back(arg_lits[i][it[i]]);
                    }
                    if (!root)
                        lits.push_back(nk);
                    mk_clause(lits.size(), lits.c_ptr());
                }
                while (product_iterator_next(szs.size(), szs.c_ptr(), it.c_ptr()));
            }
            return DONE;
        }
        
#define TRY(_MATCHER_)                                          \
    r = _MATCHER_(t, first, t == root);                         \
    if (r == CONT) goto loop;                                   \
    if (r == DONE) { m_frame_stack.pop_back(); continue; }
        
        
        void checkpoint() {
            cooperate("tseitin cnf");
            if (m.canceled())
                throw tactic_exception(TACTIC_CANCELED_MSG);
            if (memory::get_allocation_size() > m_max_memory)
                throw tactic_exception(TACTIC_MAX_MEMORY_MSG);
        }

        void process(expr * n, expr_dependency * dep) {
            m_curr_dep = dep;
            bool visited = true;
            visit(n, visited, true);
            if (visited) {
                expr_ref l(m);
                get_lit(n, false, l);
                mk_clause(l);
                return;
            }
            expr * root = n;
            
            app * t; bool first; mres r;
            while (!m_frame_stack.empty()) {
            loop:
                checkpoint();
                frame & fr = m_frame_stack.back();
                t = fr.m_t;
                first = fr.m_first;
                fr.m_first = false;
                TRY(match_or_3and);
                TRY(match_or);
                TRY(match_iff3);
                // TRY(match_iff_or);
                TRY(match_iff);
                TRY(match_ite);
                TRY(match_not);
                UNREACHABLE();
            }
        }

        void reset_cache() {
            m_cache.reset();
            m_cache_domain.reset();
        }

        void operator()(goal_ref const & g, 
                        goal_ref_buffer & result) {
            SASSERT(g->is_well_sorted());
            tactic_report report("tseitin-cnf", *g);
            fail_if_proof_generation("tseitin-cnf", g);
            m_produce_models      = g->models_enabled();
            m_produce_unsat_cores = g->unsat_core_enabled(); 

            m_occs(*g);
            reset_cache();
            m_deps.reset();
            m_fresh_vars.reset();
            m_frame_stack.reset();
            m_clauses.reset();
            if (m_produce_models)
                m_mc = alloc(generic_model_converter, m, "tseitin");
            else
                m_mc = nullptr;

            unsigned size = g->size();
            for (unsigned idx = 0; idx < size; idx++) {
                process(g->form(idx), g->dep(idx));
                g->update(idx, m.mk_true(), nullptr, nullptr); // to save memory
            }

            SASSERT(!m_produce_unsat_cores || m_clauses.size() == m_deps.size());

            g->reset();
            unsigned sz = m_clauses.size();
            expr_fast_mark1 added;
            for (unsigned i = 0; i < sz; i++) {
                expr * cls = m_clauses.get(i);
                if (added.is_marked(cls))
                    continue;
                added.mark(cls);
                if (m_produce_unsat_cores)
                    g->assert_expr(cls, nullptr, m_deps.get(i));
                else
                    g->assert_expr(cls);
            }
            if (m_produce_models && !m_fresh_vars.empty()) 
                g->add(m_mc.get());
            g->inc_depth();
            result.push_back(g.get());
            TRACE("tseitin_cnf", g->display(tout););
            SASSERT(g->is_well_sorted());
        }
    };
    
    imp *      m_imp;
    params_ref m_params;
public:
    tseitin_cnf_tactic(ast_manager & m, params_ref const & p):
        m_params(p) {
        m_imp = alloc(imp, m, p);
    }

    tactic * translate(ast_manager & m) override {
        return alloc(tseitin_cnf_tactic, m, m_params);
    }
        
    ~tseitin_cnf_tactic() override {
        dealloc(m_imp);
    }

    void updt_params(params_ref const & p) override {
        m_params = p;
        m_imp->updt_params(p);
    }

    void collect_param_descrs(param_descrs & r) override {
        insert_max_memory(r);
        r.insert("common_patterns", CPK_BOOL, "(default: true) minimize the number of auxiliary variables during CNF encoding by identifing commonly used patterns");
        r.insert("distributivity", CPK_BOOL, "(default: true) minimize the number of auxiliary variables during CNF encoding by applying distributivity over unshared subformulas");
        r.insert("distributivity_blowup", CPK_UINT, "(default: 32) maximum overhead for applying distributivity during CNF encoding");
        r.insert("ite_chaing", CPK_BOOL, "(default: true) minimize the number of auxiliary variables during CNF encoding by identifing if-then-else chains");                                                       
        r.insert("ite_extra", CPK_BOOL, "(default: true) add redundant clauses (that improve unit propagation) when encoding if-then-else formulas");
    }
    
    void operator()(goal_ref const & in, goal_ref_buffer & result) override {
        (*m_imp)(in, result);
        report_tactic_progress(":cnf-aux-vars", m_imp->m_num_aux_vars);
    }
    
    void cleanup() override {
        ast_manager & m = m_imp->m;
        imp * d = alloc(imp, m, m_params);
        d->m_num_aux_vars = m_imp->m_num_aux_vars;
        std::swap(d, m_imp);        
        dealloc(d);
    }

    void collect_statistics(statistics & st) const override {
        st.update("cnf encoding aux vars", m_imp->m_num_aux_vars);
    }
    
    void reset_statistics() override {
        m_imp->m_num_aux_vars = 0;
    }
};

tactic * mk_tseitin_cnf_core_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(tseitin_cnf_tactic, m, p));
}

tactic * mk_tseitin_cnf_tactic(ast_manager & m, params_ref const & p) {
    params_ref simp_p = p;
    simp_p.set_bool("elim_and", true);
    simp_p.set_bool("blast_distinct", true);
    return or_else(mk_tseitin_cnf_core_tactic(m, p),
                   and_then(using_params(mk_simplify_tactic(m, p), simp_p),
                            mk_tseitin_cnf_core_tactic(m, p)));
}
