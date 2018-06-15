/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    elim_uncnstr_vars.cpp

Abstract:

    Eliminated unconstrained variables.

Author:

    Leonardo (leonardo) 2011-10-22

Notes:

--*/
#include "tactic/tactical.h"
#include "tactic/generic_model_converter.h"
#include "ast/rewriter/rewriter_def.h"
#include "ast/arith_decl_plugin.h"
#include "ast/bv_decl_plugin.h"
#include "ast/array_decl_plugin.h"
#include "ast/datatype_decl_plugin.h"
#include "tactic/core/collect_occs.h"
#include "util/cooperate.h"
#include "ast/ast_smt2_pp.h"
#include "ast/ast_ll_pp.h"

class elim_uncnstr_tactic : public tactic {

    struct imp {
        // unconstrained vars collector

        typedef generic_model_converter mc;

        struct rw_cfg : public default_rewriter_cfg {
            bool                   m_produce_proofs;
            obj_hashtable<expr> &  m_vars;
            ref<mc>                m_mc;
            arith_util             m_a_util;
            bv_util                m_bv_util;
            array_util             m_ar_util;
            datatype_util          m_dt_util;
            app_ref_vector         m_fresh_vars;
            obj_map<app, app*>     m_cache;
            app_ref_vector         m_cache_domain;
            unsigned long long     m_max_memory;
            unsigned               m_max_steps;
            
            rw_cfg(ast_manager & m, bool produce_proofs, obj_hashtable<expr> & vars, mc * _m, 
                   unsigned long long max_memory, unsigned max_steps):
                m_produce_proofs(produce_proofs),
                m_vars(vars),
                m_mc(_m),
                m_a_util(m),
                m_bv_util(m),
                m_ar_util(m),
                m_dt_util(m),
                m_fresh_vars(m),
                m_cache_domain(m),
                m_max_memory(max_memory),
                m_max_steps(max_steps) {
            }
            
            ast_manager & m() const { return m_a_util.get_manager(); }
            
            bool max_steps_exceeded(unsigned num_steps) const { 
                cooperate("elim-uncnstr-vars");
                if (memory::get_allocation_size() > m_max_memory)
                    throw tactic_exception(TACTIC_MAX_MEMORY_MSG);
                return num_steps > m_max_steps;
            }
            
            bool uncnstr(expr * arg) const {
                return m_vars.contains(arg);
            }
            
            bool uncnstr(unsigned num, expr * const * args) const {
                for (unsigned i = 0; i < num; i++)
                    if (!uncnstr(args[i]))
                        return false;
                return true;
            }
            
            /**
               \brief Create a fresh variable for abstracting (f args[0] ... args[num-1])
               Return true if it a new variable was created, and false if the variable already existed for this
               application. Store the variable in v
            */
            bool mk_fresh_uncnstr_var_for(app * t, app * & v) {
                if (m_cache.find(t, v)) {
                    return false; // variable already existed for this application
                }
                
                v = m().mk_fresh_const(nullptr, m().get_sort(t));
                TRACE("elim_uncnstr_bug", tout << "eliminating:\n" << mk_ismt2_pp(t, m()) << "\n";);
                TRACE("elim_uncnstr_bug_ll", tout << "eliminating:\n" << mk_bounded_pp(t, m()) << "\n";);
                m_fresh_vars.push_back(v);
                if (m_mc) m_mc->hide(v);
                m_cache_domain.push_back(t);
                m_cache.insert(t, v);
                return true;
            }

            bool mk_fresh_uncnstr_var_for(func_decl * f, unsigned num, expr * const * args, app * & v) {
                return mk_fresh_uncnstr_var_for(m().mk_app(f, num, args), v);
            }
            
            bool mk_fresh_uncnstr_var_for(func_decl * f, expr * arg1, expr * arg2, app * & v) {
                return mk_fresh_uncnstr_var_for(m().mk_app(f, arg1, arg2), v);
            }
            
            bool mk_fresh_uncnstr_var_for(func_decl * f, expr * arg, app * & v) {
                return mk_fresh_uncnstr_var_for(m().mk_app(f, arg), v);
            }
            
            void add_def(expr * v, expr * def) {
                SASSERT(uncnstr(v));
                SASSERT(to_app(v)->get_num_args() == 0);
                if (m_mc)
                    m_mc->add(to_app(v)->get_decl(), def);
            }
            
            void add_defs(unsigned num, expr * const * args, expr * u, expr * identity) {
                if (m_mc) {
                    add_def(args[0], u);
                    for (unsigned i = 1; i < num; i++)
                        add_def(args[i], identity);
                }
            }
            
            // return a term that is different from t.
            bool mk_diff(expr * t, expr_ref & r) {
                sort * s = m().get_sort(t);
                if (m().is_bool(s)) {
                    r = m().mk_not(t);
                    return true;
                }
                family_id fid = s->get_family_id();
                if (fid == m_a_util.get_family_id()) {
                    r = m_a_util.mk_add(t, m_a_util.mk_numeral(rational(1), s));
                    return true;
                }
                if (fid == m_bv_util.get_family_id()) {
                    r = m().mk_app(m_bv_util.get_family_id(), OP_BNOT, t);
                    return true;
                }
                if (fid == m_ar_util.get_family_id()) {
                    if (m().is_uninterp(get_array_range(s)))
                        return false;
                    unsigned arity = get_array_arity(s);
                    for (unsigned i = 0; i < arity; i++)
                        if (m().is_uninterp(get_array_domain(s, i)))
                            return false;
                    // building 
                    // r = (store t i1 ... in d)
                    // where i1 ... in are arbitrary values
                    // and d is a term different from (select t i1 ... in)
                    ptr_buffer<expr> new_args;
                    new_args.push_back(t);
                    for (unsigned i = 0; i < arity; i++)
                        new_args.push_back(m().get_some_value(get_array_domain(s, i)));
                    expr_ref sel(m());
                    sel = m().mk_app(fid, OP_SELECT, new_args.size(), new_args.c_ptr());
                    expr_ref diff_sel(m());
                    if (!mk_diff(sel, diff_sel))
                        return false;
                    new_args.push_back(diff_sel);
                    r = m().mk_app(fid, OP_STORE, new_args.size(), new_args.c_ptr());
                    return true;
                }
                if (fid == m_dt_util.get_family_id()) {
                    // In the current implementation, I only handle the case where
                    // the datatype has a recursive constructor.
                    ptr_vector<func_decl> const & constructors = *m_dt_util.get_datatype_constructors(s);
                    for (func_decl * constructor : constructors) {
                        unsigned num    = constructor->get_arity();
                        unsigned target = UINT_MAX;
                        for (unsigned i = 0; i < num; i++) {
                            sort * s_arg = constructor->get_domain(i);
                            if (s == s_arg) {
                                target = i;
                                continue;
                            }
                            if (m().is_uninterp(s_arg))
                                break;
                        }
                        if (target == UINT_MAX)
                            continue;
                        // use the constructor the distinct term constructor(...,t,...)
                        ptr_buffer<expr> new_args;
                        for (unsigned i = 0; i < num; i++) {
                            if (i == target) {
                                new_args.push_back(t);
                            }
                            else {
                                new_args.push_back(m().get_some_value(constructor->get_domain(i)));
                            }
                        }
                        r = m().mk_app(constructor, new_args.size(), new_args.c_ptr());
                        return true;
                    }
                    // TODO: handle more cases.
                    return false;
                }
                return false;
            }

            app * process_eq(func_decl * f, expr * arg1, expr * arg2) {
                expr * v;
                expr * t;
                if (uncnstr(arg1)) {
                    v = arg1;
                    t = arg2;
                }
                else if (uncnstr(arg2)) {
                    v = arg2;
                    t = arg1;
                }
                else {
                    return nullptr;
                }
                
                sort * s = m().get_sort(arg1);
                
                // Remark:
                // I currently do not support unconstrained vars that have
                // uninterpreted sorts, for the following reasons:
                // - Soundness
                //     (forall ((x S) (y S)) (= x y))
                //     (not (= c1 c2))
                //
                //   The constants c1 and c2 have only one occurrence in
                //   the formula above, but they are not really unconstrained.
                //   The quantifier forces S to have interpretations of size 1.
                //   If we replace (= c1 c2) with fresh k. The formula will
                //   become satisfiable. 
                //
                // - Even if the formula is quantifier free, I would still
                //   have to build an interpretation for the eliminated 
                //   variables.
                //
                if (!m().is_fully_interp(s))
                    return nullptr;
                
                // If the interpreted sort has only one element,
                // then it is unsound to eliminate the unconstrained variable in the equality
                sort_size sz = s->get_num_elements();
                
                if (sz.is_finite() && sz.size() <= 1)
                    return nullptr;
                
                if (!m_mc) {
                    // easy case, model generation is disabled.
                    app * u;
                    mk_fresh_uncnstr_var_for(f, arg1, arg2, u);
                    return u;
                }
                
                expr_ref d(m());
                if (mk_diff(t, d)) {
                    app * u;
                    if (!mk_fresh_uncnstr_var_for(f, arg1, arg2, u))
                        return u;
                    add_def(v, m().mk_ite(u, t, d));
                    return u;
                }
                return nullptr;
            }
            
            app * process_basic_app(func_decl * f, unsigned num, expr * const * args) {
                SASSERT(f->get_family_id() == m().get_basic_family_id());
                switch (f->get_decl_kind()) {
                case OP_ITE:
                    SASSERT(num == 3);
                    if (uncnstr(args[1]) && uncnstr(args[2])) {
                        app * r;
                        if (!mk_fresh_uncnstr_var_for(f, num, args, r))
                            return r;
                        add_def(args[1], r);
                        add_def(args[2], r);
                        return r;
                    }
                    if (uncnstr(args[0]) && uncnstr(args[1])) {
                        app * r;
                        if (!mk_fresh_uncnstr_var_for(f, num, args, r))
                            return r;
                        add_def(args[0], m().mk_true());
                        add_def(args[1], r);
                        return r;
                    }
                    if (uncnstr(args[0]) && uncnstr(args[2])) {
                        app * r;
                        if (!mk_fresh_uncnstr_var_for(f, num, args, r))
                            return r;
                        add_def(args[0], m().mk_false());
                        add_def(args[2], r);
                        return r;
                    }
                    return nullptr;
                case OP_NOT:
                    SASSERT(num == 1);
                    if (uncnstr(args[0])) {
                        app * r;
                        if (!mk_fresh_uncnstr_var_for(f, num, args, r))
                            return r;
                        if (m_mc)
                            add_def(args[0], m().mk_not(r));
                        return r;
                    }
                    return nullptr;
                case OP_AND:
                    if (num > 0 && uncnstr(num, args)) {
                        app * r;
                        if (!mk_fresh_uncnstr_var_for(f, num, args, r))
                            return r;
                        if (m_mc)
                            add_defs(num, args, r, m().mk_true());
                        return r;
                    }
                    return nullptr;
                case OP_OR:
                    if (num > 0 && uncnstr(num, args)) {
                        app * r;
                        if (!mk_fresh_uncnstr_var_for(f, num, args, r))
                            return r;
                        if (m_mc)
                            add_defs(num, args, r, m().mk_false());
                        return r;
                    }
                    return nullptr;
                case OP_EQ:
                    SASSERT(num == 2);
                    return process_eq(f, args[0], args[1]);
                default:
                    return nullptr;
                }
            }

            app * process_le_ge(func_decl * f, expr * arg1, expr * arg2, bool le) {
                expr * v;
                expr * t;
                if (uncnstr(arg1)) {
                    v = arg1;
                    t = arg2;
                }
                else if (uncnstr(arg2)) {
                    v = arg2;
                    t = arg1;
                    le = !le;
                }
                else {
                    return nullptr;
                }
                app * u;
                if (!mk_fresh_uncnstr_var_for(f, arg1, arg2, u))
                    return u;
                if (!m_mc)
                    return u;
                // v = ite(u, t, t + 1) if le
                // v = ite(u, t, t - 1) if !le
                add_def(v, m().mk_ite(u, t, m_a_util.mk_add(t, m_a_util.mk_numeral(rational(le ? 1 : -1), m().get_sort(arg1)))));
                return u;
            }

            app * process_add(family_id fid, decl_kind add_k, decl_kind sub_k, unsigned num, expr * const * args) {
                if (num == 0)
                    return nullptr;
                unsigned i;
                expr * v = nullptr;
                for (i = 0; i < num; i++) {
                    expr * arg = args[i];
                    if (uncnstr(arg)) {
                        v = arg;
                        break;
                    }
                }
                if (v == nullptr)
                    return nullptr;
                app  * u;
                if (!mk_fresh_uncnstr_var_for(m().mk_app(fid, add_k, num, args), u))
                    return u;
                if (!m_mc) 
                    return u;
                ptr_buffer<expr> new_args;
                for (unsigned j = 0; j < num; j++) {
                    if (j == i)
                        continue;
                    new_args.push_back(args[j]);
                }
                if (new_args.empty()) {
                    add_def(v, u);
                }
                else {
                    expr * rest;
                    if (new_args.size() == 1)
                        rest = new_args[0];
                    else
                        rest = m().mk_app(fid, add_k, new_args.size(), new_args.c_ptr());
                    add_def(v, m().mk_app(fid, sub_k, u, rest));
                }
                return u;
            }
            
            app * process_arith_mul(func_decl * f, unsigned num, expr * const * args) {
                if (num == 0)
                    return nullptr;
                sort * s = m().get_sort(args[0]);
                if (uncnstr(num, args)) {
                    app * r;
                    if (!mk_fresh_uncnstr_var_for(f, num, args, r))
                        return r;
                    if (m_mc)
                        add_defs(num, args, r, m_a_util.mk_numeral(rational(1), s));
                    return r;
                }
                // c * v case for reals
                bool is_int;
                rational val;
                if (num == 2 && uncnstr(args[1]) && m_a_util.is_numeral(args[0], val, is_int) && !is_int) {
                    if (val.is_zero())
                        return nullptr;
                    app * r;
                    if (!mk_fresh_uncnstr_var_for(f, num, args, r))
                        return r;
                    if (m_mc) {
                        val = rational(1) / val;
                        add_def(args[1], m_a_util.mk_mul(m_a_util.mk_numeral(val, false), r));
                    }
                    return r;
                }
                return nullptr;
            }
            
            app * process_arith_app(func_decl * f, unsigned num, expr * const * args) {
                
                SASSERT(f->get_family_id() == m_a_util.get_family_id());
                switch (f->get_decl_kind()) {
                case OP_ADD:
                    return process_add(f->get_family_id(), OP_ADD, OP_SUB, num, args);
                case OP_MUL:
                    return process_arith_mul(f, num, args);
                case OP_LE:
                    SASSERT(num == 2);
                    return process_le_ge(f, args[0], args[1], true);
                case OP_GE:
                    SASSERT(num == 2);
                    return process_le_ge(f, args[0], args[1], false);
                default:
                    return nullptr;
                }
            }
            
            app * process_bv_mul(func_decl * f, unsigned num, expr * const * args) {
                if (num == 0)
                    return nullptr;
                if (uncnstr(num, args)) {
                    sort * s = m().get_sort(args[0]);
                    app * r;
                    if (!mk_fresh_uncnstr_var_for(f, num, args, r))
                        return r;
                    if (m_mc)
                        add_defs(num, args, r, m_bv_util.mk_numeral(rational(1), s));
                    return r;
                }
                // c * v (c is even) case
                unsigned bv_size;
                rational val;
                rational inv;
                if (num == 2 && 
                    uncnstr(args[1]) && 
                    m_bv_util.is_numeral(args[0], val, bv_size) &&
                    m_bv_util.mult_inverse(val, bv_size, inv)) {
                    app * r;
                    if (!mk_fresh_uncnstr_var_for(f, num, args, r))
                        return r;
                    sort * s = m().get_sort(args[1]);
                    if (m_mc)
                        add_def(args[1], m_bv_util.mk_bv_mul(m_bv_util.mk_numeral(inv, s), r));
                    return r;
                }
                return nullptr;
            }
            
            app * process_extract(func_decl * f, expr * arg) {
                if (!uncnstr(arg))
                    return nullptr;
                app * r;
                if (!mk_fresh_uncnstr_var_for(f, arg, r))
                    return r;
                if (!m_mc)
                    return r;
                unsigned high    = m_bv_util.get_extract_high(f);
                unsigned low     = m_bv_util.get_extract_low(f);
                unsigned bv_size = m_bv_util.get_bv_size(m().get_sort(arg));
                if (bv_size == high - low + 1) {
                    add_def(arg, r);
                }
                else {
                    ptr_buffer<expr> args;
                    if (high < bv_size - 1)
                        args.push_back(m_bv_util.mk_numeral(rational(0), bv_size - high - 1));
                    args.push_back(r);
                    if (low > 0)
                        args.push_back(m_bv_util.mk_numeral(rational(0), low));
                    add_def(arg, m_bv_util.mk_concat(args.size(), args.c_ptr()));
                }
                return r;
            }
            
            app * process_bv_div(func_decl * f, expr * arg1, expr * arg2) {
                if (uncnstr(arg1) && uncnstr(arg2)) {
                    sort * s = m().get_sort(arg1);
                    app * r;
                    if (!mk_fresh_uncnstr_var_for(f, arg1, arg2, r))
                        return r;
                    if (!m_mc)
                        return r;
                    add_def(arg1, r);
                    add_def(arg2, m_bv_util.mk_numeral(rational(1), s));
                    return r;
                }
                return nullptr;
            }
            
            app * process_concat(func_decl * f, unsigned num, expr * const * args) {
                if (num == 0)
                    return nullptr;
                if (!uncnstr(num, args))
                    return nullptr;
                app * r;
                if (!mk_fresh_uncnstr_var_for(f, num, args, r))
                    return r;
                if (m_mc) {
                    unsigned i = num;
                    unsigned low = 0;
                    while (i > 0) {
                        --i;
                        expr * arg  = args[i];
                        unsigned sz = m_bv_util.get_bv_size(arg);
                        add_def(arg, m_bv_util.mk_extract(low + sz - 1, low, r));
                        low += sz;
                    }
                }
                return r;
            }
            
            app * process_bv_le(func_decl * f, expr * arg1, expr * arg2, bool is_signed) {
                if (m_produce_proofs) {
                    // The result of bv_le is not just introducing a new fresh name,
                    // we need a side condition.
                    // TODO: the correct proof step
                    return nullptr;
                }
                if (uncnstr(arg1)) {
                    // v <= t
                    expr * v = arg1;
                    expr * t = arg2;
                    // v <= t --->  (u or t == MAX)   u is fresh
                    //     add definition v = ite(u or t == MAX, t, t+1)
                    unsigned bv_sz = m_bv_util.get_bv_size(arg1);
                    rational MAX;
                    if (is_signed)
                        MAX = rational::power_of_two(bv_sz - 1) - rational(1);
                    else
                        MAX = rational::power_of_two(bv_sz) - rational(1);
                    app * u;
                    bool is_new = mk_fresh_uncnstr_var_for(f, arg1, arg2, u);
                    app * r = m().mk_or(u, m().mk_eq(t, m_bv_util.mk_numeral(MAX, bv_sz)));
                    if (m_mc && is_new)
                        add_def(v, m().mk_ite(r, t, m_bv_util.mk_bv_add(t, m_bv_util.mk_numeral(rational(1), bv_sz))));
                    return r;
                }
                if (uncnstr(arg2)) {
                    // v >= t
                    expr * v = arg2;
                    expr * t = arg1;
                    // v >= t --->  (u ot t == MIN)  u is fresh
                    //    add definition v = ite(u or t == MIN, t, t-1)
                    unsigned bv_sz = m_bv_util.get_bv_size(arg1);
                    rational MIN;
                    if (is_signed)
                        MIN = -rational::power_of_two(bv_sz - 1);
                    else
                        MIN = rational(0);
                    app * u;
                    bool is_new = mk_fresh_uncnstr_var_for(f, arg1, arg2, u);
                    app * r = m().mk_or(u, m().mk_eq(t, m_bv_util.mk_numeral(MIN, bv_sz)));
                    if (m_mc && is_new)
                        add_def(v, m().mk_ite(r, t, m_bv_util.mk_bv_sub(t, m_bv_util.mk_numeral(rational(1), bv_sz))));
                    return r;
                }
                return nullptr;
            }
            
            app * process_bv_app(func_decl * f, unsigned num, expr * const * args) {
                SASSERT(f->get_family_id() == m_bv_util.get_family_id());
                switch (f->get_decl_kind()) {
                case OP_BADD:
                    return process_add(f->get_family_id(), OP_BADD, OP_BSUB, num, args);
                case OP_BMUL:
                    return process_bv_mul(f, num, args);
                case OP_BSDIV:
                case OP_BUDIV:
                case OP_BSDIV_I:
                case OP_BUDIV_I:
                    SASSERT(num == 2);
                    return process_bv_div(f, args[0], args[1]);
                case OP_SLEQ:
                    SASSERT(num == 2);
                    return process_bv_le(f, args[0], args[1], true);
                case OP_ULEQ:
                    SASSERT(num == 2);
                    return process_bv_le(f, args[0], args[1], false);
                case OP_CONCAT:
                    return process_concat(f, num, args);
                case OP_EXTRACT:
                    SASSERT(num == 1);
                    return process_extract(f, args[0]);
                case OP_BNOT:
                    SASSERT(num == 1);
                    if (uncnstr(args[0])) {
                        app * r;
                        if (!mk_fresh_uncnstr_var_for(f, num, args, r))
                            return r;
                        if (m_mc)
                            add_def(args[0], m().mk_app(f, r));
                        return r;
                    }
                    return nullptr;
                case OP_BOR:
                    if (num > 0 && uncnstr(num, args)) {
                        sort * s = m().get_sort(args[0]);
                        app * r;
                        if (!mk_fresh_uncnstr_var_for(f, num, args, r))
                            return r;
                        if (m_mc)
                            add_defs(num, args, r, m_bv_util.mk_numeral(rational(0), s));
                        return r;
                    }
                    return nullptr;
                default:
                    return nullptr;
                }
            }
            
            app * process_array_app(func_decl * f, unsigned num, expr * const * args) {
                SASSERT(f->get_family_id() == m_ar_util.get_family_id());
                switch (f->get_decl_kind()) {
                case OP_SELECT:
                    if (uncnstr(args[0])) {
                        app * r;
                        if (!mk_fresh_uncnstr_var_for(f, num, args, r))
                            return r;
                        sort * s = m().get_sort(args[0]);
                        if (m_mc)
                            add_def(args[0], m_ar_util.mk_const_array(s, r));
                        return r;
                    }
                    return nullptr;
                case OP_STORE:
                    if (uncnstr(args[0]) && uncnstr(args[num-1])) {
                        app * r;
                        if (!mk_fresh_uncnstr_var_for(f, num, args, r))
                            return r;
                        if (m_mc) {
                            add_def(args[num-1], m().mk_app(m_ar_util.get_family_id(), OP_SELECT, num-1, args));
                            add_def(args[0], r);
                        }
                        return r;
                    }
                default:
                    return nullptr;
                }
            }
            
            app * process_datatype_app(func_decl * f, unsigned num, expr * const * args) {
                if (m_dt_util.is_recognizer(f)) {
                    SASSERT(num == 1);
                    if (uncnstr(args[0])) {
                        if (!m_mc) {
                            app * r;
                            mk_fresh_uncnstr_var_for(f, num, args, r);
                            return r;
                        }
                        // TODO: handle model generation
                    }
                }
                else if (m_dt_util.is_accessor(f)) {
                    SASSERT(num == 1);
                    if (uncnstr(args[0])) {
                        if (!m_mc) {
                            app * r;
                            mk_fresh_uncnstr_var_for(f, num, args, r);
                            return r;
                        }
                        func_decl * c = m_dt_util.get_accessor_constructor(f);
                        for (unsigned i = 0; i < c->get_arity(); i++) 
                            if (!m().is_fully_interp(c->get_domain(i)))
                                return nullptr;
                        app * u;
                        if (!mk_fresh_uncnstr_var_for(f, num, args, u))
                            return u;
                        ptr_vector<func_decl> const & accs = *m_dt_util.get_constructor_accessors(c);
                        ptr_buffer<expr> new_args;
                        for (unsigned i = 0; i < accs.size(); i++) {
                            if (accs[i] == f) 
                                new_args.push_back(u);
                            else
                                new_args.push_back(m().get_some_value(c->get_domain(i)));
                        }
                        add_def(args[0], m().mk_app(c, new_args.size(), new_args.c_ptr()));
                        return u;
                    }
                }
                else if (m_dt_util.is_constructor(f)) {
                    if (uncnstr(num, args)) {
                        app * u;
                        if (!mk_fresh_uncnstr_var_for(f, num, args, u))
                            return u;
                        if (!m_mc)
                            return u;
                        ptr_vector<func_decl> const & accs = *m_dt_util.get_constructor_accessors(f);
                        for (unsigned i = 0; i < num; i++) {
                            add_def(args[i], m().mk_app(accs[i], u));
                        }
                        return u;
                    }
                }
                return nullptr;
            }
            
            br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
                if (num == 0)
                    return BR_FAILED;
                family_id fid = f->get_family_id();
                if (fid == null_family_id)
                    return BR_FAILED;
                
                for (unsigned i = 0; i < num; i++) {
                    if (!is_ground(args[i]))
                        return BR_FAILED; // non-ground terms are not handled.
                }
                
                app * u = nullptr;
                
                if (fid == m().get_basic_family_id())
                    u = process_basic_app(f, num, args);
                else if (fid == m_a_util.get_family_id())
                    u = process_arith_app(f, num, args);
                else if (fid == m_bv_util.get_family_id())
                    u = process_bv_app(f, num, args);
                else if (fid == m_ar_util.get_family_id())
                    u = process_array_app(f, num, args);
                else if (fid == m_dt_util.get_family_id())
                    u = process_datatype_app(f, num, args);
                
                if (u == nullptr)
                    return BR_FAILED;
                
                result = u;
                if (m_produce_proofs) {
                    expr * s    = m().mk_app(f, num, args);
                    expr * eq   = m().mk_eq(s, u);
                    proof * pr1 = m().mk_def_intro(eq);
                    result_pr   = m().mk_apply_def(s, u, pr1);
                }
                
                return BR_DONE;
            }
        };
        
        class rw : public rewriter_tpl<rw_cfg> {
            rw_cfg m_cfg;
        public:
            rw(ast_manager & m, bool produce_proofs, obj_hashtable<expr> & vars, mc * _m, 
               unsigned long long max_memory, unsigned max_steps):
                rewriter_tpl<rw_cfg>(m, produce_proofs, m_cfg),
                m_cfg(m, produce_proofs, vars, _m, max_memory, max_steps) {
            }
        };
        
        ast_manager &                    m_manager;
        ref<mc>                          m_mc;
        obj_hashtable<expr>              m_vars;
        scoped_ptr<rw>                   m_rw;
        unsigned                         m_num_elim_apps;
        unsigned long long               m_max_memory;
        unsigned                         m_max_steps;
        
        imp(ast_manager & m, params_ref const & p):
            m_manager(m),
            m_num_elim_apps(0) {
            updt_params(p);
        }
        
        void updt_params(params_ref const & p) {
            m_max_memory     = megabytes_to_bytes(p.get_uint("max_memory", UINT_MAX));
            m_max_steps      = p.get_uint("max_steps", UINT_MAX);
        }
        
        ast_manager & m() { return m_manager; }
        
        void init_mc(bool produce_models) {
            m_mc = nullptr;
            if (produce_models) {
                m_mc = alloc(mc, m(), "elim_uncstr");
            }
        }
        
        void init_rw(bool produce_proofs) {
            m_rw = alloc(rw, m(), produce_proofs, m_vars, m_mc.get(), m_max_memory, m_max_steps);            
        }

        void operator()(goal_ref const & g, goal_ref_buffer & result) {
            bool produce_proofs = g->proofs_enabled();
            
            TRACE("elim_uncnstr_bug", g->display(tout););
            tactic_report report("elim-uncnstr-vars", *g);
            m_vars.reset();
            collect_occs p;
            p(*g, m_vars);
            if (m_vars.empty()) {
                result.push_back(g.get());
                // did not increase depth since it didn't do anything.
                return;
            }
            bool modified = true;
            TRACE("elim_uncnstr", tout << "unconstrained variables...\n";
                  for (expr * v : m_vars) tout << mk_ismt2_pp(v, m()) << " "; 
                  tout << "\n";);
            init_mc(g->models_enabled());
            init_rw(produce_proofs);
            
            expr_ref   new_f(m());
            proof_ref  new_pr(m());
            unsigned round = 0;
            unsigned size  = g->size();
            unsigned idx   = 0;
            while (true) {
                for (; idx < size; idx++) {
                    expr * f = g->form(idx);
                    m_rw->operator()(f, new_f, new_pr);
                    if (f == new_f)
                        continue;
                    modified = true;
                    if (produce_proofs) {
                        proof * pr = g->pr(idx);
                        new_pr     = m().mk_modus_ponens(pr, new_pr);
                    }
                    g->update(idx, new_f, new_pr, g->dep(idx));
                }
                if (!modified) {
                    if (round == 0) {                        
                    }
                    else {
                        m_num_elim_apps = m_rw->cfg().m_fresh_vars.size();
                        g->add(m_mc.get());                        
                    }
                    TRACE("elim_uncnstr", if (m_mc) m_mc->display(tout); else tout << "no mc\n";);
                    m_mc = nullptr;
                    m_rw = nullptr;                    
                    result.push_back(g.get());
                    g->inc_depth();
                    return;
                }
                modified = false;
                round ++;
                size       = g->size();
                m_rw->reset(); // reset cache
                m_vars.reset(); 
                {
                    collect_occs p;
                    p(*g, m_vars);
                }
                if (m_vars.empty()) 
                    idx = size; // force to finish 
                else
                    idx = 0;
            }
        }
            
    };
    
    imp *      m_imp;
    params_ref m_params;
public:
   elim_uncnstr_tactic(ast_manager & m, params_ref const & p):
        m_params(p) {
        m_imp = alloc(imp, m, p);
    }

    tactic * translate(ast_manager & m) override {
        return alloc(elim_uncnstr_tactic, m, m_params);
    }
        
    ~elim_uncnstr_tactic() override {
        dealloc(m_imp);
    }

    void updt_params(params_ref const & p) override {
        m_params = p;
        m_imp->updt_params(p);
    }
    
    void collect_param_descrs(param_descrs & r) override {
        insert_max_memory(r);
        insert_max_steps(r);
    }

    void operator()(goal_ref const & g, 
                    goal_ref_buffer & result) override {
        (*m_imp)(g, result);
        report_tactic_progress(":num-elim-apps", get_num_elim_apps());
    }
    
    void cleanup() override {
        unsigned num_elim_apps = get_num_elim_apps();
        ast_manager & m = m_imp->m_manager;        
        imp * d = alloc(imp, m, m_params);
        std::swap(d, m_imp);        
        dealloc(d);
        m_imp->m_num_elim_apps = num_elim_apps;
    }

    unsigned get_num_elim_apps() const {
        return m_imp->m_num_elim_apps;
    }

    void collect_statistics(statistics & st) const override {
        st.update("eliminated applications", get_num_elim_apps());
    }
    
    void reset_statistics() override {
        m_imp->m_num_elim_apps = 0;
    }

};

tactic * mk_elim_uncnstr_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(elim_uncnstr_tactic, m, p));
}
