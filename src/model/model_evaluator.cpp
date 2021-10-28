/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    model_evaluator.cpp

Abstract:

    Evaluate expressions in a given model.

Author:

    Leonardo de Moura (leonardo) 2011-04-30.

Revision History:

--*/
#include "ast/ast_pp.h"
#include "ast/ast_util.h"
#include "ast/for_each_expr.h"
#include "ast/recfun_decl_plugin.h"
#include "ast/rewriter/rewriter_types.h"
#include "ast/rewriter/bool_rewriter.h"
#include "ast/rewriter/arith_rewriter.h"
#include "ast/rewriter/bv_rewriter.h"
#include "ast/rewriter/pb_rewriter.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/datatype_rewriter.h"
#include "ast/rewriter/array_rewriter.h"
#include "ast/rewriter/fpa_rewriter.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/rewriter/rewriter_def.h"
#include "ast/rewriter/var_subst.h"
#include "model/model_smt2_pp.h"
#include "model/model.h"
#include "model/model_evaluator_params.hpp"
#include "model/model_evaluator.h"
#include "model/model_v2_pp.h"


namespace mev {

struct evaluator_cfg : public default_rewriter_cfg {
    ast_manager &                   m;
    model_core &                    m_model;
    params_ref                      m_params;
    bool_rewriter                   m_b_rw;
    arith_rewriter                  m_a_rw;
    bv_rewriter                     m_bv_rw;
    array_rewriter                  m_ar_rw;
    datatype_rewriter               m_dt_rw;
    pb_rewriter                     m_pb_rw;
    fpa_rewriter                    m_f_rw;
    seq_rewriter                    m_seq_rw;
    array_util                      m_ar;
    arith_util                      m_au;
    fpa_util                        m_fpau;
    datatype::util                  m_dt;
    unsigned long long              m_max_memory;
    unsigned                        m_max_steps;
    bool                            m_model_completion;
    bool                            m_array_equalities;
    bool                            m_array_as_stores;
    obj_map<func_decl, expr*>       m_def_cache;
    expr_ref_vector                 m_pinned;

    evaluator_cfg(ast_manager & m, model_core & md, params_ref const & p):
        m(m),
        m_model(md),
        m_params(p),
        m_b_rw(m),
        // We must allow customers to set parameters for arithmetic rewriter/evaluator.
        // In particular, the maximum degree of algebraic numbers that will be evaluated.
        m_a_rw(m, p),
        m_bv_rw(m),
        // See comment above. We want to allow customers to set :sort-store
        m_ar_rw(m, p),
        m_dt_rw(m),
        m_pb_rw(m),
        m_f_rw(m),
        m_seq_rw(m),
        m_ar(m),
        m_au(m),
        m_fpau(m),
        m_dt(m),
        m_pinned(m) {
        bool flat = true;
        m_b_rw.set_flat(flat);
        m_a_rw.set_flat(flat);
        m_bv_rw.set_flat(flat);
        m_bv_rw.set_mkbv2num(true);
        m_ar_rw.set_expand_select_store(true);
        m_ar_rw.set_expand_select_ite(true);
        updt_params(p);
        //add_unspecified_function_models(md);
    }

    void updt_params(params_ref const & _p) {
        model_evaluator_params p(_p);
        m_max_memory       = megabytes_to_bytes(p.max_memory());
        m_max_steps        = p.max_steps();
        m_model_completion = p.completion();
        m_array_equalities = p.array_equalities();
        m_array_as_stores  = p.array_as_stores();
    }

    bool evaluate(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
        func_interp * fi = m_model.get_func_interp(f);
        bool r = (fi != nullptr) && eval_fi(fi, num, args, result);
        CTRACE("model_evaluator", r, tout << "reduce_app " << f->get_name() << "\n";
               for (unsigned i = 0; i < num; i++) tout << mk_ismt2_pp(args[i], m) << "\n";
               tout << "---->\n" << mk_ismt2_pp(result, m) << "\n";);
        return r;
    }

    // Try to use the entries to quickly evaluate the fi
    bool eval_fi(func_interp * fi, unsigned num, expr * const * args, expr_ref & result) {
        if (fi->num_entries() == 0)
            return false; // let get_macro handle it.

        SASSERT(fi->get_arity() == num);

        bool actuals_are_values = true;

        for (unsigned i = 0; actuals_are_values && i < num; i++)
            actuals_are_values = m.is_value(args[i]);

        if (!actuals_are_values)
            return false; // let get_macro handle it

        func_entry * entry = fi->get_entry(args);
        if (entry != nullptr) {
            result = entry->get_result();
            return true;
        }

        return false;
    }

    bool reduce_quantifier(quantifier * old_q,
                           expr * new_body,
                           expr * const * new_patterns,
                           expr * const * new_no_patterns,
                           expr_ref & result,
                           proof_ref & result_pr) {
        th_rewriter th(m);
        return th.reduce_quantifier(old_q, new_body, new_patterns, new_no_patterns, result, result_pr);
    }

    br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
        auto st = reduce_app_core(f, num, args, result, result_pr);
        CTRACE("model_evaluator", st != BR_FAILED, 
               tout << st << " " << mk_pp(f, m) << "  ";
               for (unsigned i = 0; i < num; ++i) tout << mk_pp(args[i], m) << " ";
               tout << "\n--> " << result << "\n";);
               
        return st;
    }

    br_status reduce_app_core(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
        result_pr = nullptr;
        family_id fid = f->get_family_id();
        bool _is_uninterp = fid != null_family_id && m.get_plugin(fid)->is_considered_uninterpreted(f);
        br_status st = BR_FAILED;
#if 0
        struct pp {
            func_decl* f;
            expr_ref& r;
            pp(func_decl* f, expr_ref& r) :f(f), r(r) {}
            ~pp() { TRACE("model_evaluator", tout << mk_pp(f, r.m()) << " " << r << "\n";); }
        };
        pp _pp(f, result);
#endif


        if (num == 0 && (fid == null_family_id || _is_uninterp || m_ar.is_as_array(f))) {
            expr * val = m_model.get_const_interp(f);
            if (val != nullptr) {
                result = val;
                st = m_ar.is_as_array(val) ? BR_REWRITE1 : BR_DONE;
                TRACE("model_evaluator", tout << result << "\n";);
                return st;
            }
            if (!m_model_completion)
                return BR_FAILED;
            
            if (!m_ar.is_as_array(f)) {
                sort * s   = f->get_range();
                expr * val = m_model.get_some_value(s);
                m_model.register_decl(f, val);
                result = val;
                return BR_DONE;
            }
            // fall through
        }


        if (fid == m_b_rw.get_fid()) {
            decl_kind k = f->get_decl_kind();
            if (k == OP_EQ) {
                // theory dispatch for =
                SASSERT(num == 2);
                sort* s = args[0]->get_sort();
                family_id s_fid = s->get_family_id();
                if (s_fid == m_a_rw.get_fid())
                    st = m_a_rw.mk_eq_core(args[0], args[1], result);
                else if (s_fid == m_bv_rw.get_fid())
                    st = m_bv_rw.mk_eq_core(args[0], args[1], result);
                else if (s_fid == m_dt_rw.get_fid())
                    st = m_dt_rw.mk_eq_core(args[0], args[1], result);
                else if (s_fid == m_f_rw.get_fid())
                    st = m_f_rw.mk_eq_core(args[0], args[1], result);
                else if (s_fid == m_seq_rw.get_fid())
                    st = m_seq_rw.mk_eq_core(args[0], args[1], result);
                else if (s_fid == m_ar_rw.get_fid())
                    st = mk_array_eq(args[0], args[1], result);
                else if (m.are_equal(args[0], args[1])) {
                    result = m.mk_true();
                    st = BR_DONE;
                }
                else if (m.are_distinct(args[0], args[1])) {
                    result = m.mk_false();
                    st = BR_DONE;
                }
                if (st != BR_FAILED)
                    return st;
            }
            return m_b_rw.mk_app_core(f, num, args, result);
        }
        if (fid == m_a_rw.get_fid())
            st = m_a_rw.mk_app_core(f, num, args, result);
        else if (fid == m_bv_rw.get_fid())
            st = m_bv_rw.mk_app_core(f, num, args, result);
        else if (fid == m_ar_rw.get_fid())
            st = m_ar_rw.mk_app_core(f, num, args, result);
        else if (fid == m_dt_rw.get_fid())
            st = m_dt_rw.mk_app_core(f, num, args, result);
        else if (fid == m_pb_rw.get_fid())
            st = m_pb_rw.mk_app_core(f, num, args, result);
        else if (fid == m_f_rw.get_fid())
            st = m_f_rw.mk_app_core(f, num, args, result);
        else if (fid == m_seq_rw.get_fid())
            st = m_seq_rw.mk_app_core(f, num, args, result);
        else if (fid == m.get_label_family_id() && num == 1) {
            result = args[0];
            st = BR_DONE;
        }
        else if (evaluate(f, num, args, result)) 
            st = BR_REWRITE1;        
        if (st == BR_FAILED && !m.is_builtin_family_id(fid)) 
            st = evaluate_partial_theory_func(f, num, args, result, result_pr);        
        if (st == BR_DONE && is_app(result)) {
            app* a = to_app(result);
            if (evaluate(a->get_decl(), a->get_num_args(), a->get_args(), result))
                st = BR_REWRITE1;              
        }

        if (st == BR_DONE && is_app(result) && expand_as_array(to_app(result)->get_decl(), result))
            return BR_REWRITE_FULL;

        if (st == BR_FAILED && expand_as_array(f, result))
            return BR_REWRITE_FULL;        
        return st;
    }

    bool expand_as_array(func_decl* f, expr_ref& result) {
        if (!m_model_completion)
            return false;
        func_decl* g = nullptr;
        if (!m_ar.is_as_array(f, g))
            return false;
        expr* def = nullptr;
        if (m_def_cache.find(g, def)) {
            result = def;
            TRACE("model_evaluator", tout << result << "\n";);
            return true;
        }
        expr_ref tmp(m);
        func_interp* fi = m_model.get_func_interp(g);
        if (fi && !fi->get_else()) {
            fi->set_else(m_model.get_some_value(g->get_range()));
        }
        if (fi && (tmp = fi->get_array_interp(g))) {
            model_evaluator ev(m_model, m_params);
            ev.set_model_completion(false);
            result = ev(tmp);
            m_pinned.push_back(result);
            m_def_cache.insert(g, result);
            TRACE("model_evaluator", tout << mk_pp(g, m) << " " << result << "\n";);
            return true;
        }
        
        TRACE("model_evaluator",
            tout << "could not get array interpretation " << mk_pp(g, m) << " " << fi << "\n";
            tout << m_model << "\n";);                    

        return false;
    }

    void expand_stores(expr_ref& val) {
        TRACE("model_evaluator", tout << val << "\n";);
        vector<expr_ref_vector> stores;
        expr_ref else_case(m);
        bool _unused;
        if (m_array_as_stores &&
            m_ar.is_array(val) &&
            extract_array_func_interp(val, stores, else_case, _unused)) {
            sort* srt = val->get_sort();
            val = m_ar.mk_const_array(srt, else_case);
            for (unsigned i = stores.size(); i-- > 0; ) {
                expr_ref_vector args(m);
                args.push_back(val);
                args.append(stores[i].size(), stores[i].data());
                val = m_ar.mk_store(args);
            }
            TRACE("model_evaluator", tout << val << "\n";);
        }
    }

    bool reduce_macro() { return true; }

    bool get_macro(func_decl * f, expr * & def, quantifier * & , proof * &) {
        func_interp * fi = m_model.get_func_interp(f);
        def = nullptr;
        if (fi != nullptr) {
            if (fi->is_partial()) {
                if (m_model_completion) {
                    sort * s   = f->get_range();
                    expr * val = m_model.get_some_value(s);
                    fi->set_else(val);
                }
                else
                    return false;
            }
            def = fi->get_interp();
            SASSERT(def != nullptr);
        }
        else if (m_model_completion &&
            (f->get_family_id() == null_family_id ||
             m.get_plugin(f->get_family_id())->is_considered_uninterpreted(f))) {
            sort * s   = f->get_range();
            expr * val = m_model.get_some_value(s);
            func_interp * new_fi = alloc(func_interp, m, f->get_arity());
            new_fi->set_else(val);
            m_model.register_decl(f, new_fi);
            def = val;
            SASSERT(def != nullptr);
        }

        CTRACE("model_evaluator", def != nullptr, tout << "get_macro for " << f->get_name() << " (model completion: " << m_model_completion << ") " << mk_pp(def, m) << "\n";);

        return def != nullptr;
    }

    br_status evaluate_partial_theory_func(func_decl * f,
                                           unsigned num, expr * const * args,
                                           expr_ref & result, proof_ref & result_pr) {
        SASSERT(f != nullptr);
        SASSERT(!m.is_builtin_family_id(f->get_family_id()));
        result = nullptr;
        result_pr = nullptr;

        if (f->get_family_id() == m_fpau.get_family_id() &&
            !m_fpau.is_considered_uninterpreted(f, num, args)) {
            // cwinter: should this be unreachable?
            return BR_FAILED;
        }

        func_interp * fi = m_model.get_func_interp(f);

        func_decl_ref f_ui(m);
        if (!fi && m_au.is_considered_uninterpreted(f, num, args, f_ui)) {
            if (f_ui) {
                fi = m_model.get_func_interp(f_ui); 
            }

            if (!fi) {
                result = m_au.mk_numeral(rational(0), f->get_range());
                return BR_DONE;
            }
        }
        else if (!fi && m_fpau.is_considered_uninterpreted(f, num, args)) {
            result = m.get_some_value(f->get_range());
            return BR_DONE;
        }
        else if (m_dt.is_accessor(f) && !is_ground(args[0])) {
            result = m.mk_app(f, num, args);
            return BR_DONE;            
        }
        if (fi) {
            if (fi->is_partial())
                fi->set_else(m.get_some_value(f->get_range()));

            var_subst vs(m, false);
            result = vs(fi->get_interp(), num, args);
            if (!is_ground(result.get()) && recfun::util(m).is_defined(f))
                return BR_DONE;
            return BR_REWRITE_FULL;
        }

        return BR_FAILED;
    }


    bool max_steps_exceeded(unsigned num_steps) const {
        if (memory::get_allocation_size() > m_max_memory)
            throw rewriter_exception(Z3_MAX_MEMORY_MSG);
        return num_steps > m_max_steps;
    }

    br_status mk_array_eq(expr* a, expr* b, expr_ref& result) {

        if (a == b) {
            result = m.mk_true();
            return BR_DONE;
        }
        if (!m_array_equalities) {
            return m_ar_rw.mk_eq_core(a, b, result);
        }
        TRACE("model_evaluator", tout << "mk_array_eq " << m_array_equalities << " "
            << mk_pp(a, m) << " " << mk_pp(b, m) << "\n";);

        vector<expr_ref_vector> stores1, stores2;
        bool args_are_unique1, args_are_unique2;
        expr_ref else1(m), else2(m);
        if (extract_array_func_interp(a, stores1, else1, args_are_unique1) &&
            extract_array_func_interp(b, stores2, else2, args_are_unique2)) {
            expr_ref_vector conj(m), args1(m), args2(m);
            if (m.are_equal(else1, else2)) {
                // no op
            }
            else if (m.are_distinct(else1, else2) && !(else1->get_sort()->get_info()->get_num_elements().is_finite())) {
                result = m.mk_false();
                return BR_DONE;
            }
            else {
                conj.push_back(m.mk_eq(else1, else2));
            }
            if (args_are_unique1 && args_are_unique2 && !stores1.empty()) {
                TRACE("model_evaluator", tout << "args are unique " << conj << "\n";);
                return mk_array_eq_core(stores1, else1, stores2, else2, conj, result);
            }

            // TBD: this is too inefficient.
            args1.push_back(a);
            args2.push_back(b);
            stores1.append(stores2);
            for (unsigned i = 0; i < stores1.size(); ++i) {
                args1.resize(1); args1.append(stores1[i].size() - 1, stores1[i].data());
                args2.resize(1); args2.append(stores1[i].size() - 1, stores1[i].data());
                expr_ref s1(m_ar.mk_select(args1.size(), args1.data()), m);
                expr_ref s2(m_ar.mk_select(args2.size(), args2.data()), m);
                conj.push_back(m.mk_eq(s1, s2));
            }
            result = mk_and(conj);
            TRACE("model_evaluator", tout << mk_pp(a, m) << " == " << mk_pp(b, m) << " -> " << conj << "\n";
                  for (auto& s : stores1) tout << "store: " << s << "\n"; );
            return BR_REWRITE_FULL;
        }
        return m_ar_rw.mk_eq_core(a, b, result);
    }

    struct args_eq {
        unsigned m_arity;
        args_eq(unsigned arity): m_arity(arity) {}
        bool operator()(expr * const* args1, expr* const* args2) const {
            for (unsigned i = 0; i < m_arity; ++i) {
                if (args1[i] != args2[i]) {
                    return false;
                }
            }
            return true;
        }
    };

    struct args_hash {
        unsigned m_arity;
        args_hash(unsigned arity): m_arity(arity) {}
        unsigned operator()(expr * const* args) const {
            return get_composite_hash(args, m_arity, default_kind_hash_proc<expr*const*>(), *this);
        }
        unsigned operator()(expr* const* args, unsigned idx) const {
            return args[idx]->hash();
        }
    };

    typedef hashtable<expr*const*, args_hash, args_eq> args_table;

    br_status mk_array_eq_core(vector<expr_ref_vector> const& stores1, expr* else1,
                               vector<expr_ref_vector> const& stores2, expr* else2,
                               expr_ref_vector& conj, expr_ref& result) {
        unsigned arity = stores1[0].size()-1; // TBD: fix arity.
        args_hash ah(arity);
        args_eq   ae(arity);
        args_table table1(DEFAULT_HASHTABLE_INITIAL_CAPACITY, ah, ae);
        args_table table2(DEFAULT_HASHTABLE_INITIAL_CAPACITY, ah, ae);
        TRACE("model_evaluator",
              tout << "arity " << arity << "\n";
              for (auto& v : stores1) tout << "stores1: " << v << "\n";
              for (auto& v : stores2) tout << "stores2: " << v << "\n";
              tout << "else1: " << mk_pp(else1, m) << "\n";
              tout << "else2: " << mk_pp(else2, m) << "\n";
              tout << "conj: " << conj << "\n";);

        // stores with smaller index take precedence
        for (unsigned i = stores1.size(); i-- > 0; ) {
            table1.insert(stores1[i].data());
        }

        for (unsigned i = 0, sz = stores2.size(); i < sz; ++i) {
            if (table2.contains(stores2[i].data())) {
                // first insertion takes precedence.
                TRACE("model_evaluator", tout << "duplicate " << stores2[i] << "\n";);
                continue;
            }
            table2.insert(stores2[i].data());
            expr * const* args = nullptr;
            expr* val = stores2[i][arity];
            if (table1.find(stores2[i].data(), args)) {
                TRACE("model_evaluator", tout << "found value " << stores2[i] << "\n";);
                table1.remove(args);
                switch (compare(args[arity], val)) {
                case l_true: break;
                case l_false: result = m.mk_false(); return BR_DONE;
                default: conj.push_back(m.mk_eq(val, args[arity])); break;
                }
            }
            else {
                TRACE("model_evaluator", tout << "not found value " << stores2[i] << "\n";);
                switch (compare(else1, val)) {
                case l_true: break;
                case l_false: result = m.mk_false(); return BR_DONE;
                default: conj.push_back(m.mk_eq(else1, val)); break;
                }
            }
        }
        for (auto const& t : table1) {
            switch (compare((t)[arity], else2)) {
            case l_true: break;
            case l_false: result = m.mk_false(); return BR_DONE;
            default: conj.push_back(m.mk_eq((t)[arity], else2)); break;
            }
        }
        result = mk_and(conj);
        return BR_REWRITE_FULL;
    }

    lbool compare(expr* a, expr* b) {
        if (m.are_equal(a, b)) return l_true;
        if (m.are_distinct(a, b)) return l_false;
        return l_undef;
    }


    bool args_are_values(expr_ref_vector const& store, bool& are_unique) {
        bool are_values = true;
        for (unsigned j = 0; are_values && j + 1 < store.size(); ++j) {
            are_values = m.is_value(store[j]);
            are_unique &= m.is_unique_value(store[j]);
        }
        SASSERT(!are_unique || are_values);
        return are_values;
    }


    bool extract_array_func_interp(expr* a, vector<expr_ref_vector>& stores, expr_ref& else_case, bool& are_unique) {
        SASSERT(m_ar.is_array(a));
        bool are_values = true;
        are_unique = true;
        TRACE("model_evaluator", tout << mk_pp(a, m) << "\n";);

        while (m_ar.is_store(a)) {
            expr_ref_vector store(m);
            store.append(to_app(a)->get_num_args()-1, to_app(a)->get_args()+1);
            are_values &= args_are_values(store, are_unique);
            stores.push_back(store);
            a = to_app(a)->get_arg(0);
        }

        if (m_ar.is_const(a)) {
            else_case = to_app(a)->get_arg(0);
            return true;
        }

        if (m_ar_rw.has_index_set(a, else_case, stores)) {
            for (auto const& store : stores) {
                are_values &= args_are_values(store, are_unique);
            }
            return true;
        }
        if (!m_ar.is_as_array(a)) {
            TRACE("model_evaluator", tout << "no translation: " << mk_pp(a, m) << "\n";);
            TRACE("model_evaluator", tout << m_model << "\n";);
            return false;
        }

        func_decl* f = m_ar.get_as_array_func_decl(to_app(a));
        func_interp* g = m_model.get_func_interp(f);
        if (!g) {
            TRACE("model_evaluator", tout << "no interpretation for " << mk_pp(f, m) << "\n";);
            return false;
        }
        else_case = g->get_else();
        if (!else_case) {
            TRACE("model_evaluator", tout << "no else case " << mk_pp(a, m) << "\n";);
            return false;
        }
        bool ground = is_ground(else_case);
        unsigned sz = g->num_entries();
        expr_ref_vector store(m);
        for (unsigned i = 0; i < sz; ++i) {
            store.reset();
            func_entry const* fe = g->get_entry(i);
            expr* res = fe->get_result();
            if (m.are_equal(else_case, res)) {
                continue;
            }
            ground &= is_ground(res);
            store.append(g->get_arity(), fe->get_args());
            store.push_back(res);
            for (expr* arg : store) {
                ground &= is_ground(arg);
            }
            stores.push_back(store);
        }
        if (!ground) {
            TRACE("model_evaluator", tout << "could not extract ground array interpretation: " << mk_pp(a, m) << "\n";);
            return false;
        }
        return true;
    }
};
}

struct model_evaluator::imp : public rewriter_tpl<mev::evaluator_cfg> {
    mev::evaluator_cfg m_cfg;
    imp(model_core & md, params_ref const & p):
        rewriter_tpl<mev::evaluator_cfg>(md.get_manager(),
                                    false, // no proofs for evaluator
                                    m_cfg),
        m_cfg(md.get_manager(), md, p) {
    }
    void expand_stores(expr_ref &val) {m_cfg.expand_stores(val);}
    void reset() {
        rewriter_tpl<mev::evaluator_cfg>::reset();
        m_cfg.reset();
        m_cfg.m_def_cache.reset();
    }
};

model_evaluator::model_evaluator(model_core & md, params_ref const & p) {
    m_imp = alloc(imp, md, p);
}

ast_manager & model_evaluator::m() const {
    return m_imp->m();
}

model_evaluator::~model_evaluator() {
    dealloc(m_imp);
}

void model_evaluator::updt_params(params_ref const & p) {
    m_imp->cfg().updt_params(p);
}

void model_evaluator::get_param_descrs(param_descrs & r) {
    model_evaluator_params::collect_param_descrs(r);
}

void model_evaluator::set_model_completion(bool f) {
    if (m_imp->cfg().m_model_completion != f) {
        reset();
        m_imp->cfg().m_model_completion = f;
    }
}

bool model_evaluator::get_model_completion() const {
    return m_imp->cfg().m_model_completion;
}

void model_evaluator::set_expand_array_equalities(bool f) {
    m_imp->cfg().m_array_equalities = f;
}

unsigned model_evaluator::get_num_steps() const {
    return m_imp->get_num_steps();
}

void model_evaluator::cleanup(params_ref const & p) {
    model_core & md = m_imp->cfg().m_model;
    m_imp->~imp();
    new (m_imp) imp(md, p);
}

void model_evaluator::reset(params_ref const & p) {
    m_imp->reset();
    updt_params(p);
}

void model_evaluator::reset(model_core &model, params_ref const& p) {
    m_imp->~imp();
    new (m_imp) imp(model, p);
}


void model_evaluator::operator()(expr * t, expr_ref & result) {
    TRACE("model_evaluator", tout << mk_ismt2_pp(t, m()) << "\n";);
    m_imp->operator()(t, result);
    m_imp->expand_stores(result);
    TRACE("model_evaluator", tout << "eval: " << mk_ismt2_pp(t, m()) << " --> " << result << "\n";);
}

expr_ref model_evaluator::operator()(expr * t) {
    expr_ref result(m());
    this->operator()(t, result);
    return result;
}

expr_ref_vector model_evaluator::operator()(expr_ref_vector const& ts) {
    expr_ref_vector rs(m());
    for (expr* t : ts) rs.push_back((*this)(t));
    return rs;
}


bool model_evaluator::is_true(expr* t) {
    expr_ref tmp(m());
    return eval(t, tmp, true) && m().is_true(tmp);
}

bool model_evaluator::is_false(expr* t) {
    expr_ref tmp(m());
    return eval(t, tmp, true) && m().is_false(tmp);
}

bool model_evaluator::is_true(expr_ref_vector const& ts) {
    for (expr* t : ts) if (!is_true(t)) return false;
    return true;
}

bool model_evaluator::are_equal(expr* s, expr* t) {
    if (m().are_equal(s, t)) return true;
    if (m().are_distinct(s, t)) return false;
    expr_ref t1(m()), t2(m());
    eval(t, t1, true);
    eval(s, t2, true);
    return m().are_equal(t1, t2);
}

bool model_evaluator::eval(expr* t, expr_ref& r, bool model_completion) {
    set_model_completion(model_completion);
    try {
        r = (*this)(t);
        return true;
    }
    catch (model_evaluator_exception &ex) {
        (void)ex;
        TRACE("model_evaluator", tout << ex.msg () << "\n";);
        return false;
    }
}

bool model_evaluator::eval(expr_ref_vector const& ts, expr_ref& r, bool model_completion) {
    expr_ref tmp(m());
    tmp = mk_and(ts);
    return eval(tmp, r, model_completion);
}

void model_evaluator::set_solver(expr_solver* solver) {
    m_imp->m_cfg.m_seq_rw.set_solver(solver);
}

bool model_evaluator::has_solver() {
    return m_imp->m_cfg.m_seq_rw.has_solver();
}

model_core const & model_evaluator::get_model() const {
    return m_imp->cfg().m_model;
}
