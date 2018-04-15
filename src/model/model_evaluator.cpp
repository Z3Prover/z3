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
#include "model/model.h"
#include "model/model_evaluator_params.hpp"
#include "ast/rewriter/rewriter_types.h"
#include "model/model_evaluator.h"
#include "ast/rewriter/bool_rewriter.h"
#include "ast/rewriter/arith_rewriter.h"
#include "ast/rewriter/bv_rewriter.h"
#include "ast/rewriter/pb_rewriter.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/datatype_rewriter.h"
#include "ast/rewriter/array_rewriter.h"
#include "ast/rewriter/fpa_rewriter.h"
#include "ast/rewriter/rewriter_def.h"
#include "util/cooperate.h"
#include "ast/ast_pp.h"
#include "ast/ast_util.h"
#include "model/model_smt2_pp.h"
#include "ast/rewriter/var_subst.h"


struct evaluator_cfg : public default_rewriter_cfg {
    ast_manager &                   m;
    model_core &                    m_model;
    bool_rewriter                   m_b_rw;
    arith_rewriter                  m_a_rw;
    bv_rewriter                     m_bv_rw;
    array_rewriter                  m_ar_rw;
    datatype_rewriter               m_dt_rw;
    pb_rewriter                     m_pb_rw;
    fpa_rewriter                    m_f_rw;
    seq_rewriter                    m_seq_rw;
    array_util                      m_ar;
    unsigned long long              m_max_memory;
    unsigned                        m_max_steps;
    bool                            m_model_completion;
    bool                            m_cache;
    bool                            m_array_equalities;

    evaluator_cfg(ast_manager & m, model_core & md, params_ref const & p):
        m(m),
        m_model(md),
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
        m_ar(m) {
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
        m_cache            = p.cache();
        m_array_equalities = p.array_equalities();
    }

    bool evaluate(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
        func_interp * fi = m_model.get_func_interp(f);
        return (fi != nullptr) && eval_fi(fi, num, args, result);
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

    br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
        result_pr = nullptr;
        family_id fid = f->get_family_id();
        bool is_uninterp = fid != null_family_id && m.get_plugin(fid)->is_considered_uninterpreted(f);
        if (num == 0 && (fid == null_family_id || is_uninterp)) {
            expr * val = m_model.get_const_interp(f);
            if (val != nullptr) {
                result = val;
                return BR_DONE;
            }

            if (m_model_completion) {
                sort * s   = f->get_range();
                expr * val = m_model.get_some_value(s);
                m_model.register_decl(f, val);
                result = val;
                return BR_DONE;
            }
            return BR_FAILED;
        }

        br_status st = BR_FAILED;

        if (fid == m_b_rw.get_fid()) {
            decl_kind k = f->get_decl_kind();
            if (k == OP_EQ) {
                // theory dispatch for =
                SASSERT(num == 2);
                family_id s_fid = m.get_sort(args[0])->get_family_id();
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
        else if (evaluate(f, num, args, result)) {
            TRACE("model_evaluator", tout << "reduce_app " << f->get_name() << "\n";
                  for (unsigned i = 0; i < num; i++) tout << mk_ismt2_pp(args[i], m) << "\n";
                  tout << "---->\n" << mk_ismt2_pp(result, m) << "\n";);
            return BR_REWRITE1;
        }
        if (st == BR_FAILED && !m.is_builtin_family_id(fid))
            st = evaluate_partial_theory_func(f, num, args, result, result_pr);
        if (st == BR_DONE && is_app(result)) {
            app* a = to_app(result);
            if (evaluate(a->get_decl(), a->get_num_args(), a->get_args(), result)) {
                return BR_REWRITE1;
            }
        }
        CTRACE("model_evaluator", st != BR_FAILED, tout << result << "\n";);
        return st;
    }

    void expand_value(expr_ref& val) {
        vector<expr_ref_vector> stores;
        expr_ref else_case(m);
        bool _unused;
        if (m_ar.is_array(val) && extract_array_func_interp(val, stores, else_case, _unused)) {
            sort* srt = m.get_sort(val);
            val = m_ar.mk_const_array(srt, else_case);
            for (unsigned i = stores.size(); i > 0; ) {
                --i;
                expr_ref_vector args(m);
                args.push_back(val);
                args.append(stores[i].size(), stores[i].c_ptr());
                val = m_ar.mk_store(args.size(), args.c_ptr());
            }
        }
    }

    bool get_macro(func_decl * f, expr * & def, quantifier * & q, proof * & def_pr) {

#define TRACE_MACRO TRACE("model_evaluator", tout << "get_macro for " << f->get_name() << " (model completion: " << m_model_completion << ")\n";);

        func_interp * fi = m_model.get_func_interp(f);

        if (fi != nullptr) {
            TRACE_MACRO;
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
            SASSERT(def != 0);
            return true;
        }

        if (m_model_completion &&
            (f->get_family_id() == null_family_id ||
             m.get_plugin(f->get_family_id())->is_considered_uninterpreted(f)))
        {
            TRACE_MACRO;
            sort * s   = f->get_range();
            expr * val = m_model.get_some_value(s);
            func_interp * new_fi = alloc(func_interp, m, f->get_arity());
            new_fi->set_else(val);
            m_model.register_decl(f, new_fi);
            def = val;
            return true;
        }

        return false;
    }

    br_status evaluate_partial_theory_func(func_decl * f,
                                           unsigned num, expr * const * args,
                                           expr_ref & result, proof_ref & result_pr) {
        SASSERT(f != 0);
        SASSERT(!m.is_builtin_family_id(f->get_family_id()));
        result = nullptr;
        result_pr = nullptr;

        func_interp * fi = m_model.get_func_interp(f);
        if (fi) {
            if (fi->is_partial())
                fi->set_else(m.get_some_value(f->get_range()));

            var_subst vs(m, false);
            vs(fi->get_interp(), num, args, result);
            return BR_REWRITE_FULL;
        }

        return BR_FAILED;
    }


    bool max_steps_exceeded(unsigned num_steps) const {
        cooperate("model evaluator");
        if (memory::get_allocation_size() > m_max_memory)
            throw rewriter_exception(Z3_MAX_MEMORY_MSG);
        return num_steps > m_max_steps;
    }

    bool cache_results() const { return m_cache; }


    br_status mk_array_eq(expr* a, expr* b, expr_ref& result) {
        if (a == b) {
            result = m.mk_true();
            return BR_DONE;
        }
        if (!m_array_equalities) {
            return BR_FAILED;
        }

        vector<expr_ref_vector> stores1, stores2;
        bool args_are_unique1, args_are_unique2;
        expr_ref else1(m), else2(m);
        if (extract_array_func_interp(a, stores1, else1, args_are_unique1) &&
            extract_array_func_interp(b, stores2, else2, args_are_unique2)) {
            expr_ref_vector conj(m), args1(m), args2(m);
            if (m.are_equal(else1, else2)) {
                // no op
            }
            else if (m.are_distinct(else1, else2) && !(m.get_sort(else1)->get_info()->get_num_elements().is_finite())) {
                result = m.mk_false();
                return BR_DONE;
            }
            else {
                conj.push_back(m.mk_eq(else1, else2));
            }
            if (args_are_unique1 && args_are_unique2 && !stores1.empty()) {
                return mk_array_eq_core(stores1, else1, stores2, else2, conj, result);
            }

            // TBD: this is too inefficient.
            args1.push_back(a);
            args2.push_back(b);
            stores1.append(stores2);
            for (unsigned i = 0; i < stores1.size(); ++i) {
                args1.resize(1); args1.append(stores1[i].size() - 1, stores1[i].c_ptr());
                args2.resize(1); args2.append(stores1[i].size() - 1, stores1[i].c_ptr());
                expr_ref s1(m_ar.mk_select(args1.size(), args1.c_ptr()), m);
                expr_ref s2(m_ar.mk_select(args2.size(), args2.c_ptr()), m);
                conj.push_back(m.mk_eq(s1, s2));
            }
            result = m.mk_and(conj.size(), conj.c_ptr());
            return BR_REWRITE_FULL;
        }
        return BR_FAILED;
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

        // stores with smaller index take precedence
        for (unsigned i = stores1.size(); i > 0; ) {
            --i;
            table1.insert(stores1[i].c_ptr());
        }

        for (unsigned i = 0, sz = stores2.size(); i < sz; ++i) {
            if (table2.contains(stores2[i].c_ptr())) {
                // first insertion takes precedence.
                continue;
            }
            table2.insert(stores2[i].c_ptr());
            expr * const* args = nullptr;
            expr* val = stores2[i][arity];
            if (table1.find(stores2[i].c_ptr(), args)) {
                switch (compare(args[arity], val)) {
                case l_true: table1.remove(args); break;
                case l_false: result = m.mk_false(); return BR_DONE;
                default: conj.push_back(m.mk_eq(val, args[arity])); break;
                }
            }
            else {
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

        if (!m_ar.is_as_array(a)) {
            TRACE("model_evaluator", tout << "no translation: " << mk_pp(a, m) << "\n";);
            return false;
        }

        func_decl* f = m_ar.get_as_array_func_decl(to_app(a));
        func_interp* g = m_model.get_func_interp(f);
		if (!g) return false;
        unsigned sz = g->num_entries();
        unsigned arity = f->get_arity();
        unsigned base_sz = stores.size();
        for (unsigned i = 0; i < sz; ++i) {
            expr_ref_vector store(m);
            func_entry const* fe = g->get_entry(i);
            store.append(arity, fe->get_args());
            store.push_back(fe->get_result());
            for (unsigned j = 0; j < store.size(); ++j) {
                if (!is_ground(store[j].get())) {
                    TRACE("model_evaluator", tout << "could not extract array interpretation: " << mk_pp(a, m) << "\n" << mk_pp(store[j].get(), m) << "\n";);
                    return false;
                }
            }
            stores.push_back(store);
        }
        else_case = g->get_else();
        if (!else_case) {
            TRACE("model_evaluator", tout << "no else case " << mk_pp(a, m) << "\n";
                  /*model_smt2_pp(tout, m, m_model, 0);*/
                  );
            return false;
        }
        if (!is_ground(else_case)) {
            TRACE("model_evaluator", tout << "non-ground else case " << mk_pp(a, m) << "\n" << else_case << "\n";);
            return false;
        }
        for (unsigned i = stores.size(); are_values && i > base_sz; ) {
            --i;
            if (m.are_equal(else_case, stores[i].back())) {
                for (unsigned j = i + 1; j < stores.size(); ++j) {
                    stores[j-1].reset();
                    stores[j-1].append(stores[j]);
                }
                stores.pop_back();
                continue;
            }
            are_values &= args_are_values(stores[i], are_unique);
        }
        TRACE("model_evaluator", tout << "else case: " << mk_pp(else_case, m) << "\n";);
        return true;
    }



};

template class rewriter_tpl<evaluator_cfg>;

struct model_evaluator::imp : public rewriter_tpl<evaluator_cfg> {
    evaluator_cfg m_cfg;
    imp(model_core & md, params_ref const & p):
        rewriter_tpl<evaluator_cfg>(md.get_manager(),
                                    false, // no proofs for evaluator
                                    m_cfg),
        m_cfg(md.get_manager(), md, p) {
        set_cancel_check(false);
    }

    void expand_value (expr_ref &val) {
        m_cfg.expand_value (val);
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
    m_imp->cfg().m_model_completion = f;
}

void model_evaluator::set_expand_array_equalities(bool f) {
    m_imp->cfg().m_array_equalities = f;
}

unsigned model_evaluator::get_num_steps() const {
    return m_imp->get_num_steps();
}

void model_evaluator::cleanup(params_ref const & p) {
    model_core & md = m_imp->cfg().m_model;
    dealloc(m_imp);
    m_imp = alloc(imp, md, p);
}

void model_evaluator::reset(params_ref const & p) {
    m_imp->reset();
    updt_params(p);
}

void model_evaluator::operator()(expr * t, expr_ref & result) {
    TRACE("model_evaluator", tout << mk_ismt2_pp(t, m()) << "\n";);
    m_imp->operator()(t, result);
    m_imp->expand_value(result);
}

expr_ref model_evaluator::operator()(expr * t) {
    TRACE("model_evaluator", tout << mk_ismt2_pp(t, m()) << "\n";);
    expr_ref result(m());
    this->operator()(t, result);
    return result;
}
