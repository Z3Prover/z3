/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    th_rewriter.h

Abstract:

    Rewriter for applying all builtin (cheap) theory rewrite rules.

Author:

    Leonardo (leonardo) 2011-04-07

Notes:

--*/
#include "params/rewriter_params.hpp"
#include "ast/rewriter/th_rewriter.h"
#include "ast/rewriter/bool_rewriter.h"
#include "ast/rewriter/arith_rewriter.h"
#include "ast/rewriter/bv_rewriter.h"
#include "ast/rewriter/datatype_rewriter.h"
#include "ast/rewriter/array_rewriter.h"
#include "ast/rewriter/fpa_rewriter.h"
#include "ast/rewriter/dl_rewriter.h"
#include "ast/rewriter/pb_rewriter.h"
#include "ast/rewriter/recfun_rewriter.h"
#include "ast/rewriter/seq_rewriter.h"
#include "ast/rewriter/rewriter_def.h"
#include "ast/rewriter/var_subst.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "ast/expr_substitution.h"
#include "ast/ast_smt2_pp.h"
#include "ast/ast_pp.h"
#include "ast/ast_util.h"
#include "ast/well_sorted.h"

namespace {
struct th_rewriter_cfg : public default_rewriter_cfg {
    bool_rewriter       m_b_rw;
    arith_rewriter      m_a_rw;
    bv_rewriter         m_bv_rw;
    array_rewriter      m_ar_rw;
    datatype_rewriter   m_dt_rw;
    fpa_rewriter        m_f_rw;
    dl_rewriter         m_dl_rw;
    pb_rewriter         m_pb_rw;
    seq_rewriter        m_seq_rw;
    recfun_rewriter     m_rec_rw;
    arith_util          m_a_util;
    bv_util             m_bv_util;
    expr_safe_replace   m_rep;
    bool                m_new_subst { false };
    expr_ref_vector     m_pinned;
    unsigned long long  m_max_memory; // in bytes
    unsigned            m_max_steps;    
    bool                m_pull_cheap_ite;
    bool                m_flat;
    bool                m_cache_all;
    bool                m_push_ite_arith;
    bool                m_push_ite_bv;
    bool                m_ignore_patterns_on_ground_qbody;
    bool                m_rewrite_patterns;

    // substitution support
    expr_dependency_ref m_used_dependencies; // set of dependencies of used substitutions
    expr_substitution * m_subst;

    ast_manager & m() const { return m_b_rw.m(); }

    void updt_local_params(params_ref const & _p) {
        rewriter_params p(_p);
        m_flat           = p.flat();
        m_max_memory     = megabytes_to_bytes(p.max_memory());
        m_max_steps      = p.max_steps();
        m_pull_cheap_ite = p.pull_cheap_ite();
        m_cache_all      = p.cache_all();
        m_push_ite_arith = p.push_ite_arith();
        m_push_ite_bv    = p.push_ite_bv();
        m_ignore_patterns_on_ground_qbody = p.ignore_patterns_on_ground_qbody();
        m_rewrite_patterns = p.rewrite_patterns();
    }

    void updt_params(params_ref const & p) {
        m_b_rw.updt_params(p);
        m_a_rw.updt_params(p);
        m_bv_rw.updt_params(p);
        m_ar_rw.updt_params(p);
        m_f_rw.updt_params(p);
        m_seq_rw.updt_params(p);
        updt_local_params(p);
    }

    bool flat_assoc(func_decl * f) const {
        if (!m_flat) return false;
        family_id fid = f->get_family_id();
        if (fid == null_family_id)
            return false;
        decl_kind k   = f->get_decl_kind();
        if (fid == m_b_rw.get_fid())
            return k == OP_AND || k == OP_OR;
        if (fid == m_a_rw.get_fid())
            return k == OP_ADD;
        if (fid == m_bv_rw.get_fid())
            return k == OP_BADD || k == OP_BOR || k == OP_BAND || k == OP_BXOR;
        return false;
    }

    bool rewrite_patterns() const { return m_rewrite_patterns; }

    bool cache_all_results() const { return m_cache_all; }

    bool max_steps_exceeded(unsigned num_steps) const {
        if (m_max_memory != SIZE_MAX && 
            memory::get_allocation_size() > m_max_memory)
            throw rewriter_exception(Z3_MAX_MEMORY_MSG);
        return num_steps > m_max_steps;
    }

    // Return true if t is of the form
    //    (= t #b0)
    //    (= t #b1)
    //    (= #b0 t)
    //    (= #b1 t)
    bool is_eq_bit(expr * t, expr * & x, unsigned & val) {
        if (!m().is_eq(t))
            return false;
        expr * lhs = to_app(t)->get_arg(0);
        if (!m_bv_rw.is_bv(lhs))
            return false;
        if (m_bv_rw.get_bv_size(lhs) != 1)
            return false;
        expr * rhs = to_app(t)->get_arg(1);
        rational v;
        unsigned sz;
        if (m_bv_rw.is_numeral(lhs, v, sz)) {
            x    = rhs;
            val  = v.get_unsigned();
            SASSERT(val == 0 || val == 1);
            return true;
        }
        if (m_bv_rw.is_numeral(rhs, v, sz)) {
            x   = lhs;
            val  = v.get_unsigned();
            SASSERT(val == 0 || val == 1);
            return true;
        }
        return false;
    }

    // (iff (= x bit1) A)
    // --->
    // (= x (ite A bit1 bit0))
    br_status apply_tamagotchi(expr * lhs, expr * rhs, expr_ref & result) {
        expr * x;
        unsigned val;
        if (is_eq_bit(lhs, x, val)) {
            result = m().mk_eq(x, m().mk_ite(rhs, m_bv_rw.mk_numeral(val, 1), m_bv_rw.mk_numeral(1-val, 1)));
            return BR_REWRITE2;
        }
        if (is_eq_bit(rhs, x, val)) {
            result = m().mk_eq(x, m().mk_ite(lhs, m_bv_rw.mk_numeral(val, 1), m_bv_rw.mk_numeral(1-val, 1)));
            return BR_REWRITE2;
        }
        return BR_FAILED;
    }

    br_status reduce_app_core(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
        family_id fid = f->get_family_id();
        if (fid == null_family_id)
            return BR_FAILED;
        br_status st = BR_FAILED;
        if (fid == m_b_rw.get_fid()) {
            decl_kind k = f->get_decl_kind();
            if (k == OP_EQ) {
                // theory dispatch for =
                SASSERT(num == 2);
                family_id s_fid = args[0]->get_sort()->get_family_id();
                if (s_fid == m_a_rw.get_fid()) 
                    st = m_a_rw.mk_eq_core(args[0], args[1], result);
                else if (s_fid == m_bv_rw.get_fid())
                    st = m_bv_rw.mk_eq_core(args[0], args[1], result);
                else if (s_fid == m_dt_rw.get_fid())
                    st = m_dt_rw.mk_eq_core(args[0], args[1], result);
                else if (s_fid == m_f_rw.get_fid())
                    st = m_f_rw.mk_eq_core(args[0], args[1], result);
                else if (s_fid == m_ar_rw.get_fid())
                    st = m_ar_rw.mk_eq_core(args[0], args[1], result);
                else if (s_fid == m_seq_rw.get_fid())
                    st = m_seq_rw.mk_eq_core(args[0], args[1], result);
                if (st != BR_FAILED)
                    return st;     
            }
            if (k == OP_EQ) {
                SASSERT(num == 2);
                st = apply_tamagotchi(args[0], args[1], result);
                if (st != BR_FAILED)
                    return st;
            }
            if (k == OP_ITE) {
                SASSERT(num == 3);
                family_id s_fid = args[1]->get_sort()->get_family_id();
                if (s_fid == m_bv_rw.get_fid())
                    st = m_bv_rw.mk_ite_core(args[0], args[1], args[2], result);
                if (st != BR_FAILED)
                    return st;
            }
            if ((k == OP_AND || k == OP_OR) && m_seq_rw.u().has_re()) {
                st = m_seq_rw.mk_bool_app(f, num, args, result); 
                if (st != BR_FAILED)
                    return st;
            }
            if (k == OP_EQ && m_seq_rw.u().has_seq() && is_app(args[0]) && 
                to_app(args[0])->get_family_id() == m_seq_rw.get_fid()) {
                st = m_seq_rw.mk_eq_core(args[0], args[1], result);
                if (st != BR_FAILED)
                    return st;
            }

            return m_b_rw.mk_app_core(f, num, args, result);
        }
        if (fid == m_a_rw.get_fid() && OP_LE == f->get_decl_kind() && m_seq_rw.u().has_seq()) {
            st = m_seq_rw.mk_le_core(args[0], args[1], result);
            if (st != BR_FAILED)
                return st;
        }
        if (fid == m_a_rw.get_fid() && OP_GE == f->get_decl_kind() && m_seq_rw.u().has_seq()) {
            st = m_seq_rw.mk_le_core(args[1], args[0], result);
            if (st != BR_FAILED)
                return st;
        }
        if (fid == m_a_rw.get_fid())
            return m_a_rw.mk_app_core(f, num, args, result);
        if (fid == m_bv_rw.get_fid())
            return m_bv_rw.mk_app_core(f, num, args, result);
        if (fid == m_ar_rw.get_fid())
            return m_ar_rw.mk_app_core(f, num, args, result);
        if (fid == m_dt_rw.get_fid())
            return m_dt_rw.mk_app_core(f, num, args, result);
        if (fid == m_f_rw.get_fid())
            return m_f_rw.mk_app_core(f, num, args, result);
        if (fid == m_dl_rw.get_fid())
            return m_dl_rw.mk_app_core(f, num, args, result);
        if (fid == m_pb_rw.get_fid())
            return m_pb_rw.mk_app_core(f, num, args, result);
        if (fid == m_seq_rw.get_fid())
            return m_seq_rw.mk_app_core(f, num, args, result);
        if (fid == m_rec_rw.get_fid())
            return m_rec_rw.mk_app_core(f, num, args, result);
        return BR_FAILED;
    }

    // auxiliary function for pull_ite_core
    expr * mk_eq_value(expr * lhs, expr * value) {
        if (m().are_equal(lhs, value)) {
            return m().mk_true();
        }
        else if (m().are_distinct(lhs, value)) {
            return m().mk_false();
        }
        return m().mk_eq(lhs, value);
    }

    template<bool SWAP>
    br_status pull_ite_core(func_decl * p, app * ite, app * value, expr_ref & result) {
        if (m().is_eq(p)) {
            result = m().mk_ite(ite->get_arg(0),
                                mk_eq_value(ite->get_arg(1), value),
                                mk_eq_value(ite->get_arg(2), value));
            return BR_REWRITE2;
        }
        else {
            if (SWAP) {
                result = m().mk_ite(ite->get_arg(0),
                                    m().mk_app(p, value, ite->get_arg(1)),
                                    m().mk_app(p, value, ite->get_arg(2)));
                return BR_REWRITE2;
            }
            else {
                result = m().mk_ite(ite->get_arg(0),
                                    m().mk_app(p, ite->get_arg(1), value),
                                    m().mk_app(p, ite->get_arg(2), value));
                return BR_REWRITE2;
            }
        }
    }

    // Return true if t is an ite-value-tree form defined as:
    //    ite-value-tree := (ite c <subtree> <subtree>)
    //    subtree        := value
    //                   |  (ite c <subtree> <subtree>)
    //
    bool is_ite_value_tree(expr * t) {
        if (!m().is_ite(t))
            return false;
        ptr_buffer<app> todo;
        todo.push_back(to_app(t));
        while (!todo.empty()) {
            app * ite = todo.back();
            todo.pop_back();
            expr * arg1 = ite->get_arg(1);
            expr * arg2 = ite->get_arg(2);

            if (m().is_ite(arg1) && arg1->get_ref_count() == 1) // do not apply on shared terms, since it may blowup
                todo.push_back(to_app(arg1));
            else if (!m().is_value(arg1))
                return false;

            if (m().is_ite(arg2) && arg2->get_ref_count() == 1) // do not apply on shared terms, since it may blowup
                todo.push_back(to_app(arg2));
            else if (!m().is_value(arg2))
                return false;
        }
        return true;
    }

    br_status pull_ite(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
        if (num == 2 && m().is_bool(f->get_range()) && !m().is_bool(args[0])) {
            if (m().is_ite(args[0])) {
                if (m().is_value(args[1]))
                    return pull_ite_core<false>(f, to_app(args[0]), to_app(args[1]), result);
                if (m().is_ite(args[1]) && to_app(args[0])->get_arg(0) == to_app(args[1])->get_arg(0)) {
                    // (p (ite C A1 B1) (ite C A2 B2)) --> (ite (p A1 A2) (p B1 B2))
                    result = m().mk_ite(to_app(args[0])->get_arg(0),
                                        m().mk_app(f, to_app(args[0])->get_arg(1), to_app(args[1])->get_arg(1)),
                                        m().mk_app(f, to_app(args[0])->get_arg(2), to_app(args[1])->get_arg(2)));
                    return BR_REWRITE2;
                }
            }
            if (m().is_ite(args[1]) && m().is_value(args[0]))
                return pull_ite_core<true>(f, to_app(args[1]), to_app(args[0]), result);
        }
        family_id fid = f->get_family_id();
        if (num == 2 && (fid == m().get_basic_family_id() || fid == m_a_rw.get_fid() || fid == m_bv_rw.get_fid())) {
            // (f v3 (ite c v1 v2)) --> (ite v (f v3 v1) (f v3 v2))
            if (m().is_value(args[0]) && is_ite_value_tree(args[1]))
                return pull_ite_core<true>(f, to_app(args[1]), to_app(args[0]), result);

            // (f (ite c v1 v2) v3) --> (ite v (f v1 v3) (f v2 v3))
            if (m().is_value(args[1]) && is_ite_value_tree(args[0]))
                return pull_ite_core<false>(f, to_app(args[0]), to_app(args[1]), result);
        }
        return BR_FAILED;
    }

    br_status pull_ite(expr_ref & result) {
        expr * t = result.get();
        if (is_app(t)) {
            br_status st = pull_ite(to_app(t)->get_decl(), to_app(t)->get_num_args(), to_app(t)->get_args(), result);
            if (st != BR_FAILED)
                return st;
        }
        return BR_DONE;
    }

    bool is_arith_bv_app(expr * t) const {
        if (!is_app(t))
            return false;
        family_id fid = to_app(t)->get_family_id();
        return ((fid == m_a_rw.get_fid() && m_push_ite_arith) ||
                (fid == m_bv_rw.get_fid() && m_push_ite_bv));
    }

    bool get_neutral_elem(app * t, expr_ref & n) {
        family_id fid = t->get_family_id();
        if (fid == m_a_rw.get_fid()) {
            switch (t->get_decl_kind()) {
            case OP_ADD: n = m_a_util.mk_numeral(rational::zero(), t->get_sort()); return true;
            case OP_MUL: n = m_a_util.mk_numeral(rational::one(), t->get_sort()); return true;
            default:
                return false;
            }
        }
        if (fid == m_bv_rw.get_fid()) {
            switch (t->get_decl_kind()) {
            case OP_BADD: n = m_bv_util.mk_numeral(rational::zero(), t->get_sort()); return true;
            case OP_BMUL: n = m_bv_util.mk_numeral(rational::one(), t->get_sort()); return true;
            default:
                return false;
            }
        }
        return false;
    }

    /**
       \brief Try to "unify" t1 and t2
       Examples
         (+ 2 a) (+ 3 a) -->  2, 3, a
         (+ 2 a) a       -->  2, 0, a
         ...
    */
    bool unify_core(app * t1, expr * t2, expr_ref & new_t1, expr_ref & new_t2, expr_ref & c, bool & first) {
        if (t1->get_num_args() != 2)
            return false;
        expr * a1 = t1->get_arg(0);
        expr * b1 = t1->get_arg(1);
        if (t2 == b1) {
            if (get_neutral_elem(t1, new_t2)) {
                new_t1 = a1;
                c      = b1;
                first  = false;
                return true;
            }
        }
        else if (t2 == a1) {
            if (get_neutral_elem(t1, new_t2)) {
                new_t1 = b1;
                c      = a1;
                first  = true;
                return true;
            }
        }
        else if (is_app_of(t2, t1->get_decl()) && to_app(t2)->get_num_args() == 2) {
            expr * a2 = to_app(t2)->get_arg(0);
            expr * b2 = to_app(t2)->get_arg(1);
            if (b1 == b2) {
                new_t1 = a1;
                new_t2 = a2;
                c      = b2;
                first  = false;
                return true;
            }
            if (a1 == a2) {
                new_t1 = b1;
                new_t2 = b2;
                c      = a1;
                first  = true;
                return true;
            }
            if (t1->get_decl()->is_commutative()) {
                if (a1 == b2) {
                    new_t1 = b1;
                    new_t2 = a2;
                    c      = a1;
                    first  = true; // doesn't really matter for commutative ops.
                    return true;
                }
                if (b1 == a2) {
                    new_t1 = a1;
                    new_t2 = b2;
                    c      = b1;
                    first  = false; // doesn't really matter for commutative ops.
                    return true;
                }
            }
        }
        return false;
    }

    // Return true if t1 and t2 are of the form:
    //   t + a1*x1 + ... + an*xn
    //   t' + a1*x1 + ... + an*xn
    // Store t in new_t1, t' in new_t2 and (a1*x1 + ... + an*xn) in c.
    bool unify_add(app * t1, expr * t2, expr_ref & new_t1, expr_ref & new_t2, expr_ref & c) {
        unsigned num1 = t1->get_num_args();
        expr * const * ms1 = t1->get_args();
        if (num1 < 2)
            return false;
        unsigned num2;
        expr * const * ms2;
        if (m_a_util.is_add(t2)) {
            num2 = to_app(t2)->get_num_args();
            ms2  = to_app(t2)->get_args();
        }
        else {
            num2 = 1;
            ms2  = &t2;
        }
        if (num1 != num2 && num1 != num2 + 1 && num1 != num2 - 1)
            return false;
        new_t1 = nullptr;
        new_t2 = nullptr;
        expr_fast_mark1 visited1;
        expr_fast_mark2 visited2;
        for (unsigned i = 0; i < num1; i++) {
            expr * arg = ms1[i];
            visited1.mark(arg);
        }
        for (unsigned i = 0; i < num2; i++) {
            expr * arg = ms2[i];
            visited2.mark(arg);
            if (visited1.is_marked(arg))
                continue;
            if (new_t2)
                return false; // more than one missing term
            new_t2 = arg;
        }
        for (unsigned i = 0; i < num1; i++) {
            expr * arg = ms1[i];
            if (visited2.is_marked(arg))
                continue;
            if (new_t1)
                return false; // more than one missing term
            new_t1 = arg;
        }
        // terms matched...
        bool is_int = m_a_util.is_int(t1);
        if (!new_t1)
            new_t1 = m_a_util.mk_numeral(rational::zero(), is_int);
        if (!new_t2)
            new_t2 = m_a_util.mk_numeral(rational::zero(), is_int);
        // mk common part
        ptr_buffer<expr> args;
        for (unsigned i = 0; i < num1; i++) {
            expr * arg = ms1[i];
            if (arg == new_t1.get())
                continue;
            args.push_back(arg);
        }
        SASSERT(!args.empty());
        if (args.size() == 1)
            c = args[0];
        else
            c = m_a_util.mk_add(args.size(), args.data());
        return true;
    }

    bool unify(expr * t1, expr * t2, func_decl * & f, expr_ref & new_t1, expr_ref & new_t2, expr_ref & c, bool & first) {
#if 0
        // Did not work for ring benchmarks

        // Hack for handling more complex cases of + apps
        // such as (+ 2 t1 t2 t3) and (+ 3 t3 t2 t1)
        if (m_a_util.is_add(t1)) {
            first = true; // doesn't matter for AC ops
            f     = to_app(t1)->get_decl();
            if (unify_add(to_app(t1), t2, new_t1, new_t2, c))
                return true;
        }
        if (m_a_util.is_add(t2)) {
            first = true; // doesn't matter for AC ops
            f     = to_app(t2)->get_decl();
            if (unify_add(to_app(t2), t1, new_t2, new_t1, c))
                return true;
        }
#endif

        if (is_arith_bv_app(t1)) {
            f = to_app(t1)->get_decl();
            return unify_core(to_app(t1), t2, new_t1, new_t2, c, first);
        }
        else if (is_arith_bv_app(t2)) {
            f = to_app(t2)->get_decl();
            return unify_core(to_app(t2), t1, new_t2, new_t1, c, first);
        }
        else {
            return false;
        }
    }

    // Apply transformations of the form
    //
    // (ite c (+ k1 a) (+ k2 a)) --> (+ (ite c k1 k2) a)
    // (ite c (* k1 a) (* k2 a)) --> (* (ite c k1 k2) a)
    //
    // These transformations are useful for bit-vector problems, since
    // they will minimize the number of adders/multipliers/etc
    br_status push_ite(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
        if (!m().is_ite(f))
            return BR_FAILED;
        expr * c = args[0];
        expr * t = args[1];
        expr * e = args[2];
        func_decl * f_prime = nullptr;
        expr_ref new_t(m()), new_e(m()), common(m());
        bool first;
        TRACE("push_ite", tout << "unifying:\n" << mk_ismt2_pp(t, m()) << "\n" << mk_ismt2_pp(e, m()) << "\n";);
        if (unify(t, e, f_prime, new_t, new_e, common, first)) {
            if (first)
                result = m().mk_app(f_prime, common, m().mk_ite(c, new_t, new_e));
            else
                result = m().mk_app(f_prime, m().mk_ite(c, new_t, new_e), common);
            return BR_DONE;
        }
        TRACE("push_ite", tout << "failed\n";);
        return BR_FAILED;
    }

    br_status push_ite(expr_ref & result) {
        expr * t = result.get();
        if (m().is_ite(t)) {
            br_status st = push_ite(to_app(t)->get_decl(), to_app(t)->get_num_args(), to_app(t)->get_args(), result);
            if (st != BR_FAILED)
                return st;
        }
        return BR_DONE;
    }

    void count_down_subterm_references(expr * e, map<expr *, unsigned, ptr_hash<expr>, ptr_eq<expr>> & reference_map) {
        if (is_app(e)) {
            app * a = to_app(e);
            for (unsigned i = 0; i < a->get_num_args(); ++i) {
                expr * child = a->get_arg(i);
                unsigned countdown = reference_map.get(child, child->get_ref_count()) - 1;
                reference_map.insert(child,  countdown);
                if (countdown == 0)
                    count_down_subterm_references(child, reference_map);
            }
        }
    }

    void log_rewrite_axiom_instantiation(func_decl * f, unsigned num, expr * const * args, expr_ref & result) {
        family_id fid = f->get_family_id();
        if (fid == m_b_rw.get_fid()) {
            decl_kind k = f->get_decl_kind();
            if (k == OP_EQ) {
                SASSERT(num == 2);
                fid = args[0]->get_sort()->get_family_id();
            }
            else if (k == OP_ITE) {
                SASSERT(num == 3);
                fid = args[1]->get_sort()->get_family_id();
            }
        }
        app_ref tmp(m());
        tmp = m().mk_app(f, num, args);
        m().trace_stream() << "[inst-discovered] theory-solving " << static_cast<void *>(nullptr) << " " << m().get_family_name(fid) << "# ; #" << tmp->get_id() << "\n";
        tmp = m().mk_eq(tmp, result);
        m().trace_stream() << "[instance] " << static_cast<void *>(nullptr) << " #" << tmp->get_id() << "\n";

        // Make sure that both the result term and equality were newly introduced.
        if (tmp->get_ref_count() == 1) {
            if (result->get_ref_count() == 1) {
                map<expr *, unsigned, ptr_hash<expr>, ptr_eq<expr>> reference_map;
                count_down_subterm_references(result, reference_map);

                // Any term that was newly introduced by the rewrite step is only referenced within / reachable from the result term.
                for (auto kv : reference_map) {
                    if (kv.m_value == 0) {
                        m().trace_stream() << "[attach-enode] #" << kv.m_key->get_id() << " 0\n";
                    }
                }

                m().trace_stream() << "[attach-enode] #" << result->get_id() << " 0\n";
            }
            m().trace_stream() << "[attach-enode] #" << tmp->get_id() << " 0\n";
        }
        m().trace_stream() << "[end-of-instance]\n";
        m().trace_stream().flush();
    }

    br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
        result_pr = nullptr;
        br_status st = reduce_app_core(f, num, args, result);

        if (st != BR_FAILED && m().has_trace_stream()) {
            log_rewrite_axiom_instantiation(f, num, args, result);
        }

        if (st != BR_DONE && st != BR_FAILED) {
            CTRACE("th_rewriter_step", st != BR_FAILED,
                   tout << f->get_name() << "\n";
                   for (unsigned i = 0; i < num; i++) tout << mk_ismt2_pp(args[i], m()) << "\n";
                   tout << "---------->\n" << mk_ismt2_pp(result, m()) << "\n";);
            return st;
        }
        if (m_push_ite_bv || m_push_ite_arith) {
            if (st == BR_FAILED)
                st = push_ite(f, num, args, result);
            else
                st = push_ite(result);
        }
        if (m_pull_cheap_ite) {
            if (st == BR_FAILED)
                st = pull_ite(f, num, args, result);
            else
                st = pull_ite(result);
        }
        CTRACE("th_rewriter_step", st != BR_FAILED,
               tout << f->get_name() << "\n";
               for (unsigned i = 0; i < num; i++) tout << mk_ismt2_pp(args[i], m()) << "\n";
               tout << "---------->\n" << mk_ismt2_pp(result, m()) << "\n";);
        return st;
    }

    expr_ref mk_app(func_decl* f, unsigned num_args, expr* const* args) {
        expr_ref result(m());
        proof_ref pr(m());
        if (BR_FAILED == reduce_app(f, num_args, args, result, pr)) {
            result = m().mk_app(f, num_args, args);
        }
        return result;
    }

    void apply_subst(ptr_buffer<expr>& patterns) {
        if (!m_subst)
            return;
        if (patterns.empty())
            return;
        if (m_new_subst) {
            m_rep.reset();
            for (auto kv : m_subst->sub())
                m_rep.insert(kv.m_key, kv.m_value);
            m_new_subst = false;
        }
        expr_ref tmp(m());
        for (unsigned i = 0; i < patterns.size(); ++i) {
            m_rep(patterns[i], tmp);
            m_pinned.push_back(tmp);
            patterns[i] = tmp;
        }
    }


    bool reduce_quantifier(quantifier * old_q,
                           expr * new_body,
                           expr * const * new_patterns,
                           expr * const * new_no_patterns,
                           expr_ref & result,
                           proof_ref & result_pr) {
        quantifier_ref q1(m());
        proof_ref p1(m()); 
        if (is_quantifier(new_body) &&
            to_quantifier(new_body)->get_kind() == old_q->get_kind() &&
            to_quantifier(new_body)->get_kind() != lambda_k && 
            !old_q->has_patterns() &&
            !to_quantifier(new_body)->has_patterns()) {

            quantifier * nested_q = to_quantifier(new_body);

            ptr_buffer<sort> sorts;
            buffer<symbol>   names;
            sorts.append(old_q->get_num_decls(), old_q->get_decl_sorts());
            names.append(old_q->get_num_decls(), old_q->get_decl_names());
            sorts.append(nested_q->get_num_decls(), nested_q->get_decl_sorts());
            names.append(nested_q->get_num_decls(), nested_q->get_decl_names());

            q1 = m().mk_quantifier(old_q->get_kind(),
                                   sorts.size(),
                                   sorts.data(),
                                   names.data(),
                                   nested_q->get_expr(),
                                   std::min(old_q->get_weight(), nested_q->get_weight()),
                                   old_q->get_qid(),
                                   old_q->get_skid(),
                                   0, nullptr, 0, nullptr);

            SASSERT(is_well_sorted(m(), q1));

            if (m().proofs_enabled()) {
                p1 = m().mk_pull_quant(old_q, q1);
            }
        }
        else if (old_q->get_kind() == lambda_k &&
                 is_ground(new_body)) {
            result = m_ar_rw.util().mk_const_array(old_q->get_sort(), new_body);
            if (m().proofs_enabled()) {
                result_pr = m().mk_rewrite(old_q, result);
            }
            return true;
        }
        else {
            ptr_buffer<expr> new_patterns_buf;
            ptr_buffer<expr> new_no_patterns_buf;

            new_patterns_buf.append(old_q->get_num_patterns(), new_patterns);
            new_no_patterns_buf.append(old_q->get_num_no_patterns(), new_no_patterns);

            remove_duplicates(new_patterns_buf);
            remove_duplicates(new_no_patterns_buf);

            apply_subst(new_patterns_buf);

            q1 = m().update_quantifier(old_q,
                                       new_patterns_buf.size(), new_patterns_buf.data(), new_no_patterns_buf.size(), new_no_patterns_buf.data(),
                                       new_body);
            m_pinned.reset();
            TRACE("reduce_quantifier", tout << mk_ismt2_pp(old_q, m()) << "\n----->\n" << mk_ismt2_pp(q1, m()) << "\n";);
            SASSERT(is_well_sorted(m(), q1));
            if (m().proofs_enabled() && q1 != old_q) {
                p1 = m().mk_rewrite(old_q, q1);
            }
        }
        SASSERT(old_q->get_sort() == q1->get_sort());
        result = elim_unused_vars(m(), q1, params_ref());


        TRACE("reduce_quantifier", tout << "after elim_unused_vars:\n" << result << "\n";);

        result_pr = nullptr;
        if (m().proofs_enabled()) {
            proof_ref p2(m());
            if (q1.get() != result.get() && q1->get_kind() != lambda_k) 
                p2 = m().mk_elim_unused_vars(q1, result);
            result_pr = m().mk_transitivity(p1, p2);
        }
        SASSERT(old_q->get_sort() == result->get_sort());
        return true;
    }

    th_rewriter_cfg(ast_manager & m, params_ref const & p):
        m_b_rw(m, p),
        m_a_rw(m, p),
        m_bv_rw(m, p),
        m_ar_rw(m, p),
        m_dt_rw(m),
        m_f_rw(m, p),
        m_dl_rw(m),
        m_pb_rw(m),
        m_seq_rw(m),
        m_rec_rw(m),
        m_a_util(m),
        m_bv_util(m),
        m_rep(m),
        m_pinned(m),
        m_used_dependencies(m),
        m_subst(nullptr) {
        updt_local_params(p);
    }

    void set_substitution(expr_substitution * s) {
        reset();
        m_subst = s;
        m_new_subst = true;
    }

    void reset() {
        m_subst = nullptr;
    }

    bool get_subst(expr * s, expr * & t, proof * & pr) {
        if (m_subst == nullptr)
            return false;
        expr_dependency * d = nullptr;
        if (m_subst->find(s, t, pr, d)) {
            m_used_dependencies = m().mk_join(m_used_dependencies, d);
            return true;
        }
        return false;
    }


};
}

struct th_rewriter::imp : public rewriter_tpl<th_rewriter_cfg> {
    th_rewriter_cfg m_cfg;
    imp(ast_manager & m, params_ref const & p):
        rewriter_tpl<th_rewriter_cfg>(m, m.proofs_enabled(), m_cfg),
        m_cfg(m, p) {
    }
    expr_ref mk_app(func_decl* f, unsigned sz, expr* const* args) {
        return m_cfg.mk_app(f, sz, args);
    }

    void set_solver(expr_solver* solver) {
        m_cfg.m_seq_rw.set_solver(solver);
    }
};

th_rewriter::th_rewriter(ast_manager & m, params_ref const & p):
    m_params(p) {
    m_imp = alloc(imp, m, p);
}

ast_manager & th_rewriter::m() const {
    return m_imp->m();
}

void th_rewriter::updt_params(params_ref const & p) {
    m_params = p;
    m_imp->cfg().updt_params(p);
}

void th_rewriter::get_param_descrs(param_descrs & r) {
    bool_rewriter::get_param_descrs(r);
    arith_rewriter::get_param_descrs(r);
    bv_rewriter::get_param_descrs(r);
    array_rewriter::get_param_descrs(r);
    rewriter_params::collect_param_descrs(r);
}

th_rewriter::~th_rewriter() {
    dealloc(m_imp);
}

unsigned th_rewriter::get_cache_size() const {
    return m_imp->get_cache_size();
}

unsigned th_rewriter::get_num_steps() const {
    return m_imp->get_num_steps();
}


void th_rewriter::cleanup() {
    ast_manager & m = m_imp->m();
    m_imp->~imp();
    new (m_imp) imp(m, m_params);
}

void th_rewriter::reset() {
    m_imp->reset();
    m_imp->cfg().reset();
}

void th_rewriter::operator()(expr_ref & term) {
    expr_ref result(term.get_manager());
    m_imp->operator()(term, result);
    term = std::move(result);
}

void th_rewriter::operator()(expr * t, expr_ref & result) {
    m_imp->operator()(t, result);
}

void th_rewriter::operator()(expr * t, expr_ref & result, proof_ref & result_pr) {
    m_imp->operator()(t, result, result_pr);
}

expr_ref th_rewriter::operator()(expr * n, unsigned num_bindings, expr * const * bindings) {
    return m_imp->operator()(n, num_bindings, bindings);
}

void th_rewriter::set_substitution(expr_substitution * s) {
    m_imp->reset(); // reset the cache
    m_imp->cfg().set_substitution(s);
}

expr_dependency * th_rewriter::get_used_dependencies() {
    return m_imp->cfg().m_used_dependencies;
}

void th_rewriter::reset_used_dependencies() {
    if (get_used_dependencies() != nullptr) {
        set_substitution(m_imp->cfg().m_subst); // reset cache preserving subst
        m_imp->cfg().m_used_dependencies = nullptr;
    }
}

expr_ref th_rewriter::mk_app(func_decl* f, unsigned num_args, expr* const* args) {
    return m_imp->mk_app(f, num_args, args);
}

void th_rewriter::set_solver(expr_solver* solver) {
    m_imp->set_solver(solver);
}


bool th_rewriter::reduce_quantifier(quantifier * old_q, 
                                    expr * new_body, 
                                    expr * const * new_patterns, 
                                    expr * const * new_no_patterns,
                                    expr_ref & result,
                                    proof_ref & result_pr) {
    return m_imp->cfg().reduce_quantifier(old_q, new_body, new_patterns, new_no_patterns, result, result_pr);
}
