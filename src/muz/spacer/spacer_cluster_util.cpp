/**++
Copyright (c) 2020 Arie Gurfinkel

Module Name:

    spacer_cluster_util.cpp

Abstract:

   Utility methods for clustering

Author:

    Hari Govind
    Arie Gurfinkel

Notes:

--*/

#include "ast/arith_decl_plugin.h"
#include "ast/ast.h"
#include "ast/ast_pp.h"
#include "ast/for_each_expr.h"
#include "ast/rewriter/rewriter.h"
#include "ast/rewriter/rewriter_def.h"
#include "ast/rewriter/th_rewriter.h"
#include "muz/spacer/spacer_util.h"

namespace spacer {
/// Arithmetic term order
struct arith_add_less_proc {
    const arith_util &m_arith;

    arith_add_less_proc(const arith_util &arith) : m_arith(arith) {}

    bool operator()(expr *e1, expr *e2) const {
        if (e1 == e2) return false;

        ast_lt_proc ast_lt;
        expr *k1 = nullptr, *t1 = nullptr, *k2 = nullptr, *t2 = nullptr;

        // k1*t1 < k2*t2 iff  t1 < t2 or  t1 == t2 && k1 < k2
        // k1 and k2 can be null

        if (!m_arith.is_mul(e1, k1, t1)) { t1 = e1; }
        if (!m_arith.is_mul(e2, k2, t2)) { t2 = e2; }

        SASSERT(t1 && t2);
        if (t1 != t2) return ast_lt(t1, t2);

        //  here: t1 == t2 && k1 != k2
        SASSERT(k1 != k2);

        // check for null
        if (!k1 || !k2) return !k1;
        return ast_lt(k1, k2);
    }
};

struct bool_and_less_proc {
    ast_manager &m;
    const arith_util &m_arith;
    bool_and_less_proc(ast_manager &mgr, const arith_util &arith)
        : m(mgr), m_arith(arith) {}

    bool operator()(expr *e1, expr *e2) const {
        expr *a1 = nullptr, *a2 = nullptr;
        bool is_not1, is_not2;
        if (e1 == e2) return false;

        is_not1 = m.is_not(e1, a1);
        a1 = is_not1 ? a1 : e1;
        is_not2 = m.is_not(e2, a2);
        a2 = is_not2 ? a2 : e2;

        return a1 == a2 ? is_not1 < is_not2 : arith_lt(a1, a2);
    }

    bool arith_lt(expr *e1, expr *e2) const {
        ast_lt_proc ast_lt;
        expr *t1, *k1, *t2, *k2;

        if (e1 == e2) return false;

        if (e1->get_kind() != e2->get_kind()) return e1->get_kind() < e2->get_kind();
        if (!is_app(e1)) return ast_lt(e1, e2);

        app *a1 = to_app(e1), *a2 = to_app(e2);

        if (a1->get_family_id() != a2->get_family_id())
            return a1->get_family_id() < a2->get_family_id();
        if (a1->get_decl_kind() != a2->get_decl_kind())
            return a1->get_decl_kind() < a2->get_decl_kind();

        if (!(m_arith.is_le(e1, t1, k1) || m_arith.is_lt(e1, t1, k1) ||
              m_arith.is_ge(e1, t1, k1) || m_arith.is_gt(e1, t1, k1))) {
            t1 = e1;
            k1 = nullptr;
        }
        if (!(m_arith.is_le(e2, t2, k2) || m_arith.is_lt(e2, t2, k2) ||
              m_arith.is_ge(e2, t2, k2) || m_arith.is_gt(e2, t2, k2))) {
            t2 = e2;
            k2 = nullptr;
        }

        if (!k1 || !k2) { return k1 == k2 ? ast_lt(t1, t2) : k1 < k2; }

        if (t1 == t2) return ast_lt(k1, k2);

        if (t1->get_kind() != t2->get_kind())
          return t1->get_kind() < t2->get_kind();

        if (!is_app(t1)) return ast_lt(t1, t2);

        unsigned d1 = to_app(t1)->get_depth();
        unsigned d2 = to_app(t2)->get_depth();
        if (d1 != d2) return d1 < d2;

        // AG: order by the leading uninterpreted constant
        expr *u1 = nullptr, *u2 = nullptr;

        u1 = get_first_uc(t1);
        u2 = get_first_uc(t2);
        if (!u1 || !u2) { return u1 == u2 ? ast_lt(t1, t2) : u1 < u2; }
        return u1 == u2 ? ast_lt(t1, t2) : ast_lt(u1, u2);
    }

    /// Returns first in left-most traversal uninterpreted constant of \p e
    ///
    /// Returns null when no uninterpreted constant is found.
    /// Recursive, assumes that expression is shallow and recursion is bounded.
    expr *get_first_uc(expr *e) const {
        expr *t, *k;
        if (is_uninterp_const(e))
            return e;
        else if (m_arith.is_add(e)) {
            if (to_app(e)->get_num_args() == 0) return nullptr;
            expr *a1 = to_app(e)->get_arg(0);
            // HG: for 3 + a, returns nullptr
            return get_first_uc(a1);
        } else if (m_arith.is_mul(e, k, t)) {
            return get_first_uc(t);
        }
        return nullptr;
    }
};

// Rewriter for normalize_order()
struct term_ordered_rpp : public default_rewriter_cfg {
    ast_manager &m;
    arith_util m_arith;
    arith_add_less_proc m_add_less;
    bool_and_less_proc m_and_less;

    term_ordered_rpp(ast_manager &man)
        : m(man), m_arith(m), m_add_less(m_arith), m_and_less(m, m_arith) {}

    bool is_add(func_decl const *n) const {
        return is_decl_of(n, m_arith.get_family_id(), OP_ADD);
    }

    br_status reduce_app(func_decl *f, unsigned num, expr *const *args,
                         expr_ref &result, proof_ref &result_pr) {
        br_status st = BR_FAILED;

        if (is_add(f)) {
            ptr_buffer<expr> kids;
            kids.append(num, args);
            std::stable_sort(kids.data(), kids.data() + kids.size(),
                             m_add_less);
            result = m_arith.mk_add(num, kids.data());
            return BR_DONE;
        }

        if (m.is_and(f)) {
            ptr_buffer<expr> kids;
            kids.append(num, args);
            std::stable_sort(kids.data(), kids.data() + kids.size(),
                             m_and_less);
            result = m.mk_and(num, kids.data());
            return BR_DONE;
        }
        return st;
    }
};

// Normalize an arithmetic expression using term order
void normalize_order(expr *e, expr_ref &out) {
    params_ref params;
    // -- arith_rewriter params
    params.set_bool("sort_sums", true);
    // params.set_bool("gcd_rounding", true);
    // params.set_bool("arith_lhs", true);
    // -- poly_rewriter params
    // params.set_bool("som", true);
    // params.set_bool("flat", true);

    // apply theory rewriter
    th_rewriter rw1(out.m(), params);
    rw1(e, out);

    STRACE("spacer_normalize_order'",
           tout << "OUT Before:" << mk_pp(out, out.m()) << "\n";);
    // apply term ordering
    term_ordered_rpp t_ordered(out.m());
    rewriter_tpl<term_ordered_rpp> rw2(out.m(), false, t_ordered);
    rw2(out.get(), out);
    STRACE("spacer_normalize_order'",
           tout << "OUT After :" << mk_pp(out, out.m()) << "\n";);
}

/// Multiply an expression \p fml by a rational \p num
///
/// \p fml should be of sort Int, Real, or BitVec
/// multiplication is simplifying
void mul_by_rat(expr_ref &fml, rational num) {
    if (num.is_one()) return;

    ast_manager &m = fml.get_manager();
    arith_util m_arith(m);
    bv_util m_bv(m);
    expr_ref e(m);
    SASSERT(m_arith.is_int_real(fml) || m_bv.is_bv(fml));
    if (m_arith.is_int_real(fml)) {
        e = m_arith.mk_mul(m_arith.mk_numeral(num, m_arith.is_int(fml)), fml);
    } else if (m_bv.is_bv(fml)) {
        unsigned sz = m_bv.get_bv_size(fml);
        e = m_bv.mk_bv_mul(m_bv.mk_numeral(num, sz), fml);
    }

    // use theory rewriter to simplify
    params_ref params;
    params.set_bool("som", true);
    params.set_bool("flat", true);
    th_rewriter rw(m, params);
    rw(e, fml);
}
} // namespace spacer
template class rewriter_tpl<spacer::term_ordered_rpp>;
