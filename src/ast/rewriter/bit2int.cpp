/*++
Copyright (c) 2009 Microsoft Corporation

Module Name:

    bit2cpp.cpp

Abstract:

    Routines for simplifying bit2int expressions.
    This propagates bv2int over arithmetical symbols as much as possible, 
    converting arithmetic operations into bit-vector operations.

Author:

    Nikolaj Bjorner (nbjorner) 2009-08-28

Revision History:

--*/

#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/for_each_ast.h"
#include "ast/rewriter/bit2int.h"

bit2int::bit2int(ast_manager & m) : 
    m(m), m_bv_util(m), m_rewriter(m), m_arith_util(m), m_cache(m, false), m_bit0(m) {
    m_bit0     = m_bv_util.mk_numeral(0,1);
}

void bit2int::operator()(expr * n, expr_ref & result, proof_ref& p) {
    flush_cache();
    expr_reduce emap(*this);
    for_each_ast(emap, n);
    result = get_cached(n);
    if (m.proofs_enabled() && n != result.get()) {
        // TBD: rough
        p = m.mk_rewrite(n, result);
    }
    TRACE("bit2int", 
          tout << mk_pp(n, m) << "======>\n" << result << "\n";);

}


unsigned bit2int::get_b2i_size(expr* n) {
    expr* arg = nullptr;
    VERIFY(m_bv_util.is_bv2int(n, arg));
    return m_bv_util.get_bv_size(arg);
}

unsigned bit2int::get_numeral_bits(numeral const& k) {
    numeral two(2);
    numeral n(abs(k));
    unsigned num_bits = 1;
    n = div(n, two);
    while (n.is_pos()) {
        ++num_bits;
        n = div(n, two);
    }
    return num_bits;
}

void bit2int::align_size(expr* e, unsigned sz, expr_ref& result) {
    unsigned sz1 = m_bv_util.get_bv_size(e);
    SASSERT(sz1 <= sz);
    result = m_rewriter.mk_zero_extend(sz - sz1, e);
}

void bit2int::align_sizes(expr_ref& a, expr_ref& b) {
    unsigned sz1 = m_bv_util.get_bv_size(a);
    unsigned sz2 = m_bv_util.get_bv_size(b);
    if (sz1 > sz2) {
        b = m_rewriter.mk_zero_extend(sz1 - sz2, b);    
    }
    else if (sz2 > sz1) {
        a = m_rewriter.mk_zero_extend(sz2-sz1, a);    
    }
}

bool bit2int::extract_bv(expr* n, unsigned& sz, bool& sign, expr_ref& bv) {
    numeral k;
    bool is_int;
    expr* r = nullptr;
    if (m_bv_util.is_bv2int(n, r)) {
        bv = r;
        sz = m_bv_util.get_bv_size(bv);
        sign = false;
        return true;
    }
    else if (m_arith_util.is_numeral(n, k, is_int) && is_int) {
        sz = get_numeral_bits(k);
        bv = m_bv_util.mk_numeral(k, m_bv_util.mk_sort(sz));
        sign = k.is_neg();
        return true;
    }
    else {
        return false;
    }
}


bool bit2int::mk_add(expr* e1, expr* e2, expr_ref& result) {
    unsigned sz1, sz2;
    bool sign1, sign2;
    expr_ref tmp1(m), tmp2(m), tmp3(m);
    
    if (extract_bv(e1, sz1, sign1, tmp1) && !sign1 &&
        extract_bv(e2, sz2, sign2, tmp2) && !sign2) {
        unsigned sz;
        numeral k;
        if (m_bv_util.is_numeral(tmp1, k, sz) && k.is_zero()) {
            result = e2;
            return true;
        }
        if (m_bv_util.is_numeral(tmp2, k, sz) && k.is_zero()) {
            result = e1;
            return true;
        }
        align_sizes(tmp1, tmp2);
        tmp1 = m_rewriter.mk_zero_extend(1, tmp1);
        tmp2 = m_rewriter.mk_zero_extend(1, tmp2);
        SASSERT(m_bv_util.get_bv_size(tmp1) == m_bv_util.get_bv_size(tmp2));
        tmp3 = m_rewriter.mk_bv_add(tmp1, tmp2);
        result = m_rewriter.mk_bv2int(tmp3);
        return true;
    }
    return false;
}

bool bit2int::mk_comp(eq_type ty, expr* e1, expr* e2, expr_ref& result) {
    unsigned sz1, sz2;
    bool sign1, sign2;
    expr_ref tmp1(m), tmp2(m), tmp3(m);
    if (extract_bv(e1, sz1, sign1, tmp1) && !sign1 &&
        extract_bv(e2, sz2, sign2, tmp2) && !sign2) {
        align_sizes(tmp1, tmp2);
        SASSERT(m_bv_util.get_bv_size(tmp1) == m_bv_util.get_bv_size(tmp2));
        switch(ty) {
        case lt:
            tmp3 = m_rewriter.mk_ule(tmp2, tmp1);
            result = m.mk_not(tmp3);
            break;
        case le:
            result = m_rewriter.mk_ule(tmp1, tmp2);
            break;
        case eq:
            result = m.mk_eq(tmp1, tmp2);
            break;
        }
        return true;
    }
    return false;
}

bool bit2int::mk_mul(expr* e1, expr* e2, expr_ref& result) {
    unsigned sz1, sz2;
    bool sign1, sign2;
    expr_ref tmp1(m), tmp2(m);
    expr_ref tmp3(m);
    
    if (extract_bv(e1, sz1, sign1, tmp1) &&
        extract_bv(e2, sz2, sign2, tmp2)) {
        align_sizes(tmp1, tmp2);
        tmp1 = m_rewriter.mk_zero_extend(m_bv_util.get_bv_size(tmp1), tmp1);
        tmp2 = m_rewriter.mk_zero_extend(m_bv_util.get_bv_size(tmp2), tmp2);

        SASSERT(m_bv_util.get_bv_size(tmp1) == m_bv_util.get_bv_size(tmp2));
        tmp3 = m_rewriter.mk_bv_mul(tmp1, tmp2);
        result = m_rewriter.mk_bv2int(tmp3);
        if (sign1 != sign2) {
            result = m_arith_util.mk_uminus(result);
        }
        return true;
    }
    return false;
}

bool bit2int::is_bv_poly(expr* n, expr_ref& pos, expr_ref& neg) {
    ptr_vector<expr> todo;
    expr_ref tmp(m);
    numeral k;
    bool is_int;
    todo.push_back(n);
    neg = pos = m_rewriter.mk_bv2int(m_bit0);
        
    while (!todo.empty()) {
        n = todo.back();
        todo.pop_back();
        expr* arg1 = nullptr, *arg2 = nullptr;
        if (m_bv_util.is_bv2int(n)) {
            VERIFY(mk_add(n, pos, pos));
        }
        else if (m_arith_util.is_numeral(n, k, is_int) && is_int) {
            if (k.is_nonneg()) {
                VERIFY(mk_add(n, pos, pos));
            }
            else {
                tmp = m_arith_util.mk_numeral(-k, true);
                VERIFY(mk_add(tmp, neg, neg));
            }
        }
        else if (m_arith_util.is_add(n)) {
            for (expr* arg : *to_app(n)) {
                todo.push_back(arg);
            }
        }
        else if (m_arith_util.is_mul(n, arg1, arg2) &&
                 m_arith_util.is_numeral(arg1, k, is_int) && is_int && k.is_minus_one() &&
                 m_bv_util.is_bv2int(arg2)) {
            VERIFY(mk_add(arg2, neg, neg));
        }
        else if (m_arith_util.is_mul(n, arg1, arg2) &&
                 m_arith_util.is_numeral(arg2, k, is_int) && is_int && k.is_minus_one() &&
                 m_bv_util.is_bv2int(arg1)) {
            VERIFY(mk_add(arg1, neg, neg));
        }
        else if (m_arith_util.is_uminus(n, arg1) &&
                 m_bv_util.is_bv2int(arg1)) {
            VERIFY(mk_add(arg1, neg, neg));
        }
        else {
            TRACE("bit2int", tout << "Not a poly: " << mk_pp(n, m) << "\n";);
            return false;
        }
    }
    return true;
}

void bit2int::visit(quantifier* q) {
    expr_ref result(m);
    result = get_cached(q->get_expr());
    result = m.update_quantifier(q, result);                                                   
    cache_result(q, result);
}

void bit2int::visit(app* n) {
    func_decl* f = n->get_decl();
    unsigned num_args = n->get_num_args();

    m_args.reset();
    for (expr* arg : *n) {
        m_args.push_back(get_cached(arg));
    }

    expr* const* args = m_args.c_ptr();

    bool has_b2i = 
        m_arith_util.is_le(n) || m_arith_util.is_ge(n) || m_arith_util.is_gt(n) || 
        m_arith_util.is_lt(n) || m.is_eq(n);
    expr_ref result(m);
    for (unsigned i = 0; !has_b2i && i < num_args; ++i) {
        has_b2i = m_bv_util.is_bv2int(args[i]);
    }
    if (!has_b2i) {
        result = m.mk_app(f, num_args, args);
        cache_result(n, result);
        return;
    }
    //
    // bv2int(x) + bv2int(y) -> bv2int(pad(x) + pad(y))
    // bv2int(x) + k         -> bv2int(pad(x) + pad(k))
    // bv2int(x) * bv2int(y) -> bv2int(pad(x) * pad(y))
    // bv2int(x) * k         -> sign(k)*bv2int(pad(x) * pad(k))
    // bv2int(x) - bv2int(y) <= z -> bv2int(x) <= bv2int(y) + z
    // bv2int(x) <= z - bv2int(y) -> bv2int(x) + bv2int(y) <= z
    //
    
    expr* e1 = nullptr, *e2 = nullptr;
    expr_ref tmp1(m), tmp2(m);
    expr_ref tmp3(m);
    expr_ref pos1(m), neg1(m);
    expr_ref pos2(m), neg2(m);
    expr_ref e2bv(m);
    bool sign2;
    numeral k;
    unsigned sz2;

    if (num_args >= 2) {
        e1 = args[0];
        e2 = args[1];
    }

    if (m_arith_util.is_add(n) && num_args >= 1) {
        result = e1;
        for (unsigned i = 1; i < num_args; ++i) {
            e1 = result;
            e2 = args[i];
            if (!mk_add(e1, e2, result)) {
                result = m.mk_app(f, num_args, args);
                cache_result(n, result);
                return;
            }
        }
        cache_result(n, result);        
    }
    else if (m_arith_util.is_mul(n) && num_args >= 1) {
        result = e1;
        for (unsigned i = 1; i < num_args; ++i) {
            e1 = result;
            e2 = args[i];
            if (!mk_mul(e1, e2, result)) {
                result = m.mk_app(f, num_args, args);
                cache_result(n, result);
                return;
            }
        }
        cache_result(n, result);        
    }
    else if (m.is_eq(n) && 
             is_bv_poly(e1, pos1, neg1) &&
             is_bv_poly(e2, pos2, neg2) &&
             mk_add(pos1, neg2, tmp1) &&
             mk_add(neg1, pos2, tmp2) &&
             mk_comp(eq, tmp1, tmp2, result)) {
        cache_result(n, result);
    }
    else if (m_arith_util.is_le(n) && 
             is_bv_poly(e1, pos1, neg1) &&
             is_bv_poly(e2, pos2, neg2) &&
             mk_add(pos1, neg2, tmp1) &&
             mk_add(neg1, pos2, tmp2) &&
             mk_comp(le, tmp1, tmp2, result)) {
        cache_result(n, result);
    }
    else if (m_arith_util.is_lt(n) && 
             is_bv_poly(e1, pos1, neg1) &&
             is_bv_poly(e2, pos2, neg2) &&
             mk_add(pos1, neg2, tmp1) &&
             mk_add(neg1, pos2, tmp2) &&
             mk_comp(lt, tmp1, tmp2, result)) {
        cache_result(n, result);
    }
    else if (m_arith_util.is_ge(n) && 
             is_bv_poly(e1, pos1, neg1) &&
             is_bv_poly(e2, pos2, neg2) &&
             mk_add(pos1, neg2, tmp1) &&
             mk_add(neg1, pos2, tmp2) &&
             mk_comp(le, tmp2, tmp1, result)) {
        cache_result(n, result);
    }
    else if (m_arith_util.is_gt(n) && 
             is_bv_poly(e1, pos1, neg1) &&
             is_bv_poly(e2, pos2, neg2) &&
             mk_add(pos1, neg2, tmp1) &&
             mk_add(neg1, pos2, tmp2) &&
             mk_comp(lt, tmp2, tmp1, result)) {
        cache_result(n, result);
    }
    else if (m_arith_util.is_mod(n) &&
             is_bv_poly(e1, pos1, neg1) &&
             extract_bv(e2, sz2, sign2, e2bv) && !sign2) {
        //
        // (pos1 - neg1) mod e2 = (pos1 + (e2 - (neg1 mod e2))) mod e2
        //
        unsigned sz_p, sz_n, sz;
        bool sign_p, sign_n;
        expr_ref tmp_p(m), tmp_n(m);
        VERIFY(extract_bv(pos1, sz_p, sign_p, tmp_p));
        VERIFY(extract_bv(neg1, sz_n, sign_n, tmp_n));
        SASSERT(!sign_p && !sign_n);

        // pos1 mod e2
        if (m_bv_util.is_numeral(tmp_n, k, sz) && k.is_zero()) {
            tmp1 = tmp_p;
            tmp2 = e2bv;
            align_sizes(tmp1, tmp2);
            tmp3 = m_rewriter.mk_bv_urem(tmp1, tmp2);
            result = m_rewriter.mk_bv2int(tmp3);
            cache_result(n, result);
            return;
        }

        // neg1 mod e2;
        tmp1 = tmp_n;
        tmp2 = e2bv;
        align_sizes(tmp1, tmp2);
        tmp3 = m_rewriter.mk_bv_urem(tmp1, tmp2);
        // e2 - (neg1 mod e2)
        tmp1 = e2bv;
        tmp2 = tmp3;
        align_sizes(tmp1, tmp2);
        tmp3 = m_rewriter.mk_bv_sub(tmp1, tmp2);
        // pos1 + (e2 - (neg1 mod e2))
        tmp1 = tmp_p;
        tmp2 = tmp3;
        align_sizes(tmp1, tmp2);
        tmp_p = m_rewriter.mk_zero_extend(1, tmp1);
        tmp_n = m_rewriter.mk_zero_extend(1, tmp2);
        tmp1 = m_rewriter.mk_bv_add(tmp_p, tmp_n);
        // (pos1 + (e2 - (neg1 mod e2))) mod e2
        tmp2 = e2bv;
        align_sizes(tmp1, tmp2);
        tmp3 = m_rewriter.mk_bv_urem(tmp1, tmp2);
        result = m_rewriter.mk_bv2int(tmp3);

        cache_result(n, result);
    }
    else {
        result = m.mk_app(f, num_args, args);
        cache_result(n, result);
    }
}

expr * bit2int::get_cached(expr * n) const { 
    expr* r = nullptr;
    proof* p = nullptr;
    const_cast<bit2int*>(this)->m_cache.get(n, r, p);
    CTRACE("bit2int", !r, tout << mk_pp(n, m) << "\n";);
    return r;
}

void bit2int::cache_result(expr * n, expr * r) { 
    TRACE("bit2int_verbose", tout << "caching:\n" << mk_pp(n, m) <<
          "======>\n" << mk_ll_pp(r, m) << "\n";);
    m_cache.insert(n, r, nullptr); 
}
