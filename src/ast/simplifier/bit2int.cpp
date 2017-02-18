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

#include "bit2int.h"
#include "ast_pp.h"
#include "ast_ll_pp.h"
#include "for_each_ast.h"

#define CHECK(_x_) if (!(_x_)) { UNREACHABLE(); }

bit2int::bit2int(ast_manager & m) : 
    m_manager(m), m_bv_util(m), m_arith_util(m), m_cache(m), m_bit0(m) {
    m_bit0     = m_bv_util.mk_numeral(0,1);
}

void bit2int::operator()(expr * m, expr_ref & result, proof_ref& p) {
    flush_cache();
    expr_reduce emap(*this);
    for_each_ast(emap, m);
    result = get_cached(m);
    if (m_manager.proofs_enabled() && m != result.get()) {
        // TBD: rough
        p = m_manager.mk_rewrite(m, result);
    }
    TRACE("bit2int", 
          tout << mk_pp(m, m_manager) << "======>\n" 
          << mk_pp(result, m_manager) << "\n";);

}


unsigned bit2int::get_b2i_size(expr* n) {
    SASSERT(m_bv_util.is_bv2int(n));
    return m_bv_util.get_bv_size(to_app(n)->get_arg(0));
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
    m_bv_simplifier->mk_zeroext(sz-sz1, e, result);    
}

void bit2int::align_sizes(expr_ref& a, expr_ref& b) {
    unsigned sz1 = m_bv_util.get_bv_size(a);
    unsigned sz2 = m_bv_util.get_bv_size(b);
    expr_ref tmp(m_manager);
    if (sz1 > sz2) {
        m_bv_simplifier->mk_zeroext(sz1-sz2, b, tmp);    
        b = tmp;
    }
    else if (sz2 > sz1) {
        m_bv_simplifier->mk_zeroext(sz2-sz1, a, tmp);    
        a = tmp;
    }
}

bool bit2int::extract_bv(expr* n, unsigned& sz, bool& sign, expr_ref& bv) {
    numeral k;
    bool is_int;
    if (m_bv_util.is_bv2int(n)) {
        bv = to_app(n)->get_arg(0);
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
    expr_ref tmp1(m_manager), tmp2(m_manager), tmp3(m_manager);
    
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
        m_bv_simplifier->mk_zeroext(1, tmp1, tmp1);
        m_bv_simplifier->mk_zeroext(1, tmp2, tmp2);
        SASSERT(m_bv_util.get_bv_size(tmp1) == m_bv_util.get_bv_size(tmp2));
        m_bv_simplifier->mk_add(tmp1, tmp2, tmp3);
        m_bv_simplifier->mk_bv2int(tmp3, m_arith_util.mk_int(), result);
        return true;
    }
    return false;
}

bool bit2int::mk_comp(eq_type ty, expr* e1, expr* e2, expr_ref& result) {
    unsigned sz1, sz2;
    bool sign1, sign2;
    expr_ref tmp1(m_manager), tmp2(m_manager), tmp3(m_manager);
    if (extract_bv(e1, sz1, sign1, tmp1) && !sign1 &&
        extract_bv(e2, sz2, sign2, tmp2) && !sign2) {
        align_sizes(tmp1, tmp2);
        SASSERT(m_bv_util.get_bv_size(tmp1) == m_bv_util.get_bv_size(tmp2));
        switch(ty) {
        case lt:
            m_bv_simplifier->mk_leq_core(false, tmp2, tmp1, tmp3);
            result = m_manager.mk_not(tmp3);
            break;
        case le:
            m_bv_simplifier->mk_leq_core(false,tmp1, tmp2, result);
            break;
        case eq:
            result = m_manager.mk_eq(tmp1,tmp2);
            break;
        }
        return true;
    }
    return false;
}

bool bit2int::mk_mul(expr* e1, expr* e2, expr_ref& result) {
    unsigned sz1, sz2;
    bool sign1, sign2;
    expr_ref tmp1(m_manager), tmp2(m_manager);
    expr_ref tmp3(m_manager);
    
    if (extract_bv(e1, sz1, sign1, tmp1) &&
        extract_bv(e2, sz2, sign2, tmp2)) {
        align_sizes(tmp1, tmp2);
        m_bv_simplifier->mk_zeroext(m_bv_util.get_bv_size(tmp1), tmp1, tmp1);
        m_bv_simplifier->mk_zeroext(m_bv_util.get_bv_size(tmp2), tmp2, tmp2);

        SASSERT(m_bv_util.get_bv_size(tmp1) == m_bv_util.get_bv_size(tmp2));
        m_bv_simplifier->mk_mul(tmp1, tmp2, tmp3);
        m_bv_simplifier->mk_bv2int(tmp3, m_arith_util.mk_int(), result);
        if (sign1 != sign2) {
            result = m_arith_util.mk_uminus(result);
        }
        return true;
    }
    return false;
}

bool bit2int::is_bv_poly(expr* n, expr_ref& pos, expr_ref& neg) {
    ptr_vector<expr> todo;
    expr_ref tmp(m_manager);
    numeral k;
    bool is_int;
    todo.push_back(n);
    m_bv_simplifier->mk_bv2int(m_bit0, m_arith_util.mk_int(), pos);
    m_bv_simplifier->mk_bv2int(m_bit0, m_arith_util.mk_int(), neg);
        
    while (!todo.empty()) {
        n = todo.back();
        todo.pop_back();
        if (m_bv_util.is_bv2int(n)) {
            CHECK(mk_add(n, pos, pos));
        }
        else if (m_arith_util.is_numeral(n, k, is_int) && is_int) {
            if (k.is_nonneg()) {
                CHECK(mk_add(n, pos, pos));
            }
            else {
                tmp = m_arith_util.mk_numeral(-k, true);
                CHECK(mk_add(tmp, neg, neg));
            }
        }
        else if (m_arith_util.is_add(n)) {
            for (unsigned i = 0; i < to_app(n)->get_num_args(); ++i) {
                todo.push_back(to_app(n)->get_arg(i));
            }
        }
        else if (m_arith_util.is_mul(n) &&
                 to_app(n)->get_num_args() == 2 &&
                 m_arith_util.is_numeral(to_app(n)->get_arg(0), k, is_int) && is_int && k.is_minus_one() &&
                 m_bv_util.is_bv2int(to_app(n)->get_arg(1))) {
            CHECK(mk_add(to_app(n)->get_arg(1), neg, neg));
        }
        else if (m_arith_util.is_mul(n) &&
                 to_app(n)->get_num_args() == 2 &&
                 m_arith_util.is_numeral(to_app(n)->get_arg(1), k, is_int) && is_int && k.is_minus_one() &&
                 m_bv_util.is_bv2int(to_app(n)->get_arg(0))) {
            CHECK(mk_add(to_app(n)->get_arg(0), neg, neg));
        }
        else if (m_arith_util.is_uminus(n) &&
                 m_bv_util.is_bv2int(to_app(n)->get_arg(0))) {
            CHECK(mk_add(to_app(n)->get_arg(0), neg, neg));
        }
        else {
            TRACE("bit2int", tout << "Not a poly: " << mk_pp(n, m_manager) << "\n";);
            return false;
        }
    }
    return true;
}

void bit2int::visit(quantifier* q) {
    expr_ref result(m_manager);
    result = get_cached(q->get_expr());
    result = m_manager.update_quantifier(q, result);                                                   
    cache_result(q, result);
}

void bit2int::visit(app* n) {
    func_decl* f = n->get_decl();
    unsigned num_args = n->get_num_args();

    m_args.reset();
    for (unsigned i = 0; i < num_args; ++i) {
        m_args.push_back(get_cached(n->get_arg(i)));
    }

    expr* const* args = m_args.c_ptr();

    bool has_b2i = 
        m_arith_util.is_le(n) || m_arith_util.is_ge(n) || m_arith_util.is_gt(n) || 
        m_arith_util.is_lt(n) || m_manager.is_eq(n);
    expr_ref result(m_manager);
    for (unsigned i = 0; !has_b2i && i < num_args; ++i) {
        has_b2i = m_bv_util.is_bv2int(args[i]);
    }
    if (!has_b2i) {
        result = m_manager.mk_app(f, num_args, args);
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
    
    expr* e1 = 0, *e2 = 0;
    expr_ref tmp1(m_manager), tmp2(m_manager);
    expr_ref tmp3(m_manager);
    expr_ref pos1(m_manager), neg1(m_manager);
    expr_ref pos2(m_manager), neg2(m_manager);
    expr_ref e2bv(m_manager);
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
                result = m_manager.mk_app(f, num_args, args);
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
                result = m_manager.mk_app(f, num_args, args);
                cache_result(n, result);
                return;
            }
        }
        cache_result(n, result);        
    }
    else if (m_manager.is_eq(n) && 
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
        expr_ref tmp_p(m_manager), tmp_n(m_manager);
        CHECK(extract_bv(pos1, sz_p, sign_p, tmp_p));
        CHECK(extract_bv(neg1, sz_n, sign_n, tmp_n));
        SASSERT(!sign_p && !sign_n);

        // pos1 mod e2
        if (m_bv_util.is_numeral(tmp_n, k, sz) && k.is_zero()) {
            tmp1 = tmp_p;
            tmp2 = e2bv;
            align_sizes(tmp1, tmp2);
            m_bv_simplifier->mk_bv_urem(tmp1, tmp2, tmp3);
            m_bv_simplifier->mk_bv2int(tmp3, m_arith_util.mk_int(), result);
            cache_result(n, result);
            return;
        }

        // neg1 mod e2;
        tmp1 = tmp_n;
        tmp2 = e2bv;
        align_sizes(tmp1, tmp2);
        m_bv_simplifier->mk_bv_urem(tmp1, tmp2, tmp3);
        // e2 - (neg1 mod e2)
        tmp1 = e2bv;
        tmp2 = tmp3;
        align_sizes(tmp1, tmp2);
        m_bv_simplifier->mk_sub(tmp1, tmp2, tmp3);
        // pos1 + (e2 - (neg1 mod e2))
        tmp1 = tmp_p;
        tmp2 = tmp3;
        align_sizes(tmp1, tmp2);
        m_bv_simplifier->mk_zeroext(1, tmp1, tmp_p);
        m_bv_simplifier->mk_zeroext(1, tmp2, tmp_n);
        m_bv_simplifier->mk_add(tmp_p, tmp_n, tmp1);
        // (pos1 + (e2 - (neg1 mod e2))) mod e2
        tmp2 = e2bv;
        align_sizes(tmp1, tmp2);
        m_bv_simplifier->mk_bv_urem(tmp1, tmp2, tmp3);

        m_bv_simplifier->mk_bv2int(tmp3, m_arith_util.mk_int(), result);

        cache_result(n, result);
    }
    else {
        result = m_manager.mk_app(f, num_args, args);
        cache_result(n, result);
    }
}

expr * bit2int::get_cached(expr * n) const { 
    return const_cast<bit2int*>(this)->m_cache.find(n);
}

void bit2int::cache_result(expr * n, expr * r) { 
    TRACE("bit2int_verbose", tout << "caching:\n" << mk_ll_pp(n, m_manager) <<
          "======>\n" << mk_ll_pp(r, m_manager) << "\n";);
    m_cache.insert(n, r); 
}
