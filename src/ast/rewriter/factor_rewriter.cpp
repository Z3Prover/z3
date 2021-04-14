/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    factor_rewriter.cpp

Abstract:

    Rewriting utilities for factoring polynomials in equations,
    and inequalities.

Author:

    Nikolaj (nbjorner) 2011-19-05

Notes:

--*/

#include "ast/rewriter/factor_rewriter.h"
#include "ast/ast_pp.h"
#include "ast/rewriter/rewriter_def.h"

factor_rewriter::factor_rewriter(ast_manager & m): m_manager(m), m_arith(m), m_factors(m) {
}

br_status factor_rewriter::mk_app_core(
    func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {

    if (m().is_eq(f)) { SASSERT(num_args == 2);  return mk_eq(args[0], args[1], result); }

    if(f->get_family_id() == a().get_family_id()) {
        switch (f->get_decl_kind()) {
        case OP_LE:   SASSERT(num_args == 2); return mk_le(args[0], args[1], result);
        case OP_GE:   SASSERT(num_args == 2); return mk_ge(args[0], args[1], result);
        case OP_LT:   SASSERT(num_args == 2); return mk_lt(args[0], args[1], result);
        case OP_GT:   SASSERT(num_args == 2); return mk_gt(args[0], args[1], result);
        default: return BR_FAILED;
        }
    }
    return BR_FAILED;
}

br_status factor_rewriter::mk_eq(expr * arg1, expr * arg2, expr_ref & result) {
    if (!a().is_real(arg1) && !m_arith.is_int(arg1)) {
        return BR_FAILED;
    }
    mk_adds(arg1, arg2);
    mk_muls();
    if (m_muls.empty()) {
        result = m().mk_true();
        return BR_DONE;
    }
    if (!extract_factors()) {
        TRACE("factor_rewriter", tout << mk_pp(arg1, m()) << " = " << mk_pp(arg2, m()) << "\n";);
        return BR_FAILED;
    }
    powers_t::iterator it = m_powers.begin(), end = m_powers.end();
    expr_ref_vector eqs(m());
    for(; it != end; ++it) {
        expr* e = it->m_key;
        eqs.push_back(m().mk_eq(e, a().mk_numeral(rational(0), e->get_sort())));  
    }
    result = m().mk_or(eqs.size(), eqs.data());    
    return BR_DONE;
}

br_status factor_rewriter::mk_le(expr * arg1, expr * arg2, expr_ref & result) {
    mk_adds(arg1, arg2);
    mk_muls();
    if (m_muls.empty()) {
        result = m().mk_true();
        return BR_DONE;
    }
    if (!extract_factors()) {
        TRACE("factor_rewriter", tout << mk_pp(arg1, m()) << " <= " << mk_pp(arg2, m()) << "\n";);
        return BR_FAILED;
    }

    // a^2 * b^3 * c <= 0 -> 
    // a = 0 \/ (b = 0 \/ b > 0 & c <= 0 \/ b < 0 & c >= 0)
    // 

    expr_ref neg(m());
    expr_ref_vector eqs(m());
    mk_is_negative(neg, eqs);
    eqs.push_back(neg);
    result = m().mk_or(eqs.size(), eqs.data());
    TRACE("factor_rewriter", 
          tout << mk_pp(arg1, m()) << " <= " << mk_pp(arg2, m()) << "\n";
          tout << mk_pp(result.get(), m()) << "\n";);
    return BR_DONE;
}

br_status factor_rewriter::mk_lt(expr * arg1, expr * arg2, expr_ref & result) {
    mk_adds(arg1, arg2);
    mk_muls();
    if (m_muls.empty()) {
        result = m().mk_false();
        return BR_DONE;
    }
    if (!extract_factors()) {
        TRACE("factor_rewriter", tout << mk_pp(arg1, m()) << " < " << mk_pp(arg2, m()) << "\n";);
        return BR_FAILED;
    }
    // a^2 * b^3 * c < 0 -> 
    // a != 0 /\ (b > 0 & c < 0 \/ b < 0 & c > 0)
    // 

    expr_ref neg(m());
    expr_ref_vector eqs(m());
    mk_is_negative(neg, eqs);
    for (unsigned i = 0; i < eqs.size(); ++i) {
        eqs[i] = m().mk_not(eqs[i].get());
    }
    eqs.push_back(neg);
    result = m().mk_and(eqs.size(), eqs.data());
    TRACE("factor_rewriter", tout << mk_pp(result.get(), m()) << "\n";);
    return BR_DONE;
}

void factor_rewriter::mk_is_negative(expr_ref& result, expr_ref_vector& eqs) {
    powers_t::iterator it = m_powers.begin(), end = m_powers.end();
    SASSERT(m_powers.size() >= 1);
    SASSERT(it != end);
    expr_ref neg0(m()), neg(m()), pos0(m()), pos(m()), tmp(m());
    expr* e = it->m_key;
    expr_ref zero(a().mk_numeral(rational(0), e->get_sort()), m());
    expr_ref_vector conjs(m());
    pos0 = m().mk_true();
    neg0 = m().mk_false();
    for(; it != end; ++it) {
        e = it->m_key;
        eqs.push_back(m().mk_eq(zero, e));
        if (!even(it->m_value)) {
            pos = a().mk_lt(zero, e);
            neg = a().mk_lt(e, zero);
            if (m().is_false(neg0)) {
                neg0 = neg;
                pos0 = pos;
            }
            else {
                tmp = m().mk_or(m().mk_and(pos, pos0), m().mk_and(neg, neg0));
                neg0 = m().mk_or(m().mk_and(neg, pos0), m().mk_and(pos, neg0));
                pos0 = tmp;
            }
        }
    }
    result = neg0;
}

// convert arg1 - arg2 into 
// sum of monomials
// m_adds: sum of products.
// m_muls: list of products
void factor_rewriter::mk_adds(expr* arg1, expr* arg2) {
    m_adds.reset();
    m_adds.push_back(std::make_pair(arg1, true));
    m_adds.push_back(std::make_pair(arg2, false));
    rational k;
    for (unsigned i = 0; i < m_adds.size();) {
        bool sign = m_adds[i].second;
        expr* _e   = m_adds[i].first;

        TRACE("factor_rewriter", tout << i << " " << mk_pp(_e, m_manager) << "\n";);

        if (!is_app(_e)) {
            ++i;
            continue;
        }
        app* e = to_app(_e);
        if (a().is_add(e) && e->get_num_args() > 0) {
            m_adds[i].first = e->get_arg(0);
            for (unsigned j = 1; j < e->get_num_args(); ++j) {
                m_adds.push_back(std::make_pair(e->get_arg(j),sign));
            }            
        }
        else if (a().is_sub(e) && e->get_num_args() > 0) {
            m_adds[i].first = e->get_arg(0);
            for (unsigned j = 1; j < e->get_num_args(); ++j) {
                m_adds.push_back(std::make_pair(e->get_arg(j),!sign));
            }
        }
        else if (a().is_uminus(e)) {
            m_adds[i].first = e->get_arg(0);
            m_adds[i].second = !sign;
        }
        else if (a().is_numeral(e, k) && k.is_zero()) {
            unsigned sz = m_adds.size();
            m_adds[i] = m_adds[sz-1];
            m_adds.resize(sz-1);
        }
        else {
            ++i;
        }
    }
    TRACE("factor_rewriter",
        for (unsigned i = 0; i < m_adds.size(); ++i) {
            if (!m_adds[i].second) tout << "-"; else tout << "+";
            tout << mk_pp(m_adds[i].first, m()) << " ";
        }
        tout << "\n";
        );
}

void factor_rewriter::mk_muls() {
    m_muls.reset();
    for (unsigned i = 0; i < m_adds.size(); ++i) {
        m_muls.push_back(ptr_vector<expr>());
        m_muls.back().push_back(m_adds[i].first);
        mk_expand_muls(m_muls.back());
        if (m_muls.back().empty()) {
            m_muls.pop_back();
            m_adds.erase(m_adds.begin() + i);
            --i;
        }
    }
    TRACE("factor_rewriter", 
        for (unsigned i = 0; i < m_muls.size(); ++i) {
            for (unsigned j = 0; j < m_muls[i].size(); ++j) {
                tout << mk_pp(m_muls[i][j], m()) << " ";
            }
            tout << "\n";
        }
        tout << "\n";
        );
}

void factor_rewriter::mk_expand_muls(ptr_vector<expr>& muls) {
    for (unsigned i = 0; i < muls.size(); ) {
        expr* _e   = muls[i];
        if (!is_app(_e)) {
            ++i;
            continue;
        }
        app* e = to_app(_e);
        if (a().is_mul(e) && e->get_num_args() > 0) {
            muls[i] = e->get_arg(0);
            for (unsigned j = 1; j < e->get_num_args(); ++j) {
                muls.push_back(e->get_arg(j));
            }
        }       
        else {
            ++i;
        }
    }
}

bool factor_rewriter::extract_factors() {
    m_factors.reset();
    unsigned_vector pos;
    expr* e;
    SASSERT(!m_muls.empty());
    if (m_muls.size() == 1) {
        if (m_muls[0].size() > 1) {
            m_factors.append(m_muls[0].size(), m_muls[0].data());
            if (!m_adds[0].second) {
                bool found_numeral = false;
                sort* s = m_muls[0][0]->get_sort();
                rational v;
                for (unsigned i = 0; !found_numeral && i < m_factors.size(); ++i) {
                    if (a().is_numeral(m_factors[i].get(), v)) {
                        m_factors[i] = a().mk_numeral(-v, s);
                        found_numeral = true;
                    }
                }
                if (!found_numeral) {
                    m_factors.push_back(a().mk_numeral(rational(-1),s));
                }
            }
            collect_powers();
            return true;
        }
        return false;
    }
    for (unsigned i = 0; i < m_muls[0].size(); ++i) {
        pos.reset();
        pos.push_back(i);
        e = m_muls[0][i];
        bool ok = true;
        for (unsigned j = 1; ok && j < m_muls.size(); ++j) {
            ok = false;
            unsigned k = 0;
            for (k = 0; !ok && k < m_muls[j].size(); ++k) {
                ok = m_muls[j][k] == e;
            }
            pos.push_back(k-1);
        }
        if (ok) {
            SASSERT(pos.size() == m_muls.size());
            m_factors.push_back(e);
            for (unsigned j = 0; j < pos.size(); ++j) {
                m_muls[j].erase(m_muls[j].begin() + pos[j]);
            }
            --i;
        }
    }
    if (m_factors.empty()) {
        return false;
    }
    SASSERT(m_muls.size() == m_adds.size());
    expr_ref_vector trail(m());
    sort* s = m_factors[0]->get_sort();
    for (unsigned i = 0; i < m_adds.size(); ++i) {
        switch(m_muls[i].size()) {
        case 0: 
            e = a().mk_numeral(rational(1), s);
            break;
        case 1: 
            e = m_muls[i][0];
            break;
        default: 
            e = a().mk_mul(m_muls[i].size(), m_muls[i].data()); 
            break;
        }
        if (!m_adds[i].second) {
            e = a().mk_uminus(e);
        }
        trail.push_back(e);
    }       
    switch(trail.size()) {
    case 0: 
        break;
    case 1: 
        m_factors.push_back(trail[0].get());
        break;
    default: 
        m_factors.push_back(a().mk_add(trail.size(), trail.data()));
        break;
    }
    TRACE("factor_rewriter",
        for (unsigned i = 0; i < m_factors.size(); ++i) {
            tout << mk_pp(m_factors[i].get(), m()) << " ";
        }
        tout << "\n";
        );
    collect_powers();
    return true;
}

void factor_rewriter::collect_powers() {
    m_powers.reset();
    for (expr* f : m_factors) {
        m_powers.insert_if_not_there(f, 0)++;
    }
}

template class rewriter_tpl<factor_rewriter_cfg>;
