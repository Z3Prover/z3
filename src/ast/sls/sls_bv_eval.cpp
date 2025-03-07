/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    sls_bv_eval.cpp

Author:

    Nikolaj Bjorner (nbjorner) 2024-02-07
    
--*/

#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/sls/sls_bv_eval.h"
#include "ast/sls/sls_bv_terms.h"
#include "ast/rewriter/th_rewriter.h"

namespace sls {

    bv_eval::bv_eval(sls::bv_terms& terms, sls::context& ctx): 
        m(ctx.get_manager()),
        ctx(ctx),
        terms(terms),
        m_lookahead(*this),
        bv(m),
        m_fix(*this, terms, ctx)
    {}   


    void bv_eval::register_term(expr* e) {
        if (!is_app(e))
            return;
        app* a = to_app(e);
        add_bit_vector(a);
        if (a->get_family_id() == bv.get_family_id())
            init_eval_bv(a);
        else if (bv.is_bv(e)) {
            auto& v = wval(e);
            for (unsigned i = 0; i < v.bw; ++i)
                m_tmp.set(i, false);
            v.set_repair(random_bool(), m_tmp);                     
        }
        if (bv.is_bv(e)) {
            auto& v = wval(e);
            v.bits().copy_to(v.nw, v.eval);
        }
    }

    void bv_eval::start_propagation() {
        m_lookahead.start_propagation();
    }

    void bv_eval::add_bit_vector(app* e) {
        if (!bv.is_bv(e))
            return;
        m_values.reserve(e->get_id() + 1);
        if (m_values.get(e->get_id()))
            return;
        auto v = alloc_valuation(e);
        m_values.set(e->get_id(), v);
        expr* x, * y;
        rational val;
        if (bv.is_sign_ext(e))          
            v->set_signed(e->get_parameter(0).get_int());        
        else if (bv.is_bv_ashr(e, x, y) && bv.is_numeral(y, val) && 
            val.is_unsigned() && val.get_unsigned() <= bv.get_bv_size(e)) 
            v->set_signed(val.get_unsigned());        
        return;
    }

    sls::bv_valuation* bv_eval::alloc_valuation(app* e) {
        auto bit_width = bv.get_bv_size(e);
        auto* r = alloc(sls::bv_valuation, bit_width);
        while (m_tmp.size() < 2 * r->nw) {
            m_tmp.push_back(0);
            m_tmp2.push_back(0);           
            m_tmp3.push_back(0);
            m_tmp4.push_back(0);
            m_mul_tmp.push_back(0);
            m_zero.push_back(0);
            m_one.push_back(0);
            m_a.push_back(0);
            m_b.push_back(0);
            m_nexta.push_back(0);
            m_nextb.push_back(0);
            m_aux.push_back(0);
            m_minus_one.push_back(~0);
            m_one[0] = 1;
        }
        return r;
    }

    void bv_eval::init_eval_bv(app* e) {
        if (bv.is_bv(e)) 
            eval(e).commit_eval_check_tabu();               
    }
    
    bool bv_eval::can_eval1(expr* t) const {
        expr* x, * y;
        if (!is_app(t))
            return false;
        app* e = to_app(t);
        if (m.is_eq(e, x, y))
            return bv.is_bv(x);
        if (m.is_ite(e))
            return bv.is_bv(e->get_arg(1));
        if (e->get_family_id() == bv.get_fid()) {
            switch (e->get_decl_kind()) {
            case OP_BNEG_OVFL:
            case OP_BSADD_OVFL:
            case OP_BSDIV_OVFL:
            case OP_BSMUL_NO_OVFL:
            case OP_BSMUL_NO_UDFL:
            case OP_BSMUL_OVFL:
                return false;
            default:
                return true;
            }
        }
        if (is_uninterp_const(e))
            return bv.is_bv(e);
        return false;
    }

    bool bv_eval::bval1_bv(app* e) const {
        SASSERT(m.is_bool(e));
        SASSERT(e->get_family_id() == bv.get_fid());

        auto ucompare = [&](std::function<bool(int)> const& f) {
            auto& a = wval(e->get_arg(0)); 
            auto& b = wval(e->get_arg(1)); 
            return f(mpn.compare(a.bits().data(), a.nw, b.bits().data(), b.nw));
        };

        // x <s y <=> x + 2^{bw-1} <u y + 2^{bw-1}
        auto scompare = [&](std::function<bool(int)> const& f) {
            auto& a = wval(e->get_arg(0));
            auto& b = wval(e->get_arg(1));
            add_p2_1(a, m_tmp);
            add_p2_1(b, m_tmp2);
            return f(mpn.compare(m_tmp.data(), a.nw, m_tmp2.data(), b.nw));
        };

        auto umul_overflow = [&]() {
            SASSERT(e->get_num_args() == 2);
            auto const& a = wval(e->get_arg(0));
            auto const& b = wval(e->get_arg(1));
            return a.set_mul(m_tmp2, a.bits(), b.bits());
        };

        switch (e->get_decl_kind()) {
        case OP_ULEQ: 
            return ucompare([](int i) { return i <= 0; });
        case OP_ULT: 
            return ucompare([](int i) { return i < 0; });
        case OP_UGT: 
            return ucompare([](int i) { return i > 0; });
        case OP_UGEQ: 
            return ucompare([](int i) { return i >= 0; });
        case OP_SLEQ:
            return scompare([](int i) { return i <= 0; });
        case OP_SLT:
            return scompare([](int i) { return i < 0; });
        case OP_SGT:
            return scompare([](int i) { return i > 0; });
        case OP_SGEQ:
            return scompare([](int i) { return i >= 0; });
        case OP_BIT2BOOL: {
            expr* child;
            unsigned idx;
            VERIFY(bv.is_bit2bool(e, child, idx));
            auto& a = wval(child);
            return a.bits().get(idx);
        }
        case OP_BUMUL_NO_OVFL: 
            return !umul_overflow();
        case OP_BUMUL_OVFL: 
            return umul_overflow();
        case OP_BUADD_OVFL: {
            SASSERT(e->get_num_args() == 2);
            auto const& a = wval(e->get_arg(0));
            auto const& b = wval(e->get_arg(1));
            return a.set_add(m_tmp, a.bits(), b.bits());
        }
        case OP_BNEG_OVFL:
        case OP_BSADD_OVFL:         
        case OP_BSDIV_OVFL:
        case OP_BSMUL_NO_OVFL:
        case OP_BSMUL_NO_UDFL:
        case OP_BSMUL_OVFL:
            NOT_IMPLEMENTED_YET();
            break;
        default:
            UNREACHABLE();
            break;
        }
        return false;
    }

    void bv_eval::set_bool_value_log(expr* e, bool val) {
        auto id = e->get_id();
        auto old_val = m_tmp_bool_values.get(id, l_undef);
        m_tmp_bool_values.setx(id, to_lbool(val), l_undef);
        m_tmp_bool_value_updates.push_back({ id, old_val });
        //TRACE("bv", tout << mk_bounded_pp(e, m) << " := " << val << " old: " << old_val << "\n");
    }

    void bv_eval::set_bool_value_no_log(expr* e, bool val) {
        auto id = e->get_id();
        m_tmp_bool_values.setx(id, to_lbool(val), l_undef);
    }

    bool bv_eval::get_bool_value(expr* e) const {
        SASSERT(m.is_bool(e));
        auto id = e->get_id();
        auto val = m_tmp_bool_values.get(id, l_undef);
        //TRACE("bv", tout << mk_bounded_pp(e, m) << " == " << val << "\n");
        if (val != l_undef)
            return val == l_true;     
        bool b;
        auto v = ctx.atom2bool_var(e);
        if (v != sat::null_bool_var)
            b = ctx.is_true(v);
        else
            b = bval1(e);
        m_tmp_bool_values.setx(id, to_lbool(b), l_undef);
        m_tmp_bool_value_updates.push_back({ id, l_undef });
        //TRACE("bv", tout << mk_bounded_pp(e, m) << " := " << b << " old: " << val << "\n");
        return b;
    }

    void bv_eval::restore_bool_values(unsigned r) { 
        //TRACE("bv", tout << "restore " << m_tmp_bool_value_updates.size() - r << "\n";);
        for (auto i = m_tmp_bool_value_updates.size(); i-- > r; ) {
            auto& [id, val] = m_tmp_bool_value_updates[i];
            m_tmp_bool_values.set(id, val);
        }
        m_tmp_bool_value_updates.shrink(r);
    }

    bool bv_eval::bval1_bool(app* e) const {
        SASSERT(e->get_family_id() == basic_family_id);
        switch (e->get_decl_kind()) {
        case OP_AND: {
            return all_of(*e, [&](expr* arg) { return get_bool_value(arg); });
        case OP_OR:
            return any_of(*e, [&](expr* arg) { return get_bool_value(arg); });
        case OP_NOT:
            return !get_bool_value(e->get_arg(0));
        case OP_EQ:
            if (m.is_iff(e))
                return get_bool_value(e->get_arg(0)) == get_bool_value(e->get_arg(1));
            return ctx.get_value(e->get_arg(0)) == ctx.get_value(e->get_arg(1));
        case OP_IMPLIES:
            return !get_bool_value(e->get_arg(0)) || get_bool_value(e->get_arg(1));
        case OP_ITE:
            return get_bool_value(e->get_arg(0)) ? get_bool_value(e->get_arg(1)) : get_bool_value(e->get_arg(2));
        case OP_XOR: 
            return xor_of(*e, [&](expr* arg) { return get_bool_value(arg); });                    
        case OP_TRUE:
            return true;
        case OP_FALSE:
            return false;
        case OP_DISTINCT:
            for (unsigned i = 0; i < e->get_num_args(); ++i)
                for (unsigned j = i + 1; j < e->get_num_args(); ++j)
                    if (ctx.get_value(e->get_arg(i)) == ctx.get_value(e->get_arg(j)))
                        return false;
            return true;
        default:
            UNREACHABLE();
            break;
        }
        }
        return false;
    }

    bool bv_eval::bval1(expr* t) const {
        app* e = to_app(t);
        if (e->get_family_id() == bv.get_fid())
            return bval1_bv(e);
        expr* x, * y;
        if (m.is_eq(e, x, y) && bv.is_bv(x)) 
            return wval(x).bits() == wval(y).bits();        
        if (e->get_family_id() == basic_family_id)
            return bval1_bool(e);
        return ctx.is_true(e);
    }

    sls::bv_valuation& bv_eval::eval(app* e) const {
        SASSERT(m_values.size() > e->get_id());
        SASSERT(m_values[e->get_id()]);
        auto& val = *m_values[e->get_id()];        
        eval(e, val);
        return val;        
    }

    void bv_eval::set(expr* e, sls::bv_valuation const& val) {
        m_values[e->get_id()]->set(val.bits());
    }

    void bv_eval::eval(expr* t, sls::bv_valuation& val) const {
        app* e = to_app(t);
        SASSERT(bv.is_bv(e));
        if (m.is_ite(e)) {
            SASSERT(bv.is_bv(e->get_arg(1)));
            auto& val_th = wval(e->get_arg(1));
            auto& val_el = wval(e->get_arg(2));
            bool b = m_use_tmp_bool_value ? get_bool_value(e->get_arg(0)) : bval0(e->get_arg(0));
            if (b)
                val.set(val_th.bits());
            else
                val.set(val_el.bits());
            return;
        }
        if (e->get_family_id() != bv.get_fid()) {
            val.set(wval(e).bits());
            return;
        }
        auto set_sdiv = [&]() {
            // d = udiv(abs(x), abs(y))
            // y = 0, x >= 0 -> -1
            // y = 0, x < 0 -> 1
            // x = 0, y != 0 -> 0
            // x > 0, y < 0 -> -d
            // x < 0, y > 0 -> -d
            // x > 0, y > 0 -> d
            // x < 0, y < 0 -> d
            auto& a = wval(e->get_arg(0));
            auto& b = wval(e->get_arg(1));
            bool sign_a = a.sign();
            bool sign_b = b.sign();
            if (b.is_zero()) {
                if (sign_a)
                    val.set(m_one);
                else
                    val.set(m_minus_one);
            }
            else if (a.is_zero())
                val.set(m_zero);
            else {
                if (sign_a)
                    a.set_sub(m_tmp, m_zero, a.bits());
                else
                    a.get(m_tmp);

                if (sign_b)
                    b.set_sub(m_tmp2, m_zero, b.bits());
                else
                    b.get(m_tmp2);

                set_div(m_tmp, m_tmp2, a.bw, m_tmp3, m_tmp4);
                if (sign_a == sign_b)
                    val.set(m_tmp3);
                else
                    val.set_sub(val.eval, m_zero, m_tmp3);
            }
        };

        auto mk_rotate_left = [&](unsigned n) {            
            auto& a = wval(e->get_arg(0));
            VERIFY(try_repair_rotate_left(a.bits(), val, a.bw - n));
        };

        SASSERT(e->get_family_id() == bv.get_fid());
        switch (e->get_decl_kind()) {
        case OP_BV_NUM: {
            rational n;
            VERIFY(bv.is_numeral(e, n));
            val.set_value(m_tmp, n);
            val.set(m_tmp);
            break;
        }
        case OP_BAND: {
            SASSERT(e->get_num_args() >= 2);
            auto const& a = wval(e->get_arg(0));
            auto const& b = wval(e->get_arg(1));
            for (unsigned i = 0; i < a.nw; ++i)
                val.eval[i] = a.bits()[i] & b.bits()[i];
            for (unsigned j = 2; j < e->get_num_args(); ++j) {
                auto const& c = wval(e->get_arg(j));
                for (unsigned i = 0; i < a.nw; ++i)
                    val.eval[i] &= c.bits()[i];
            }
            break;
        }
        case OP_BOR: {
            SASSERT(e->get_num_args() >= 2);
            auto const& a = wval(e->get_arg(0));
            auto const& b = wval(e->get_arg(1));
            for (unsigned i = 0; i < a.nw; ++i)
                val.eval[i] = a.bits()[i] | b.bits()[i];
            for (unsigned j = 2; j < e->get_num_args(); ++j) {
                auto const& c = wval(e->get_arg(j));
                for (unsigned i = 0; i < a.nw; ++i)
                    val.eval[i] |= c.bits()[i];
            }
            break;
        }
        case OP_BXOR: {
            SASSERT(e->get_num_args() >= 2);
            auto const& a = wval(e->get_arg(0));
            auto const& b = wval(e->get_arg(1));
            for (unsigned i = 0; i < a.nw; ++i)
                val.eval[i] = a.bits()[i] ^ b.bits()[i];
            for (unsigned j = 2; j < e->get_num_args(); ++j) {
                auto const& c = wval(e->get_arg(j));
                for (unsigned i = 0; i < a.nw; ++i)
                    val.eval[i] ^= c.bits()[i];
            }
            break;
        }
        case OP_BNAND: {
            VERIFY(e->get_num_args() == 2);
            auto const& a = wval(e->get_arg(0));
            auto const& b = wval(e->get_arg(1));
            for (unsigned i = 0; i < a.nw; ++i)
                val.eval[i] = ~(a.bits()[i] & b.bits()[i]);
            break;
        }
        case OP_BADD: {
            SASSERT(e->get_num_args() >= 2);
            auto const& a = wval(e->get_arg(0));
            auto const& b = wval(e->get_arg(1));
            for (unsigned i = 0; i < a.nw; ++i)
                val.set_add(val.eval, a.bits(), b.bits());
            for (unsigned j = 2; j < e->get_num_args(); ++j) {
                auto const& c = wval(e->get_arg(j));
                val.set_add(val.eval, val.eval, c.bits());
            }
            break;
        }
        case OP_BSUB: {
            SASSERT(e->get_num_args() == 2);
            auto const& a = wval(e->get_arg(0));
            auto const& b = wval(e->get_arg(1));
            val.set_sub(val.eval, a.bits(), b.bits());
            break;
        }
        case OP_BMUL: {
            SASSERT(e->get_num_args() > 1);
            auto const& a = wval(e->get_arg(0));
            auto const& b = wval(e->get_arg(1));
            val.set_mul(val.eval, a.bits(), b.bits(), false);
            for (unsigned j = 2; j < e->get_num_args(); ++j) {
                auto const& c = wval(e->get_arg(j));
                val.set_mul(val.eval, val.eval, c.bits(), false);
            }
            break;
        }
        case OP_CONCAT: {
            unsigned bw = 0;
            for (unsigned i = e->get_num_args(); i-- > 0;) {
                auto const& a = wval(e->get_arg(i));
                for (unsigned j = 0; j < a.bw; ++j)
                    val.eval.set(j + bw, a.get_bit(j));
                bw += a.bw;
            }
            break;
        }
        case OP_EXTRACT: {
            expr* child;
            unsigned lo, hi;
            VERIFY(bv.is_extract(e, lo, hi, child));
            auto const& a = wval(child);
            SASSERT(lo <= hi && hi + 1 <= a.bw && hi - lo + 1 == val.bw);
            for (unsigned i = lo; i <= hi; ++i)
                val.eval.set(i - lo, a.get_bit(i));            
            break;
        }
        case OP_BNOT: {
            auto& a = wval(e->get_arg(0));
            for (unsigned i = 0; i < a.nw; ++i)
                val.eval[i] = ~a.bits()[i];
            break;
        }
        case OP_BNEG: {
            auto& a = wval(e->get_arg(0));
            val.set_sub(val.eval, m_zero, a.bits());
            break;
        }
        case OP_BIT0:
            val.eval.set(0, false);
            break;
        case OP_BIT1:
            val.eval.set(0, true);            
            break;
        case OP_BSHL: {
            auto& a = wval(e->get_arg(0));
            auto& b = wval(e->get_arg(1));
            auto sh = b.to_nat(b.bw);
            if (sh == 0)
                val.set(a.bits());
            else if (sh >= b.bw)
                val.set_zero();
            else {
                for (unsigned i = 0; i < a.bw; ++i)
                    val.eval.set(i, i >= sh && a.get_bit(i - sh));
            }
            break;
        }
        case OP_BLSHR: {
            auto& a = wval(e->get_arg(0));
            auto& b = wval(e->get_arg(1));
            auto sh = b.to_nat(b.bw);
            if (sh == 0)
                val.set(a.bits());
            else if (sh >= b.bw)
                val.set_zero();
            else {
                for (unsigned i = 0; i < a.bw; ++i)
                    val.eval.set(i, i + sh < a.bw && a.get_bit(i + sh));
            }
            break;
        }
        case OP_BASHR: {
            auto& a = wval(e->get_arg(0));
            auto& b = wval(e->get_arg(1));
            auto sh = b.to_nat(b.bw);
            auto sign = a.sign();
            if (sh == 0)
                val.set(a.bits());
            else if (sh >= b.bw) {
                for (unsigned i = 0; i < a.nw; ++i)
                    m_tmp[i] = sign ? ~0 : 0;
                val.set(m_tmp);
            }
            else {
                a.set_zero(m_tmp);
                for (unsigned i = 0; i < a.bw; ++i)                    
                    m_tmp.set(i, i + sh < a.bw && a.get_bit(i + sh));
                if (sign)
                    val.set_range(m_tmp, a.bw - sh, a.bw, true);
                val.set(m_tmp);
            }
            break;
        }
        case OP_SIGN_EXT: {
            auto& a = wval(e->get_arg(0));
            a.get(m_tmp);       
            bool sign = a.sign();
            val.set_range(m_tmp, a.bw, val.bw, sign);
            val.set(m_tmp);
            break;
        }
        case OP_ZERO_EXT: {
            auto& a = wval(e->get_arg(0));
            a.get(m_tmp);
            val.set_range(m_tmp, a.bw, val.bw, false);
            val.set(m_tmp);
            break;
        }
        case OP_BUREM:
        case OP_BUREM_I:
        case OP_BUREM0: {
            auto& a = wval(e->get_arg(0));
            auto& b = wval(e->get_arg(1));

            if (b.is_zero())
                val.set(a.bits());
            else {
                set_div(a.bits(), b.bits(), b.bw, m_tmp, m_tmp2);
                val.set(m_tmp2);
            }
            break;
        }
        case OP_BSMOD:
        case OP_BSMOD_I:
        case OP_BSMOD0: {
            // u = mod(abs(x),abs(y))
            // u = 0 ->  0
            // y = 0 ->  x
            // x < 0, y < 0 ->  -u
            // x < 0, y >= 0 ->  y - u
            // x >= 0, y < 0 ->  y + u
            // x >= 0, y >= 0 ->  u
            auto& a = wval(e->get_arg(0));
            auto& b = wval(e->get_arg(1));
            if (b.is_zero())
                val.set(a.bits());
            else {
                if (a.sign())
                    a.set_sub(m_tmp3, m_zero, a.bits());
                else
                    a.set(m_tmp3, a.bits());
                if (b.sign())
                    b.set_sub(m_tmp4, m_zero, b.bits());
                else
                    a.set(m_tmp4, b.bits());  
                set_div(m_tmp3, m_tmp4, a.bw, m_tmp, m_tmp2);
                if (val.is_zero(m_tmp2))
                    val.set(m_tmp2);
                else if (a.sign() && b.sign())
                    val.set_sub(val.eval, m_zero, m_tmp2);
                else if (a.sign())
                    val.set_sub(val.eval, b.bits(), m_tmp2);
                else if (b.sign())
                    val.set_add(val.eval, b.bits(), m_tmp2);
                else
                    val.set(m_tmp2);
            }
            break;
        }
        case OP_BUDIV:
        case OP_BUDIV_I:
        case OP_BUDIV0:  {
            // x div 0 = -1
            auto& a = wval(e->get_arg(0));
            auto& b = wval(e->get_arg(1));
            if (b.is_zero()) 
                val.set(m_minus_one);            
            else {
                set_div(a.bits(), b.bits(), a.bw, m_tmp, m_tmp2);
                val.set(m_tmp);
            }
            break;
        }

        case OP_BSDIV:
        case OP_BSDIV_I:
        case OP_BSDIV0: {
            set_sdiv();
            break;
        }
        case OP_BSREM:
        case OP_BSREM0:
        case OP_BSREM_I: {
            // b = 0 -> a
            // else a - sdiv(a, b) * b
            // 
            auto& a = wval(e->get_arg(0));
            auto& b = wval(e->get_arg(1));
            if (b.is_zero()) 
                val.set(a.bits());
            else {
                set_sdiv();
                val.set_mul(m_tmp, val.eval, b.bits());
                val.set_sub(val.eval, a.bits(), m_tmp);
            }
            break;
        }
        case OP_ROTATE_LEFT: {
            unsigned n = e->get_parameter(0).get_int() % val.bw;
            mk_rotate_left(n);
            break;
        }
        case OP_ROTATE_RIGHT: {
            unsigned n = e->get_parameter(0).get_int() % val.bw;
            mk_rotate_left(val.bw - n);
            break;
        }
        case OP_EXT_ROTATE_LEFT: {
            auto& b = wval(e->get_arg(1));
            rational n = b.get_value();
            n = mod(n, rational(val.bw));
            SASSERT(n.is_unsigned());
            mk_rotate_left(n.get_unsigned());
            break;
        }
        case OP_EXT_ROTATE_RIGHT: {
            auto& b = wval(e->get_arg(1));
            rational n = b.get_value();
            n = mod(n, rational(val.bw));
            SASSERT(n.is_unsigned());
            mk_rotate_left(val.bw - n.get_unsigned());
            break;
        }
        case OP_BCOMP: {
            auto const& a = wval(e->get_arg(0));
            auto const& b = wval(e->get_arg(1));
            if (a.bits() == b.bits())
                val.set(val.eval, 1);
            else
                val.set(val.eval, 0);
            break;
        }
        case OP_INT2BV: {
            expr_ref v = ctx.get_value(e->get_arg(0));
            th_rewriter rw(m);
            v = bv.mk_int2bv(bv.get_bv_size(e), v);
            rw(v);
            rational r;
            VERIFY(bv.is_numeral(v, r));
            val.set_value(val.eval, r);
            break;
        }
        case OP_BREDAND:
        case OP_BREDOR:
        case OP_BXNOR:
            verbose_stream() << mk_bounded_pp(e, m) << "\n";
            NOT_IMPLEMENTED_YET();
            break;
        case OP_BIT2BOOL:
        case OP_UBV2INT:
        case OP_SBV2INT:
        case OP_BNEG_OVFL:
        case OP_BSADD_OVFL:
        case OP_BUADD_OVFL:
        case OP_BSDIV_OVFL:
        case OP_BSMUL_NO_OVFL:
        case OP_BSMUL_NO_UDFL:
        case OP_BSMUL_OVFL:
        case OP_BUMUL_NO_OVFL:
        case OP_BUMUL_OVFL:
        case OP_ULEQ:
        case OP_UGEQ:
        case OP_UGT:
        case OP_ULT:
        case OP_SLEQ:
        case OP_SGEQ:
        case OP_SGT:
        case OP_SLT:
            UNREACHABLE();
            break;
        default:
            UNREACHABLE();
            break;
        }
        val.clear_overflow_bits(val.eval);
    }

    digit_t bv_eval::random_bits() {
        return sls::bv_valuation::random_bits(m_rand);
    }


    bool bv_eval::is_uninterpreted(app* e) const {
        if (is_uninterp(e))
            return true;
        if (e->get_family_id() != bv.get_family_id())
            return false;
        switch (e->get_decl_kind()) {
        case OP_BSREM:
        case OP_BSREM_I:
        case OP_BSREM0:
        case OP_BSMOD:
        case OP_BSMOD_I:
        case OP_BSMOD0:
            return true;
        default:
        case OP_BSDIV:
        case OP_BSDIV_I:
        case OP_BSDIV0:
            return false;
        }
    }

    bool bv_eval::is_lookahead_phase() {
        ++m_lookahead_steps;
        if (m_lookahead_steps < m_lookahead_phase_size)
            return true;
        if (m_lookahead_steps > 10 * m_lookahead_phase_size)
            m_lookahead_steps = 0;
        return false;
    }
    
    bool bv_eval::repair_down(app* e, unsigned i) {  
        expr* arg = e->get_arg(i);
        if (m.is_value(arg))
            return false;
        if (e->get_family_id() == bv.get_family_id() && try_repair_bv(e, i)) {
            commit_eval(e, to_app(arg));
            IF_VERBOSE(11, verbose_stream() << "repair " << mk_bounded_pp(e, m) << " : " << mk_bounded_pp(arg, m) << " := " << wval(arg) << "\n";);
            ctx.new_value_eh(arg);
            return true;
        }
        if (m.is_eq(e) && bv.is_bv(arg) && try_repair_eq(e, i)) {
            commit_eval(e, to_app(arg));
            IF_VERBOSE(11, verbose_stream() << mk_bounded_pp(arg, m) << " := " << wval(arg) << "\n";);
            ctx.new_value_eh(arg);
            return true;
        }
        
        return false;
    }

    bool bv_eval::try_repair_bv(app* e, unsigned i) {
        switch (e->get_decl_kind()) {
        case OP_BAND:
            SASSERT(e->get_num_args() >= 2);
            if (e->get_num_args() == 2)
                return try_repair_band(assign_value(e), wval(e, i), wval(e, 1 - i));
            else
                return try_repair_band(e, i);
        case OP_BOR:
            SASSERT(e->get_num_args() >= 2);
            if (e->get_num_args() == 2)
                return try_repair_bor(assign_value(e), wval(e, i), wval(e, 1 - i));
            else
                return try_repair_bor(e, i);
        case OP_BXOR:
            SASSERT(e->get_num_args() >= 2);
            if (e->get_num_args() == 2)
                return try_repair_bxor(assign_value(e), wval(e, i), wval(e, 1 - i));
            else
                return try_repair_bxor(e, i);
        case OP_BADD:
            SASSERT(e->get_num_args() >= 2);
            if (e->get_num_args() == 2)
                return try_repair_add(assign_value(e), wval(e, i), wval(e, 1 - i));
            else
                return try_repair_add(e, i);
        case OP_BSUB:
            return try_repair_sub(assign_value(e), wval(e, 0), wval(e, 1), i);
        case OP_BMUL:
            SASSERT(e->get_num_args() >= 2);
            if (e->get_num_args() == 2)
                return try_repair_mul(assign_value(e), wval(e, i), assign_value(to_app(e->get_arg(1 - i))));
            else {
                auto const& a = wval(e, 0);
                auto f = [&](bvect& out, bvval const& c) {
                    a.set_mul(out, out, c.bits());
                };
                fold_oper(m_mul_tmp, e, i, f);
                m_mul_tmp.set_bw(a.bw);
                return try_repair_mul(assign_value(e), wval(e, i), m_mul_tmp);
            }
        case OP_BNOT:
            return try_repair_bnot(assign_value(e), wval(e, i));
        case OP_BNEG:
            return try_repair_bneg(assign_value(e), wval(e, i));
        case OP_BIT0:
            return false;
        case OP_BIT1:
            return false;
        case OP_UBV2INT:
        case OP_SBV2INT:
            return false;
        case OP_INT2BV:
            return try_repair_int2bv(assign_value(e), e->get_arg(0));          
        case OP_ULEQ:
            if (i == 0)
                return try_repair_ule(bval0(e), wval(e, i), wval(e, 1 - i));
            else
                return try_repair_uge(bval0(e), wval(e, i), wval(e, 1 - i));
        case OP_UGEQ:
            if (i == 0)
                return try_repair_uge(bval0(e), wval(e, i), wval(e, 1 - i));
            else
                return try_repair_ule(bval0(e), wval(e, i), wval(e, 1 - i));
        case OP_UGT:
            if (i == 0)
                return try_repair_ule(!bval0(e), wval(e, i), wval(e, 1 - i));
            else
                return try_repair_uge(!bval0(e), wval(e, i), wval(e, 1 - i));
        case OP_ULT:
            if (i == 0)
                return try_repair_uge(!bval0(e), wval(e, i), wval(e, 1 - i));
            else
                return try_repair_ule(!bval0(e), wval(e, i), wval(e, 1 - i));
        case OP_SLEQ:
            if (i == 0)
                return try_repair_sle(bval0(e), wval(e, i), wval(e, 1 - i));
            else
                return try_repair_sge(bval0(e), wval(e, i), wval(e, 1 - i));
        case OP_SGEQ:
            if (i == 0)
                return try_repair_sge(bval0(e), wval(e, i), wval(e, 1 - i));
            else
                return try_repair_sle(bval0(e), wval(e, i), wval(e, 1 - i));
        case OP_SGT:
            if (i == 0)
                return try_repair_sle(!bval0(e), wval(e, i), wval(e, 1 - i));
            else
                return try_repair_sge(!bval0(e), wval(e, i), wval(e, 1 - i));
        case OP_SLT:
            if (i == 0)
                return try_repair_sge(!bval0(e), wval(e, i), wval(e, 1 - i));
            else
                return try_repair_sle(!bval0(e), wval(e, i), wval(e, 1 - i));
        case OP_BASHR:
            return try_repair_ashr(assign_value(e), wval(e, 0), wval(e, 1), i);
        case OP_BLSHR:
            return try_repair_lshr(assign_value(e), wval(e, 0), wval(e, 1), i);
        case OP_BSHL:
            return try_repair_shl(assign_value(e), wval(e, 0), wval(e, 1), i);
        case OP_BIT2BOOL: {
            unsigned idx;
            expr* arg;
            VERIFY(bv.is_bit2bool(e, arg, idx));
            return try_repair_bit2bool(wval(e, 0), idx);
        }

        case OP_BUDIV:
        case OP_BUDIV_I:
        case OP_BUDIV0:
            return try_repair_udiv(assign_value(e), wval(e, 0), wval(e, 1), i);
        case OP_BUREM:
        case OP_BUREM_I:
        case OP_BUREM0:
            return try_repair_urem(assign_value(e), wval(e, 0), wval(e, 1), i);
        case OP_ROTATE_LEFT:
            return try_repair_rotate_left(assign_value(e), wval(e, 0), e->get_parameter(0).get_int());
        case OP_ROTATE_RIGHT:
            return try_repair_rotate_left(assign_value(e), wval(e, 0), wval(e).bw - e->get_parameter(0).get_int());
        case OP_EXT_ROTATE_LEFT:
            return try_repair_rotate_left(assign_value(e), wval(e, 0), wval(e, 1), i);
        case OP_EXT_ROTATE_RIGHT:
            return try_repair_rotate_right(assign_value(e), wval(e, 0), wval(e, 1), i);
        case OP_ZERO_EXT:
            return try_repair_zero_ext(assign_value(e), wval(e, 0));
        case OP_SIGN_EXT:
            return try_repair_sign_ext(assign_value(e), wval(e, 0));
        case OP_CONCAT: 
            return try_repair_concat(e, i);        
        case OP_EXTRACT: {
            unsigned hi, lo;
            expr* arg;
            VERIFY(bv.is_extract(e, lo, hi, arg));
            return try_repair_extract(assign_value(e), wval(arg), lo);
        }
        case OP_BUMUL_NO_OVFL:
            return try_repair_umul_ovfl(!bval0(e), wval(e, 0), wval(e, 1), i);
        case OP_BUMUL_OVFL:
            return try_repair_umul_ovfl(bval0(e), wval(e, 0), wval(e, 1), i);
        case OP_BCOMP:
            return try_repair_comp(assign_value(e), wval(e, 0), wval(e, 1), i);
        case OP_BUADD_OVFL:
         
        case OP_BNAND:
        case OP_BREDAND:
        case OP_BREDOR:
        case OP_BXNOR:
        case OP_BNEG_OVFL:
        case OP_BSADD_OVFL:
        case OP_BSDIV_OVFL:
        case OP_BSMUL_NO_OVFL:
        case OP_BSMUL_NO_UDFL:
        case OP_BSMUL_OVFL:
            verbose_stream() << mk_pp(e, m) << "\n";
            return false;
        case OP_BSDIV:
        case OP_BSDIV_I:
        case OP_BSDIV0:
            return try_repair_sdiv(assign_value(e), wval(e, 0), wval(e, 1), i);
        case OP_BSREM:
        case OP_BSREM_I:
        case OP_BSREM0:
        case OP_BSMOD:
        case OP_BSMOD_I:
        case OP_BSMOD0:

            UNREACHABLE();
            // these are currently compiled to udiv and urem.
            // there is an equation that enforces equality between the semantics
            // of these operators.
            return true;
        default:
            return false;
        }
    }

    bool bv_eval::try_repair_eq(app* e, unsigned i) {
        auto child = e->get_arg(i);        
        auto is_true = bval0(e);
        if (bv.is_bv(child)) {
            auto & a = wval(e->get_arg(i));
            auto & b = wval(e->get_arg(1 - i));
            return try_repair_eq(is_true, a, b);
        }
        return false;
    }

    bool bv_eval::try_repair_eq(bool is_true, bvval& a, bvval const& b) {
        if (is_true) {
            return (m_rand(20) != 0 && a.try_set(b.bits())) || a.set_random(m_rand);
        }
        else {
            bool try_above = m_rand(2) == 0;
            m_tmp.set_bw(a.bw);
            if (try_above) {
                a.set_add(m_tmp, b.bits(), m_one);
                if (a.set_random_at_least(m_tmp,  m_rand) && m_tmp != b.bits())
                    return true;
            }
            a.set_sub(m_tmp, b.bits(), m_one);
            if (a.set_random_at_most(m_tmp, m_rand) && m_tmp != b.bits())
                return true;
            if (!try_above) {
                a.set_add(m_tmp, b.bits(), m_one);
                if (a.set_random_at_least(m_tmp, m_rand) && m_tmp != b.bits())
                    return true;
            }
            return false;
        }
    }

    void bv_eval::fold_oper(bvect& out, app* t, unsigned i, std::function<void(bvect&, bvval const&)> const& f) {
        unsigned i2 = i == 0 ? 1 : 0;
        auto const& c = wval(t->get_arg(i2));
        for (unsigned j = 0; j < c.nw; ++j)
            out[j] = c.bits()[j];
        for (unsigned k = 1; k < t->get_num_args(); ++k) {
            if (k == i || k == i2)
                continue;
            bvval const& c = wval(t->get_arg(k));
            f(out, c);
        }
    }

    //
    // e = a & b
    // e[i] = 1 -> a[i] = 1
    // e[i] = 0 & b[i] = 1 -> a[i] = 0
    // e[i] = 0 & b[i] = 0 -> a[i] = random
    // a := e[i] | (~b[i] & a[i])

    bool bv_eval::try_repair_band(bvect const& e, bvval& a, bvval const& b) {
        for (unsigned i = 0; i < a.nw; ++i)
            m_tmp[i] = ~a.fixed(i) & (e[i] | (~b.bits()[i] & random_bits()));
        return a.set_repair(random_bool(), m_tmp);
    }

    bool bv_eval::try_repair_band(app* t, unsigned i) {
        bvect const& e = assign_value(t);
        auto f = [&](bvect& out, bvval const& c) {
            for (unsigned j = 0; j < c.nw; ++j)
                out[j] &= c.bits()[j];
        };
        fold_oper(m_tmp2, t, i, f);

        bvval& a = wval(t, i);
        for (unsigned j = 0; j < a.nw; ++j) 
            m_tmp[j] = ~a.fixed(j) & (e[j] | (~m_tmp2[j] & random_bits()));

        return a.set_repair(random_bool(), m_tmp);
    }

    //
    // e = a | b
    // set a[i] to 1 where b[i] = 0, e[i] = 1
    // set a[i] to 0 where e[i] = 0, a[i] = 1
    //     
    bool bv_eval::try_repair_bor(bvect const& e, bvval& a, bvval const& b) {
        for (unsigned i = 0; i < a.nw; ++i)
            m_tmp[i] = e[i] & (~b.bits()[i] | random_bits());
        return a.set_repair(random_bool(), m_tmp);
    }

    bool bv_eval::try_repair_bor(app* t, unsigned i) {
        bvect const& e = assign_value(t);
        auto f = [&](bvect& out, bvval const& c) {
            for (unsigned j = 0; j < c.nw; ++j)
                out[j] |= c.bits()[j];
        };
        fold_oper(m_tmp2, t, i, f);
        bvval& a = wval(t, i);
        m_tmp.set_bw(a.bw);
        for (unsigned j = 0; j < a.nw; ++j)
            m_tmp[j] = e[j] & (~m_tmp2[j] | random_bits());

        //verbose_stream() << wval(t) << " " << m_tmp << "\n";
        return a.set_repair(random_bool(), m_tmp);
    }

    bool bv_eval::try_repair_bxor(bvect const& e, bvval& a, bvval const& b) {
        for (unsigned i = 0; i < a.nw; ++i)
            m_tmp[i] = e[i] ^ b.bits()[i];
        return a.set_repair(random_bool(), m_tmp);
    }



    bool bv_eval::try_repair_bxor(app* t, unsigned i) {
        bvect const& e = assign_value(t);
        auto f = [&](bvect& out, bvval const& c) {
            for (unsigned j = 0; j < c.nw; ++j)
                out[j] ^= c.bits()[j];
        };
        fold_oper(m_tmp2, t, i, f);

        bvval& a = wval(t, i);
        for (unsigned j = 0; j < a.nw; ++j)
            m_tmp[j] = e[j] ^ m_tmp2[j];

        return a.set_repair(random_bool(), m_tmp);
    }


    //
    // first try to set a := e - b
    // If this fails, set a to a random value
    // 
    bool bv_eval::try_repair_add(bvect const& e, bvval& a, bvval const& b) {
        if (m_rand(20) != 0) {
            m_tmp.set_bw(a.bw);
            a.set_sub(m_tmp, e, b.bits());
            // verbose_stream() << "set-sub " << e << " - " << b.bits() << " = " << m_tmp << "\n";
            if (a.try_set(m_tmp))
                return true;
        }
        return a.set_random(m_rand);        
    }

    bool bv_eval::try_repair_add(app* t, unsigned i) {
        bvval& a = wval(t, i);
        bvect const& e = assign_value(t);
        if (m_rand(20) != 0) {
            auto f = [&](bvect& out, bvval const& c) {
                a.set_add(m_tmp2, m_tmp2, c.bits());
            };
            fold_oper(m_tmp2, t, i, f);
            a.set_sub(m_tmp, e, m_tmp2);
            if (a.try_set(m_tmp))
                return true;
        }
        return a.set_random(m_rand);     
    }

    bool bv_eval::try_repair_sub(bvect const& e, bvval& a, bvval & b, unsigned i) {
        if (m_rand(20) != 0) {
            if (i == 0) 
                // e = a - b -> a := e + b
                a.set_add(m_tmp, e, b.bits());        
            else 
                // b := a - e
                b.set_sub(m_tmp, a.bits(), e);       
            if (a.try_set(m_tmp))
                return true;
        }
        // fall back to a random value
        return i == 0 ? a.set_random(m_rand) : b.set_random(m_rand);        
    }

    /**
    * e = a*b, then a = e * b^-1
    * 8*e = a*(2b), then a = 4e*b^-1
    */
    bool bv_eval::try_repair_mul(bvect const& e, bvval& a, bvect const& b) {
        // verbose_stream() << e << " := " << a << " * " << b << "\n";
        unsigned parity_e = a.parity(e);
        unsigned parity_b = a.parity(b);

        if (a.is_zero(b)) {
            if (a.try_set(e))
                return true;
            a.get_variant(m_tmp, m_rand);
            if (m_rand(10) != 0)
                for (unsigned i = 0; i < b.bw - parity_b; ++i)
                    m_tmp.set(i, false);
            return a.set_repair(random_bool(), m_tmp);
        }

        if (m_rand(20) == 0) {
            a.get_variant(m_tmp, m_rand);
            return a.set_repair(random_bool(), m_tmp);            
        }      



#if 0
        verbose_stream() << "solve for " << e << "\n";

        rational r = e.get_value(e.nw);
        rational root;
        verbose_stream() << r.is_int_perfect_square(root) << "\n";
#endif
                
        
        auto& x = m_tmp;
        auto& y = m_tmp2;
        auto& quot = m_tmp3;
        auto& rem = m_tmp4;
        auto& ta = m_a;
        auto& tb = m_b;
        auto& nexta = m_nexta;
        auto& nextb = m_nextb;
        auto& aux = m_aux;
        auto bw = b.bw;
       

        // x*ta + y*tb = x

        y.set_bw(a.bw);
        b.copy_to(a.nw, y);
        //verbose_stream() << "a.nw " << a.nw << " b.nw " << b.nw << " b " << b << " y.nw " << y.nw << " y "   << y << "\n";
        if (parity_b > 0) {
            a.shift_right(y, parity_b);
            
#if 0
            for (unsigned i = parity_b; i < b.bw; ++i)
                y.set(i, m_rand(2) == 0);
#endif
        }
        //verbose_stream() << parity_b << " y " << y << "\n";

        y[a.nw] = 0;
        x[a.nw] = 0;

        
        a.set_bw((a.nw + 1)* 8 * sizeof(digit_t));
        y.set_bw(a.bw); // enable comparisons        
        a.set_zero(x);
        x.set(bw, true); // x = 2 ^ b.bw       

        a.set_one(ta);
        a.set_zero(tb);
        a.set_zero(nexta);
        a.set_one(nextb);

        rem.reserve(2 * a.nw);
        SASSERT(y <= x);
        while (y > m_zero) {
            SASSERT(y <= x);            
            set_div(x, y, a.bw, quot, rem); // quot, rem := quot_rem(x, y)
            SASSERT(y >= rem);
            a.set(x, y);                    // x := y
            a.set(y, rem);                  // y := rem
            a.set(aux, nexta);              // aux := nexta
            a.set_mul(rem, quot, nexta, false);  
            a.set_sub(nexta, ta, rem);      // nexta := ta - quot*nexta
            a.set(ta, aux);                 // ta := aux
            a.set(aux, nextb);              // aux := nextb
            a.set_mul(rem, quot, nextb, false);
            a.set_sub(nextb, tb, rem);      // nextb := tb - quot*nextb
            a.set(tb, aux);                 // tb := aux
        }

        a.set_bw(bw);
        y.set_bw(0);
        // x*a + y*b = 1
    
        tb.set_bw(0);
#if Z3DEBUG
        b.copy_to(a.nw, y);
        if (parity_b > 0)
            a.shift_right(y, parity_b);
        a.set_mul(m_tmp, tb, y, false);
        SASSERT(a.is_one(m_tmp));
#endif
        e.copy_to(b.nw, m_tmp2);
        if (parity_e > 0 && parity_b > 0)
            a.shift_right(m_tmp2, std::min(parity_b, parity_e));
        a.set_mul(m_tmp, tb, m_tmp2);
        if (a.set_repair(random_bool(), m_tmp))
            return true;
        
        return a.set_random(m_rand);
    }


    bool bv_eval::try_repair_sdiv(bvect const& e, bvval& a, bvval& b, unsigned i) {

        bool sign_a = a.sign();

        // y = 0, x >= 0 -> -1
        if (i == 0 && b.is_zero() && a.is_ones(e) && a.try_set(m_zero))
            return true;
        if (i == 0 && b.is_zero() && a.is_ones(e) && a.try_set_bit(a.bw - 1, false))
            return true;

        if (i == 1 && !sign_a && a.is_ones(e) && b.try_set(m_zero))
            return true;
            
        // y = 0, x < 0 -> 1
        if (i == 0 && b.is_zero() && a.is_one(e) && a.try_set(m_minus_one))
            return true;

        if (i == 1 && sign_a && a.is_one(e) && b.try_set(m_zero))
            return true;

        // x = 0, y != 0 -> 0
        if (i == 0 && a.is_zero(e) && !b.is_zero() && a.try_set(m_zero))
            return true;
        if (i == 1 && a.is_zero(e) && a.is_zero() && b.try_set_bit(ctx.rand(a.bw), true))
            return true;

        // e = x udiv y
        // e = 0 => x != ones
        // y = 0 => e = -1        // nothing to repair on a
        // e != -1 => max(y) >=u e

        //IF_VERBOSE(0, verbose_stream() << "sdiv " << e << " " << a << " " << b << "\n";);

        // e = udiv(abs(x), abs(y))
        // x > 0, y < 0 -> -e
        // x < 0, y > 0 -> -e
        // x > 0, y > 0 -> e
        // x < 0, y < 0 -> e

        return try_repair_udiv(e, a, b, i);
    }

    bool bv_eval::try_repair_bnot(bvect const& e, bvval& a) {
        for (unsigned i = 0; i < a.nw; ++i)
            m_tmp[i] = ~e[i];        
        a.clear_overflow_bits(m_tmp);
        return a.try_set(m_tmp);
    }

    bool bv_eval::try_repair_bneg(bvect const& e, bvval& a) {
        a.set_sub(m_tmp, m_zero, e); 
        return a.try_set(m_tmp);
    }


    // a <=s b <-> a + p2 <=u b + p2
    // 
    // NB: p2 = -p2
    // 
    // to solve x for x >s b:
    // infeasible if b + 1 = p2
    // solve for x >=s b + 1
    // 
    bool bv_eval::try_repair_sle(bool e, bvval& a, bvval const& b) {
        auto& p2 = m_b;
        b.set_zero(p2);
        p2.set(b.bw - 1, true);
        p2.set_bw(b.bw);
        bool r = false;
        if (e) 
            r = try_repair_sle(a, b.bits(), p2);        
        else {
            auto& b1 = m_nexta;
            a.set_add(b1, b.bits(), m_one);
            b1.set_bw(b.bw);
            if (p2 == b1)
                r = false;
            else
                r = try_repair_sge(a, b1, p2);
            b1.set_bw(0);
        }
        p2.set_bw(0);
        return r;
    }

    // to solve x for x <s b:
    // infeasible if b = 0
    // solve for x <=s b - 1
    // 
    bool bv_eval::try_repair_sge(bool e, bvval& a, bvval const& b) {
        auto& p2 = m_b;
        b.set_zero(p2);
        p2.set(b.bw - 1, true);
        p2.set_bw(b.bw);
        bool r = false;
        if (e)
            r = try_repair_sge(a, b.bits(), p2);
        else if (b.bits() == p2)
            r = false;
        else {
            auto& b1 = m_nexta;
            a.set_sub(b1, b.bits(), m_one);
            b1.set_bw(b.bw);
            r = try_repair_sle(a, b1, p2);
            b1.set_bw(0);
        }
        p2.set_bw(0);
        return r;
    }


    // to solve x for x <=s b:
    // let c := b + p2
    // solve for
    //    x + p2 <= c
    // 
    // x := random x <= b or x >= p2  if c >= p2 (b < p2)
    // or
    // x := random p2 <= x <= b       if c < p2  (b >= p2)
    // 
    bool bv_eval::try_repair_sle(bvval& a, bvect const& b, bvect const& p2) {
        bool r = false;
        if (b < p2) {
            bool coin = m_rand(2) == 0;
            if (coin)
                r = a.set_random_at_least(p2, m_rand);
            if (!r)
                r = a.set_random_at_most(b, m_rand);
            if (!coin && !r)
                r = a.set_random_at_least(p2, m_rand);
        }
        else 
            r = a.set_random_in_range(p2, b, m_rand);
        return r;
    }

    // solve for x >=s b
    // 
    // d := b + p2
    // 
    // x := random b <= x < p2        if d >= p2 (b < p2)
    // or
    // x := random b <= x or x < p2   if d < p2
    //  

    bool bv_eval::try_repair_sge(bvval& a, bvect const& b, bvect const& p2) {
        auto& p2_1 = m_tmp4;
        a.set_sub(p2_1, p2, m_one);
        p2_1.set_bw(a.bw);
        bool r = false;
        if (b < p2) 
            // random b <= x < p2 
            r = a.set_random_in_range(b, p2_1, m_rand);        
        else {
            // random b <= x or x < p2
            bool coin = m_rand(2) == 0;
            if (coin)
                r = a.set_random_at_most(p2_1, m_rand);
            if (!r)
                r = a.set_random_at_least(b, m_rand);
            if (!r && !coin)
                r = a.set_random_at_most(p2_1, m_rand);
        }
        p2_1.set_bw(0);
        return r;
    }

    void bv_eval::add_p2_1(bvval const& a, bvect& t) const {
        m_zero.set(a.bw - 1, true);
        a.set_add(t, a.bits(), m_zero);
        m_zero.set(a.bw - 1, false);
        a.clear_overflow_bits(t);
    }

    bool bv_eval::try_repair_ule(bool e, bvval& a, bvval const& b) {
        //verbose_stream() << "try-repair-ule " << e << " " << a << " " << b << "\n";
        if (e) {
            // a <= t
            return a.set_random_at_most(b.bits(),  m_rand);
        }
        else {
            // a > t
            m_tmp.set_bw(a.bw);
            a.set_add(m_tmp, b.bits(), m_one);
            if (a.is_zero(m_tmp))
                return false;   
            return a.set_random_at_least(m_tmp, m_rand);
        }           
    }

    bool bv_eval::try_repair_uge(bool e, bvval& a, bvval const& b) {
        if (e) {
            // a >= t
            return a.set_random_at_least(b.bits(), m_rand);
        }
        else {
            // a < t
            m_tmp.set_bw(a.bw);
            if (b.is_zero())
                return false;
            a.set_sub(m_tmp, b.bits(), m_one);
            return a.set_random_at_most(m_tmp, m_rand);
        }    
    }

    bool bv_eval::try_repair_bit2bool(bvval& a, unsigned idx) {       
        return a.try_set_bit(idx, !a.get_bit(idx));
    }

    bool bv_eval::try_repair_shl(bvect const& e, bvval& a, bvval& b, unsigned i) {
        if (i == 0) {
            unsigned sh = b.to_nat(b.bw);
            if (sh == 0) 
                return a.try_set(e);            
            else if (sh >= b.bw) 
                return false;            
            else {
                //
                // e = a << sh
                // set bw - sh low order bits to bw - sh high-order of e.
                // a[bw - sh - 1: 0] = e[bw - 1: sh]
                // a[bw - 1: bw - sh] = unchanged
                //
                for (unsigned i = 0; i < a.bw - sh; ++i)
                    m_tmp.set(i, e.get(sh + i));
                for (unsigned i = a.bw - sh; i < a.bw; ++i)
                    m_tmp.set(i, a.get_bit(i));
                a.clear_overflow_bits(m_tmp);
                return a.try_set(m_tmp);
            }
        }
        else {
            SASSERT(i == 1);
            if (a.is_zero())
                return b.set_random(m_rand);

            unsigned start = m_rand();
            for (unsigned j = 0; j <= a.bw; ++j) {
                unsigned sh = (j + start) % (a.bw + 1);
                m_tmp.set_bw(a.bw);
                m_tmp2.set_bw(a.bw);
                b.set(m_tmp, sh);
                if (!b.can_set(m_tmp))
                    continue;
                m_tmp2.set_shift_left(a.bits(), m_tmp);
                if (m_tmp2 == e && b.try_set(m_tmp)) 
                    return true;                
            }
            
            if (m_rand(2) == 0)
                return false;

            return b.set_random(m_rand);
        }
        return false;
    }

    bool bv_eval::try_repair_ashr(bvect const& e, bvval & a, bvval& b, unsigned i) {
        if (i == 0)
            return try_repair_ashr0(e, a, b);
        else
            return try_repair_ashr1(e, a, b);
    }

    bool bv_eval::try_repair_lshr(bvect const& e, bvval& a, bvval& b, unsigned i) {
        if (i == 0)
            return try_repair_lshr0(e, a, b);
        else
            return try_repair_lshr1(e, a, b);
    }

    /**
    * strong: 
    * - e = (e << b) >> b -> a := e << b, upper b bits set random
    * weak:
    *   - e = 0 -> a := random 
    *   - e > 0 -> a := random with msb(a) >= msb(e)
    */
    bool bv_eval::try_repair_lshr0(bvect const& e, bvval& a, bvval const& b) {
        
        auto& t = m_tmp;
        // t := e << b
        // t := t >> b
        t.set_shift_left(e, b.bits());
        t.set_shift_right(t, b.bits());
        bool use_strong = m_rand(10) != 0;
        if (t == e && use_strong) {
            t.set_shift_left(e, b.bits());
            unsigned n = b.bits().to_nat(e.bw);
            for (unsigned i = e.bw; i-- > e.bw - n;) 
                t.set(i, a.get_bit(i)); 
            if (a.set_repair(random_bool(), t))
                return true;                      
        }


        unsigned sh = b.to_nat(b.bw);
        if (m_rand(20) != 0) {
            if (sh == 0 && a.try_set(e))
                return true;
            else if (sh >= b.bw)
                return true;
            else if (sh < b.bw && m_rand(20) != 0) {
                // e = a >> sh
                // a[bw-1:sh] = e[bw-sh-1:0]
                // a[sh-1:0] = a[sh-1:0]                
                for (unsigned i = sh; i < a.bw; ++i)
                    t.set(i, e.get(i - sh));
                for (unsigned i = 0; i < sh; ++i)
                    t.set(i, a.get_bit(i));
                a.clear_overflow_bits(t);
                if (a.try_set(t))
                    return true;
            }
        }
        
        //bool r = try_repair_ashr(e, a, const_cast<bvval&>(b), 0);
        //verbose_stream() << "repair lshr0 " << e << " b: " << b << " a: " << a << "\n";
        //return r;

        a.get_variant(t, m_rand);
        
        unsigned msb = a.msb(e);
        if (msb > a.msb(t)) {
            unsigned num_flex = 0;
            for (unsigned i = e.bw; i-- >= msb;) 
                if (!a.fixed().get(i))
                    ++num_flex;
            if (num_flex == 0)
                return false;
            unsigned n = m_rand(num_flex);
            for (unsigned i = e.bw; i-- >= msb;) {
                if (!a.fixed().get(i)) {
                    if (n == 0) {
                        t.set(i, true);
                        break;
                    }
                    else
                        n--;
                }
            }
        }
        return a.set_repair(random_bool(), t);
    }

    /**
    * strong:
    * - clz(a) <= clz(e), e = 0 or (a >> (clz(e) - clz(a)) = e
    * - e = 0 and a = 0:  b := random
    * - e = 0 and a != 0: b := random, such that shift <= b 
    * - e != 0:           b := shift
    * where shift := clz(e) - clz(a)
    * 
    * weak:
    * - e = 0:  b := random
    * - e > 0:  b := random >= clz(e)
    */
    bool bv_eval::try_repair_lshr1(bvect const& e, bvval const& a, bvval& b) {

        auto& t = m_tmp;
        auto clza = a.clz(a.bits());
        auto clze = a.clz(e);
        t.set_bw(a.bw);

        // strong
        if (m_rand(10) != 0 && clza <= clze && (a.is_zero(e) || t.set_shift_right(a.bits(), clze - clza) == e)) {
            if (a.is_zero(e) && a.is_zero()) 
                return true;            
            unsigned shift = clze - clza;
            if (a.is_zero(e)) 
                shift = m_rand(a.bw + 1 - shift) + shift;            
            
            b.set(t, shift);
            if (b.try_set(t))
                return true;            
        }

        // no change
        if (m_rand(10) != 0) {
            if (a.is_zero(e))
                return true;
            if (b.bits() <= clze)
                return true;
        }

        // weak
        b.get_variant(t, m_rand);
        if (a.is_zero(e))             
            return b.set_repair(random_bool(), t);        
        else {
            for (unsigned i = 0; i < 4; ++i) {
                for (unsigned i = a.bw; !(t <= clze) && i-- > 0; )
                    if (!b.fixed().get(i))
                        t.set(i, false);
                if (t <= clze && b.set_repair(random_bool(), t))
                    return true;                
                b.get_variant(t, m_rand);
            }
            return false;
        }        
    }

    /**
    * strong:
    *   b  < |b| => (e << b) >>a b = e) 
    *   b >= |b| => (e = ones || e = 0)
    * - if b  < |b|: a := e << b
    * - if b >= |b|: a[bw-1] := e = ones
    * weak:
    *   
    */
    bool bv_eval::try_repair_ashr0(bvect const& e, bvval& a, bvval const& b) {
        auto& t = m_tmp;
        t.set_bw(b.bw);
        auto n = b.msb(b.bits());
        bool use_strong = m_rand(20) != 0;
        if (use_strong && n < b.bw) {
            t.set_shift_left(e, b.bits());
            bool sign = t.get(b.bw-1);
            t.set_shift_right(t, b.bits());
            if (sign) {
                for (unsigned i = b.bw; i-- > b.bw - n; )
                    t.set(i, true);
            }            
            use_strong &= t == e;
        }
        else {
            use_strong &= a.is_zero(e) || a.is_ones(e);
        }
        if (use_strong) {
            if (n < b.bw) {
                t.set_shift_left(e, b.bits());
                for (unsigned i = 0; i < n; ++i)
                    t.set(i, a.get_bit(i));
            }
            else {                
                for (unsigned i = 0; i < b.nw; ++i)
                    t[i] = a.bits()[i];
                t.set(b.bw - 1, a.is_ones(e));
            }   
            if (a.set_repair(random_bool(), t))
                return true;
        }
        if (m_rand(10) != 0) {
            if (n < b.bw) {
                t.set_shift_left(e, b.bits());
                for (unsigned i = 0; i < n; ++i)
                    t.set(i, random_bool());
            }
            else {
                a.get_variant(t, m_rand);
                t.set(b.bw - 1, a.is_ones(e));
            }
            if (a.set_repair(random_bool(), t))
                return true;
        }            
        return a.set_random(m_rand);
    }

    /*
    * strong:
    * - clz(a) <= clz(e), e = 0 or (a >>a (clz(e) - clz(a)) = e
    * - e = 0 and a = 0:  b := random
    * - e = 0 and a != 0: b := random, such that shift <= b 
    * - e != 0:           b := shift
    * where shift := clz(e) - clz(a)
    * 
    * weak:
    * - e = 0:  b := random
    * - e > 0:  b := random >= clz(e)
    */

    bool bv_eval::try_repair_ashr1(bvect const& e, bvval const& a, bvval& b) {

        auto& t = m_tmp;
        auto clza = a.clz(a.bits());
        auto clze = a.clz(e);
        t.set_bw(a.bw);

        // strong unsigned
        if (!a.get_bit(a.bw - 1) && m_rand(10) != 0 && clza <= clze && (a.is_zero(e) || t.set_shift_right(a.bits(), clze - clza) == e)) {
            if (a.is_zero(e) && a.is_zero())
                return true;
            unsigned shift = clze - clza;
            if (a.is_zero(e))
                shift = m_rand(a.bw + 1 - shift) + shift;

            b.set(t, shift);
            if (b.try_set(t))
                return true;
        }
        // strong signed
        if (a.get_bit(a.bw - 1) && m_rand(10) != 0 && clza >= clze) {
            t.set_shift_right(a.bits(), clza - clze);
            for (unsigned i = a.bw; i-- > a.bw - clza + clze; )
                t.set(i, true);
            if (e == t) {
                if (a.is_zero(e) && a.is_zero())
                    return true;
                unsigned shift = clze - clza;
                if (a.is_zero(e))
                    shift = m_rand(a.bw + 1 - shift) + shift;

                b.set(t, shift);
                if (b.try_set(t))
                    return true;
            }
        }

        // weak
        b.get_variant(t, m_rand);
        return b.set_repair(random_bool(), t);
    }

    bool bv_eval::try_repair_comp(bvect const& e, bvval& a, bvval& b, unsigned i) {
        SASSERT(e[0] == 0 || e[0] == 1);
        SASSERT(e.bw == 1);
        return try_repair_eq(e[0] == 1, i == 0 ? a : b, i == 0 ? b : a);
    }

    // e = a udiv b
    // e = 0 => a != ones
    // b = 0 => e = -1        // nothing to repair on a
    // e != -1 => max(a) >=u e

    bool bv_eval::try_repair_udiv(bvect const& e, bvval& a, bvval& b, unsigned i) {
        if (i == 0) {
            if (a.is_zero(e) && a.is_ones(a.fixed()) && a.is_ones())
                return false;            
            if (b.is_zero()) 
                return false;            
            if (!a.is_ones(e)) {
                for (unsigned i = 0; i < a.nw; ++i)
                    m_tmp[i] = ~a.fixed()[i] | a.bits()[i];
                a.clear_overflow_bits(m_tmp);
                if (e > m_tmp)
                    return false;
            }
            // e = 1 => a := b
            if (a.is_one(e)) {
                a.set(m_tmp, b.bits());
                return a.set_repair(false, m_tmp);
            }
            // b * e + r = a
            if (mul_overflow_on_fixed(b, e)) {
                a.get_variant(m_tmp, m_rand);
                return a.set_repair(random_bool(), m_tmp);
            }

            b.get_variant(m_tmp2, m_rand);
            while (b.bits() < m_tmp2)
                m_tmp2.set(b.msb(m_tmp2), false);
            while (a.set_add(m_tmp3, m_tmp, m_tmp2)) 
                m_tmp2.set(b.msb(m_tmp2), false);       
            return a.set_repair(true, m_tmp3);
        }
        else {
            if (a.is_one(e) && a.is_zero()) 
                return b.set_random(m_rand);              
            
            if (a.is_one(e)) {
                a.set(m_tmp, a.bits());
                return b.set_repair(true, m_tmp);
            }            

            // e * b + r = a
            // b = (a - r) udiv e 
            // random version of r:
            for (unsigned i = 0; i < a.nw; ++i)
                m_tmp[i] = random_bits();
            a.clear_overflow_bits(m_tmp);
            // ensure r <= m
            while (a.bits() < m_tmp)
                m_tmp.set(a.msb(m_tmp), false);
            a.set_sub(m_tmp2, a.bits(), m_tmp);
            set_div(m_tmp2, e, a.bw, m_tmp3, m_tmp4);
            return b.set_repair(random_bool(), m_tmp4);
        }
    }

    // table III in Niemetz et al
    // x urem s = t <=>
    //     ~(-s) >=u t 
    //     ((s = 0 or t = ones) => mcb(x, t))
    //     ((s != 0 and t != ones) => exists y . (mcb(x, s*y + t) and ~mulo(s, y) and ~addo(s*y, t))
    // s urem x = t <=> 
    //      (s = t => x can be >u t)
    //      (s != t => exists y . (mcb(x, y) and y >u t and (s - t) mod y = 0)


    bool bv_eval::try_repair_urem(bvect const& e, bvval& a, bvval& b, unsigned i) {

        if (i == 0) {
            if (b.is_zero()) {
                a.set(m_tmp, e);
                return a.set_repair(random_bool(), m_tmp);
            }
            // a urem b = e: b*y + e = a
            // ~Ovfl*(b, y)
            // ~Ovfl+(b*y, e) 
            // choose y at random
            // lower y as long as y*b overflows with fixed bits in b

            for (unsigned i = 0; i < a.nw; ++i)
                m_tmp[i] = random_bits();
            a.clear_overflow_bits(m_tmp);
            while (mul_overflow_on_fixed(b, m_tmp)) {
                auto i = b.msb(m_tmp);
                m_tmp.set(i, false);
            }
            while (true) {
                a.set_mul(m_tmp2, m_tmp, b.bits());
                if (!a.set_add(m_tmp3, m_tmp2, e))
                    break;
                auto i = b.msb(m_tmp);
                m_tmp.set(i, false);
            }
            return a.set_repair(random_bool(), m_tmp3);
        }
        else {
            // a urem b = e: b*y + e = a
            // b*y = a - e
            // b = (a - e) div y
            // ~Ovfl*(b, y)
            // ~Ovfl+(b*y, e)
            // choose y at random
            // lower y as long as y*b overflows with fixed bits in b
            for (unsigned i = 0; i < a.nw; ++i)
                m_tmp[i] = random_bits();
            a.set_sub(m_tmp2, a.bits(), e);
            set_div(m_tmp2, m_tmp, a.bw, m_tmp3, m_tmp4);
            return b.set_repair(random_bool(), m_tmp3);
        }
    }

    bool bv_eval::add_overflow_on_fixed(bvval const& a, bvect const& t) {
        a.set(m_tmp3, m_zero);
        for (unsigned i = 0; i < a.nw; ++i)
            m_tmp3[i] = a.fixed(i) & a.bits(i);
        return a.set_add(m_tmp4, t, m_tmp3);
    }

    bool bv_eval::mul_overflow_on_fixed(bvval const& a, bvect const& t) {
        a.set(m_tmp3, m_zero);
        for (unsigned i = 0; i < a.nw; ++i)
            m_tmp3[i] = a.fixed(i) & a.bits(i);
        return a.set_mul(m_tmp4, m_tmp3, t);
    }

    bool bv_eval::try_repair_rotate_left(bvect const& e, bvval& a, unsigned n) const {
        // a := rotate_right(e, n)
        n = (a.bw - n) % a.bw;
        for (unsigned i = a.bw - n; i < a.bw; ++i)
            m_tmp.set(i + n - a.bw, e.get(i));
        for (unsigned i = 0; i < a.bw - n; ++i)
            m_tmp.set(i + n, e.get(i));
        return a.set_repair(true, m_tmp);       
    }

    bool bv_eval::try_repair_rotate_left(bvect const& e, bvval& a, bvval& b, unsigned i) {
        if (i == 0) {
            rational n = b.get_value();
            n = mod(n, rational(b.bw));
            return try_repair_rotate_left(e, a, n.get_unsigned());
        }
        else {
            SASSERT(i == 1);
            unsigned sh = m_rand(b.bw);
            b.set(m_tmp, sh);
            return b.set_repair(random_bool(), m_tmp);
        }       
    }

    bool bv_eval::try_repair_rotate_right(bvect const& e, bvval& a, bvval& b, unsigned i) {
        if (i == 0) {
            rational n = b.get_value();
            n = mod(b.bw - n, rational(b.bw));
            return try_repair_rotate_left(e, a, n.get_unsigned());
        }
        else {
            SASSERT(i == 1);
            unsigned sh = m_rand(b.bw);
            b.set(m_tmp, sh);
            return b.set_repair(random_bool(), m_tmp);
        }
    }

    bool bv_eval::try_repair_umul_ovfl(bool e, bvval& a, bvval& b, unsigned i) {
        if (e) {
            // maximize
            if (i == 0) {
                a.max_feasible(m_tmp);
                return a.set_repair(false, m_tmp);
            }
            else {
                b.max_feasible(m_tmp);
                return b.set_repair(false, m_tmp);
            }
        }
        else {
            // minimize
            if (i == 0) {
                a.min_feasible(m_tmp);
                return a.set_repair(true, m_tmp);
            }
            else {
                b.min_feasible(m_tmp);
                return b.set_repair(true, m_tmp);
            }
        }
    }

    //
    // prefix of e must be 1s or 0 and match bit position of last bit in a.
    // set a to suffix of e, matching signs.
    //  
    bool bv_eval::try_repair_sign_ext(bvect const& e, bvval& a) {
        for (unsigned i = a.bw; i < e.bw; ++i)
            if (e.get(i) != e.get(a.bw - 1))
                return false;

        for (unsigned i = 0; i < e.nw; ++i)
            m_tmp[i] = e[i];
        a.clear_overflow_bits(m_tmp);
        return a.try_set(m_tmp);
    }

    // 
    // prefix of e must be 0s.
    // 
    bool bv_eval::try_repair_zero_ext(bvect const& e, bvval& a) {
        for (unsigned i = a.bw; i < e.bw; ++i)
            if (e.get(i))
                return false;

        for (unsigned i = 0; i < e.nw; ++i)
            m_tmp[i] = e[i];
        a.clear_overflow_bits(m_tmp);
        return a.try_set(m_tmp);
    }

    bool bv_eval::try_repair_concat(app* e, unsigned idx) {
        unsigned bw = 0;
        auto& ve = assign_value(e);
        for (unsigned j = e->get_num_args() - 1; j > idx; --j)
            bw += bv.get_bv_size(e->get_arg(j));
        auto& a = wval(e, idx);
        for (unsigned i = 0; i < a.bw; ++i)
            m_tmp.set(i, ve.get(i + bw));
        a.clear_overflow_bits(m_tmp);
        bool r = a.try_set(m_tmp);
        if (!r) {
            a.add1(m_tmp);
            r = a.try_set(m_tmp);
        }
        if (!r) {
            r = a.set_repair(random_bool(), m_tmp);
        }
        if (!r) {
            verbose_stream() << "repair concat " << mk_bounded_pp(e, m) << "\n";
            verbose_stream() << idx << " " << a << "\n" << m_tmp << "\n";

        }
        return r;
    }

    //
    // e = a[hi:lo], where hi = e.bw + lo - 1
    // for the randomized assignment, 
    // set a outside of [hi:lo] to random values with preference to 0 or 1 bits
    // 
    bool bv_eval::try_repair_extract(bvect const& e, bvval& a, unsigned lo) {
        // IF_VERBOSE(4, verbose_stream() << "repair extract a[" << lo << ":" << lo + e.bw - 1 << "] = " << e << "\n");
        if (false && m_rand(m_config.m_prob_randomize_extract)  <= 100) {
            a.get_variant(m_tmp, m_rand);
            if (0 == (m_rand(2))) {
                auto bit = 0 == (m_rand(2));
                if (!a.try_set_range(m_tmp, 0, lo, bit))
                    a.try_set_range(m_tmp, 0, lo, !bit);
            }
            if (0 == (m_rand(2))) {
                auto bit = 0 == (m_rand(2));
                if (!a.try_set_range(m_tmp, lo + e.bw, a.bw, bit))
                    a.try_set_range(m_tmp, lo + e.bw, a.bw, !bit);
            }
        }
        else
            a.get(m_tmp);
        for (unsigned i = 0; i < e.bw; ++i)
            m_tmp.set(i + lo, e.get(i));
        m_tmp.set_bw(a.bw);
        //verbose_stream() << a << " := " << m_tmp << "\n";
        if (a.try_set(m_tmp))
            return true;
        bool ok = a.set_random(m_rand);
        //verbose_stream() << "set random " << ok << " " << a << "\n";
        return ok;
    }

    bool bv_eval::try_repair_int2bv(bvect const& e, expr* arg) {
        rational r = e.get_value(e.nw);
        arith_util a(m);
        expr_ref intval(a.mk_int(r), m);
        ctx.set_value(arg, intval);
        return true;
    }

    void bv_eval::set_div(bvect const& a, bvect const& b, unsigned bw,
        bvect& quot, bvect& rem) const {
        unsigned nw = (bw + 8 * sizeof(digit_t) - 1) / (8 * sizeof(digit_t));
        unsigned bnw = nw;
        while (bnw > 1 && b[bnw - 1] == 0)
            --bnw;
        if (b[bnw-1] == 0) {
            for (unsigned i = 0; i < nw; ++i) {
                quot[i] = ~0;
                rem[i] = 0;
            }
            quot[nw - 1] = (1 << (bw % (8 * sizeof(digit_t)))) - 1;            
        }
        else {            
            for (unsigned i = 0; i < nw; ++i) 
                rem[i] = quot[i] = 0;
            mpn.div(a.data(), nw, b.data(), bnw, quot.data(), rem.data());
        }
    }

    bool bv_eval::repair_up(expr* e) {
        if (!can_eval1(e))
            return false;

        if (m.is_bool(e)) {
            bool b = bval1(e);
            auto v = ctx.atom2bool_var(e);
            if (v == sat::null_bool_var)
                ctx.set_value(e, b ? m.mk_true() : m.mk_false());
            else if (ctx.is_true(v) != b)
                ctx.flip(v);
            return true;
        }

        if (!bv.is_bv(e))
            return false;

        auto& v = eval(to_app(e));
        if (v.eval == v.bits())
            return true;

        v.commit_eval_ignore_tabu();
        ctx.new_value_eh(e);
        return true;
    }

    sls::bv_valuation& bv_eval::wval(expr* e) const { 
        // if (!m_values[e->get_id()]) verbose_stream() << mk_bounded_pp(e, m) << "\n";  
        return *m_values[e->get_id()]; 
    }


    void bv_eval::commit_eval(expr* p, app* e) {
        if (!bv.is_bv(e))
            return;
        VERIFY(wval(e).commit_eval_check_tabu());
    }

    void bv_eval::set_random(app* e) {
        if (bv.is_bv(e)) {
            auto& v = wval(e);
            if (v.set_random(m_rand))
                VERIFY(v.commit_eval_check_tabu());
        }
    }

    bool bv_eval::eval_is_correct(app* e) {
        if (!can_eval1(e))
            return false;
        if (m.is_bool(e))
            return bval0(e) == bval1(e);
        if (bv.is_bv(e)) {
            if (m.is_ite(e))
                return true;
            auto const& v = eval(e);
            return v.eval == v.bits();
        }
        UNREACHABLE();
        return false;
    }

    expr_ref bv_eval::get_value(app* e) {
        if (m.is_bool(e))
            return expr_ref(m.mk_bool_val(bval0(e)), m);
        else if (bv.is_bv(e)) {
            auto const& v = wval(e);
            rational n = v.get_value();
            return expr_ref(bv.mk_numeral(n, v.bw), m);
        }
        return expr_ref(m);
    }

    void bv_eval::collect_statistics(statistics& st) const {
        m_lookahead.collect_statistics(st);
    }

    std::ostream& bv_eval::display(std::ostream& out) const {
        auto& terms = ctx.subterms();
        for (expr* e : terms) {
            if (!bv.is_bv(e))
                continue;
            out << e->get_id() << ": " << mk_bounded_pp(e, m, 1) << " ";
            if (is_fixed0(e))
                out << "f ";
            display_value(out, e) << "\n";
        }
        return out;
    }

    std::ostream& bv_eval::display_value(std::ostream& out, expr* e) const {
        if (bv.is_bv(e)) 
            return out << wval(e);
        return out << "?";
    }

   
}
