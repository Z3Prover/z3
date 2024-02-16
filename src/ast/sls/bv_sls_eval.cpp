/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    bv_sls_eval.cpp

Author:

    Nikolaj Bjorner (nbjorner) 2024-02-07
    
--*/

#include "ast/ast_pp.h"
#include "ast/sls/bv_sls.h"

namespace bv {

    sls_eval::sls_eval(ast_manager& m): 
        m(m), 
        bv(m),
        m_fix(*this)
    {}   

    void sls_eval::init_eval(expr_ref_vector const& es, std::function<bool(expr*, unsigned)> const& eval) {
        sort_assertions(es);
        for (expr* e : m_todo) {
            if (!is_app(e))
                continue;
            app* a = to_app(e);
            if (bv.is_bv(e)) 
                add_bit_vector(e);
            if (a->get_family_id() == basic_family_id)
                init_eval_basic(a);
            else if (a->get_family_id() == bv.get_family_id())
                init_eval_bv(a);
            else if (is_uninterp(e)) {
                if (bv.is_bv(e)) {
                    auto& v = wval0(e);
                    for (unsigned i = 0; i < v.bw; ++i)
                        v.set(v.bits, i, eval(e, i));
                }
                else if (m.is_bool(e))
                    m_eval.setx(e->get_id(), eval(e, 0), false);
            }
            else {
                TRACE("sls", tout << "Unhandled expression " << mk_pp(e, m) << "\n");
            }
        }
        m_todo.reset();
    }

    /**
    * Sort all sub-expressions by depth, smallest first.
    */
    ptr_vector<expr>& sls_eval::sort_assertions(expr_ref_vector const& es) {
        expr_fast_mark1 mark;
        for (expr* e : es) {
            if (!mark.is_marked(e)) {
                mark.mark(e);
                m_todo.push_back(e);
            }
        }
        for (unsigned i = 0; i < m_todo.size(); ++i) {
            auto e = m_todo[i];
            if (!is_app(e))
                continue;
            for (expr* arg : *to_app(e)) {
                if (!mark.is_marked(arg)) {
                    mark.mark(arg);
                    m_todo.push_back(arg);
                }
            }
        }
        std::stable_sort(m_todo.begin(), m_todo.end(), [&](expr* a, expr* b) { return get_depth(a) < get_depth(b); });
        return m_todo;
    }

    bool sls_eval::add_bit_vector(expr* e) {
        auto bw = bv.get_bv_size(e);
        m_values0.reserve(e->get_id() + 1);
        if (m_values0.get(e->get_id()))
            return false;
        m_values1.reserve(e->get_id() + 1);
        m_values0.set(e->get_id(), alloc_valuation(bw));
        m_values1.set(e->get_id(), alloc_valuation(bw));
        return true;
    }

    sls_valuation* sls_eval::alloc_valuation(unsigned bit_width) {
        auto* r = alloc(sls_valuation, bit_width);
        while (m_tmp.size() < 2 * r->nw) {
            m_tmp.push_back(0);
            m_tmp2.push_back(0);           
            m_tmp3.push_back(0);
            m_tmp4.push_back(0);
            m_zero.push_back(0);
            m_one.push_back(0);
            m_minus_one.push_back(~0);
            m_one[0] = 1;
        }
        return r;
    }

    void sls_eval::init_eval_basic(app* e) {
        auto id = e->get_id();
        if (m.is_bool(e)) 
            m_eval.setx(id, bval1(e), false);                    
        else if (m.is_ite(e)) {
            SASSERT(bv.is_bv(e->get_arg(1)));
            auto& val = wval0(e);
            auto& val_th = wval0(e->get_arg(1));
            auto& val_el = wval0(e->get_arg(2));
            if (bval0(e->get_arg(0))) 
                val.set(val_th.bits);            
            else
                val.set(val_el.bits); 
        }
        else {
            UNREACHABLE();
        }             
    }

    void sls_eval::init_eval_bv(app* e) {
        if (bv.is_bv(e)) {
            auto& v = wval0(e);
            v.set(wval1(e));
        }
        else if (m.is_bool(e)) 
            m_eval.setx(e->get_id(), bval1_bv(e), false);        
    }

    bool sls_eval::bval1_basic(app* e) const {
        SASSERT(m.is_bool(e));
        SASSERT(e->get_family_id() == basic_family_id);

        auto id = e->get_id();
        switch (e->get_decl_kind()) {
        case OP_TRUE:
            return true;
        case OP_FALSE:
            return false;
        case OP_AND:
            return all_of(*to_app(e), [&](expr* arg) { return bval0(arg); });
        case OP_OR:
            return any_of(*to_app(e), [&](expr* arg) { return bval0(arg); });
        case OP_NOT:
            return !bval0(e->get_arg(0));
        case OP_XOR: {
            bool r = false;
            for (auto* arg : *to_app(e))
                r ^= bval0(arg);
            return r;
        }
        case OP_IMPLIES: {
            auto a = e->get_arg(0);
            auto b = e->get_arg(1);
            return !bval0(a) || bval0(b);
        }
        case OP_ITE: {
            auto c = bval0(e->get_arg(0));
            return bval0(c ? e->get_arg(1) : e->get_arg(2));
        }
        case OP_EQ: {
            auto a = e->get_arg(0);
            auto b = e->get_arg(1);
            if (m.is_bool(a))
                return bval0(a) == bval0(b);
            else if (bv.is_bv(a)) {
                auto const& va = wval0(a);
                auto const& vb = wval0(b);
                return va.eq(vb);
            }
            UNREACHABLE();
            break;
        }
        default:
            UNREACHABLE();
        }
        UNREACHABLE();
        return false;
    }

    bool sls_eval::bval1_bv(app* e) const {
        SASSERT(m.is_bool(e));
        SASSERT(e->get_family_id() == bv.get_fid());

        auto ucompare = [&](std::function<bool(int)> const& f) {
            auto& a = wval0(e->get_arg(0)); 
            auto& b = wval0(e->get_arg(1)); 
            return f(mpn.compare(a.bits.data(), a.nw, b.bits.data(), b.nw));
        };

        // x <s y <=> x + 2^{bw-1} <u y + 2^{bw-1}
        auto scompare = [&](std::function<bool(int)> const& f) {
            auto& a = wval0(e->get_arg(0));
            auto& b = wval0(e->get_arg(1));
            unsigned c;
            a.set(m_zero, a.bw - 1, true);
            mpn.add(a.bits.data(), a.nw, m_zero.data(), a.nw, m_tmp.data(), a.nw + 1, &c);
            mpn.add(b.bits.data(), a.nw, m_zero.data(), a.nw, m_tmp2.data(), a.nw + 1, &c);
            a.set(m_zero, a.bw - 1, false); 
            a.clear_overflow_bits(m_tmp);
            a.clear_overflow_bits(m_tmp2);
            return f(mpn.compare(m_tmp.data(), a.nw, m_tmp2.data(), b.nw));
        };

        auto umul_overflow = [&]() {
            SASSERT(e->get_num_args() == 2);
            auto const& a = wval0(e->get_arg(0));
            auto const& b = wval0(e->get_arg(1));
            mpn.mul(a.bits.data(), a.nw, b.bits.data(), b.nw, m_tmp2.data());
            for (unsigned i = a.nw; i < 2 * a.nw; ++i)
                if (m_tmp2[i] != 0)
                    return true;
            return a.has_overflow(m_tmp2);
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
            auto& a = wval0(child);
            return a.get(a.bits, idx);
        }
        case OP_BUMUL_NO_OVFL: 
            return !umul_overflow();
        case OP_BUMUL_OVFL: 
            return umul_overflow();
        case OP_BUADD_OVFL: {
            SASSERT(e->get_num_args() == 2);
            auto const& a = wval0(e->get_arg(0));
            auto const& b = wval0(e->get_arg(1));
            digit_t c = 0;
            mpn.add(a.bits.data(), a.nw, b.bits.data(), b.nw, m_tmp.data(), a.nw + 1, &c);
            return c != 0 || a.has_overflow(m_tmp);
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

    bool sls_eval::bval1(app* e) const {
        if (e->get_family_id() == basic_family_id)
            return bval1_basic(e);
        if (e->get_family_id() == bv.get_fid())
            return bval1_bv(e);
        SASSERT(is_uninterp_const(e));
        return bval0(e); 
    }

    svector<digit_t>& sls_eval::wval1(app* e) const {
        auto& val = *m_values1[e->get_id()];
        wval1(e, val);
        return val.bits;
    }

    void sls_eval::wval1(app* e, sls_valuation& val) const {
        SASSERT(bv.is_bv(e));
        if (m.is_ite(e)) {
            SASSERT(bv.is_bv(e->get_arg(1)));
            auto& val_th = wval0(e->get_arg(1));
            auto& val_el = wval0(e->get_arg(2));
            if (bval0(e->get_arg(0)))
                val.set(val_th.bits);
            else
                val.set(val_el.bits);
            return;
        }
        if (e->get_family_id() == null_family_id) {
            val.set(wval0(e).bits);
            return;
        }
        auto set_sdiv = [&]() {
            // d = udiv(abs(x), abs(y))
            // y = 0, x > 0 -> -1
            // y = 0, x <= 0 -> -1
            // x = 0, y != 0 -> 0
            // x > 0, y < 0 -> -d
            // x < 0, y > 0 -> -d
            // x > 0, y > 0 -> d
            // x < 0, y < 0 -> d
            auto& a = wval0(e->get_arg(0));
            auto& b = wval0(e->get_arg(1));
            if (a.is_zero() && b.is_zero())
                val.set(m_minus_one);
            else if (a.is_zero())
                val.set(m_zero);
            else if (b.is_zero())
                val.set(m_minus_one);
            else if (!a.sign() && b.is_zero())
                val.set(m_one);
            else {
                bool sign_a = a.sign();
                bool sign_b = b.sign();
                digit_t c;

                if (sign_a)
                    mpn.sub(m_zero.data(), a.nw, a.bits.data(), a.nw, m_tmp.data(), &c);
                else
                    a.get(m_tmp);
                val.clear_overflow_bits(m_tmp);

                if (sign_b)
                    mpn.sub(m_zero.data(), a.nw, b.bits.data(), a.nw, m_tmp2.data(), &c);
                else
                    b.get(m_tmp2);
                val.clear_overflow_bits(m_tmp2);

                mpn.div(m_tmp.data(), a.nw, m_tmp2.data(), a.nw, m_tmp3.data(), m_tmp4.data());
                if (sign_a == sign_b)
                    val.set(m_tmp3);
                else
                    mpn.sub(m_zero.data(), a.nw, m_tmp3.data(), a.nw, m_tmp.data(), &c),
                    val.set(m_tmp);
            }
            };

        auto mk_rotate_left = [&](unsigned n) {            
            auto& a = wval0(e->get_arg(0));
            VERIFY(try_repair_rotate_left(a, val, a.bw - n));
        };

        SASSERT(e->get_family_id() == bv.get_fid());
        switch (e->get_decl_kind()) {
        case OP_BV_NUM: {
            rational n;
            VERIFY(bv.is_numeral(e, n));
            val.set_value(val.bits, n);
            break;
        }
        case OP_BAND: {
            SASSERT(e->get_num_args() == 2);
            auto const& a = wval0(e->get_arg(0));
            auto const& b = wval0(e->get_arg(1));
            for (unsigned i = 0; i < a.nw; ++i)
                val.bits[i] = a.bits[i] & b.bits[i];
            break;
        }
        case OP_BOR: {
            SASSERT(e->get_num_args() == 2);
            auto const& a = wval0(e->get_arg(0));
            auto const& b = wval0(e->get_arg(1));
            for (unsigned i = 0; i < a.nw; ++i)
                val.bits[i] = a.bits[i] | b.bits[i];
            break;
        }
        case OP_BXOR: {
            SASSERT(e->get_num_args() == 2);
            auto const& a = wval0(e->get_arg(0));
            auto const& b = wval0(e->get_arg(1));
            for (unsigned i = 0; i < a.nw; ++i)
                val.bits[i] = a.bits[i] ^ b.bits[i];
            break;
        }
        case OP_BNAND: {
            SASSERT(e->get_num_args() == 2);
            auto const& a = wval0(e->get_arg(0));
            auto const& b = wval0(e->get_arg(1));
            for (unsigned i = 0; i < a.nw; ++i)
                val.bits[i] = ~(a.bits[i] & b.bits[i]);
            break;
        }
        case OP_BADD: {
            SASSERT(e->get_num_args() == 2);
            auto const& a = wval0(e->get_arg(0));
            auto const& b = wval0(e->get_arg(1));
            digit_t c;
            mpn.add(a.bits.data(), a.nw, b.bits.data(), b.nw, val.bits.data(), val.nw + 1, &c);
            break;
        }
        case OP_BSUB: {
            SASSERT(e->get_num_args() == 2);
            auto const& a = wval0(e->get_arg(0));
            auto const& b = wval0(e->get_arg(1));
            digit_t c;
            mpn.sub(a.bits.data(), a.nw, b.bits.data(), b.nw, val.bits.data(), &c);
            break;
        }
        case OP_BMUL: {
            SASSERT(e->get_num_args() == 2);
            auto const& a = wval0(e->get_arg(0));
            auto const& b = wval0(e->get_arg(1));
            mpn.mul(a.bits.data(), a.nw, b.bits.data(), b.nw, m_tmp2.data());
            val.set(m_tmp2);
            break;
        }
        case OP_CONCAT: {
            SASSERT(e->get_num_args() == 2);
            auto const& a = wval0(e->get_arg(0));
            auto const& b = wval0(e->get_arg(1));
            for (unsigned i = 0; i < b.bw; ++i)
                val.set(val.bits, i, b.get(b.bits, i));
            for (unsigned i = 0; i < a.bw; ++i)
                val.set(val.bits, i + b.bw, a.get(a.bits, i));
            break;
        }
        case OP_EXTRACT: {
            expr* child;
            unsigned lo, hi;
            VERIFY(bv.is_extract(e, lo, hi, child));
            auto const& a = wval0(child);
            SASSERT(lo <= hi && hi + 1 <= a.bw && hi - lo + 1 == val.bw);
            for (unsigned i = lo; i <= hi; ++i)
                val.set(val.bits, i - lo, a.get(a.bits, i));         
            break;
        }
        case OP_BNOT: {
            auto& a = wval0(e->get_arg(0));
            for (unsigned i = 0; i < a.nw; ++i)
                val.bits[i] = ~a.bits[i];
            break;
        }
        case OP_BNEG: {
            auto& a = wval0(e->get_arg(0));
            digit_t c;
            mpn.sub(m_zero.data(), a.nw, a.bits.data(), a.nw, val.bits.data(), &c);
            break;
        }
        case OP_BIT0:
            val.set(val.bits, 0, false);
            break;
        case OP_BIT1:
            val.set(val.bits, 0, true);
            break;
        case OP_BSHL: {
            auto& a = wval0(e->get_arg(0));
            auto& b = wval0(e->get_arg(1));
            auto sh = b.to_nat(b.bits, b.bw);
            if (sh == 0)
                val.set(a.bits);
            else if (sh >= b.bw)
                val.set_zero();
            else {
                for (unsigned i = 0; i < a.bw; ++i)
                    val.set(val.bits, i, i >= sh && a.get(a.bits, i - sh));
            }
            break;
        }
        case OP_BLSHR: {
            auto& a = wval0(e->get_arg(0));
            auto& b = wval0(e->get_arg(1));
            auto sh = b.to_nat(b.bits, b.bw);
            if (sh == 0)
                val.set(a.bits);
            else if (sh >= b.bw)
                val.set_zero();
            else {
                for (unsigned i = 0; i < a.bw; ++i)
                    val.set(val.bits, i, i + sh < a.bw && a.get(a.bits, i + sh));
            }
            break;
        }
        case OP_BASHR: {
            auto& a = wval0(e->get_arg(0));
            auto& b = wval0(e->get_arg(1));
            auto sh = b.to_nat(b.bits, b.bw);
            auto sign = a.sign();
            if (sh == 0)
                val.set(a.bits);
            else if (sh >= b.bw) {
                for (unsigned i = 0; i < a.nw; ++i)
                    val.bits[i] = sign ? ~0 : 0;
            }
            else {
                for (unsigned i = 0; i < a.bw; ++i)                    
                    val.set(val.bits, i, i + sh < a.bw && a.get(a.bits, i + sh));
                if (sign)
                    val.set_range(val.bits, a.bw - sh, a.bw, true);
            }
            break;
        }
        case OP_SIGN_EXT: {
            auto& a = wval0(e->get_arg(0));
            val.set(a.bits);
            bool sign = a.sign();
            val.set_range(val.bits, a.bw, val.bw, sign);
            break;
        }
        case OP_ZERO_EXT: {
            auto& a = wval0(e->get_arg(0));
            val.set(a.bits);
            val.set_range(val.bits, a.bw, val.bw, false);
            break;
        }
        case OP_BUREM:
        case OP_BUREM_I:
        case OP_BUREM0: {
            auto& a = wval0(e->get_arg(0));
            auto& b = wval0(e->get_arg(1));

            if (b.is_zero())
                val.set(a.bits);
            else {
                mpn.div(a.bits.data(), a.nw,
                    b.bits.data(), b.nw,
                    m_tmp.data(), // quotient
                    m_tmp2.data()); // remainder
                val.set(m_tmp2);
            }
            break;
        }
        case OP_BSMOD:
        case OP_BSMOD_I:
        case OP_BSMOD0: {
            // u = mod(x,y)
            // u = 0 ->  0
            // y = 0 ->  x
            // x < 0, y < 0 ->  -u
            // x < 0, y >= 0 ->  y - u
            // x >= 0, y < 0 ->  y + u
            // x >= 0, y >= 0 ->  u
            auto& a = wval0(e->get_arg(0));
            auto& b = wval0(e->get_arg(1));
            if (b.is_zero())
                val.set(a.bits);
            else {
                digit_t c;
                mpn.div(a.bits.data(), a.nw,
                    b.bits.data(), b.nw,
                    m_tmp.data(), // quotient
                    m_tmp2.data()); // remainder
                if (val.is_zero(m_tmp2))
                    val.set(m_tmp2);
                else if (a.sign() && b.sign())
                    mpn.sub(m_zero.data(), a.nw, m_tmp2.data(), a.nw, m_tmp.data(), &c),
                    val.set(m_tmp);
                else if (a.sign())
                    mpn.sub(b.bits.data(), a.nw, m_tmp2.data(), a.nw, m_tmp.data(), &c),
                    val.set(m_tmp);
                else if (b.sign())
                    mpn.add(b.bits.data(), a.nw, m_tmp2.data(), a.nw, m_tmp.data(), a.nw + 1, &c),
                    val.set(m_tmp);
                else
                    val.set(m_tmp2);
            }
            break;
        }
        case OP_BUDIV:
        case OP_BUDIV_I:
        case OP_BUDIV0:  {
            // x div 0 = -1
            auto& a = wval0(e->get_arg(0));
            auto& b = wval0(e->get_arg(1));
            if (b.is_zero()) 
                val.set(m_minus_one);            
            else {
                mpn.div(a.bits.data(), a.nw,
                    b.bits.data(), b.nw,
                    m_tmp.data(), // quotient
                    m_tmp2.data()); // remainder
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
            // y = 0 -> x
            // else x - sdiv(x, y) * y
            // 
            auto& a = wval0(e->get_arg(0));
            auto& b = wval0(e->get_arg(1));
            if (b.is_zero()) 
                val.set(a.bits);
            else {
                digit_t c;
                set_sdiv();
                mpn.mul(val.bits.data(), a.nw, b.bits.data(), a.nw, m_tmp.data());
                mpn.sub(a.bits.data(), a.nw, m_tmp.data(), a.nw, m_tmp2.data(), &c);
                val.set(m_tmp2);
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
            auto& b = wval0(e->get_arg(1));
            rational n;
            b.get_value(b.bits, n);
            n = mod(n, rational(val.bw));
            SASSERT(n.is_unsigned());
            mk_rotate_left(n.get_unsigned());
            break;
        }
        case OP_EXT_ROTATE_RIGHT: {
            auto& b = wval0(e->get_arg(1));
            rational n;
            b.get_value(b.bits, n);
            n = mod(n, rational(val.bw));
            SASSERT(n.is_unsigned());
            mk_rotate_left(val.bw - n.get_unsigned());
            break;
        }
        case OP_BREDAND:
        case OP_BREDOR:
        case OP_BXNOR:
        case OP_INT2BV:
        case OP_BCOMP:
            NOT_IMPLEMENTED_YET();
            break;
        case OP_BIT2BOOL:
        case OP_BV2INT:
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
        val.clear_overflow_bits(val.bits);
    }

    bool sls_eval::try_repair(app* e, unsigned i) {
        if (is_fixed0(e->get_arg(i)))
            return false;
        if (e->get_family_id() == basic_family_id)
            return try_repair_basic(e, i);
        if (e->get_family_id() == bv.get_family_id())
            return try_repair_bv(e, i);
        return false;
    }

    bool sls_eval::try_repair_basic(app* e, unsigned i) {
        switch (e->get_decl_kind()) {
        case OP_AND:
            return try_repair_and_or(e, i);
        case OP_OR:
            return try_repair_and_or(e, i);
        case OP_NOT:
            return try_repair_not(e);
        case OP_FALSE:             
            return false;
        case OP_TRUE:             
            return false;
        case OP_EQ:
            return try_repair_eq(e, i);
        case OP_IMPLIES: 
            return try_repair_implies(e, i);
        case OP_XOR:
            return try_repair_xor(e, i);
        case OP_ITE:
            return try_repair_ite(e, i);
        default:
            UNREACHABLE();
            return false;
        }
    }

    bool sls_eval::try_repair_bv(app* e, unsigned i) {
        switch (e->get_decl_kind()) {
        case OP_BAND:
            return try_repair_band(wval0(e), wval0(e, i), wval0(e, 1 - i));
        case OP_BOR:
            return try_repair_bor(wval0(e), wval0(e, i), wval0(e, 1 - i));
        case OP_BXOR:
            return try_repair_bxor(wval0(e), wval0(e, i), wval0(e, 1 - i));
        case OP_BADD:
            return try_repair_add(wval0(e), wval0(e, i), wval0(e, 1 - i));
        case OP_BMUL:
            return try_repair_mul(wval0(e), wval0(e, i), wval0(e, 1 - i));
        case OP_BNOT:
            return try_repair_bnot(wval0(e), wval0(e, i));
        case OP_BNEG:
            return try_repair_bneg(wval0(e), wval0(e, i));
        case OP_BIT0:
            return false;
        case OP_BIT1:
            return false;
        case OP_BV2INT:
            return false;
        case OP_INT2BV:
            return false;
        case OP_ULEQ:
            if (i == 0)
                return try_repair_ule(bval0(e), wval0(e, i), wval0(e, 1 - i));
            else
                return try_repair_uge(bval0(e), wval0(e, i), wval0(e, 1 - i));
        case OP_UGEQ:
            if (i == 0)
                return try_repair_uge(bval0(e), wval0(e, i), wval0(e, 1 - i));
            else
                return try_repair_ule(bval0(e), wval0(e, i), wval0(e, 1 - i));
        case OP_UGT:
            if (i == 0)
                return try_repair_ule(!bval0(e), wval0(e, i), wval0(e, 1 - i));
            else
                return try_repair_uge(!bval0(e), wval0(e, i), wval0(e, 1 - i));
        case OP_ULT:
            if (i == 0)
                return try_repair_uge(!bval0(e), wval0(e, i), wval0(e, 1 - i));
            else
                return try_repair_ule(!bval0(e), wval0(e, i), wval0(e, 1 - i));
        case OP_SLEQ:
            if (i == 0)
                return try_repair_sle(bval0(e), wval0(e, i), wval0(e, 1 - i));
            else
                return try_repair_sge(bval0(e), wval0(e, i), wval0(e, 1 - i));
        case OP_SGEQ:
            if (i == 0)
                return try_repair_sge(bval0(e), wval0(e, i), wval0(e, 1 - i));
            else
                return try_repair_sle(bval0(e), wval0(e, i), wval0(e, 1 - i));
        case OP_SGT:
            if (i == 0)
                return try_repair_sle(!bval0(e), wval0(e, i), wval0(e, 1 - i));
            else
                return try_repair_sge(!bval0(e), wval0(e, i), wval0(e, 1 - i));
        case OP_SLT:
            if (i == 0)
                return try_repair_sge(!bval0(e), wval0(e, i), wval0(e, 1 - i));
            else
                return try_repair_sle(!bval0(e), wval0(e, i), wval0(e, 1 - i));
        case OP_BASHR:
            return try_repair_ashr(wval0(e), wval0(e, 0), wval0(e, 1), i);
        case OP_BLSHR:
            return try_repair_lshr(wval0(e), wval0(e, 0), wval0(e, 1), i);
        case OP_BSHL:
            return try_repair_shl(wval0(e), wval0(e, 0), wval0(e, 1), i);
        case OP_BIT2BOOL: {
            unsigned idx;
            expr* arg;
            VERIFY(bv.is_bit2bool(e, arg, idx));
            return try_repair_bit2bool(wval0(e, 0), idx);
        }
        case OP_BSDIV:
        case OP_BSDIV_I:
        case OP_BSDIV0:
            return try_repair_sdiv(wval0(e), wval0(e, 0), wval0(e, 1), i);
        case OP_BUDIV:
        case OP_BUDIV_I:
        case OP_BUDIV0:
            return try_repair_udiv(wval0(e), wval0(e, 0), wval0(e, 1), i);
        case OP_BUREM:
        case OP_BUREM_I:
        case OP_BUREM0:
            return try_repair_urem(wval0(e), wval0(e, 0), wval0(e, 1), i);
        case OP_BSREM:
        case OP_BSREM_I:
        case OP_BSREM0:
            return try_repair_srem(wval0(e), wval0(e, 0), wval0(e, 1), i);
        case OP_BSMOD:
        case OP_BSMOD_I:
        case OP_BSMOD0:
            return try_repair_smod(wval0(e), wval0(e, 0), wval0(e, 1), i);
        case OP_ROTATE_LEFT:
            return try_repair_rotate_left(wval0(e), wval0(e, 0), e->get_parameter(0).get_int());
        case OP_ROTATE_RIGHT:
            return try_repair_rotate_left(wval0(e), wval0(e, 0), wval0(e).bw - e->get_parameter(0).get_int());
        case OP_EXT_ROTATE_LEFT:
            return try_repair_rotate_left(wval0(e), wval0(e, 0), wval0(e, 1), i);
        case OP_EXT_ROTATE_RIGHT:
        case OP_BCOMP:
        case OP_BNAND:
        case OP_BREDAND:
        case OP_BREDOR:
        case OP_BXNOR:
        case OP_BNEG_OVFL:
        case OP_BSADD_OVFL:
        case OP_BUADD_OVFL:
        case OP_BSDIV_OVFL:
        case OP_BSMUL_NO_OVFL:
        case OP_BSMUL_NO_UDFL:
        case OP_BSMUL_OVFL:
        case OP_BUMUL_NO_OVFL:
        case OP_BUMUL_OVFL:
        default:
            return false;
        }
    }

    bool sls_eval::try_repair_and_or(app* e, unsigned i) {
        auto b = bval0(e);
        auto child = e->get_arg(i);
        if (b == bval0(child))
            return false;
        m_eval[child->get_id()] = b;
        return true;
    }

    bool sls_eval::try_repair_not(app* e) {
        auto child = e->get_arg(0);
        m_eval[child->get_id()] = !bval0(e);
        return true;
    }

    bool sls_eval::try_repair_eq(app* e, unsigned i) {
        auto child = e->get_arg(i);        
        auto ev = bval0(e);
        if (m.is_bool(child)) {
            SASSERT(!is_fixed0(child));               
            auto bv = bval0(e->get_arg(1 - i));
            m_eval[child->get_id()] = ev == bv;
            return true;
        }
        else if (bv.is_bv(child)) {
            auto & a = wval0(e->get_arg(i));
            auto & b = wval0(e->get_arg(1 - i));
            if (ev) 
                return a.try_set(b.bits);
            else {
                // pick random bit to differ  
                a.get(m_tmp);
                unsigned start = m_rand(a.bw);
                for (unsigned idx = 0; idx < a.bw; ++idx) {
                    unsigned j = (idx + start) % a.bw;
                    if (!a.get(a.fixed, j)) {
                        a.set(m_tmp, idx, !b.get(b.bits, j));
                        bool r = a.try_set(m_tmp);
                        if (r)
                            return true;
                        a.set(m_tmp, j, b.get(b.bits, j));
                    }
                }
                // could be due to bounds?
                return false;
            }
        }
        return false;
    }

    bool sls_eval::try_repair_xor(app* e, unsigned i) {
        bool ev = bval0(e);
        bool bv = bval0(e->get_arg(1 - i));
        auto child = e->get_arg(i);
        m_eval[child->get_id()] = ev != bv;
        return true;
    }

    bool sls_eval::try_repair_ite(app* e, unsigned i) {
        auto child = e->get_arg(i);
        bool c = bval0(e->get_arg(0));
        if (i == 0) {
            m_eval[child->get_id()] = !c;
            return true;
        }
        if (c != (i == 1))
            return false;
        if (m.is_bool(e)) {
            m_eval[child->get_id()] = bval0(e);
            return true;
        }
        if (bv.is_bv(e)) 
            return wval0(child).try_set(wval0(e).bits);        
        return false;
    }

    bool sls_eval::try_repair_implies(app* e, unsigned i) {
        auto child = e->get_arg(i);
        bool ev = bval0(e);
        bool av = bval0(child);
        bool bv = bval0(e->get_arg(1 - i));
        if (i == 0) {
            if (ev == (!av || bv))
                return false;
        }
        else if (ev != (!bv || av))
            return false;
        m_eval[child->get_id()] = ev;
        return true;
    }

    //
    // e = a & b
    // e[i] = 1 -> a[i] = 1
    // e[i] = 0 & b[i] = 1 -> a[i] = 0
    //
    // a := e[i] | (~b[i] & a[i])

    bool sls_eval::try_repair_band(bvval const& e, bvval& a, bvval const& b) {
        for (unsigned i = 0; i < e.nw; ++i)
            m_tmp[i] = e.bits[i] | (~b.bits[i] & a.bits[i]);
        return a.try_set(m_tmp);
    }

    //
    // e = a | b
    // set a[i] to 1 where b[i] = 0, e[i] = 1
    // set a[i] to 0 where e[i] = 0, a[i] = 1
    //     
    bool sls_eval::try_repair_bor(bvval const& e, bvval& a, bvval const& b) {
        for (unsigned i = 0; i < e.nw; ++i)
            m_tmp[i] = e.bits[i] & (a.bits[i] | ~b.bits[i]);
        return a.try_set(m_tmp);       
    }

    bool sls_eval::try_repair_bxor(bvval const& e, bvval& a, bvval const& b) {
        for (unsigned i = 0; i < e.nw; ++i)
            m_tmp[i] = e.bits[i] ^ b.bits[i];
        return a.try_set(m_tmp);
    }

    bool sls_eval::try_repair_add(bvval const& e, bvval& a, bvval const& b) {
        digit_t c;
        mpn.sub(e.bits.data(), e.nw, b.bits.data(), e.nw, m_tmp.data(), &c);
        return a.try_set(m_tmp);
    }

    /**
    * e = a*b, then a = e * b^-1
    * 8*e = a*(2b), then a = 4e*b^-1
    */
    bool sls_eval::try_repair_mul(bvval const& e, bvval& a, bvval const& b) {
        if (b.is_zero()) {
            if (a.is_zero()) {
                a.set(m_tmp, 1);                
                return a.try_set(m_tmp);
            }
            return false;
        }
        rational ne, nb;
        e.get_value(e.bits, ne);
        b.get_value(b.bits, nb);
        unsigned parity_e = e.parity(e.bits);
        unsigned parity_b = b.parity(b.bits);
        if (parity_b > 0)
            ne /= rational::power_of_two(std::min(parity_b, parity_e));
        auto inv_b = nb.pseudo_inverse(b.bw);
        rational na = mod(inv_b * ne, rational::power_of_two(a.bw));
        a.set_value(m_tmp, na);
        return a.try_set(m_tmp);      
    }

    bool sls_eval::try_repair_bnot(bvval const& e, bvval& a) {
        for (unsigned i = 0; i < e.nw; ++i)
            m_tmp[i] = ~e.bits[i];
        return a.try_set(m_tmp);       
    }

    bool sls_eval::try_repair_bneg(bvval const& e, bvval& a) {
        digit_t c;
        mpn.sub(m_zero.data(), e.nw, e.bits.data(), e.nw, m_tmp.data(), &c);        
        return a.try_set(m_tmp);
    }

    bool sls_eval::try_repair_ule(bool e, bvval& a, bvval const& b) {
        if (e) 
            return a.try_set(b.bits);
        else {
            digit_t c;           
            mpn.add(b.bits.data(), a.nw, m_one.data(), a.nw, &c, a.nw + 1, m_tmp.data());       
            return a.try_set(m_tmp);
        }        
    }

    bool sls_eval::try_repair_uge(bool e, bvval& a, bvval const& b) {
        if (e)
            return a.try_set(b.bits);
        else {
            digit_t c;
            mpn.sub(b.bits.data(), a.nw, m_one.data(), a.nw, m_tmp.data(), &c);          
            return a.try_set(m_tmp);
        }        
    }

    bool sls_eval::try_repair_sle(bool e, bvval& a, bvval const& b) {
        return try_repair_ule(e, a, b);
    }

    bool sls_eval::try_repair_sge(bool e, bvval& a, bvval const& b) {
        return try_repair_uge(e, a, b);
    }

    bool sls_eval::try_repair_bit2bool(bvval& a, unsigned idx) {
        for (unsigned i = 0; i < a.nw; ++i)
            m_tmp[i] = a.bits[i];
        a.set(m_tmp, idx, !a.get(a.bits, idx));
        return a.try_set(m_tmp);
    }

    bool sls_eval::try_repair_shl(bvval const& e, bvval& a, bvval& b, unsigned i) {
        if (i == 0) {
            unsigned sh = b.to_nat(b.bits, b.bw);
            if (sh == 0) 
                return a.try_set(e.bits);            
            else if (sh >= b.bw) 
                return false;            
            else {
                //
                // e = a << sh
                // set bw - sh low order bits to bw - sh high-order of e.
                // a[bw - sh - 1: 0] = e[bw - 1: sh]
                // a[bw - 1: bw - sh] = unchanged
                //
                for (unsigned i = 0; i < e.bw - sh; ++i)
                    e.set(m_tmp, i, e.get(e.bits, sh + i));
                for (unsigned i = e.bw - sh; i < e.bw; ++i)
                    e.set(m_tmp, i, e.get(a.bits, i));
                return a.try_set(m_tmp);
            }
        }
        else {
            // NB. blind sub-range of possible values for b
            SASSERT(i == 1);
            unsigned sh = m_rand(a.bw + 1);
            b.set(m_tmp, sh);
            return b.try_set(m_tmp);
        }
        return false;
    }

    bool sls_eval::try_repair_ashr(bvval const& e, bvval & a, bvval& b, unsigned i) {
        if (i == 0) {
            unsigned sh = b.to_nat(b.bits, b.bw);
            if (sh == 0)
                return a.try_set(e.bits);
            else if (sh >= b.bw)
                return false;
            else {
                // e = a >> sh
                // a[bw-1:sh] = e[bw-sh-1:0]
                // a[sh-1:0] = a[sh-1:0]                
                // ignore sign
                for (unsigned i = 0; i < a.bw - sh; ++i)
                    a.set(m_tmp, i + sh, e.get(e.bits, i));
                for (unsigned i = 0; i < sh; ++i)
                    a.set(m_tmp, i, a.get(a.bits, i));
                return a.try_set(m_tmp);
            }
        }
        else {
            // NB. blind sub-range of possible values for b
            SASSERT(i == 1);
            unsigned sh = m_rand(a.bw + 1);
            b.set(m_tmp, sh);
            return b.try_set(m_tmp);
        }
        return false;
    }

    bool sls_eval::try_repair_lshr(bvval const& e, bvval& a, bvval& b, unsigned i) {
        return try_repair_ashr(e, a, b, i);
    }

    bool sls_eval::try_repair_sdiv(bvval const& e, bvval& a, bvval& b, unsigned i) {
        return false;
    }

    bool sls_eval::try_repair_udiv(bvval const& e, bvval& a, bvval& b, unsigned i) {
        return false;
    }

    bool sls_eval::try_repair_smod(bvval const& e, bvval& a, bvval& b, unsigned i) {
        return false;
    }

    bool sls_eval::try_repair_urem(bvval const& e, bvval& a, bvval& b, unsigned i) {
        return false;
    }

    bool sls_eval::try_repair_srem(bvval const& e, bvval& a, bvval& b, unsigned i) {
        return false;
    }

    bool sls_eval::try_repair_rotate_left(bvval const& e, bvval& a, unsigned n) const {
        // a := rotate_right(e, n)
        n = (a.bw - n) % a.bw;
        for (unsigned i = a.bw - n; i < a.bw; ++i)
            a.set(m_tmp, i + n - a.bw, e.get(e.bits, i));
        for (unsigned i = 0; i < a.bw - n; ++i)
            a.set(m_tmp, i + a.bw - n, e.get(e.bits, i));
        return a.try_set(m_tmp);
    }

    bool sls_eval::try_repair_rotate_left(bvval const& e, bvval& a, bvval& b, unsigned i) {
        if (i == 0) {
            rational n;
            b.get_value(b.bits, n);
            n = mod(n, rational(b.bw));
            return try_repair_rotate_left(e, a, n.get_unsigned());
        }
        else {
            SASSERT(i == 1);
            unsigned sh = m_rand(b.bw);
            b.set(m_tmp, sh);
            return b.try_set(m_tmp);
        }       
    }

    void sls_eval::repair_up(expr* e) {
        if (!is_app(e))
            return;
        if (m.is_bool(e))
            set(e, bval1(to_app(e)));
        else if (bv.is_bv(e)) 
            wval0(e).try_set(wval1(to_app(e)));        
    }
}
