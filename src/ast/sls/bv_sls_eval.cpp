/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    bv_sls_eval.cpp

Author:

    Nikolaj Bjorner (nbjorner) 2024-02-07
    
--*/

#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/sls/bv_sls.h"

namespace bv {

    sls_eval::sls_eval(ast_manager& m): 
        m(m), 
        bv(m),
        m_fix(*this)
    {}   

    void sls_eval::init_eval(expr_ref_vector const& es, std::function<bool(expr*, unsigned)> const& eval) {
        auto& terms = sort_assertions(es);
        for (expr* e : terms) {
            if (!is_app(e))
                continue;
            app* a = to_app(e);
            if (bv.is_bv(e)) 
                add_bit_vector(a);
            if (a->get_family_id() == basic_family_id)
                init_eval_basic(a);
            else if (a->get_family_id() == bv.get_family_id())
                init_eval_bv(a);
            else if (is_uninterp(e)) {
                if (bv.is_bv(e)) {
                    auto& v = wval(e);
                    for (unsigned i = 0; i < v.bw; ++i)
                        m_tmp.set(i, eval(e, i));
                    v.set_repair(random_bool(), m_tmp);
                }
                else if (m.is_bool(e))
                    m_eval.setx(e->get_id(), eval(e, 0), false);
            }
            else {
                TRACE("sls", tout << "Unhandled expression " << mk_pp(e, m) << "\n");
            }
        }
        terms.reset();
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

    bool sls_eval::add_bit_vector(app* e) {
        m_values.reserve(e->get_id() + 1);
        if (m_values.get(e->get_id()))
            return false;
        auto v = alloc_valuation(e);
        m_values.set(e->get_id(), v);
        expr* x, * y;
        rational val;
        if (bv.is_sign_ext(e))          
            v->set_signed(e->get_parameter(0).get_int());        
        else if (bv.is_bv_ashr(e, x, y) && bv.is_numeral(y, val) && 
            val.is_unsigned() && val.get_unsigned() <= bv.get_bv_size(e)) 
            v->set_signed(val.get_unsigned());        
        return true;
    }

    sls_valuation* sls_eval::alloc_valuation(app* e) {
        auto bit_width = bv.get_bv_size(e);
        auto* r = alloc(sls_valuation, bit_width);
        while (m_tmp.size() < 2 * r->nw) {
            m_tmp.push_back(0);
            m_tmp2.push_back(0);           
            m_tmp3.push_back(0);
            m_tmp4.push_back(0);
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

    void sls_eval::init_eval_basic(app* e) {
        auto id = e->get_id();
        if (m.is_bool(e)) 
            m_eval.setx(id, bval1(e), false);                    
        else if (m.is_ite(e)) {
            SASSERT(bv.is_bv(e->get_arg(1)));
            auto& val = wval(e);
            auto& val_th = wval(e->get_arg(1));
            auto& val_el = wval(e->get_arg(2));
            if (bval0(e->get_arg(0))) 
                val.set(val_th.bits());            
            else
                val.set(val_el.bits()); 
        }
        else {
            UNREACHABLE();
        }             
    }

    void sls_eval::init_eval_bv(app* e) {
        if (bv.is_bv(e)) 
            eval(e).commit_eval();        
        else if (m.is_bool(e)) 
            m_eval.setx(e->get_id(), bval1_bv(e), false);        
    }

    bool sls_eval::bval1_basic(app* e) const {
        SASSERT(m.is_bool(e));
        SASSERT(e->get_family_id() == basic_family_id);

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
                auto const& va = wval(a);
                auto const& vb = wval(b);
                return va.eq(vb);
            }
            return m.are_equal(a, b);
        }
        case OP_DISTINCT:
        default:
            verbose_stream() << mk_bounded_pp(e, m) << "\n";
            UNREACHABLE();
            break;
        }
        UNREACHABLE();
        return false;
    }
    
    bool sls_eval::can_eval1(app* e) const {
        expr* x, * y, * z;
        if (m.is_eq(e, x, y))
            return m.is_bool(x) || bv.is_bv(x);
        if (m.is_ite(e, x, y, z))
            return m.is_bool(y) || bv.is_bv(y);
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
        if (e->get_family_id() == basic_family_id)
            return true;
        if (is_uninterp_const(e))
            return m.is_bool(e) || bv.is_bv(e);
        return false;
    }

    bool sls_eval::bval1_bv(app* e) const {
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
            return a.get_bit(idx);
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

    bool sls_eval::bval1(app* e) const {
        if (e->get_family_id() == basic_family_id)
            return bval1_basic(e);
        if (e->get_family_id() == bv.get_fid())
            return bval1_bv(e);
        SASSERT(is_uninterp_const(e));
        return bval0(e); 
    }

    sls_valuation& sls_eval::eval(app* e) const {
        auto& val = *m_values[e->get_id()];        
        eval(e, val);
        return val;        
    }

    void sls_eval::eval(app* e, sls_valuation& val) const {
        SASSERT(bv.is_bv(e));
        if (m.is_ite(e)) {
            SASSERT(bv.is_bv(e->get_arg(1)));
            auto& val_th = wval(e->get_arg(1));
            auto& val_el = wval(e->get_arg(2));
            if (bval0(e->get_arg(0)))
                val.set(val_th.bits());
            else
                val.set(val_el.bits());
            return;
        }
        if (e->get_family_id() == null_family_id) {
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
            SASSERT(e->get_num_args() == 2);
            auto const& a = wval(e->get_arg(0));
            auto const& b = wval(e->get_arg(1));
            for (unsigned i = 0; i < a.nw; ++i)
                val.eval[i] = a.bits()[i] & b.bits()[i];
            break;
        }
        case OP_BOR: {
            SASSERT(e->get_num_args() == 2);
            auto const& a = wval(e->get_arg(0));
            auto const& b = wval(e->get_arg(1));
            for (unsigned i = 0; i < a.nw; ++i)
                val.eval[i] = a.bits()[i] | b.bits()[i];
            break;
        }
        case OP_BXOR: {
            SASSERT(e->get_num_args() == 2);
            auto const& a = wval(e->get_arg(0));
            auto const& b = wval(e->get_arg(1));
            for (unsigned i = 0; i < a.nw; ++i)
                val.eval[i] = a.bits()[i] ^ b.bits()[i];
            break;
        }
        case OP_BNAND: {
            SASSERT(e->get_num_args() == 2);
            auto const& a = wval(e->get_arg(0));
            auto const& b = wval(e->get_arg(1));
            for (unsigned i = 0; i < a.nw; ++i)
                val.eval[i] = ~(a.bits()[i] & b.bits()[i]);
            break;
        }
        case OP_BADD: {
            SASSERT(e->get_num_args() == 2);
            auto const& a = wval(e->get_arg(0));
            auto const& b = wval(e->get_arg(1));
            val.set_add(val.eval, a.bits(), b.bits());
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
            SASSERT(e->get_num_args() == 2);
            auto const& a = wval(e->get_arg(0));
            auto const& b = wval(e->get_arg(1));
            val.set_mul(m_tmp2, a.bits(), b.bits());
            val.set(m_tmp2);
            break;
        }
        case OP_CONCAT: {
            SASSERT(e->get_num_args() == 2);
            auto const& a = wval(e->get_arg(0));
            auto const& b = wval(e->get_arg(1));
            for (unsigned i = 0; i < b.bw; ++i)
                val.eval.set(i, b.get_bit(i));
            for (unsigned i = 0; i < a.bw; ++i)
                val.eval.set(i + b.bw, a.get_bit(i));
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
        case OP_BREDAND:
        case OP_BREDOR:
        case OP_BXNOR:
        case OP_INT2BV:

            verbose_stream() << mk_bounded_pp(e, m) << "\n";
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
        val.clear_overflow_bits(val.eval);
    }

    digit_t sls_eval::random_bits() {
        return sls_valuation::random_bits(m_rand);
    }

    bool sls_eval::try_repair(app* e, unsigned i) {      
        if (is_fixed0(e->get_arg(i)))
            return false;
        else if (e->get_family_id() == basic_family_id)
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
            return try_repair_band(eval_value(e), wval(e, i), wval(e, 1 - i));
        case OP_BOR:
            return try_repair_bor(eval_value(e), wval(e, i), wval(e, 1 - i));
        case OP_BXOR:
            return try_repair_bxor(eval_value(e), wval(e, i), wval(e, 1 - i));
        case OP_BADD:
            return try_repair_add(eval_value(e), wval(e, i), wval(e, 1 - i));
        case OP_BSUB:
            return try_repair_sub(eval_value(e), wval(e, 0), wval(e, 1), i);
        case OP_BMUL:
            return try_repair_mul(eval_value(e), wval(e, i), wval(e, 1 - i));
        case OP_BNOT:
            return try_repair_bnot(eval_value(e), wval(e, i));
        case OP_BNEG:
            return try_repair_bneg(eval_value(e), wval(e, i));
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
            return try_repair_ashr(eval_value(e), wval(e, 0), wval(e, 1), i);
        case OP_BLSHR:
            return try_repair_lshr(eval_value(e), wval(e, 0), wval(e, 1), i);
        case OP_BSHL:
            return try_repair_shl(eval_value(e), wval(e, 0), wval(e, 1), i);
        case OP_BIT2BOOL: {
            unsigned idx;
            expr* arg;
            VERIFY(bv.is_bit2bool(e, arg, idx));
            return try_repair_bit2bool(wval(e, 0), idx);
        }

        case OP_BUDIV:
        case OP_BUDIV_I:
        case OP_BUDIV0:
            return try_repair_udiv(eval_value(e), wval(e, 0), wval(e, 1), i);
        case OP_BUREM:
        case OP_BUREM_I:
        case OP_BUREM0:
            return try_repair_urem(eval_value(e), wval(e, 0), wval(e, 1), i);
        case OP_ROTATE_LEFT:
            return try_repair_rotate_left(eval_value(e), wval(e, 0), e->get_parameter(0).get_int());
        case OP_ROTATE_RIGHT:
            return try_repair_rotate_left(eval_value(e), wval(e, 0), wval(e).bw - e->get_parameter(0).get_int());
        case OP_EXT_ROTATE_LEFT:
            return try_repair_rotate_left(eval_value(e), wval(e, 0), wval(e, 1), i);
        case OP_EXT_ROTATE_RIGHT:
            return try_repair_rotate_right(eval_value(e), wval(e, 0), wval(e, 1), i);
        case OP_ZERO_EXT:
            return try_repair_zero_ext(eval_value(e), wval(e, 0));
        case OP_SIGN_EXT:
            return try_repair_sign_ext(eval_value(e), wval(e, 0));
        case OP_CONCAT:
            return try_repair_concat(eval_value(e), wval(e, 0), wval(e, 1), i);
        case OP_EXTRACT: {
            unsigned hi, lo;
            expr* arg;
            VERIFY(bv.is_extract(e, lo, hi, arg));
            return try_repair_extract(eval_value(e), wval(arg), lo);
        }
        case OP_BUMUL_NO_OVFL:
            return try_repair_umul_ovfl(!bval0(e), wval(e, 0), wval(e, 1), i);
        case OP_BUMUL_OVFL:
            return try_repair_umul_ovfl(bval0(e), wval(e, 0), wval(e, 1), i);
        case OP_BCOMP:
            return try_repair_comp(eval_value(e), wval(e, 0), wval(e, 1), i);
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
        case OP_BSREM:
        case OP_BSREM_I:
        case OP_BSREM0:
        case OP_BSMOD:
        case OP_BSMOD_I:
        case OP_BSMOD0:
        case OP_BSDIV:
        case OP_BSDIV_I:
        case OP_BSDIV0:
            // these are currently compiled to udiv and urem.
            UNREACHABLE();
            return false;
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
        auto is_true = bval0(e);
        if (m.is_bool(child)) {
            SASSERT(!is_fixed0(child));               
            auto bv = bval0(e->get_arg(1 - i));
            m_eval[child->get_id()] = is_true == bv;
            return true;
        }
        else if (bv.is_bv(child)) {
            auto & a = wval(e->get_arg(i));
            auto & b = wval(e->get_arg(1 - i));
            return try_repair_eq(is_true, a, b);
        }
        return false;
    }

    bool sls_eval::try_repair_eq(bool is_true, bvval& a, bvval const& b) {
        if (is_true) {
            if (m_rand(20) != 0) 
                if (a.try_set(b.bits()))
                    return true;
            
            return a.set_random(m_rand);
        }
        else {
            bool try_above = m_rand(2) == 0;
            if (try_above) {
                a.set_add(m_tmp, b.bits(), m_one);
                if (!a.is_zero(m_tmp) && a.set_random_at_least(m_tmp,  m_rand))
                    return true;
            }
            a.set_sub(m_tmp, b.bits(), m_one);
            if (!a.is_zero(m_tmp) && a.set_random_at_most(m_tmp, m_rand))
                return true;
            if (!try_above) {
                a.set_add(m_tmp, b.bits(), m_one);
                if (!a.is_zero(m_tmp) && a.set_random_at_least(m_tmp, m_rand))
                    return true;
            }
            return false;
        }
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
            return wval(child).try_set(wval(e).bits());        
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
    // e[i] = 0 & b[i] = 0 -> a[i] = random
    // a := e[i] | (~b[i] & a[i])

    bool sls_eval::try_repair_band(bvect const& e, bvval& a, bvval const& b) {
        for (unsigned i = 0; i < a.nw; ++i)
            m_tmp[i] = ~a.fixed[i] & (e[i] | (~b.bits()[i] & random_bits()));
        return a.set_repair(random_bool(), m_tmp);
    }

    //
    // e = a | b
    // set a[i] to 1 where b[i] = 0, e[i] = 1
    // set a[i] to 0 where e[i] = 0, a[i] = 1
    //     
    bool sls_eval::try_repair_bor(bvect const& e, bvval& a, bvval const& b) {
        for (unsigned i = 0; i < a.nw; ++i)
            m_tmp[i] = e[i] & (~b.bits()[i] | random_bits());
        return a.set_repair(random_bool(), m_tmp);
    }

    bool sls_eval::try_repair_bxor(bvect const& e, bvval& a, bvval const& b) {
        for (unsigned i = 0; i < a.nw; ++i)
            m_tmp[i] = e[i] ^ b.bits()[i];
        return a.set_repair(random_bool(), m_tmp);
    }


    //
    // first try to set a := e - b
    // If this fails, set a to a random value
    // 
    bool sls_eval::try_repair_add(bvect const& e, bvval& a, bvval const& b) {
        if (m_rand(20) != 0) {
            a.set_sub(m_tmp, e, b.bits());
            if (a.try_set(m_tmp))
                return true;
        }
        return a.set_random(m_rand);        
    }

    bool sls_eval::try_repair_sub(bvect const& e, bvval& a, bvval & b, unsigned i) {
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
        return a.set_random(m_rand);        
    }

    /**
    * e = a*b, then a = e * b^-1
    * 8*e = a*(2b), then a = 4e*b^-1
    */
    bool sls_eval::try_repair_mul(bvect const& e, bvval& a, bvval const& b) {
        unsigned parity_e = b.parity(e);
        unsigned parity_b = b.parity(b.bits());

        if (b.is_zero(e)) {
            a.get_variant(m_tmp, m_rand);
            if (m_rand(10) != 0)
                for (unsigned i = 0; i < b.bw - parity_b; ++i)
                    m_tmp.set(i, false);
            return a.set_repair(random_bool(), m_tmp);
        }

        if (b.is_zero() || m_rand(20) == 0) {
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

        b.get(y);
        if (parity_b > 0) {
            b.shift_right(y, parity_b);
#if 0
            for (unsigned i = parity_b; i < b.bw; ++i)
                y.set(i, m_rand(2) == 0);
#endif
        }

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
        b.get(y);
        if (parity_b > 0)
            b.shift_right(y, parity_b);
        a.set_mul(m_tmp, tb, y);
        SASSERT(a.is_one(m_tmp));
#endif
        e.copy_to(b.nw, m_tmp2);
        if (parity_e > 0 && parity_b > 0)
            b.shift_right(m_tmp2, std::min(parity_b, parity_e));
        a.set_mul(m_tmp, tb, m_tmp2);
        if (a.set_repair(random_bool(), m_tmp))
            return true;

        return a.set_random(m_rand);
    }

    bool sls_eval::try_repair_bnot(bvect const& e, bvval& a) {
        for (unsigned i = 0; i < a.nw; ++i)
            m_tmp[i] = ~e[i];        
        a.clear_overflow_bits(m_tmp);
        return a.try_set(m_tmp);
    }

    bool sls_eval::try_repair_bneg(bvect const& e, bvval& a) {
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
    bool sls_eval::try_repair_sle(bool e, bvval& a, bvval const& b) {
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
    bool sls_eval::try_repair_sge(bool e, bvval& a, bvval const& b) {
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
    bool sls_eval::try_repair_sle(bvval& a, bvect const& b, bvect const& p2) {
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

    bool sls_eval::try_repair_sge(bvval& a, bvect const& b, bvect const& p2) {
        auto& p2_1 = m_tmp4;
        a.set_sub(p2_1, p2, m_one);
        p2_1.set_bw(a.bw);
        bool r = false;
        if (p2 < b) 
            // random b <= x < p2 
            r = a.set_random_in_range(b, p2_1, m_rand);        
        else {
            // random b <= x or x < p2
            bool coin = m_rand(2) == 0;
            if (coin)
                r = a.set_random_at_most(p2_1,m_rand);
            if (!r)
                r = a.set_random_at_least(b,  m_rand);
            if (!r && !coin)
                r = a.set_random_at_most(p2_1,  m_rand);
        }
        p2_1.set_bw(0);
        return r;
    }

    void sls_eval::add_p2_1(bvval const& a, bvect& t) const {
        m_zero.set(a.bw - 1, true);
        a.set_add(t, a.bits(), m_zero);
        m_zero.set(a.bw - 1, false);
        a.clear_overflow_bits(t);
    }

    bool sls_eval::try_repair_ule(bool e, bvval& a, bvval const& b) {
        if (e) {
            // a <= t
            return a.set_random_at_most(b.bits(),  m_rand);
        }
        else {
            // a > t
            a.set_add(m_tmp, b.bits(), m_one);
            if (a.is_zero(m_tmp))
                return false;   
            return a.set_random_at_least(m_tmp, m_rand);
        }           
    }

    bool sls_eval::try_repair_uge(bool e, bvval& a, bvval const& b) {
        if (e) {
            // a >= t
            return a.set_random_at_least(b.bits(), m_rand);
        }
        else {
            // a < t
            if (b.is_zero())
                return false;
            a.set_sub(m_tmp, b.bits(), m_one);
            return a.set_random_at_most(m_tmp, m_rand);
        }    
    }

    bool sls_eval::try_repair_bit2bool(bvval& a, unsigned idx) {       
        return a.try_set_bit(idx, !a.get_bit(idx));
    }

    bool sls_eval::try_repair_shl(bvect const& e, bvval& a, bvval& b, unsigned i) {
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
            // NB. blind sub-range of possible values for b
            SASSERT(i == 1);
            unsigned sh = m_rand(a.bw + 1);
            b.set(m_tmp, sh);
            return b.try_set(m_tmp);
        }
        return false;
    }

    bool sls_eval::try_repair_ashr(bvect const& e, bvval & a, bvval& b, unsigned i) {
        if (i == 0)
            return try_repair_ashr0(e, a, b);
        else
            return try_repair_ashr1(e, a, b);
    }

    bool sls_eval::try_repair_lshr(bvect const& e, bvval& a, bvval& b, unsigned i) {
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
    bool sls_eval::try_repair_lshr0(bvect const& e, bvval& a, bvval const& b) {
        
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
                if (!a.fixed.get(i))
                    ++num_flex;
            if (num_flex == 0)
                return false;
            unsigned n = m_rand(num_flex);
            for (unsigned i = e.bw; i-- >= msb;) {
                if (!a.fixed.get(i)) {
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
    bool sls_eval::try_repair_lshr1(bvect const& e, bvval const& a, bvval& b) {

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
                    if (!b.fixed.get(i))
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
    bool sls_eval::try_repair_ashr0(bvect const& e, bvval& a, bvval const& b) {
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

    bool sls_eval::try_repair_ashr1(bvect const& e, bvval const& a, bvval& b) {

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

    bool sls_eval::try_repair_comp(bvect const& e, bvval& a, bvval& b, unsigned i) {
        SASSERT(e[0] == 0 || e[0] == 1);
        SASSERT(e.bw == 1);
        return try_repair_eq(e[0] == 1, i == 0 ? a : b, i == 0 ? b : a);
    }

    // e = a udiv b
    // e = 0 => a != ones
    // b = 0 => e = -1        // nothing to repair on a
    // e != -1 => max(a) >=u e

    bool sls_eval::try_repair_udiv(bvect const& e, bvval& a, bvval& b, unsigned i) {
        if (i == 0) {
            if (a.is_zero(e) && a.is_ones(a.fixed) && a.is_ones())
                return false;            
            if (b.is_zero()) 
                return false;            
            if (!a.is_ones(e)) {
                for (unsigned i = 0; i < a.nw; ++i)
                    m_tmp[i] = ~a.fixed[i] | a.bits()[i];
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


    bool sls_eval::try_repair_urem(bvect const& e, bvval& a, bvval& b, unsigned i) {

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

    bool sls_eval::add_overflow_on_fixed(bvval const& a, bvect const& t) {
        a.set(m_tmp3, m_zero);
        for (unsigned i = 0; i < a.nw; ++i)
            m_tmp3[i] = a.fixed[i] & a.bits()[i];
        return a.set_add(m_tmp4, t, m_tmp3);
    }

    bool sls_eval::mul_overflow_on_fixed(bvval const& a, bvect const& t) {
        a.set(m_tmp3, m_zero);
        for (unsigned i = 0; i < a.nw; ++i)
            m_tmp3[i] = a.fixed[i] & a.bits()[i];
        return a.set_mul(m_tmp4, m_tmp3, t);
    }

    bool sls_eval::try_repair_rotate_left(bvect const& e, bvval& a, unsigned n) const {
        // a := rotate_right(e, n)
        n = (a.bw - n) % a.bw;
        for (unsigned i = a.bw - n; i < a.bw; ++i)
            m_tmp.set(i + n - a.bw, e.get(i));
        for (unsigned i = 0; i < a.bw - n; ++i)
            m_tmp.set(i + n, e.get(i));
        return a.set_repair(true, m_tmp);       
    }

    bool sls_eval::try_repair_rotate_left(bvect const& e, bvval& a, bvval& b, unsigned i) {
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

    bool sls_eval::try_repair_rotate_right(bvect const& e, bvval& a, bvval& b, unsigned i) {
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

    bool sls_eval::try_repair_umul_ovfl(bool e, bvval& a, bvval& b, unsigned i) {
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
    bool sls_eval::try_repair_sign_ext(bvect const& e, bvval& a) {
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
    bool sls_eval::try_repair_zero_ext(bvect const& e, bvval& a) {
        for (unsigned i = a.bw; i < e.bw; ++i)
            if (e.get(i))
                return false;

        for (unsigned i = 0; i < e.nw; ++i)
            m_tmp[i] = e[i];
        a.clear_overflow_bits(m_tmp);
        return a.try_set(m_tmp);
    }

    bool sls_eval::try_repair_concat(bvect const& e, bvval& a, bvval& b, unsigned idx) {
        bool r = false;
        if (idx == 0) {
            for (unsigned i = 0; i < a.bw; ++i)
                m_tmp.set(i, e.get(i + b.bw));
            a.clear_overflow_bits(m_tmp);
            r = a.try_set(m_tmp);
        }
        else {
            for (unsigned i = 0; i < b.bw; ++i)
                m_tmp.set(i, e.get(i));
            b.clear_overflow_bits(m_tmp);
            r = b.try_set(m_tmp);
        }       
        return r;
    }

    //
    // e = a[hi:lo], where hi = e.bw + lo - 1
    // for the randomized assignment, 
    // set a outside of [hi:lo] to random values with preference to 0 or 1 bits
    // 
    bool sls_eval::try_repair_extract(bvect const& e, bvval& a, unsigned lo) {
        if (m_rand(m_config.m_prob_randomize_extract)  <= 100) {
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
        if (a.try_set(m_tmp))
            return true;
        return a.set_random(m_rand);
    }

    void sls_eval::set_div(bvect const& a, bvect const& b, unsigned bw,
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

    bool sls_eval::repair_up(expr* e) {
        if (!is_app(e))
            return false;
        if (m.is_bool(e)) {
            auto b = bval1(to_app(e));
            if (is_fixed0(e))
                return b == bval0(e);
            m_eval[e->get_id()] = b;
            return true;
        }
        if (bv.is_bv(e)) {
            auto& v = eval(to_app(e));
            
            for (unsigned i = 0; i < v.nw; ++i)
                if (0 != (v.fixed[i] & (v.bits()[i] ^ v.eval[i]))) {
                    v.bits().copy_to(v.nw, v.eval);
                    return false;
                }
            if (v.commit_eval())
                return true;
            v.bits().copy_to(v.nw, v.eval);
            return false;
        }
        return false;
    }

    sls_valuation& sls_eval::wval(expr* e) const { 
        // if (!m_values[e->get_id()]) verbose_stream() << mk_bounded_pp(e, m) << "\n";  
        return *m_values[e->get_id()]; 
    }

    void sls_eval::init_eval(app* t) {
        if (m.is_bool(t))
            set(t, bval1(t));
        else if (bv.is_bv(t)) {
            auto& v = wval(t);
            v.bits().copy_to(v.nw, v.eval);
        }
    }

    void sls_eval::commit_eval(app* e) {
        if (m.is_bool(e)) {
            set(e, bval1(e));
        }
        else {
            VERIFY(wval(e).commit_eval());
        }
    }

    void sls_eval::set_random(app* e) {
        if (bv.is_bv(e))
            eval(e).set_random(m_rand);
    }

    bool sls_eval::eval_is_correct(app* e) {
        if (!can_eval1(e))
            return false;
        if (m.is_bool(e))
            return bval0(e) == bval1(e);
        if (bv.is_bv(e)) {
            auto const& v = wval(e);
            return v.eval == v.bits();
        }
        UNREACHABLE();
        return false;
    }

    bool sls_eval::re_eval_is_correct(app* e) {
        if (!can_eval1(e))
            return false;
        if (m.is_bool(e))
            return bval0(e) ==bval1(e);
        if (bv.is_bv(e)) {
            auto const& v = eval(e);
            return v.eval == v.bits();
        }
        UNREACHABLE();
        return false;
    }

    expr_ref sls_eval::get_value(app* e) {
        if (m.is_bool(e))
            return expr_ref(m.mk_bool_val(bval0(e)), m);
        else if (bv.is_bv(e)) {
            auto const& v = wval(e);
            rational n = v.get_value();
            return expr_ref(bv.mk_numeral(n, v.bw), m);
        }
        return expr_ref(m);
    }

    std::ostream& sls_eval::display(std::ostream& out, expr_ref_vector const& es) {
        auto& terms = sort_assertions(es);
        for (expr* e : terms) {
            out << e->get_id() << ": " << mk_bounded_pp(e, m, 1) << " ";
            if (is_fixed0(e))
                out << "f ";
            display_value(out, e) << "\n";
        }
        terms.reset();
        return out;
    }

    std::ostream& sls_eval::display_value(std::ostream& out, expr* e) {
        if (bv.is_bv(e)) 
            return out << wval(e);
        if (m.is_bool(e))
            return out << (bval0(e)?"T":"F");
        return out << "?";
    }
}
