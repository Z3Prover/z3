/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    bv_sls_fixed.cpp

Author:

    Nikolaj Bjorner (nbjorner) 2024-02-07
    
--*/

#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/sls/bv_sls_fixed.h"
#include "ast/sls/bv_sls_eval.h"

namespace bv {

    sls_fixed::sls_fixed(sls_eval& ev):
        ev(ev),
        m(ev.m),
        bv(ev.bv)
    {}

    void sls_fixed::init(expr_ref_vector const& es) {
        ev.sort_assertions(es);
        for (expr* e : ev.m_todo) {
            if (!is_app(e))
                continue;
            app* a = to_app(e);
            ev.m_fixed.setx(a->get_id(), is_fixed1(a), false);
            if (a->get_family_id() == basic_family_id)
                init_fixed_basic(a);
            else if (a->get_family_id() == bv.get_family_id())
                init_fixed_bv(a);
            else
                ;
        }
        init_ranges(es);
        ev.m_todo.reset();        
    }


    void sls_fixed::init_ranges(expr_ref_vector const& es) {
        for (expr* e : es) {
            bool sign = m.is_not(e, e);
            if (is_app(e))
                init_range(to_app(e), sign);
        }
        
        for (expr* e : ev.m_todo)
            propagate_range_up(e);
    }

    void sls_fixed::propagate_range_up(expr* e) {
        expr* t, * s;
        rational v;
        if (bv.is_concat(e, t, s)) {
            auto& vals = wval(s);
            if (vals.lo() != vals.hi() && (vals.lo() < vals.hi() || vals.hi() == 0))
                // lo <= e
                add_range(e, vals.lo(), rational::zero(), false);
            auto valt = wval(t);
            if (valt.lo() != valt.hi() && (valt.lo() < valt.hi() || valt.hi() == 0)) {
                // (2^|s|) * lo <= e < (2^|s|) * hi
                auto p = rational::power_of_two(bv.get_bv_size(s));
                add_range(e, valt.lo() * p, valt.hi() * p, false);
            }
        }        
        else if (bv.is_bv_add(e, s, t) && bv.is_numeral(s, v)) {
            auto& val = wval(t);
            if (val.lo() != val.hi()) 
                add_range(e, v + val.lo(), v + val.hi(), false);  
        }
        else if (bv.is_bv_add(e, t, s) && bv.is_numeral(s, v)) {
            auto& val = wval(t);
            if (val.lo() != val.hi()) 
                add_range(e, v + val.lo(), v + val.hi(), false);          
        }
        // x in [1, 4[   => -x in [-3, 0[
        // x in [lo, hi[ => -x in [-hi + 1, -lo + 1[
        else if (bv.is_bv_mul(e, s, t) && bv.is_numeral(s, v) && 
            v + 1 == rational::power_of_two(bv.get_bv_size(e))) {
            auto& val = wval(t);
            if (val.lo() != val.hi())
                add_range(e, -val.hi() + 1, - val.lo() + 1, false);
        }
    }

    // s <=s t           <=> s + K <= t + K,   K = 2^{bw-1}

    bool sls_fixed::init_range(app* e, bool sign) {
        expr* s, * t, * x, * y;
        rational a, b;
        unsigned idx;
        auto N = [&](expr* s) {
            auto b = bv.get_bv_size(s);
            return b > 0 ? rational::power_of_two(b - 1) : rational(0);
        };
        if (bv.is_ule(e, s, t)) {
            get_offset(s, x, a);
            get_offset(t, y, b);
            return init_range(x, a, y, b, sign);
        }
        else if (bv.is_ult(e, s, t)) {
            get_offset(s, x, a);
            get_offset(t, y, b);
            return init_range(y, b, x, a, !sign);
        }            
        else if (bv.is_uge(e, s, t)) {
            get_offset(s, x, a);
            get_offset(t, y, b);
            return init_range(y, b, x, a, sign);
        }            
        else if (bv.is_ugt(e, s, t)) {
            get_offset(s, x, a);
            get_offset(t, y, b);
            return init_range(x, a, y, b, !sign);
        }            
        else if (bv.is_sle(e, s, t)) {
            get_offset(s, x, a);
            get_offset(t, y, b);
            return init_range(x, a + N(s), y, b + N(s), sign);
        }            
        else if (bv.is_slt(e, s, t)) {
            get_offset(s, x, a);
            get_offset(t, y, b);
            return init_range(y, b + N(s), x, a + N(s), !sign);
        }
        else if (bv.is_sge(e, s, t)) {
            get_offset(s, x, a);
            get_offset(t, y, b);
            return init_range(y, b + N(s), x, a + N(s), sign);
        }
        else if (bv.is_sgt(e, s, t)) {
            get_offset(s, x, a);
            get_offset(t, y, b);
            return init_range(x, a + N(s), y, b + N(s), !sign);
        }
        else if (m.is_eq(e, s, t)) {
            if (bv.is_numeral(s, a))
                init_eq(t, a, sign);
            else if (bv.is_numeral(t, a))
                init_eq(s, a, sign);
            else
                return false;
            return true;
        }
        else if (bv.is_bit2bool(e, s, idx)) {
            auto& val = wval(s);
            val.try_set_bit(idx, !sign);
            val.fixed.set(idx, true);
            val.tighten_range();
            return true;
        }

        return false;
    }

    bool sls_fixed::init_eq(expr* t, rational const& a, bool sign) {        
        unsigned lo, hi;
        rational b(0);
        // verbose_stream() << mk_bounded_pp(t, m) << " == " << a << "\n";
        expr* s = nullptr;        
        if (sign)
            // 1 <= t - a
            init_range(nullptr, rational(1), t, -a, false);
        else
            // t - a <= 0
            init_range(t, -a, nullptr, rational::zero(), false);
        if (!sign && bv.is_bv_not(t, s)) {
            for (unsigned i = 0; i < bv.get_bv_size(s); ++i)
                if (!a.get_bit(i))
                    b += rational::power_of_two(i);
            init_eq(s, b, false);
            return true;
        }
        expr* x, * y;
        if (!sign && bv.is_concat(t, x, y)) {
            auto sz = bv.get_bv_size(y);
            auto k = rational::power_of_two(sz);
            init_eq(y, mod(a, k), false);
            init_eq(x, div(a + k - 1, k), false);
            return true;
        }
        if (bv.is_extract(t, lo, hi, s)) {
            if (hi == lo) {
                sign = sign ? a == 1 : a == 0;
                auto& val = wval(s);
                if (val.try_set_bit(lo, !sign)) 
                    val.fixed.set(lo, true);                                    
                val.tighten_range();
            }
            else if (!sign) {
                auto& val = wval(s);
                for (unsigned i = lo; i <= hi; ++i) 
                    if (val.try_set_bit(i, a.get_bit(i - lo)))
                        val.fixed.set(i, true);                
                val.tighten_range();
                // verbose_stream() << lo << " " << hi << " " << val << " := " << a << "\n";
            }

            if (!sign && hi + 1 == bv.get_bv_size(s)) {
                // s < 2^lo * (a + 1) 
                rational b = rational::power_of_two(lo) * (a + 1) - 1;
                rational offset;
                get_offset(s, t, offset);
                // t + offset <= b
                init_range(t, offset, nullptr, b, false);
            }
        }
        return true;
    }

    // 
    // x + a <= b        <=> x in [-a, b - a + 1[  b != -1
    // a <= x + b        <=> x in [a - b, -b[      a != 0
    // x + a <= x + b    <=> x in [-a, -b[         a != b
    //
    // x + a < b         <=> ! (b <= x + a) <=> x not in [-b, a - b + 1[ <=> x in [a - b + 1, -b [  b != 0
    // a < x + b         <=> ! (x + b <= a) <=> x not in [-a, b - a [ <=> x in [b - a, -a [         a != -1
    // x + a < x + b     <=> ! (x + b <= x + a) <=> x in [-a, -b [                                  a != b
    // 
    bool sls_fixed::init_range(expr* x, rational const& a, expr* y, rational const& b, bool sign) {
        if (!x && !y)
            return false;
        if (!x) 
            return add_range(y, a - b, -b, sign);
        else if (!y) 
            return add_range(x, -a, b - a + 1, sign);        
        else if (x == y) 
            return add_range(x, -a, -b, sign);
        return false;
    }

    bool sls_fixed::add_range(expr* e, rational lo, rational hi, bool sign) {
        auto& v = wval(e);
        lo = mod(lo, rational::power_of_two(bv.get_bv_size(e)));
        hi = mod(hi, rational::power_of_two(bv.get_bv_size(e)));
        if (lo == hi)
            return false;
        if (sign)
            std::swap(lo, hi);
        v.add_range(lo, hi);
        expr* x, * y;
        if (v.lo() == 0 && bv.is_concat(e, x, y)) {
            auto sz = bv.get_bv_size(y);
            auto k = rational::power_of_two(sz);
            lo = v.lo();
            hi = v.hi();
            if (hi <= k) {
                add_range(y, lo, hi, false);
                init_eq(x, lo, false);
            }
            else {
                hi = div(hi + k - 1, k);
                add_range(x, lo, hi, false);
            }
        }
        return true;
    }

    void sls_fixed::get_offset(expr* e, expr*& x, rational& offset) {
        expr* s, * t;
        x = e;
        offset = 0;
        rational n;
        while (true) {
            if (bv.is_bv_add(x, s, t) && bv.is_numeral(s, n)) {
                x = t;
                offset += n;
                continue;
            }
            if (bv.is_bv_add(x, s, t) && bv.is_numeral(t, n)) {
                x = s;
                offset += n;
                continue;
            }
            break;
        }
        if (bv.is_numeral(e, n))
            offset += n,
            x = nullptr;
    }

    sls_valuation& sls_fixed::wval(expr* e) {
        return ev.wval(e);
    }

    void sls_fixed::init_fixed_basic(app* e) {
        if (bv.is_bv(e) && m.is_ite(e)) {
            auto& val = wval(e);
            auto& val_th = wval(e->get_arg(1));
            auto& val_el = wval(e->get_arg(2));
            for (unsigned i = 0; i < val.nw; ++i)
                val.fixed[i] = val_el.fixed[i] & val_th.fixed[i] & ~(val_el.bits(i) ^ val_th.bits(i));
        }
    }

    void sls_fixed::init_fixed_bv(app* e) {
        if (bv.is_bv(e))
            set_fixed_bw(e);
    }

    bool sls_fixed::is_fixed1(app* e) const {
        if (is_uninterp(e))
            return false;
        if (e->get_family_id() == basic_family_id)
            return is_fixed1_basic(e);
        return all_of(*e, [&](expr* arg) { return ev.is_fixed0(arg); });
    }

    bool sls_fixed::is_fixed1_basic(app* e) const {
        switch (e->get_decl_kind()) {
        case OP_TRUE:
        case OP_FALSE:
            return true;
        case OP_AND:
            return any_of(*e, [&](expr* arg) { return ev.is_fixed0(arg) && !ev.bval0(e); });
        case OP_OR:
            return any_of(*e, [&](expr* arg) { return ev.is_fixed0(arg) && ev.bval0(e); });
        default:
            return all_of(*e, [&](expr* arg) { return ev.is_fixed0(arg); });
        }
    }
    
    void sls_fixed::set_fixed_bw(app* e) {
        SASSERT(bv.is_bv(e));
        SASSERT(e->get_family_id() == bv.get_fid());
        auto& v = ev.wval(e);
        if (all_of(*e, [&](expr* arg) { return ev.is_fixed0(arg); })) {
            for (unsigned i = 0; i < v.bw; ++i)
                v.fixed.set(i, true);
            ev.m_fixed.setx(e->get_id(), true, false);
            return;
        }
        switch (e->get_decl_kind()) {
        case OP_BAND: {
            auto& a = wval(e->get_arg(0));
            auto& b = wval(e->get_arg(1));
            // (a.fixed & b.fixed) | (a.fixed & ~a.bits) | (b.fixed & ~b.bits)
            for (unsigned i = 0; i < a.nw; ++i)
                v.fixed[i] = (a.fixed[i] & b.fixed[i]) | (a.fixed[i] & ~a.bits(i)) | (b.fixed[i] & ~b.bits(i));
            break;
        }
        case OP_BOR: {
            auto& a = wval(e->get_arg(0));
            auto& b = wval(e->get_arg(1));
            // (a.fixed & b.fixed) | (a.fixed & a.bits) | (b.fixed & b.bits)
            for (unsigned i = 0; i < a.nw; ++i)
                v.fixed[i] = (a.fixed[i] & b.fixed[i]) | (a.fixed[i] & a.bits(i)) | (b.fixed[i] & b.bits(i));
            break;
        }
        case OP_BXOR: {
            auto& a = wval(e->get_arg(0));
            auto& b = wval(e->get_arg(1));
            for (unsigned i = 0; i < a.nw; ++i)
                v.fixed[i] = a.fixed[i] & b.fixed[i];
            break;
        }
        case OP_BNOT: {
            auto& a = wval(e->get_arg(0));
            for (unsigned i = 0; i < a.nw; ++i)
                v.fixed[i] = a.fixed[i];
            break;
        }
        case OP_BADD: {
            auto& a = wval(e->get_arg(0));
            auto& b = wval(e->get_arg(1));
            bool pfixed = true;
            for (unsigned i = 0; i < v.bw; ++i) {
                if (pfixed && a.fixed.get(i) && b.fixed.get(i)) 
                    v.fixed.set(i, true);                
                else if (!pfixed && a.fixed.get(i) && b.fixed.get(i) &&
                    !a.get_bit(i) && !b.get_bit(i)) {
                    pfixed = true;
                    v.fixed.set(i, false);
                }
                else {
                    pfixed = false;
                    v.fixed.set(i, false);
                }
            }
            break;
        }
        case OP_BMUL: {
            auto& a = wval(e->get_arg(0));
            auto& b = wval(e->get_arg(1));
            unsigned j = 0, k = 0, zj = 0, zk = 0, hzj = 0, hzk = 0;
            // i'th bit depends on bits j + k = i
            // if the first j, resp k bits are 0, the bits j + k are 0  
            for (; j < v.bw; ++j)
                if (!a.fixed.get(j))
                    break;
            for (; k < v.bw; ++k)
                if (!b.fixed.get(k))
                    break;
            for (; zj < v.bw; ++zj)
                if (!a.fixed.get(zj) || a.get_bit(zj))
                    break;
            for (; zk < v.bw; ++zk)
                if (!b.fixed.get(zk) || b.get_bit(zk))
                    break;
            for (; hzj < v.bw; ++hzj)
                if (!a.fixed.get(v.bw - hzj - 1) || a.get_bit(v.bw - hzj - 1))
                    break;
            for (; hzk < v.bw; ++hzk)
                if (!b.fixed.get(v.bw - hzk - 1) || b.get_bit(v.bw - hzk - 1))
                    break;


            if (j > 0 && k > 0) {
                for (unsigned i = 0; i < std::min(k, j); ++i) {
                    SASSERT(!v.get_bit(i));
                    v.fixed.set(i, true);
                }
            }
            // lower zj + jk bits are 0
            if (zk > 0 || zj > 0) {
                for (unsigned i = 0; i < zk + zj; ++i) {
                    SASSERT(!v.get_bit(i));
                    v.fixed.set(i, true);
                }
            }
            // upper bits are 0, if enough high order bits of a, b are 0.
            // TODO - buggy
            if (false && hzj < v.bw && hzk < v.bw && hzj + hzk > v.bw) {
                hzj = v.bw - hzj;
                hzk = v.bw - hzk;
                for (unsigned i = hzj + hzk - 1; i < v.bw; ++i) {
                    SASSERT(!v.get_bit(i));
                    v.fixed.set(i, true);
                }
            }            
            break;
        }
        case OP_CONCAT: {
            auto& a = wval(e->get_arg(0));
            auto& b = wval(e->get_arg(1));
            for (unsigned i = 0; i < b.bw; ++i)
                v.fixed.set(i, b.fixed.get(i));
            for (unsigned i = 0; i < a.bw; ++i)
                v.fixed.set(i + b.bw, a.fixed.get(i));
            break;
        }
        case OP_EXTRACT: {
            expr* child;
            unsigned lo, hi;
            VERIFY(bv.is_extract(e, lo, hi, child));
            auto& a = wval(child);
            for (unsigned i = lo; i <= hi; ++i)
                v.fixed.set(i - lo, a.fixed.get(i));
            break;
        }
        case OP_BNEG: {
            auto& a = wval(e->get_arg(0));
            bool pfixed = true;
            for (unsigned i = 0; i < v.bw; ++i) {
                if (pfixed && a.fixed.get(i))
                    v.fixed.set(i, true);
                else {
                    pfixed = false;
                    v.fixed.set(i, false);
                }
            }
            break;
        }
        case OP_BSHL: {
            // determine range of b.
            // if b = 0, then inherit fixed from a
            // if b >= v.bw then make e fixed to 0
            // if 0 < b < v.bw is known, then inherit shift of fixed values of a
            // if 0 < b < v.bw but not known, then inherit run lengths of equal bits of a
            // that are fixed.
            break;
        }

        case OP_BASHR:
        case OP_BLSHR:
        case OP_INT2BV:
        case OP_BCOMP:
        case OP_BNAND:
        case OP_BREDAND:
        case OP_BREDOR:
        case OP_BSDIV:
        case OP_BSDIV_I:
        case OP_BSDIV0:
        case OP_BUDIV:
        case OP_BUDIV_I:
        case OP_BUDIV0:
        case OP_BUREM:
        case OP_BUREM_I:
        case OP_BUREM0:
        case OP_BSMOD:
        case OP_BSMOD_I:
        case OP_BSMOD0:       
        case OP_BXNOR:
            // NOT_IMPLEMENTED_YET();
            break;
        case OP_BV_NUM:
        case OP_BIT0:
        case OP_BIT1:
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
        case OP_BIT2BOOL: 
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
        }      
    }
}
