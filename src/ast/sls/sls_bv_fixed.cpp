/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    bv_sls_fixed.cpp

Author:

    Nikolaj Bjorner (nbjorner) 2024-02-07

--*/

#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/sls/sls_bv_fixed.h"
#include "ast/sls/sls_bv_terms.h"
#include "ast/sls/sls_bv_eval.h"

namespace sls {

    bv_fixed::bv_fixed(bv_eval& ev, bv_terms& terms, sls::context& ctx) :
        ev(ev),
        m(ev.m),
        bv(ev.bv),
        ctx(ctx)
    {
    }

    void bv_fixed::init() {

        //return;

        for (auto e : ctx.subterms())
            set_fixed(e);

        //ctx.display(verbose_stream());

        for (auto lit : ctx.unit_literals()) {
            auto a = ctx.atom(lit.var());
            if (!a)
                continue;
            if (is_app(a))
                init_range(to_app(a), lit.sign());
            ev.m_is_fixed.setx(a->get_id(), true, false);
        }
        //ctx.display(verbose_stream());

        for (auto e : ctx.subterms())
            propagate_range_up(e);

        //ctx.display(verbose_stream());
    }

    void bv_fixed::propagate_range_up(expr* e) {
        expr* t, * s;
        rational v;
        if (bv.is_concat(e, t, s)) {
            auto& vals = ev.wval(s);
            if (vals.lo() != vals.hi() && (vals.lo() < vals.hi() || vals.hi() == 0))
                // lo <= e
                add_range(e, vals.lo(), rational::zero(), false);
            auto valt = ev.wval(t);
            if (valt.lo() != valt.hi() && (valt.lo() < valt.hi() || valt.hi() == 0)) {
                // (2^|s|) * lo <= e < (2^|s|) * hi
                auto p = rational::power_of_two(bv.get_bv_size(s));
                add_range(e, valt.lo() * p, valt.hi() * p, false);
            }
        }
        else if (bv.is_bv_add(e, s, t) && bv.is_numeral(s, v)) {
            auto& val = ev.wval(t);
            if (val.lo() != val.hi())
                add_range(e, v + val.lo(), v + val.hi(), false);
        }
        else if (bv.is_bv_add(e, t, s) && bv.is_numeral(s, v)) {
            auto& val = ev.wval(t);
            if (val.lo() != val.hi())
                add_range(e, v + val.lo(), v + val.hi(), false);
        }
        // x in [1, 4[   => -x in [-3, 0[
        // x in [lo, hi[ => -x in [-hi + 1, -lo + 1[
        else if (bv.is_bv_mul(e, s, t) && bv.is_numeral(s, v) &&
            v + 1 == rational::power_of_two(bv.get_bv_size(e))) {
            auto& val = ev.wval(t);
            if (val.lo() != val.hi())
                add_range(e, -val.hi() + 1, -val.lo() + 1, false);
        }
    }

    // s <=s t           <=> s + K <= t + K,   K = 2^{bw-1}

    bool bv_fixed::init_range(app* e, bool sign) {
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
            auto& val = ev.wval(s);
            val.try_set_bit(idx, !sign);
            val.set_fixed_bit(idx, !sign);
            val.tighten_range();
            return true;
        }

        return false;
    }

    bool bv_fixed::init_eq(expr* t, rational const& a, bool sign) {
        unsigned lo, hi;
        rational b(0);
        expr* s = nullptr;
        if (sign && true)
            // 1 <= t - a
            init_range(nullptr, rational(1), t, -a, false);
        if (!sign)
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
                auto sign1 = sign ? a == 1 : a == 0;
                auto& val = ev.wval(s);
                val.try_set_bit(lo, !sign1);
                val.set_fixed_bit(lo, !sign1);
                val.tighten_range();

            }
            else if (!sign) {
                auto& val = ev.wval(s);
                for (unsigned i = lo; i <= hi; ++i) {
                    val.try_set_bit(i, a.get_bit(i - lo));
                    val.set_fixed_bit(i, a.get_bit(i - lo));
                }
                val.tighten_range();
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
    bool bv_fixed::init_range(expr* x, rational const& a, expr* y, rational const& b, bool sign) {
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

    bool bv_fixed::add_range(expr* e, rational lo, rational hi, bool sign) {
        auto& v = ev.wval(e);
        lo = mod(lo, rational::power_of_two(bv.get_bv_size(e)));
        hi = mod(hi, rational::power_of_two(bv.get_bv_size(e)));
        if (lo == hi)
            return false;
        if (sign)
            std::swap(lo, hi);
        rational r;
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
        else if (bv.is_bv_mul(e, x, y) &&
            hi != lo &&
            bv.is_numeral(x, r) &&
            r + 1 == rational::power_of_two(bv.get_bv_size(e))) {
            add_range(y, 1 - hi, 1 - lo, false);
        }
        else if (bv.is_bv_add(e, x, y) && bv.is_numeral(x, r)) {
            add_range(y, lo - r, hi - r, false);
        }
        return true;
    }

    void bv_fixed::get_offset(expr* e, expr*& x, rational& offset) {
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

    bool bv_fixed::is_fixed1(app* e) const {
        if (is_uninterp(e))
            return false;
        return all_of(*e, [&](expr* arg) { return ev.is_fixed0(arg); });
    }

    void bv_fixed::set_fixed(expr* _e) {
        if (!is_app(_e))
            return;
        auto e = to_app(_e);

        if (e->get_family_id() == bv.get_family_id() && all_of(*e, [&](expr* arg) { return ev.is_fixed0(arg); })) {
            if (bv.is_bv(e)) {
                auto& v = ev.wval(e);
                for (unsigned i = 0; i < v.bw; ++i)
                    v.set_fixed_bit(i, v.bits().get(i));
            }
            ev.m_is_fixed.setx(e->get_id(), true, false);
            return;
        }

        if (!bv.is_bv(e))
            return;
        auto& v = ev.wval(e);

        if (m.is_ite(e)) {
            auto& val_th = ev.wval(e->get_arg(1));
            auto& val_el = ev.wval(e->get_arg(2));
            for (unsigned i = 0; i < v.nw; ++i) {
                auto mask = val_el.fixed(i) & val_th.fixed(i) & ~(val_el.bits(i) ^ val_th.bits(i));
                v.set_fixed_word(i, mask, v.bits(i));
                return;
            }
        }

        if (e->get_family_id() != bv.get_fid())
            return;
        switch (e->get_decl_kind()) {
        case OP_BAND: {
            if (e->get_num_args() == 2) {
                auto& a = ev.wval(e->get_arg(0));
                auto& b = ev.wval(e->get_arg(1));
                // (a.fixed & b.fixed) | (a.fixed & ~a.bits) | (b.fixed & ~b.bits)
                for (unsigned i = 0; i < a.nw; ++i) {
                    auto mask = (a.fixed(i) & b.fixed(i)) | (a.fixed(i) & ~a.bits(i)) | (b.fixed(i) & ~b.bits(i));
                    v.set_fixed_word(i, mask, v.bits(i));
                }
            }
            break;
        }
        case OP_BOR: {
            if (e->get_num_args() == 2) {
                auto& a = ev.wval(e->get_arg(0));
                auto& b = ev.wval(e->get_arg(1));
                // (a.fixed & b.fixed) | (a.fixed & a.bits) | (b.fixed & b.bits)
                for (unsigned i = 0; i < a.nw; ++i) {
                    auto mask = (a.fixed(i) & b.fixed(i)) | (a.fixed(i) & a.bits(i)) | (b.fixed(i) & b.bits(i));
                    v.set_fixed_word(i, mask, v.bits(i));
                }
            }
            break;
        }
        case OP_BXOR: {
            if (e->get_num_args() == 2) {
                auto& a = ev.wval(e->get_arg(0));
                auto& b = ev.wval(e->get_arg(1));
                for (unsigned i = 0; i < a.nw; ++i)
                    v.set_fixed_word(i, a.fixed(i) & b.fixed(i), v.bits(i));
            }
            break;
        }
        case OP_BNOT: {
            auto& a = ev.wval(e->get_arg(0));
            for (unsigned i = 0; i < a.nw; ++i)
                v.set_fixed_word(i, a.fixed(i), v.bits(i));
            break;
        }
        case OP_BADD: {
            bool pfixed = true;
            for (unsigned i = 0; i < v.bw; ++i) {
                for (unsigned j = 0; pfixed && j < e->get_num_args(); ++j) {
                    auto& a = ev.wval(e->get_arg(j));
                    pfixed &= a.fixed().get(i);
                }
                if (pfixed)
                    v.set_fixed_bit(i, v.get_bit(i));
            }
            break;
        }
        case OP_BMUL: {
            if (e->get_num_args() == 2) {
                SASSERT(e->get_num_args() == 2);
                auto& a = ev.wval(e->get_arg(0));
                auto& b = ev.wval(e->get_arg(1));
                unsigned j = 0, k = 0, zj = 0, zk = 0, hzj = 0, hzk = 0;
                // i'th bit depends on bits j + k = i
                // if the first j, resp k bits are 0, the bits j + k are 0  
                for (; j < v.bw; ++j)
                    if (!a.fixed().get(j))
                        break;
                for (; k < v.bw; ++k)
                    if (!b.fixed().get(k))
                        break;
                for (; zj < v.bw; ++zj)
                    if (!a.fixed().get(zj) || a.get_bit(zj))
                        break;
                for (; zk < v.bw; ++zk)
                    if (!b.fixed().get(zk) || b.get_bit(zk))
                        break;
                for (; hzj < v.bw; ++hzj)
                    if (!a.fixed().get(v.bw - hzj - 1) || a.get_bit(v.bw - hzj - 1))
                        break;
                for (; hzk < v.bw; ++hzk)
                    if (!b.fixed().get(v.bw - hzk - 1) || b.get_bit(v.bw - hzk - 1))
                        break;


                if (j > 0 && k > 0) {
                    for (unsigned i = 0; i < std::min(k, j); ++i)                         
                        v.set_fixed_bit(i, v.get_bit(i));                    
                }
                // lower zj + jk bits are 0
                if (zk > 0 || zj > 0) {
                    for (unsigned i = 0; i < zk + zj; ++i) {
                        SASSERT(!v.get_bit(i));
                        v.set_fixed_bit(i, false);
                    }
                }
                // upper bits are 0, if enough high order bits of a, b are 0.
                // TODO - buggy
                if (false && hzj < v.bw && hzk < v.bw && hzj + hzk > v.bw) {
                    hzj = v.bw - hzj;
                    hzk = v.bw - hzk;
                    for (unsigned i = hzj + hzk - 1; i < v.bw; ++i) {
                        SASSERT(!v.get_bit(i));
                        v.set_fixed_bit(i, false);
                    }
                }
            }
            else {
                bool pfixed = true;
                for (unsigned i = 0; i < v.bw; ++i) {
                    for (unsigned j = 0; pfixed && j < e->get_num_args(); ++j) {
                        auto& a = ev.wval(e->get_arg(j));
                        pfixed &= a.fixed().get(i);
                    }
                    if (pfixed)
                        v.set_fixed_bit(i, v.get_bit(i));
                }
            }
            break;
        }
        case OP_CONCAT: {
            unsigned bw = 0;
            for (unsigned i = e->get_num_args(); i-- > 0; ) {
                auto& a = ev.wval(e->get_arg(i));
                for (unsigned j = 0; j < a.bw; ++j)
                    if (a.fixed().get(j))
                        v.set_fixed_bit(bw + j, v.get_bit(bw + j));
                bw += a.bw;
            }
            break;
        }
        case OP_EXTRACT: {
            expr* child;
            unsigned lo, hi;
            VERIFY(bv.is_extract(e, lo, hi, child));
            auto& a = ev.wval(child);
            for (unsigned i = lo; i <= hi; ++i)
                if (a.fixed().get(i))
                    v.set_fixed_bit(i - lo, v.get_bit(i));
            break;
        }
        case OP_BNEG: {
            auto& a = ev.wval(e->get_arg(0));
            bool pfixed = true;
            for (unsigned i = 0; i < v.bw; ++i) {
                if (pfixed && a.fixed().get(i))
                    v.set_fixed_bit(i, v.get_bit(i));
                else
                    pfixed = false;
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
