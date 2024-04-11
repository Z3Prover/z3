/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    polysat_internalize.cpp

Abstract:

    PolySAT internalize

Author:

    Nikolaj Bjorner (nbjorner) 2022-01-26

--*/

#include "params/bv_rewriter_params.hpp"
#include "sat/smt/polysat_solver.h"
#include "sat/smt/euf_solver.h"

namespace polysat {

    euf::theory_var solver::mk_var(euf::enode* n) {
        theory_var v = euf::th_euf_solver::mk_var(n);
        ctx.attach_th_var(n, this, v);
        return v;
    }

    sat::literal solver::internalize(expr* e, bool sign, bool root) {
        force_push();
        SASSERT(m.is_bool(e));
        if (!visit_rec(m, e, sign, root))
            return sat::null_literal;
        sat::literal lit = expr2literal(e);
        if (sign)
            lit.neg();
        return lit;
    }

    void solver::internalize(expr* e) {
        force_push();
        visit_rec(m, e, false, false);
    }

    bool solver::visit(expr* e) {
        force_push();
        if (!is_app(e) || to_app(e)->get_family_id() != get_id()) {
            ctx.internalize(e);
            return true;
        }
        m_stack.push_back(sat::eframe(e));
        return false;
    }

    bool solver::visited(expr* e) {
        euf::enode* n = expr2enode(e);
        return n && n->is_attached_to(get_id());
    }

    bool solver::post_visit(expr* e, bool sign, bool root) {
        euf::enode* n = expr2enode(e);
        app* a = to_app(e);

        if (visited(e))
            return true;

        SASSERT(!n || !n->is_attached_to(get_id()));
        if (!n)
            n = mk_enode(e, false);

        SASSERT(!n->is_attached_to(get_id()));
        mk_var(n);
        SASSERT(n->is_attached_to(get_id()));
        internalize_polysat(a);
        return true;
    }

    void solver::internalize_polysat(app* a) {

#define if_unary(F) if (a->get_num_args() == 1) { internalize_unary(a, [&](pdd const& p) { return F(p); }); break; }

        switch (a->get_decl_kind()) {
        case OP_BMUL:             internalize_mul(a); break;
        case OP_BADD:             internalize_binary(a, [&](pdd const& p, pdd const& q) { return p + q; }); break;
        case OP_BSUB:             internalize_binary(a, [&](pdd const& p, pdd const& q) { return p - q; }); break;
        case OP_BLSHR:            internalize_lshr(a); break;
        case OP_BSHL:             internalize_shl(a); break;
        case OP_BASHR:            internalize_ashr(a); break;
        case OP_BAND:             internalize_band(a); break;
        case OP_BOR:              internalize_bor(a); break;
        case OP_BXOR:             internalize_bxor(a); break;
        case OP_BNAND:            if_unary(m_core.bnot); internalize_bnand(a); break;
        case OP_BNOR:             if_unary(m_core.bnot); internalize_bnor(a); break;
        case OP_BXNOR:            if_unary(m_core.bnot); internalize_bxnor(a); break;
        case OP_BNOT:             internalize_unary(a, [&](pdd const& p) { return m_core.bnot(p); }); break;
        case OP_BNEG:             internalize_unary(a, [&](pdd const& p) { return -p; }); break;
        case OP_MKBV:             internalize_mkbv(a); break;
        case OP_BV_NUM:           internalize_num(a); break;
        case OP_ULEQ:             internalize_le<false, false, false>(a); break;
        case OP_SLEQ:             internalize_le<true, false, false>(a); break;
        case OP_UGEQ:             internalize_le<false, true, false>(a); break;
        case OP_SGEQ:             internalize_le<true, true, false>(a); break;
        case OP_ULT:              internalize_le<false, true, true>(a); break;
        case OP_SLT:              internalize_le<true, true, true>(a); break;
        case OP_UGT:              internalize_le<false, false, true>(a); break;
        case OP_SGT:              internalize_le<true, false, true>(a); break;

        case OP_BUMUL_NO_OVFL:    internalize_binary_predicate(a, [&](pdd const& p, pdd const& q) { return ~m_core.umul_ovfl(p, q); }); break;
        case OP_BSMUL_NO_OVFL:    internalize_smul_no_ovfl(a); break;
        case OP_BSMUL_NO_UDFL:    internalize_smul_no_udfl(a); break;
            
        case OP_BUMUL_OVFL:       internalize_binary_predicate(a, [&](pdd const& p, pdd const& q) { return m_core.umul_ovfl(p, q); }); break;
        case OP_BSMUL_OVFL:
        case OP_BSDIV_OVFL:
        case OP_BNEG_OVFL:
        case OP_BUADD_OVFL:
        case OP_BSADD_OVFL:
        case OP_BUSUB_OVFL:
        case OP_BSSUB_OVFL:
            verbose_stream() << mk_pp(a, m) << "\n";
            // handled by bv_rewriter for now
            UNREACHABLE();
            break;

        case OP_BUDIV_I:          internalize_udiv_i(a); break;
        case OP_BUREM_I:          internalize_urem_i(a); break;

        case OP_BUDIV:            internalize_div_rem(a, true); break;
        case OP_BUREM:            internalize_div_rem(a, false); break;
        case OP_BSDIV0:           UNREACHABLE(); break;
        case OP_BUDIV0:           UNREACHABLE(); break;
        case OP_BSREM0:           UNREACHABLE(); break;
        case OP_BUREM0:           UNREACHABLE(); break;
        case OP_BSMOD0:           UNREACHABLE(); break;

        case OP_EXTRACT:          internalize_extract(a); break;
        case OP_CONCAT:           internalize_concat(a); break;
        case OP_ZERO_EXT:         internalize_zero_extend(a); break;
        case OP_SIGN_EXT:         internalize_sign_extend(a); break;

        case OP_BSREM:
        case OP_BSREM_I:
        case OP_BSMOD:
        case OP_BSMOD_I:
        case OP_BSDIV:
        case OP_BSDIV_I:
        case OP_BREDOR:  // x > 0               unary, return single bit, 1 if at least one input bit is set.
        case OP_BREDAND: // x == 2^K - 1        unary, return single bit, 1 if all input bits are set.
        case OP_BCOMP:   // x == y ? 1 : 0      binary, return single bit, 1 if the arguments are equal.
        case OP_ROTATE_LEFT:
        case OP_ROTATE_RIGHT:
        case OP_EXT_ROTATE_LEFT:
        case OP_EXT_ROTATE_RIGHT:
        case OP_INT2BV:
        case OP_BV2INT:
            if (bv.is_bv(a))
                expr2pdd(a);
            m_delayed_axioms.push_back(a);
            ctx.push(push_back_vector(m_delayed_axioms));
            break;

        default:
            IF_VERBOSE(0, verbose_stream() << mk_pp(a, m) << "\n");
            NOT_IMPLEMENTED_YET();
            return;
        }
#undef if_unary
    }

    class solver::mk_atom_trail : public trail {
        solver& th;
        sat::bool_var m_var;
    public:
        mk_atom_trail(sat::bool_var v, solver& th) : th(th), m_var(v) {}
        void undo() override {
            th.erase_bv2a(m_var);
        }
    };

    solver::atom* solver::mk_atom(sat::bool_var bv, signed_constraint& sc) {
        auto a = get_bv2a(bv);
        if (a)
            return a;
        auto index = m_core.register_constraint(sc, dependency(bv));
        a = new (get_region()) atom(bv, index);
        insert_bv2a(bv, a);
        ctx.push(mk_atom_trail(bv, *this));
        return a;
    }

    void solver::internalize_binary_predicate(app* e, std::function<polysat::signed_constraint(pdd, pdd)> const& fn) {
        auto p = expr2pdd(e->get_arg(0));
        auto q = expr2pdd(e->get_arg(1));
        auto sc = fn(p, q);
        sat::literal lit = expr2literal(e);
        if (lit.sign())
            sc = ~sc;
        mk_atom(lit.var(), sc);
    }

    void solver::internalize_udiv_i(app* e) {
        expr* x, * y;
        expr_ref rm(m);
        if (bv.is_bv_udivi(e, x, y))
            rm = bv.mk_bv_urem_i(x, y);
        else if (bv.is_bv_udiv(e, x, y))
            rm = bv.mk_bv_urem(x, y);
        else
            UNREACHABLE();
        internalize(rm);
    }

    // From "Hacker's Delight", section 2-2. Addition Combined with Logical Operations;
    // found via Int-Blasting paper; see https://doi.org/10.1007/978-3-030-94583-1_24
    // (p + q) - band(p, q);
    void solver::internalize_bor(app* n) {
        if (n->get_num_args() == 2) {
            expr* x, * y;
            VERIFY(bv.is_bv_or(n, x, y));
            m_core.bor(expr2pdd(x), expr2pdd(y), expr2pdd(n));
        }
        else {
            expr_ref z(n->get_arg(0), m);
            for (unsigned i = 1; i < n->get_num_args(); ++i) {
                z = bv.mk_bv_or(z, n->get_arg(i));
                ctx.internalize(z);
            }
            internalize_set(n, expr2pdd(z));
        }
    }


    // From "Hacker's Delight", section 2-2. Addition Combined with Logical Operations;
    // found via Int-Blasting paper; see https://doi.org/10.1007/978-3-030-94583-1_24
    // (p + q) - 2*band(p, q);
    void solver::internalize_bxor(app* n) {
        internalize_binary(n, [&](expr* const& x, expr* const& y) {
            return bv.mk_bv_sub(bv.mk_bv_add(x, y), bv.mk_bv_add(bv.mk_bv_and(x, y), bv.mk_bv_and(x, y)));
            });
    }

    void solver::internalize_bnor(app* n) {
        internalize_binary(n, [&](expr* const& x, expr* const& y) { return bv.mk_bv_not(bv.mk_bv_or(x, y)); });
    }

    void solver::internalize_bnand(app* n) {
        internalize_binary(n, [&](expr* const& x, expr* const& y) { return bv.mk_bv_not(bv.mk_bv_and(x, y)); });
    }

    void solver::internalize_bxnor(app* n) {
        internalize_binary(n, [&](expr* const& x, expr* const& y) { return bv.mk_bv_not(bv.mk_bv_xor(x, y)); });
    }

    void solver::internalize_band(app* n) {
        if (n->get_num_args() == 2) {
            expr* x, * y;
            VERIFY(bv.is_bv_and(n, x, y));
            m_core.band(expr2pdd(x), expr2pdd(y), expr2pdd(n));
        }
        else {
            expr_ref z(n->get_arg(0), m);
            for (unsigned i = 1; i < n->get_num_args(); ++i) {
                z = bv.mk_bv_and(z, n->get_arg(i));
                ctx.internalize(z);
            }
            internalize_set(n, expr2pdd(z));
        }
    }

    void solver::internalize_lshr(app* n) {
        expr* x, * y;
        VERIFY(bv.is_bv_lshr(n, x, y));
        m_core.lshr(expr2pdd(x), expr2pdd(y), expr2pdd(n));
    }

    void solver::internalize_ashr(app* n) {
        expr* x, * y;
        VERIFY(bv.is_bv_ashr(n, x, y));
        m_core.ashr(expr2pdd(x), expr2pdd(y), expr2pdd(n));
    }

    void solver::internalize_shl(app* n) {
        expr* x, * y;
        VERIFY(bv.is_bv_shl(n, x, y));
        m_core.shl(expr2pdd(x), expr2pdd(y), expr2pdd(n));
    }

    bool solver::propagate_delayed_axioms() {
        if (m_delayed_axioms_qhead == m_delayed_axioms.size())
            return false;
        ctx.push(value_trail(m_delayed_axioms_qhead));
        for (; m_delayed_axioms_qhead < m_delayed_axioms.size() && !inconsistent(); ++m_delayed_axioms_qhead) {
            app* e = m_delayed_axioms[m_delayed_axioms_qhead];
            expr* x, * y;
            unsigned n = 0;
            if (bv.is_bv_sdiv(e, x, y))
                axiomatize_sdiv(e, x, y);
            else if (bv.is_bv_sdivi(e, x, y))
                axiomatize_sdiv(e, x, y);
            else if (bv.is_bv_srem(e, x, y))
                axiomatize_srem(e, x, y);
            else if (bv.is_bv_sremi(e, x, y))
                axiomatize_srem(e, x, y);
            else if (bv.is_bv_smod(e, x, y))
                axiomatize_smod(e, x, y);
            else if (bv.is_bv_smodi(e, x, y))
                axiomatize_smod(e, x, y);
            else if (bv.is_redand(e, x))
                axiomatize_redand(e, x);
            else if (bv.is_redor(e, x))
                axiomatize_redor(e, x);
            else if (bv.is_comp(e, x, y))
                axiomatize_comp(e, x, y);
            else if (bv.is_rotate_left(e, n, x))
                axiomatize_rotate_left(e, n, x);
            else if (bv.is_rotate_right(e, n, x))
                axiomatize_rotate_right(e, n, x);
            else if (bv.is_ext_rotate_left(e, x, y))
                axiomatize_ext_rotate_left(e, x, y);
            else if (bv.is_ext_rotate_right(e, x, y))
                axiomatize_ext_rotate_right(e, x, y);
            else if (bv.is_bv2int(e, x))
                axiomatize_bv2int(e, x);
            else if (bv.is_int2bv(e, n, x))
                axiomatize_int2bv(e, n, x);
            else if (bv.is_extract(e))
                axioms_for_extract(e);
            else if (bv.is_concat(e))
                axioms_for_concat(e);
            else
                UNREACHABLE();
        }
        return true;
    }

    void solver::axiomatize_int2bv(app* e, unsigned sz, expr* x) {
        // e = int2bv(x)
        // bv2int(int2bv(x)) = x mod N   
        rational N = rational::power_of_two(sz);
        add_axiom("int2bv", { eq_internalize(bv.mk_bv2int(e), m_autil.mk_mod(x, m_autil.mk_int(N))) });
    }

    void solver::axiomatize_bv2int(app* e, expr* x) {
        // e := bv2int(x)
        // e = sum_bits(x)
        unsigned sz = bv.get_bv_size(x);
        expr* one = m_autil.mk_int(1);
        expr* zero = m_autil.mk_int(0);
        expr* r = zero;
        pdd p = expr2pdd(x);
        for (unsigned i = 0; i < sz; ++i)
            r = m_autil.mk_add(r, m.mk_ite(constraint2expr(m_core.bit(p, i)), one, zero));
        add_axiom("bv2int", { eq_internalize(e, r) });
    }


    expr* solver::rotate_left(app* e, unsigned n, expr* x) {
        unsigned sz = bv.get_bv_size(x);
        n = n % sz;
        if (n == 0 || sz == 1)
            return x;
        else
            return bv.mk_concat(bv.mk_extract(n, 0, x), bv.mk_extract(sz - 1, sz - n - 1, x));
    }

    void solver::axiomatize_rotate_left(app* e, unsigned n, expr* x) {
        // e = x[n : 0] ++ x[sz - 1, sz - n - 1] 
        add_axiom("rotate-left", { eq_internalize(e, rotate_left(e, n, x)) });
    }

    void solver::axiomatize_rotate_right(app* e, unsigned n, expr* x) {
        unsigned sz = bv.get_bv_size(x);
        axiomatize_rotate_left(e, sz - n, x);
    }

    void solver::axiomatize_ext_rotate_left(app* e, expr* x, expr* y) {
        unsigned sz = bv.get_bv_size(x);
        for (unsigned i = 0; i < sz; ++i)
            add_axiom("ext-rotate-left", { ~eq_internalize(bv.mk_numeral(i, sz), y), eq_internalize(e, rotate_left(e, i, x)) });
        add_axiom("ext-rotate-left", { ~mk_literal(bv.mk_ule(bv.mk_numeral(sz, sz), y)), eq_internalize(e, bv.mk_zero(sz)) });
    }

    void solver::axiomatize_ext_rotate_right(app* e, expr* x, expr* y) {
        unsigned sz = bv.get_bv_size(x);
        for (unsigned i = 0; i < sz; ++i)
            add_axiom("ext-rotate-right", { ~eq_internalize(bv.mk_numeral(i, sz), y), eq_internalize(e, rotate_left(e, sz - i, x)) });
        add_axiom("ext-rotate-right", { ~mk_literal(bv.mk_ule(bv.mk_numeral(sz, sz), y)), eq_internalize(e, bv.mk_zero(sz)) });
    }

    // x = N - 1
    void solver::axiomatize_redand(app* e, expr* x) {
        unsigned sz = bv.get_bv_size(x);
        rational N = rational::power_of_two(sz);
        equiv_axiom("redand", expr2literal(e), eq_internalize(x, bv.mk_numeral(N - 1, sz)));
    }

    void solver::axiomatize_redor(app* e, expr* x) {
        unsigned sz = bv.get_bv_size(x);
        equiv_axiom("redor", expr2literal(e), ~eq_internalize(x, bv.mk_zero(sz)));
    }

    void solver::axiomatize_comp(app* e, expr* x, expr* y) {
        unsigned sz = bv.get_bv_size(x);
        auto eq = eq_internalize(x, y);
        add_axiom("bv-comp", { ~eq, eq_internalize(e, bv.mk_numeral(1, sz)) });
        add_axiom("bv-comp", { eq, eq_internalize(e, bv.mk_numeral(0, sz)) });
    }

    // y = 0 -> x
    // else x - sdiv(x, y) * y
    void solver::axiomatize_srem(app* e, expr* x, expr* y) {
        unsigned sz = bv.get_bv_size(x);
        sat::literal y_eq0 = eq_internalize(y, bv.mk_zero(sz));
        add_axiom("srem", { ~y_eq0, eq_internalize(e, x) });
        add_axiom("srem", { y_eq0, eq_internalize(e, bv.mk_bv_sub(x, bv.mk_bv_mul(bv.mk_bv_sdiv(x, y), y))) });
    }

    // u := umod(x, y)
    // u = 0 ->  0
    // y = 0 ->  x
    // x < 0, y < 0 ->  -u
    // x < 0, y >= 0 ->  y - u
    // x >= 0, y < 0 ->  y + u
    // x >= 0, y >= 0 ->  u
    void solver::axiomatize_smod(app* e, expr* x, expr* y) {
        unsigned sz = bv.get_bv_size(x);
        expr* u = bv.mk_bv_urem(x, y);
        rational N = rational::power_of_two(bv.get_bv_size(x));
        expr_ref signx = mk_ule(bv.mk_numeral(N / 2, sz), x);
        expr_ref signy = mk_ule(bv.mk_numeral(N / 2, sz), y);
        sat::literal lsignx = mk_literal(signx);
        sat::literal lsigny = mk_literal(signy);
        sat::literal u_eq0 = eq_internalize(u, bv.mk_zero(sz));
        sat::literal y_eq0 = eq_internalize(y, bv.mk_zero(sz));
        auto name = "smod";

        add_axiom(name, { ~u_eq0, eq_internalize(e, bv.mk_zero(sz)) });
        add_axiom(name, { u_eq0, ~y_eq0, eq_internalize(e, x) });
        add_axiom(name, { ~lsignx, ~lsigny, eq_internalize(e, bv.mk_bv_neg(u)) });
        add_axiom(name, { y_eq0, ~lsignx, lsigny, eq_internalize(e, bv.mk_bv_sub(y, u)) });
        add_axiom(name, { y_eq0, lsignx, ~lsigny, eq_internalize(e, bv.mk_bv_add(y, u)) });
        add_axiom(name, { y_eq0, lsignx, lsigny, eq_internalize(e, u) });
    }

    expr_ref solver::mk_ite(expr* c, expr* t, expr* e) {
        expr_ref _c(c, m), _t(t, m), _e(e, m);
        if (m.is_true(c))
            return _t;
        if (m.is_false(c))
            return _e;
        return expr_ref(m.mk_ite(c, t, e), m);
    }

    expr_ref solver::mk_ule(expr* l, expr* r) {
        expr_ref res(bv.mk_ule(l, r), m);
        ctx.get_rewriter()(res);
        return res;
    }



    // d = udiv(abs(x), abs(y))
    // y = 0, x > 0 -> 1
    // y = 0, x <= 0 -> -1
    // x = 0, y != 0 -> 0
    // x > 0, y < 0 -> -d
    // x < 0, y > 0 -> -d
    // x > 0, y > 0 -> d
    // x < 0, y < 0 -> d
    void solver::axiomatize_sdiv(app* e, expr* x, expr* y) {
        unsigned sz = bv.get_bv_size(x);
        rational N = rational::power_of_two(bv.get_bv_size(x));
        expr_ref signx = mk_ule(bv.mk_numeral(N / 2, sz), x);
        expr_ref signy = mk_ule(bv.mk_numeral(N / 2, sz), y);
        expr_ref absx = mk_ite(signx, bv.mk_bv_neg(x), x);
        expr_ref absy = mk_ite(signy, bv.mk_bv_neg(y), y);
        expr* d = bv.mk_bv_udiv(absx, absy);
        sat::literal lsignx = mk_literal(signx);
        sat::literal lsigny = mk_literal(signy);
        sat::literal y_eq0 = eq_internalize(y, bv.mk_zero(sz));
        sat::literal x_eq0 = eq_internalize(x, bv.mk_zero(sz));
        auto name = "sdiv";
        add_axiom(name, { ~y_eq0, ~lsignx, eq_internalize(e, bv.mk_numeral(1, sz)) });
        add_axiom(name, { ~y_eq0, lsignx, eq_internalize(e, bv.mk_numeral(N - 1, sz)) });
        add_axiom(name, { y_eq0, ~x_eq0, eq_internalize(e, bv.mk_zero(sz)) });
        add_axiom(name, { y_eq0, lsignx, ~lsigny, eq_internalize(e, bv.mk_bv_neg(d)) });
        add_axiom(name, { y_eq0, ~lsignx, lsigny, eq_internalize(e, bv.mk_bv_neg(d)) });
        add_axiom(name, { y_eq0, lsignx, lsigny, eq_internalize(e, d) });
        add_axiom(name, { y_eq0, ~lsignx, ~lsigny, eq_internalize(e, d) });
    }

    void solver::internalize_urem_i(app* rem) {
        expr* x, * y;
        euf::enode* n = expr2enode(rem);
        SASSERT(n && n->is_attached_to(get_id()));
        theory_var v = n->get_th_var(get_id());
        if (m_var2pdd_valid.get(v, false))
            return;
        expr_ref quot(m);
        if (bv.is_bv_uremi(rem, x, y))
            quot = bv.mk_bv_udiv_i(x, y);
        else if (bv.is_bv_urem(rem, x, y))
            quot = bv.mk_bv_udiv(x, y);
        else
            UNREACHABLE();
        m_var2pdd_valid.setx(v, true, false);
        ctx.internalize(quot);
        m_var2pdd_valid.setx(v, false, false);
        quot_rem(quot, rem, x, y);
    }
    
    void solver::internalize_smul_no_ovfl(app* e) {
        auto x = e->get_arg(0);
        auto y = e->get_arg(1);
        auto sz = bv.get_bv_size(x);
        auto lit = mk_literal(e);
        // x' = ite(signx, -x, x)
        // y' = ite(signy, -y, y)
        // lit <=> signx != signy || (not umul_ovfl(x',y') && x'*y' < 2^{N-1})
        // expands to:
        // lit => signx != signy or not umul_ovfl(x',y')
        // lit => signx != signy or not x'*y' < 2^{N-1}
        // signx != signy => lit
        // not umul_ovfl(x',y') & x'*y' < 2^{N-1} => lit
                
        auto signx = bv.mk_slt(x, bv.mk_zero(sz));
        auto signy = bv.mk_slt(y, bv.mk_zero(sz));
        auto same_sign = eq_internalize(signx, signy);
        auto x1 = m.mk_ite(signx, bv.mk_bv_neg(x), x);
        auto y1 = m.mk_ite(signy, bv.mk_bv_neg(y), y);
        auto umul_noovfl = mk_literal(bv.mk_bvumul_no_ovfl(x1, y1));
        auto small = ~mk_literal(bv.mk_ule(bv.mk_numeral(rational::power_of_two(sz - 1), sz), bv.mk_bv_mul(x1, y1)));
        add_axiom("smul_no_ovfl", { ~lit, ~same_sign, ~umul_noovfl }, false);
        add_axiom("smul_no_ovfl", { ~lit, ~same_sign, small }, false);
        add_axiom("smul_no_ovfl", { same_sign, lit }, false);
        add_axiom("smul_no_ovfl", { umul_noovfl, ~small, lit }, false);
    }
    
    void solver::internalize_smul_no_udfl(app* e) {
        auto x = e->get_arg(0);
        auto y = e->get_arg(1);
        auto sz = bv.get_bv_size(x);
        auto lit = mk_literal(e);
        // x' = ite(signx, -x, x)
        // y' = ite(signy, -y, y)
        // lit <=> signx = signy || (not umul_ovfl(x',y') && x'*y' <= 2^{N-1})
        // expands to:
        // lit => signx = signy or not umul_ovfl(x',y')
        // lit => signx = signy or not x'*y' <= 2^{N-1}
        // signx = signy => lit
        // not umul_ovfl(x',y') & x'*y' <= 2^{N-1} => lit
                
        auto signx = bv.mk_slt(x, bv.mk_zero(sz));
        auto signy = bv.mk_slt(y, bv.mk_zero(sz));
        auto same_sign = eq_internalize(signx, signy);
        auto x1 = m.mk_ite(signx, bv.mk_bv_neg(x), x);
        auto y1 = m.mk_ite(signy, bv.mk_bv_neg(y), y);
        auto umul_noovfl = mk_literal(bv.mk_bvumul_no_ovfl(x1, y1));
        auto small = mk_literal(bv.mk_ule(bv.mk_bv_mul(x1, y1), bv.mk_numeral(rational::power_of_two(sz - 1), sz)));
        add_axiom("smul_no_udfl", { ~lit, same_sign, ~umul_noovfl }, false);
        add_axiom("smul_no_udfl", { ~lit, same_sign, small }, false);
        add_axiom("smul_no_udfl", { ~same_sign, lit }, false);
        add_axiom("smul_no_udfl", { umul_noovfl, ~small, lit }, false);
    }

    void solver::quot_rem(expr* quot, expr* rem, expr* x, expr* y) {
        pdd a = expr2pdd(x);
        pdd b = expr2pdd(y);
        auto& m = a.manager();
        unsigned sz = m.power_of_2();
        if (b.is_zero()) {
            // By SMT-LIB specification, b = 0 ==> q = -1, r = a.
            internalize_set(quot, m.mk_val(m.max_value()));
            internalize_set(rem, a);
            return;
        }
        if (b.is_one()) {
            internalize_set(quot, a);
            internalize_set(rem, m.zero());
            return;
        }

        if (a.is_val() && b.is_val()) {
            rational const av = a.val();
            rational const bv = b.val();
            SASSERT(!bv.is_zero());
            rational rv;
            rational qv = machine_div_rem(av, bv, rv);
            pdd q = m.mk_val(qv);
            pdd r = m.mk_val(rv);
            SASSERT_EQ(a, b * q + r);
            SASSERT(b.val() * q.val() + r.val() <= m.max_value());
            SASSERT(r.val() <= (b * q + r).val());
            SASSERT(r.val() < b.val());
            internalize_set(quot, q);
            internalize_set(rem, r);
            return;
        }


        // Axioms for quotient/remainder
        // 
        //      x = y*q + r
        //      multiplication does not overflow in b*q
        //      addition does not overflow in (y*q) + r; for now expressed as: r <= yq+r
        //      y ≠ 0  ==>  r < y
        //      y = 0  ==>  q = -1
        // TODO: when x,y become evaluable, can we actually propagate q,r? doesn't seem like it.
        //       Maybe we need something like an op_constraint for better propagation.

        add_axiom("quot-rem", { eq_internalize(bv.mk_bv_add(bv.mk_bv_mul(y, quot), rem), x)}, false);
        add_axiom("quot-rem", { mk_literal(bv.mk_bvumul_no_ovfl(quot, y)) }, false);
        // r <= b*q+r
        //  { apply equivalence:  p <= q  <=>  q-p <= -p-1 }
        // b*q <= -r-1
        auto minus_one = bv.mk_numeral(rational::power_of_two(sz) - 1, sz);
        auto zero = bv.mk_numeral(0, sz);
        add_axiom("quot-rem", { mk_literal(bv.mk_ule(bv.mk_bv_mul(y, quot), bv.mk_bv_sub(minus_one, rem))) }, false);
        auto c_eq = eq_internalize(y, zero);
        add_axiom("quot-rem", { c_eq, ~mk_literal(bv.mk_ule(y, rem)) }, false);
        add_axiom("quot-rem", { ~c_eq, eq_internalize(quot, minus_one) }, false);
    }

    void solver::internalize_sign_extend(app* e) {
        expr* arg = e->get_arg(0);
        unsigned sz = bv.get_bv_size(e);
        unsigned arg_sz = bv.get_bv_size(arg);
        unsigned sz2 = sz - arg_sz;
        var2pdd(expr2enode(e)->get_th_var(get_id()));
        auto name = "sign extend";
        if (arg_sz == sz)
            add_axiom(name, { eq_internalize(e, arg) });
        else {
            sat::literal lt0 = ctx.mk_literal(bv.mk_slt(arg, bv.mk_numeral(0, arg_sz)));
            // arg < 0 ==> e = concat(1...1, arg)
            // arg >= 0 ==> e = concat(0...0, arg)
            add_axiom(name, { lt0, eq_internalize(e, bv.mk_concat(bv.mk_numeral(rational::power_of_two(sz2) - 1, sz2), arg)) });
            add_axiom(name, { ~lt0, eq_internalize(e, bv.mk_concat(bv.mk_numeral(0, sz2), arg)) });
        }
    }

    void solver::internalize_zero_extend(app* e) {
        expr* arg = e->get_arg(0);
        unsigned sz = bv.get_bv_size(e);
        unsigned arg_sz = bv.get_bv_size(arg);
        unsigned sz2 = sz - arg_sz;
        var2pdd(expr2enode(e)->get_th_var(get_id()));
        auto name = "zero extend";
        if (arg_sz == sz)
            add_axiom(name, { eq_internalize(e, arg) });
        else
            // e = concat(0...0, arg)
            add_axiom(name, { eq_internalize(e, bv.mk_concat(bv.mk_numeral(0, sz2), arg)) });
    }

    void solver::internalize_div_rem(app* e, bool is_div) {
        bv_rewriter_params p(s().params());
        if (p.hi_div0()) {
            if (is_div)
                internalize_udiv_i(e);
            else
                internalize_urem_i(e);
            return;
        }
        expr* arg1 = e->get_arg(0);
        expr* arg2 = e->get_arg(1);
        unsigned sz = bv.get_bv_size(e);
        expr_ref zero(bv.mk_numeral(0, sz), m);
        sat::literal eqZ = eq_internalize(arg2, zero);
        sat::literal eqU = eq_internalize(e, is_div ? bv.mk_bv_udiv0(arg1) : bv.mk_bv_urem0(arg1));
        sat::literal eqI = eq_internalize(e, is_div ? bv.mk_bv_udiv_i(arg1, arg2) : bv.mk_bv_urem_i(arg1, arg2));
        auto name = "div-rem";
        add_axiom(name, { ~eqZ, eqU });
        add_axiom(name, { eqZ, eqI });
        ctx.add_aux(~eqZ, eqU);
        ctx.add_aux(eqZ, eqI);
    }

    void solver::internalize_num(app* a) {
        rational val;
        unsigned sz = 0;
        VERIFY(bv.is_numeral(a, val, sz));
        auto p = m_core.value(val, sz);
        internalize_set(a, p);
    }

    void solver::internalize_mul(app* a) {
        vector<dd::pdd> args;
        for (expr* arg : *to_app(a))
            args.push_back(expr2pdd(arg));
        if (args.size() == 1) {
            internalize_set(a, args[0]);
            return;
        }
        if (args.size() == 2 && args[0].is_val()) {
            internalize_set(a, args[0] * args[1]);
            return;
        }
        if (args.size() == 2 && args[1].is_val()) {
            internalize_set(a, args[0] * args[1]);
            return;
        }
        auto pv = m_core.mul(args.size(), args.data());
        m_pddvar2var.setx(pv, get_th_var(a), UINT_MAX);
        internalize_set(a, m_core.var(pv));
    }

    // TODO - test that internalize works with recursive call on bit2bool
    void solver::internalize_mkbv(app* a) {
        unsigned i = 0;
        for (expr* arg : *a) {
            expr_ref b2b(m);
            b2b = bv.mk_bit2bool(a, i);
            sat::literal bit_i = ctx.internalize(b2b, false, false);
            sat::literal lit = expr2literal(arg);
            equiv_axiom("mkbv", lit, bit_i);
#if 0
            ctx.add_aux_equiv(lit, bit_i);
#endif
            ++i;
        }
    }

    void solver::internalize_extract(app* e) {
        ensure_pdd_var(e->get_arg(0));
        m_delayed_axioms.push_back(e);
        ctx.push(push_back_vector(m_delayed_axioms));
        var2pdd(expr2enode(e)->get_th_var(get_id()));
    }

    // x[hi:lo] = 0 or x >= 2^lo
    // x[w-1:lo] = 0 => x < 2^lo
    void solver::axioms_for_extract(app* e) {
        unsigned hi, lo;
        expr* x;
        VERIFY(bv.is_extract(e, lo, hi, x));
        auto sz_e = hi - lo + 1;
        auto sz_x = bv.get_bv_size(x);
        auto eq0 = eq_internalize(e, bv.mk_numeral(0, sz_e));
        auto gelo = mk_literal(bv.mk_ule(bv.mk_numeral(rational::power_of_two(lo), sz_x), x));
        auto name = "extract";
        add_axiom(name, { eq0, gelo });
        if (hi + 1 == sz_x)
            add_axiom(name, { ~eq0, ~gelo });
    }

    // e = hi lo
    // hi = 0 <=> e < 2^|lo|
    void solver::axioms_for_concat(app* e) {    
        if (e->get_num_args() == 2) {
            expr* hi = e->get_arg(0);
            auto sz_e = bv.get_bv_size(e);
            auto sz_h = bv.get_bv_size(hi);
            auto eq0 = eq_internalize(hi, bv.mk_numeral(0, sz_h));
            auto gtlo = ~mk_literal(bv.mk_ule(bv.mk_numeral(rational::power_of_two(sz_e - sz_h), sz_e), e));
            add_axiom("hi = 0 => concat(hi, lo) < 2^|lo|", { ~eq0, gtlo });
            add_axiom("concat(hi, lo) < 2^|lo| => hi = 0", { eq0, ~gtlo });
        }
        else {
            expr* last = e->get_arg(e->get_num_args() - 1);
            for (unsigned i = e->get_num_args() - 1; i-- > 0; )
                last = bv.mk_concat(e->get_arg(i), last);
            add_axiom("concat-assoc", { eq_internalize(e, last) });
        }
    }

    void solver::ensure_pdd_var(expr* e) {
        auto n = expr2enode(e);
        auto v = n->get_th_var(get_id());
        auto q = var2pdd(v);
        if (q.is_val() || q.is_var())
            return;
        unsigned bv_size = get_bv_size(v);
        pvar pv = m_core.add_var(bv_size);
        pdd p = m_core.var(pv);
        ctx.push(vector_value_trail(m_var2pdd, v));
        m_pddvar2var.setx(pv, v, UINT_MAX);
        m_var2pdd[v] = p;
        auto sc = m_core.eq(p, q);
        dependency d = dependency::axiom();
        auto idx = m_core.register_constraint(sc, d);
        TRACE("bv", tout << "add definition for " << mk_pp(e, m) << " " << p << ": " << sc << "\n";);
        m_core.assign_eh(idx, false);
    }

    //
    // subterms under concatentation and extract need to be variables or constants such that 
    // viable can perform proper slices.
    //
    void solver::internalize_concat(app* e) {
        SASSERT(bv.is_concat(e));
        for (auto arg : *e)
            ensure_pdd_var(arg);        
        m_delayed_axioms.push_back(e);
        ctx.push(push_back_vector(m_delayed_axioms));
        var2pdd(expr2enode(e)->get_th_var(get_id()));
    }

    void solver::internalize_par_unary(app* e, std::function<pdd(pdd, unsigned)> const& fn) {
        pdd const p = expr2pdd(e->get_arg(0));
        unsigned const par = e->get_parameter(0).get_int();
        internalize_set(e, fn(p, par));
    }

    void solver::internalize_binary(app* e, std::function<pdd(pdd, pdd)> const& fn) {
        SASSERT(e->get_num_args() >= 1);
        auto p = expr2pdd(e->get_arg(0));
        for (unsigned i = 1; i < e->get_num_args(); ++i)
            p = fn(p, expr2pdd(e->get_arg(i)));
        internalize_set(e, p);
    }

    void solver::internalize_binary(app* e, std::function<expr* (expr*, expr*)> const& fn) {
        SASSERT(e->get_num_args() >= 1);
        expr* r = e->get_arg(0);
        for (unsigned i = 1; i < e->get_num_args(); ++i)
            r = fn(r, e->get_arg(i));
        ctx.internalize(r);
        internalize_set(e, var2pdd(expr2enode(r)->get_th_var(get_id())));
    }

    void solver::internalize_unary(app* e, std::function<pdd(pdd)> const& fn) {
        SASSERT(e->get_num_args() == 1);
        auto p = expr2pdd(e->get_arg(0));
        internalize_set(e, fn(p));
    }

    template<bool Signed, bool Rev, bool Negated>
    void solver::internalize_le(app* e) {
        SASSERT(e->get_num_args() == 2);
        auto p = expr2pdd(e->get_arg(0));
        auto q = expr2pdd(e->get_arg(1));
        if (Rev)
            std::swap(p, q);
        auto sc = Signed ? m_core.sle(p, q) : m_core.ule(p, q);
        if (Negated)
            sc = ~sc;

        sat::literal lit = expr2literal(e);
        if (lit.sign())
            sc = ~sc;
        mk_atom(lit.var(), sc);
    }

    pdd solver::mk_ite(signed_constraint const& sc, pdd const& p, pdd const& q) {
        expr_ref cond = constraint2expr(sc);
        expr_ref th = pdd2expr(p);
        expr_ref el = pdd2expr(q);
        expr* ite = m.mk_ite(cond, th, el);
        ctx.internalize(ite);
        euf::enode* n = expr2enode(ite);
        if (!n->is_attached_to(get_id())) {
            auto v = mk_var(n);
            pvar r = m_core.add_var(bv.get_bv_size(th));
            internalize_set(v, m_core.var(r));
        }
        return expr2pdd(ite);
    }

    pdd solver::mk_zero_extend(unsigned n, pdd const& p) {
        expr_ref pe = pdd2expr(p);
        auto ze = bv.mk_zero_extend(n, pe);
        ctx.internalize(ze);
        return expr2pdd(ze);
    }

    dd::pdd solver::expr2pdd(expr* e) {
        return var2pdd(get_th_var(e));
    }

    dd::pdd solver::var2pdd(euf::theory_var v) {
        if (!m_var2pdd_valid.get(v, false)) {
            unsigned bv_size = get_bv_size(v);
            pvar pv = m_core.add_var(bv_size);
            m_pddvar2var.setx(pv, v, UINT_MAX);
            pdd p = m_core.var(pv);
            internalize_set(v, p);
            return p;
        }
        return m_var2pdd[v];
    }

    void solver::apply_sort_cnstr(euf::enode* n, sort* s) {
        if (!bv.is_bv(n->get_expr()))
            return;
        theory_var v = n->get_th_var(get_id());
        if (v == euf::null_theory_var)
            v = mk_var(n);
        var2pdd(v);
    }

    void solver::internalize_set(expr* e, pdd const& p) {
        internalize_set(get_th_var(e), p);
    }

    void solver::internalize_set(euf::theory_var v, pdd const& p) {
        SASSERT_EQ(get_bv_size(v), p.power_of_2());
        m_var2pdd.reserve(get_num_vars(), p);
        m_var2pdd_valid.reserve(get_num_vars(), false);
        ctx.push(set_bitvector_trail(m_var2pdd_valid, v));
        m_var2pdd[v].reset(p.manager());
        m_var2pdd[v] = p;
    }

    void solver::eq_internalized(euf::enode* n) {
        SASSERT(m.is_eq(n->get_expr()));
    }

    struct solver::undo_add_eq : public trail {
        solver& s;
        unsigned sz;
        unsigned index;
    public:
        undo_add_eq(solver& s, unsigned sz, unsigned i) : s(s), sz(sz), index(i) {}
        void undo() override {
            SASSERT(index == s.m_eqs.back().index());
            s.m_eq2constraint[sz].remove(index);
            s.m_eqs.pop_back();
        }
    };

    constraint_id solver::eq_constraint(pdd p, pdd q, bool sign, dependency d) {
        pdd r = p - q;
        constraint_id idx;
        std::pair<constraint_id, bool> elem;
        bool is_new = true;
        unsigned sz = r.manager().power_of_2();
        m_eq2constraint.reserve(sz + 1);
        if (m_eq2constraint[sz].find(r.index(), elem)) {
            if (elem.second == sign)
                return elem.first;
            is_new = false;
        }
        auto sc = m_core.eq(p, q);
        idx = m_core.register_constraint(sc, d);
        if (is_new) {
            m_eq2constraint[sz].insert(r.index(), { idx, sign });
            m_eqs.push_back(r);
            ctx.push(undo_add_eq(*this, sz, r.index()));
        }
        return idx;
    }


}