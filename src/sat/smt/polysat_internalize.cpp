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
        case OP_BMUL:             internalize_binary(a, [&](pdd const& p, pdd const& q) { return p * q; }); break;
        case OP_BADD:             internalize_binary(a, [&](pdd const& p, pdd const& q) { return p + q; }); break;
        case OP_BSUB:             internalize_binary(a, [&](pdd const& p, pdd const& q) { return p - q; }); break;
        case OP_BLSHR:            internalize_binary(a, [&](pdd const& p, pdd const& q) { return m_core.lshr(p, q); }); break;
        case OP_BSHL:             internalize_binary(a, [&](pdd const& p, pdd const& q) { return m_core.shl(p, q); }); break;
        case OP_BAND:             internalize_binary(a, [&](pdd const& p, pdd const& q) { return m_core.band(p, q); }); break;
        case OP_BOR:              internalize_binary(a, [&](pdd const& p, pdd const& q) { return m_core.bor(p, q); }); break;
        case OP_BXOR:             internalize_binary(a, [&](pdd const& p, pdd const& q) { return m_core.bxor(p, q); }); break;
        case OP_BNAND:            if_unary(m_core.bnot); internalize_binary(a, [&](pdd const& p, pdd const& q) { return m_core.bnand(p, q); }); break;
        case OP_BNOR:             if_unary(m_core.bnot); internalize_binary(a, [&](pdd const& p, pdd const& q) { return m_core.bnor(p, q); }); break;
        case OP_BXNOR:            if_unary(m_core.bnot); internalize_binary(a, [&](pdd const& p, pdd const& q) { return m_core.bxnor(p, q); }); break;
        case OP_BNOT:             internalize_unary(a, [&](pdd const& p) { return m_core.bnot(p); }); break;
        case OP_BNEG:             internalize_unary(a, [&](pdd const& p) { return -p; }); break;
        case OP_MKBV:             internalize_mkbv(a); break;
        case OP_BV_NUM:           internalize_num(a); break;
        case OP_ULEQ:             internalize_le<false, false, false>(a); break;
        case OP_SLEQ:             internalize_le<true,  false, false>(a); break;
        case OP_UGEQ:             internalize_le<false, true,  false>(a); break;
        case OP_SGEQ:             internalize_le<true,  true,  false>(a); break;
        case OP_ULT:              internalize_le<false, true,  true>(a); break;
        case OP_SLT:              internalize_le<true,  true,  true>(a); break;
        case OP_UGT:              internalize_le<false, false, true>(a); break;
        case OP_SGT:              internalize_le<true,  false, true>(a); break;

        case OP_BUMUL_NO_OVFL:    internalize_binaryc(a, [&](pdd const& p, pdd const& q) { return m_core.umul_ovfl(p, q); }); break;
        case OP_BSMUL_NO_OVFL:    internalize_binaryc(a, [&](pdd const& p, pdd const& q) { return m_core.smul_ovfl(p, q); }); break;
        case OP_BSMUL_NO_UDFL:    internalize_binaryc(a, [&](pdd const& p, pdd const& q) { return m_core.smul_udfl(p, q); }); break;

        case OP_BUMUL_OVFL:
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
        case OP_ZERO_EXT:         internalize_par_unary(a, [&](pdd const& p, unsigned sz) { return m_core.zero_ext(p, sz); }); break;
        case OP_SIGN_EXT:         internalize_par_unary(a, [&](pdd const& p, unsigned sz) { return m_core.sign_ext(p, sz); }); break;

            // polysat::solver should also support at least:
        case OP_BREDAND: // x == 2^K - 1        unary, return single bit, 1 if all input bits are set.
        case OP_BREDOR:  // x > 0               unary, return single bit, 1 if at least one input bit is set.
        case OP_BCOMP:   // x == y              binary, return single bit, 1 if the arguments are equal.
        case OP_BSDIV:            
        case OP_BSREM:            
        case OP_BSMOD:     
        case OP_BSDIV_I:            
        case OP_BSREM_I:                        
        case OP_BSMOD_I:
        case OP_BASHR:
            IF_VERBOSE(0, verbose_stream() << mk_pp(a, m) << "\n");
            NOT_IMPLEMENTED_YET();
            return;
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

    void solver::mk_atom(sat::bool_var bv, signed_constraint& sc) {
        if (get_bv2a(bv))
            return;
        sat::literal lit(bv, false);
        auto index = m_core.register_constraint(sc, dependency(lit, 0));
        auto a = new (get_region()) atom(bv, index);
        insert_bv2a(bv, a);
        ctx.push(mk_atom_trail(bv, *this));
    }

    void solver::internalize_binaryc(app* e, std::function<polysat::signed_constraint(pdd, pdd)> const& fn) {
        auto p = expr2pdd(e->get_arg(0));
        auto q = expr2pdd(e->get_arg(1));
        auto sc = ~fn(p, q);
        sat::literal lit = expr2literal(e);
        if (lit.sign())
            sc = ~sc;
        mk_atom(lit.var(), sc);
    }

    void solver::internalize_udiv_i(app* e) {
        expr* x, *y;
        VERIFY(bv.is_bv_udivi(e, x, y) || bv.is_bv_udiv(e, x, y));
        app_ref rm(bv.mk_bv_urem_i(x, y), m);
        internalize(rm);
    }

    void solver::internalize_urem_i(app* e) {
        expr* x, *y;
        if (expr2enode(e))
            return;
        VERIFY(bv.is_bv_uremi(e, x, y) || bv.is_bv_urem(e, x, y));
        auto [quot, rem] = quot_rem(x, y);
        internalize_set(e, rem);
        internalize_set(bv.mk_bv_udiv_i(x, y), quot);
    }

    std::pair<pdd, pdd> solver::quot_rem(expr* x, expr* y) {
        pdd a = expr2pdd(x);
        pdd b = expr2pdd(y);
        auto& m = a.manager();
        unsigned sz = m.power_of_2();
        if (b.is_zero())
            // By SMT-LIB specification, b = 0 ==> q = -1, r = a.
            return { m.mk_val(m.max_value()), a };

        if (b.is_one())
            return { a, m.zero() };

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
            return { std::move(q), std::move(r) };
        }
        
        expr* quot = bv.mk_bv_udiv_i(x, y);
        expr* rem = bv.mk_bv_urem_i(x, y);

        ctx.internalize(quot);
        ctx.internalize(rem);
        auto quotv = expr2enode(quot)->get_th_var(get_id());
        auto remv  = expr2enode(rem)->get_th_var(get_id());

        pdd q = var2pdd(quotv);
        pdd r = var2pdd(remv);

        // Axioms for quotient/remainder
        // 
        //      a = b*q + r
        //      multiplication does not overflow in b*q
        //      addition does not overflow in (b*q) + r; for now expressed as: r <= bq+r
        //      b ≠ 0  ==>  r < b
        //      b = 0  ==>  q = -1
        // TODO: when a,b become evaluable, can we actually propagate q,r? doesn't seem like it.
        //       Maybe we need something like an op_constraint for better propagation.
        add_polysat_clause("[axiom] quot_rem 1", { m_core.eq(b * q + r - a) }, false);
        add_polysat_clause("[axiom] quot_rem 2", { ~m_core.umul_ovfl(b, q) }, false);
        // r <= b*q+r
        //  { apply equivalence:  p <= q  <=>  q-p <= -p-1 }
        // b*q <= -r-1
        add_polysat_clause("[axiom] quot_rem 3", { m_core.ule(b * q, -r - 1) }, false);

        auto c_eq = m_core.eq(b);
        if (!c_eq.is_always_true())
            add_polysat_clause("[axiom] quot_rem 4", { c_eq, ~m_core.ule(b, r) }, false);
        if (!c_eq.is_always_false())
            add_polysat_clause("[axiom] quot_rem 5", { ~c_eq, m_core.eq(q + 1) }, false);

        return { std::move(q), std::move(r) };
    }

    void solver::internalize_div_rem(app* e, bool is_div) {
        bv_rewriter_params p(s().params());
        if (p.hi_div0()) {
            if (bv.is_bv_udivi(e))
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
        add_clause(~eqZ, eqU);
        add_clause(eqZ, eqI);
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

    // TODO - test that internalize works with recursive call on bit2bool
    void solver::internalize_mkbv(app* a) {
        unsigned i = 0;
        for (expr* arg : *a) {
            expr_ref b2b(m);
            b2b = bv.mk_bit2bool(a, i);            
            sat::literal bit_i = ctx.internalize(b2b, false, false);
            sat::literal lit = expr2literal(arg);
            add_equiv(lit, bit_i);
#if 0
            ctx.add_aux_equiv(lit, bit_i);
#endif
            ++i;
        }
    }

    void solver::internalize_extract(app* e) {
        unsigned const hi = bv.get_extract_high(e);
        unsigned const lo = bv.get_extract_low(e);
        auto const src = expr2pdd(e->get_arg(0));
        auto const p = m_core.extract(src, hi, lo);
        SASSERT_EQ(p.power_of_2(), hi - lo + 1);
        internalize_set(e, p);
    }

    void solver::internalize_concat(app* e) {
        SASSERT(bv.is_concat(e));
        vector<pdd> args;
        for (expr* arg : *e)
            args.push_back(expr2pdd(arg));
        auto const p = m_core.concat(args.size(), args.data());
        internalize_set(e, p);
    }

    void solver::internalize_par_unary(app* e, std::function<pdd(pdd,unsigned)> const& fn) {
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
#if 0
        m_var2pdd[v].reset(p.manager());
#endif
        m_var2pdd[v] = p;
    }

    void solver::eq_internalized(euf::enode* n) {
        SASSERT(m.is_eq(n->get_expr()));
    }


}
