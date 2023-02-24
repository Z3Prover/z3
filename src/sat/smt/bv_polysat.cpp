/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    bv_polysat.cpp

Abstract:

    PolySAT interface to bit-vector

Author:

    Nikolaj Bjorner (nbjorner) 2022-01-26

Notes:
- equality propagation from polysat?
- reuse bit propagation from bv-solver?
- finish other bit-vector operations
- introduce gradual bit-blasting?

--*/

#include "params/bv_rewriter_params.hpp"
#include "sat/smt/bv_solver.h"
#include "sat/smt/euf_solver.h"
#include "math/polysat/solver.h"

namespace bv {

    typedef polysat::pdd pdd;

    void solver::internalize_polysat(app* a) {

#define if_unary(F) if (a->get_num_args() == 1) { polysat_unary(a, [&](pdd const& p) { return F(p); }); break; }

        switch (to_app(a)->get_decl_kind()) {
        case OP_BMUL:             polysat_binary(a, [&](pdd const& p, pdd const& q) { return p * q; }); break;
        case OP_BADD:             polysat_binary(a, [&](pdd const& p, pdd const& q) { return p + q; }); break;
        case OP_BSUB:             polysat_binary(a, [&](pdd const& p, pdd const& q) { return p - q; }); break;
        case OP_BLSHR:            polysat_binary(a, [&](pdd const& p, pdd const& q) { return m_polysat.lshr(p, q); }); break;
        case OP_BSHL:             polysat_binary(a, [&](pdd const& p, pdd const& q) { return m_polysat.shl(p, q); }); break;
        case OP_BAND:             polysat_binary(a, [&](pdd const& p, pdd const& q) { return m_polysat.band(p, q); }); break;
        case OP_BOR:              polysat_binary(a, [&](pdd const& p, pdd const& q) { return m_polysat.bor(p, q); }); break;
        case OP_BXOR:             polysat_binary(a, [&](pdd const& p, pdd const& q) { return m_polysat.bxor(p, q); }); break;
        case OP_BNAND:            if_unary(m_polysat.bnot); polysat_binary(a, [&](pdd const& p, pdd const& q) { return m_polysat.bnand(p, q); }); break;
        case OP_BNOR:             if_unary(m_polysat.bnot); polysat_binary(a, [&](pdd const& p, pdd const& q) { return m_polysat.bnor(p, q); }); break;
        case OP_BXNOR:            if_unary(m_polysat.bnot); polysat_binary(a, [&](pdd const& p, pdd const& q) { return m_polysat.bxnor(p, q); }); break;
        case OP_BNOT:             polysat_unary(a, [&](pdd const& p) { return m_polysat.bnot(p); }); break;

        case OP_BNEG:             polysat_unary(a, [&](pdd const& p) { return -p; }); break;
        case OP_MKBV:             polysat_mkbv(a); break;
        case OP_BV_NUM:           polysat_num(a); break;
            
        case OP_ULEQ:             polysat_le<false, false, false>(a); break;
        case OP_SLEQ:             polysat_le<true,  false, false>(a); break;
        case OP_UGEQ:             polysat_le<false, true,  false>(a); break;
        case OP_SGEQ:             polysat_le<true,  true,  false>(a); break;
        case OP_ULT:              polysat_le<false, true,  true>(a); break;
        case OP_SLT:              polysat_le<true,  true,  true>(a); break;
        case OP_UGT:              polysat_le<false, false, true>(a); break;
        case OP_SGT:              polysat_le<true,  false, true>(a); break;

        case OP_BUMUL_NO_OVFL:    polysat_binaryc(a, [&](pdd const& p, pdd const& q) { return m_polysat.umul_ovfl(p, q); }); break;
        case OP_BSMUL_NO_OVFL:    polysat_binaryc(a, [&](pdd const& p, pdd const& q) { return m_polysat.smul_ovfl(p, q); }); break;
        case OP_BSMUL_NO_UDFL:    polysat_binaryc(a, [&](pdd const& p, pdd const& q) { return m_polysat.smul_udfl(p, q); }); break;
            
        case OP_BUDIV_I:          polysat_div_rem_i(a, true); break;       
        case OP_BUREM_I:          polysat_div_rem_i(a, false); break;

        case OP_BUDIV:            polysat_div_rem(a, true); break;            
        case OP_BUREM:            polysat_div_rem(a, false); break;
        case OP_BSDIV0:           break;
        case OP_BUDIV0:           break;
        case OP_BSREM0:           break;
        case OP_BUREM0:           break;
        case OP_BSMOD0:           break;

            // polysat::solver should also support at least:
        case OP_BREDAND: // x == 2^K - 1
        case OP_BREDOR:  // x > 0
        case OP_BSDIV:            
        case OP_BSREM:            
        case OP_BSMOD:     
        case OP_BSDIV_I:            
        case OP_BSREM_I:                        
        case OP_BSMOD_I:
        case OP_BASHR:
        case OP_BCOMP:
        case OP_SIGN_EXT:
        case OP_ZERO_EXT:
        case OP_CONCAT:
        case OP_EXTRACT:
            std::cout << mk_pp(a, m) << "\n";
            NOT_IMPLEMENTED_YET();
            return;
        default:
            std::cout << "fall back to circuit " << mk_pp(a, m) << "\n";
            NOT_IMPLEMENTED_YET();
            return;
#if 0
            // TODO: this path leads to segfault / floating point exception
            internalize_circuit(a);
            break;            
#endif
        }
#undef if_unary
    }

    void solver::polysat_binaryc(app* e, std::function<polysat::signed_constraint(polysat::pdd, polysat::pdd)> const& fn) {
        auto p = expr2pdd(e->get_arg(0));
        auto q = expr2pdd(e->get_arg(1));
        auto sc = ~fn(p, q);
        sat::literal lit = expr2literal(e);
        atom* a = mk_atom(lit.var());
        a->m_sc = sc;
    }

    void solver::polysat_div_rem_i(app* e, bool is_div) {
        auto p = expr2pdd(e->get_arg(0));
        auto q = expr2pdd(e->get_arg(1));
        auto [quot, rem] = m_polysat.quot_rem(p, q);
        polysat_set(e, is_div ? quot : rem);        
    }

    void solver::polysat_div_rem(app* e, bool is_div) {
        bv_rewriter_params p(s().params());
        if (p.hi_div0()) {
            polysat_div_rem_i(e, is_div);
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

    void solver::polysat_num(app* a) {
        numeral val;
        unsigned sz = 0;
        VERIFY(bv.is_numeral(a, val, sz));
        auto p = m_polysat.value(val, sz);
        polysat_set(a, p);
    }

    // TODO - test that internalize works with recursive call on bit2bool
    void solver::polysat_mkbv(app* a) {
        unsigned i = 0;
        for (expr* arg : *a) {
            expr_ref b2b(m);
            b2b = bv.mk_bit2bool(a, i);            
            sat::literal bit_i = ctx.internalize(b2b, false, false);
            sat::literal lit = expr2literal(arg);
            add_equiv(lit, bit_i);
            ctx.add_aux_equiv(lit, bit_i);
            ++i;
        }
    }

    void solver::polysat_binary(app* e, std::function<polysat::pdd(polysat::pdd, polysat::pdd)> const& fn) {
        SASSERT(e->get_num_args() >= 1);
        auto p = expr2pdd(e->get_arg(0));
        for (unsigned i = 1; i < e->get_num_args(); ++i) 
            p = fn(p, expr2pdd(e->get_arg(i)));
        polysat_set(e, p);
    }

    void solver::polysat_unary(app* e, std::function<polysat::pdd(polysat::pdd)> const& fn) {
        SASSERT(e->get_num_args() == 1);
        auto p = expr2pdd(e->get_arg(0));
        polysat_set(e, fn(p));
    }

    template<bool Signed, bool Rev, bool Negated>
    void solver::polysat_le(app* e) {
        auto p = expr2pdd(e->get_arg(0));
        auto q = expr2pdd(e->get_arg(1));
        if (Rev)
            std::swap(p, q);
        
        auto sc = Signed ? m_polysat.sle(p, q) : m_polysat.ule(p, q);
        if (Negated)
            sc = ~sc;
        
        sat::literal lit = expr2literal(e);
        atom* a = mk_atom(lit.var());
        a->m_sc = sc;
    }

    void solver::polysat_bit2bool(atom* a, expr* e, unsigned idx) {
        if (!use_polysat())
            return;
        pdd p = expr2pdd(e);
        a->m_sc = m_polysat.bit(p, idx);
    }

    void solver::polysat_assign(atom* a) {
        polysat::signed_constraint sc = a->m_sc;
        if (!sc)
            return;
        SASSERT(s().value(a->m_bv) != l_undef);
        bool sign = l_false == s().value(a->m_bv);
        sat::literal lit(a->m_bv, sign);
        if (sign)
            sc = ~sc;
        m_polysat.assign_eh(sc, polysat::dependency(1 + 2*lit.index()));
    }

    bool solver::polysat_merge_eh(theory_var r1, theory_var r2, theory_var v1, theory_var v2) {
        if (!use_polysat())
            return false;
        pdd p = var2pdd(r1);
        pdd q = var2pdd(r2);
        auto sc = m_polysat.eq(p, q);
        m_var_eqs.setx(m_var_eqs_head, std::make_pair(v1, v2), std::make_pair(v1, v2));
        ctx.push(value_trail<unsigned>(m_var_eqs_head));        
        m_polysat.assign_eh(sc, polysat::dependency(2 * m_var_eqs_head)); 
        m_var_eqs_head++;
        return true;
    }

    bool solver::polysat_diseq_eh(euf::th_eq const& ne) {
        if (!use_polysat())
            return false;
        euf::theory_var v1 = ne.v1(), v2 = ne.v2();
        pdd p = var2pdd(v1);
        pdd q = var2pdd(v2);
        auto sc = ~m_polysat.eq(p, q);
        sat::literal neq = ~expr2literal(ne.eq());
        m_polysat.assign_eh(sc, polysat::dependency(1 + 2 * neq.index()));
        return true;
    }

    void solver::polysat_propagate() {
        if (!use_polysat())
            return;
        lbool r = m_polysat.unit_propagate();
        if (r == l_false)
            polysat_core();
    }

    lbool solver::polysat_final() {
        if (!use_polysat())
            return l_true;
        lbool r = m_polysat.check_sat();
        if (r == l_false) 
            polysat_core();
        return r;
    }

    void solver::polysat_core() {
        polysat::dependency_vector deps;
        sat::literal_vector core;
        euf::enode_pair_vector eqs;
        m_polysat.unsat_core(deps);
        for (auto n : deps) {
            if (0 != (n.val() & 1))
                core.push_back(sat::to_literal(n.val() / 2));
            else {
                auto [v1, v2] = m_var_eqs[n.val() / 2];
                eqs.push_back(euf::enode_pair(var2enode(v1), var2enode(v2)));
            }
        }
        auto ex = mk_bv2ext_justification(core, eqs);
        ctx.set_conflict(ex);
    }

    polysat::pdd solver::expr2pdd(expr* e) {
        return var2pdd(get_th_var(e));
    }

    polysat::pdd solver::var2pdd(euf::theory_var v) {
        if (!m_var2pdd_valid.get(v, false)) {
            unsigned bv_size = get_bv_size(v);
            polysat::pvar pv = m_polysat.add_var(bv_size);
            m_pddvar2var.setx(pv, v, UINT_MAX);
            pdd p = m_polysat.var(pv);
            polysat_set(v, p);
#ifndef NDEBUG
            // expr* e = var2enode(v)->get_expr();
            // std::cerr << "var2pdd:     " << mk_ismt2_pp(e, m) << " -> " << p << std::endl;
#endif
            return p;
        }
        return m_var2pdd[v];
    }

    bool solver::polysat_sort_cnstr(euf::enode* n) {
        if (!use_polysat())
            return false;
        if (!bv.is_bv(n->get_expr()))
            return false;
        theory_var v = n->get_th_var(get_id());
        if (v == euf::null_theory_var) 
            v = mk_var(n);
        var2pdd(v);
        return true;
    }

    void solver::polysat_set(expr* e, pdd const& p) {
        polysat_set(get_th_var(e), p);
    }

    void solver::polysat_set(euf::theory_var v, pdd const& p) {
        m_var2pdd.reserve(get_num_vars(), p);
        m_var2pdd_valid.reserve(get_num_vars(), false);
        ctx.push(set_bitvector_trail(m_var2pdd_valid, v));
        m_var2pdd[v] = p;
#ifndef NDEBUG
        // expr* e = var2enode(v)->get_expr();
        // std::cerr << "polysat_set: " << mk_ismt2_pp(e, m) << " -> " << p << std::endl;
#endif
    }

    void solver::polysat_pop(unsigned n) {
        if (!use_polysat())
            return;
        m_polysat.pop(n);
    }

    void solver::polysat_push() {
        if (!use_polysat())
            return;
        m_polysat.push();
    }

    void solver::polysat_add_value(euf::enode* n, model& mdl, expr_ref_vector& values) {
        auto p = expr2pdd(n->get_expr());
        rational val;
        VERIFY(m_polysat.try_eval(p, val));
        values[n->get_root_id()] = bv.mk_numeral(val, get_bv_size(n));        
    }   

    void solver::polysat_display(std::ostream& out) const {
        if (!use_polysat())
            return;
        m_polysat.display(out);
        for (unsigned v = 0; v < get_num_vars(); ++v) 
            if (m_var2pdd_valid.get(v, false))
                out << ctx.bpp(var2enode(v)) << " := " << m_var2pdd[v] << "\n";        
    }
}
