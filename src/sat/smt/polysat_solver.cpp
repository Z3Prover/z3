/*---
Copyright (c 2022 Microsoft Corporation

Module Name:

    polysat_solver.cpp

Abstract:

    PolySAT interface to bit-vector

Author:

    Nikolaj Bjorner (nbjorner) 2022-01-26

Notes:
The solver adds literals to polysat::core, calls propagation and check
The result of polysat::core::check is one of:
- is_sat: the model is complete
- is_unsat: there is a Boolean conflict. The SAT solver backtracks and resolves the conflict.
- new_eq: the solver adds a new equality literal to the SAT solver.
- new_lemma: there is a conflict, but it is resolved by backjumping and adding a lemma to the SAT solver.
- giveup: Polysat was unable to determine satisfiability.

--*/

#include "ast/euf/euf_bv_plugin.h"
#include "sat/smt/polysat_solver.h"
#include "sat/smt/euf_solver.h"
#include "sat/smt/polysat/polysat_ule.h"
#include "sat/smt/polysat/polysat_umul_ovfl.h"


namespace polysat {

    solver::solver(euf::solver& ctx, theory_id id):
        euf::th_euf_solver(ctx, symbol("bv"), id),
        bv(ctx.get_manager()),
        m_autil(ctx.get_manager()),
        m_core(*this),
        m_lemma(ctx.get_manager())
    {
        ctx.get_egraph().add_plugin(alloc(euf::bv_plugin, ctx.get_egraph()));
    }

    unsigned solver::get_bv_size(euf::enode* n) {
        return bv.get_bv_size(n->get_expr());
    }

    unsigned solver::get_bv_size(theory_var v) {
        return bv.get_bv_size(var2expr(v));        
    }

    bool solver::unit_propagate() {
        return m_core.propagate();
    }

    sat::check_result solver::check() {
        return m_core.check();
    }

    void solver::asserted(literal l) {
        TRACE("bv", tout << "asserted: " << l << "\n";);
        atom* a = get_bv2a(l.var());
        if (!a)
            return;
        force_push();
        m_core.assign_eh(a->m_index, l.sign(), dependency(l, s().lvl(l)));
    }

    void solver::set_conflict(dependency_vector const& core) {
        auto [lits, eqs] = explain_deps(core);
        auto ex = euf::th_explain::conflict(*this, lits, eqs, nullptr);
        ctx.set_conflict(ex);
    }

    std::pair<sat::literal_vector, euf::enode_pair_vector> solver::explain_deps(dependency_vector const& deps) {
        sat::literal_vector core;
        euf::enode_pair_vector eqs;
        for (auto d : deps) {
            if (d.is_literal()) {
                core.push_back(d.literal());
            }
            else {
                auto const [v1, v2] = d.eq();
                euf::enode* const n1 = var2enode(v1);
                euf::enode* const n2 = var2enode(v2);
                VERIFY(n1->get_root() == n2->get_root());
                eqs.push_back(euf::enode_pair(n1, n2));
            }
        }
        DEBUG_CODE({
            for (auto lit : core)
                VERIFY(s().value(lit) == l_true);
            for (auto const& [n1, n2] : eqs)
                VERIFY(n1->get_root() == n2->get_root());
            });
        IF_VERBOSE(10,
            for (auto lit : core)
                verbose_stream() << "    " << lit << ":  " << mk_ismt2_pp(literal2expr(lit), m) << "\n";
            for (auto const& [n1, n2] : eqs)
                verbose_stream() << "    " << ctx.bpp(n1) << "  ==  " << ctx.bpp(n2) << "\n";);

        return { core, eqs };
    }

    void solver::set_lemma(vector<signed_constraint> const& lemma, unsigned level, dependency_vector const& core) {
        auto [lits, eqs] = explain_deps(core);
        auto ex = euf::th_explain::conflict(*this, lits, eqs, nullptr);
        ctx.push(value_trail<bool>(m_has_lemma));
        m_has_lemma = true;
        m_lemma_level = level;
        m_lemma.reset();
        for (auto sc : lemma)
            m_lemma.push_back(constraint2expr(sc));
        ctx.set_conflict(ex);
    }

    // If an MCSat lemma is added, then backjump based on the lemma level and 
    // add the lemma to the solver with potentially fresh literals.
    // return l_false to signal sat::solver that backjumping has been taken care of internally.
    lbool solver::resolve_conflict() {
        if (!m_has_lemma)
            return l_undef;

        unsigned num_scopes = s().scope_lvl() - m_lemma_level;

        // s().pop_reinit(num_scopes);

        sat::literal_vector lits;
        for (auto* e : m_lemma)
            lits.push_back(ctx.mk_literal(e));
        s().add_clause(lits.size(), lits.data(), sat::status::th(true, get_id(), nullptr));
        return l_false;
    }

    // Create an equality literal that represents the value assignment
    // Prefer case split to true.
    // The equality gets added in a callback using asserted().
    void solver::add_eq_literal(pvar pvar, rational const& val) {
        auto v = m_pddvar2var[pvar];
        auto n = var2enode(v);
        auto eq = eq_internalize(n->get_expr(), bv.mk_numeral(val, get_bv_size(v)));
        s().set_phase(eq);
    }

    void solver::new_eq_eh(euf::th_eq const& eq) {
        auto v1 = eq.v1(), v2 = eq.v2();
        pdd p = var2pdd(v1);
        pdd q = var2pdd(v2);
        auto sc = m_core.eq(p, q);        
        m_var_eqs.setx(m_var_eqs_head, {v1, v2}, {v1, v2});
        ctx.push(value_trail<unsigned>(m_var_eqs_head));    
        auto d = dependency(v1, v2, s().scope_lvl());
        unsigned index = m_core.register_constraint(sc, d);
        m_core.assign_eh(index, false, d); 
        m_var_eqs_head++;
    }

    void solver::new_diseq_eh(euf::th_eq const& ne) {
        euf::theory_var v1 = ne.v1(), v2 = ne.v2();
        pdd p = var2pdd(v1);
        pdd q = var2pdd(v2);
        auto sc = ~m_core.eq(p, q);
        sat::literal neq = ~expr2literal(ne.eq());
        auto d = dependency(neq, s().lvl(neq));
        auto index = m_core.register_constraint(sc, d);
        TRACE("bv", tout << neq << " := " << s().value(neq) << " @" << s().scope_lvl() << "\n");
        m_core.assign_eh(index, false, d);
    }

    // Core uses the propagate callback to add unit propagations to the trail.
    // The polysat::solver takes care of translating signed constraints into expressions, which translate into literals.
    // Everything goes over expressions/literals. polysat::core is not responsible for replaying expressions. 
    dependency solver::propagate(signed_constraint sc, dependency_vector const& deps) {
        sat::literal lit = ctx.mk_literal(constraint2expr(sc));
        auto [core, eqs] = explain_deps(deps);
        auto ex = euf::th_explain::propagate(*this, core, eqs, lit, nullptr);
        ctx.propagate(lit, ex);
        return dependency(lit, s().lvl(lit));
    }

    void solver::propagate(dependency const& d, bool sign, dependency_vector const& deps) {
        auto [core, eqs] = explain_deps(deps);
        if (d.is_literal()) {
            auto lit = d.literal();
            if (sign)
                lit.neg();
            if (s().value(lit) == l_true)
                return;
            auto ex = euf::th_explain::propagate(*this, core, eqs, lit, nullptr);
            ctx.propagate(lit, ex);
        }
        else if (sign) {  
            auto const [v1, v2] = d.eq();
            // equalities are always asserted so a negative propagation is a conflict.
            auto n1 = var2enode(v1);
            auto n2 = var2enode(v2);
            eqs.push_back({ n1, n2 });
            auto ex = euf::th_explain::conflict(*this, core, eqs, nullptr);
            ctx.set_conflict(ex);
        }
    }

    bool solver::inconsistent() const {
        return s().inconsistent();
    }

    trail_stack& solver::trail() {
        return ctx.get_trail_stack();
    }

    void solver::add_lemma(vector<signed_constraint> const& lemma) {
        sat::literal_vector lits;
        for (auto sc : lemma)
            lits.push_back(ctx.mk_literal(constraint2expr(sc)));
        s().add_clause(lits.size(), lits.data(), sat::status::th(true, get_id(), nullptr));
    }

    void solver::get_antecedents(literal l, sat::ext_justification_idx idx, literal_vector& r, bool probing) {
        auto& jst = euf::th_explain::from_index(idx);
        ctx.get_th_antecedents(l, jst, r, probing);
    }

    expr_ref solver::constraint2expr(signed_constraint const& sc) { 
        switch (sc.op()) {
        case ckind_t::ule_t: {
            auto l = pdd2expr(sc.to_ule().lhs());
            auto h = pdd2expr(sc.to_ule().rhs());
            return expr_ref(bv.mk_ule(l, h), m);
        }
        case ckind_t::umul_ovfl_t: {
            auto l = pdd2expr(sc.to_umul_ovfl().p());
            auto r = pdd2expr(sc.to_umul_ovfl().q());
            return expr_ref(bv.mk_bvumul_ovfl(l, r), m);
        }
        case ckind_t::smul_fl_t:
        case ckind_t::op_t:
            NOT_IMPLEMENTED_YET();
            break;
        }
        throw default_exception("nyi"); 
    }

    expr_ref solver::pdd2expr(pdd const& p) {
        if (p.is_val()) {
            expr* n = bv.mk_numeral(p.val(), p.power_of_2());
            return expr_ref(n, m);
        }
        auto lo = pdd2expr(p.lo());
        auto hi = pdd2expr(p.hi());
        auto v = var2enode(m_pddvar2var[p.var()]);
        hi = bv.mk_bv_mul(v->get_expr(), hi);
        return expr_ref(bv.mk_bv_add(lo, hi), m);
    }

}
