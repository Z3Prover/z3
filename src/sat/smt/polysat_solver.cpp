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
        atom* a = get_bv2a(l.var());
        TRACE("bv", tout << "asserted: " << l << "\n";);
        if (!a)
            return;
        force_push();
        auto sc = a->m_sc;
        if (l.sign())
            sc = ~sc;
        m_core.assign_eh(sc, dependency(l, s().lvl(l)));
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
                auto const [v1, v2] = m_var_eqs[d.index()];
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
            m_lemma.push_back(m_core.constraint2expr(sc));
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
        m_var_eqs.setx(m_var_eqs_head, std::make_pair(v1, v2), std::make_pair(v1, v2));
        ctx.push(value_trail<unsigned>(m_var_eqs_head));        
        m_core.assign_eh(sc, dependency(m_var_eqs_head, s().scope_lvl())); 
        m_var_eqs_head++;
    }

    void solver::new_diseq_eh(euf::th_eq const& ne) {
        euf::theory_var v1 = ne.v1(), v2 = ne.v2();
        pdd p = var2pdd(v1);
        pdd q = var2pdd(v2);
        auto sc = ~m_core.eq(p, q);
        sat::literal neq = ~expr2literal(ne.eq());
        TRACE("bv", tout << neq << " := " << s().value(neq) << " @" << s().scope_lvl() << "\n");
        m_core.assign_eh(sc, dependency(neq, s().lvl(neq)));
    }

    // Core uses the propagate callback to add unit propagations to the trail.
    // The polysat::solver takes care of translating signed constraints into expressions, which translate into literals.
    // Everything goes over expressions/literals. polysat::core is not responsible for replaying expressions. 
    void solver::propagate(signed_constraint sc, dependency_vector const& deps) {
        sat::literal lit = ctx.mk_literal(m_core.constraint2expr(sc));
        auto [core, eqs] = explain_deps(deps);
        auto ex = euf::th_explain::propagate(*this, core, eqs, lit, nullptr);
        ctx.propagate(lit, ex);
    }

    void solver::add_lemma(vector<signed_constraint> const& lemma) {
        sat::literal_vector lits;
        for (auto sc : lemma)
            lits.push_back(ctx.mk_literal(m_core.constraint2expr(sc)));
        s().add_clause(lits.size(), lits.data(), sat::status::th(true, get_id(), nullptr));
    }

    void solver::get_antecedents(literal l, sat::ext_justification_idx idx, literal_vector& r, bool probing) {
        auto& jst = euf::th_explain::from_index(idx);
        ctx.get_th_antecedents(l, jst, r, probing);
    }

}
