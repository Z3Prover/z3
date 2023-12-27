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


#include "sat/smt/polysat_solver.h"
#include "sat/smt/euf_solver.h"
#include "sat/smt/polysat/ule_constraint.h"
#include "sat/smt/polysat/umul_ovfl_constraint.h"

namespace polysat {

    solver::solver(euf::solver& ctx, theory_id id):
        euf::th_euf_solver(ctx, symbol("bv"), id),
        bv(ctx.get_manager()),
        m_autil(ctx.get_manager()),
        m_core(*this),
        m_intblast(ctx),
        m_lemma(ctx.get_manager())
    {
        m_bv_plugin = alloc(euf::bv_plugin, ctx.get_egraph());
        ctx.get_egraph().add_plugin(m_bv_plugin);
    }

    unsigned solver::get_bv_size(euf::enode* n) {
        return bv.get_bv_size(n->get_expr());
    }

    unsigned solver::get_bv_size(theory_var v) {
        return bv.get_bv_size(var2expr(v));        
    }

    bool solver::unit_propagate() {
        return m_core.propagate() || propagate_delayed_axioms();
    }

    sat::check_result solver::check() {
        switch (m_core.check()) {
        case sat::check_result::CR_DONE:
            return sat::check_result::CR_DONE;
        case sat::check_result::CR_CONTINUE:
            return sat::check_result::CR_CONTINUE;
        case sat::check_result::CR_GIVEUP: 
            return intblast();        
        }
        UNREACHABLE();
        return sat::check_result::CR_GIVEUP;
    }

    sat::check_result solver::intblast() {
        if (!m.inc())
            return sat::check_result::CR_GIVEUP;
        switch (m_intblast.check_solver_state()) {
        case l_true: {
            pvar pv = m_core.next_var();
            auto v = m_pddvar2var[pv];
            auto n = var2expr(v);
            auto val = m_intblast.get_value(n);
            sat::literal lit = eq_internalize(n, bv.mk_numeral(val, get_bv_size(v)));
            s().set_phase(lit);
            return sat::check_result::CR_CONTINUE;
        }
        case l_false: {
            IF_VERBOSE(2, verbose_stream() << "unsat core: " << m_intblast.unsat_core() << "\n");
            auto core = m_intblast.unsat_core();
            for (auto& lit : core)
                lit.neg();
            s().add_clause(core.size(), core.data(), sat::status::th(true, get_id(), nullptr));
            return sat::check_result::CR_CONTINUE;
        }
        case l_undef:
            return sat::check_result::CR_GIVEUP;
        }
        UNREACHABLE();
        return sat::check_result::CR_GIVEUP;
    }

    void solver::asserted(literal l) {
        TRACE("bv", tout << "asserted: " << l << "\n";);
        atom* a = get_bv2a(l.var());
        if (!a)
            return;
        force_push();
        m_core.assign_eh(a->m_index, l.sign(), s().lvl(l));
    }

    void solver::set_conflict(dependency_vector const& deps) {
        auto [lits, eqs] = explain_deps(deps);
        auto ex = euf::th_explain::conflict(*this, lits, eqs, nullptr);
        ctx.set_conflict(ex);
    }

    std::pair<sat::literal_vector, euf::enode_pair_vector> solver::explain_deps(dependency_vector const& deps) {
        sat::literal_vector core;
        euf::enode_pair_vector eqs;
        for (auto d : deps) {
            if (d.is_bool_var()) {
                auto bv = d.bool_var();
                auto lit = sat::literal(bv, s().value(bv) == l_false);
                core.push_back(lit);
            }
            else if (d.is_fixed_claim()) {
                auto const& o = d.fixed();
                std::function<void(euf::enode*, euf::enode*)> consume = [&](auto* a, auto* b) {
                    eqs.push_back({ a, b });
                    };
                explain_fixed(o.v, o.lo, o.hi, o.value, consume);
            }
            else if (d.is_offset_claim()) {
                auto const& offs = d.offset();
                std::function<void(euf::enode*, euf::enode*)> consume = [&](auto* a, auto* b) {
                    eqs.push_back({ a, b });
                    };
                explain_slice(offs.v, offs.w, offs.offset, consume);
            }
            else {
                auto const [v1, v2] = d.eq();
                euf::enode* const n1 = var2enode(v1);
                euf::enode* const n2 = var2enode(v2);
                VERIFY(n1->get_root() == n2->get_root());
                eqs.push_back(euf::enode_pair(n1, n2));
            }
        }
        IF_VERBOSE(10,
            for (auto lit : core)
                verbose_stream() << "    " << lit << ":  " << mk_ismt2_pp(literal2expr(lit), m) << " " << s().value(lit) << "\n";
        for (auto const& [n1, n2] : eqs)
            verbose_stream() << "    " << ctx.bpp(n1) << "  ==  " << ctx.bpp(n2) << "\n";);
        DEBUG_CODE({
            for (auto lit : core)
                SASSERT(s().value(lit) == l_true);
            for (auto const& [n1, n2] : eqs)
                SASSERT(n1->get_root() == n2->get_root());
            });


        return { core, eqs };
    }

    // Create an equality literal that represents the value assignment
    // Prefer case split to true.
    // The equality gets added in a callback using asserted().
    void solver::add_eq_literal(pvar pvar, rational const& val) {
        auto v = m_pddvar2var[pvar];
        auto n = var2enode(v);
        auto eq = eq_internalize(n->get_expr(), bv.mk_numeral(val, get_bv_size(v)));
        s().set_phase(eq);
        ctx.mark_relevant(eq);
    }

    void solver::new_eq_eh(euf::th_eq const& eq) {
        auto v1 = eq.v1(), v2 = eq.v2();
        euf::enode* n = var2enode(v1);
        if (!bv.is_bv(n->get_expr()))
            return;
        pdd p = var2pdd(v1);
        pdd q = var2pdd(v2);
        auto sc = m_core.eq(p, q);        
        m_var_eqs.setx(m_var_eqs_head, {v1, v2}, {v1, v2});
        ctx.push(value_trail<unsigned>(m_var_eqs_head));    
        auto d = dependency(v1, v2);
        constraint_id id = m_core.register_constraint(sc, d);
        m_core.assign_eh(id, false, s().scope_lvl()); 
        m_var_eqs_head++;
    }

    void solver::new_diseq_eh(euf::th_eq const& ne) {
        euf::theory_var v1 = ne.v1(), v2 = ne.v2();
        euf::enode* n = var2enode(v1);
        if (!bv.is_bv(n->get_expr()))
            return;
        pdd p = var2pdd(v1);
        pdd q = var2pdd(v2);
        auto sc = m_core.eq(p, q);
        sat::literal eq = expr2literal(ne.eq());
        auto d = dependency(eq.var());
        auto id = m_core.register_constraint(sc, d);
        TRACE("bv", tout << eq << " := " << s().value(eq) << " @" << s().scope_lvl() << "\n");
        m_core.assign_eh(id, false, s().lvl(eq));
    }

    // Core uses the propagate callback to add unit propagations to the trail.
    // The polysat::solver takes care of translating signed constraints into expressions, which translate into literals.
    // Everything goes over expressions/literals. polysat::core is not responsible for replaying expressions. 
    
    dependency solver::propagate(signed_constraint sc, dependency_vector const& deps) {
        TRACE("bv", sc.display(tout << "propagate ") << "\n");
        sat::literal lit = ctx.mk_literal(constraint2expr(sc));        
        if (s().value(lit) == l_true)
            return dependency(lit.var());
        auto [core, eqs] = explain_deps(deps);
        auto ex = euf::th_explain::propagate(*this, core, eqs, lit, nullptr);        
        ctx.propagate(lit, ex);
        return dependency(lit.var()); 
    }

    unsigned solver::level(dependency const& d) {
        if (d.is_bool_var())
            return s().lvl(d.bool_var());
        else if (d.is_eq()) {
            auto [v1, v2] = d.eq();
            sat::literal_vector lits;
            ctx.get_eq_antecedents(var2enode(v1), var2enode(v2), lits);
            unsigned level = 0;
            for (auto lit : lits)
                level = std::max(level, s().lvl(lit));
            return level;
        }
        else if (d.is_offset_claim()) {
            auto const& offs = d.offset();
            sat::literal_vector lits;
            std::function<void(euf::enode*, euf::enode*)> consume = [&](auto* a, auto* b) {
                ctx.get_eq_antecedents(a, b, lits);                
                };
            explain_slice(offs.v, offs.w, offs.offset, consume);
            unsigned level = 0;
            for (auto lit : lits)
                level = std::max(level, s().lvl(lit));
            return level;
        }
        else if (d.is_fixed_claim()) {
            auto const& f = d.fixed();
            sat::literal_vector lits;
            std::function<void(euf::enode*, euf::enode*)> consume = [&](auto* a, auto* b) {
                ctx.get_eq_antecedents(a, b, lits);
                };
            explain_fixed(f.v, f.lo, f.hi, f.value, consume);
            unsigned level = 0;
            for (auto lit : lits)
                level = std::max(level, s().lvl(lit));
            return level;
        }
        else {
            SASSERT(d.is_axiom());
            return 0;
        }
    }

    void solver::propagate(dependency const& d, bool sign, dependency_vector const& deps) {
        TRACE("bv", tout << "propagate " << d << " " << sign << "\n");
        auto [core, eqs] = explain_deps(deps);
        SASSERT(d.is_bool_var() || d.is_eq());
        if (d.is_bool_var()) {
            auto bv = d.bool_var();
            auto lit = sat::literal(bv, sign);
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

    bool solver::add_axiom(char const* name, constraint_or_dependency const* begin, constraint_or_dependency const* end, bool is_redundant) {
        sat::literal_vector lits;
        for (auto it = begin; it != end; ++it) {
            auto const& e = *it;
            if (std::holds_alternative<dependency>(e)) {
                auto d = *std::get_if<dependency>(&e);
                SASSERT(!d.is_null());
                if (d.is_bool_var()) {
                    auto bv = d.bool_var();
                    auto lit = sat::literal(bv, s().value(bv) == l_false);
                    lits.push_back(~lit);
                }
                else if (d.is_eq()) {
                    auto [v1, v2] = d.eq();
                    lits.push_back(~eq_internalize(var2enode(v1), var2enode(v2)));
                }
                else if (d.is_offset_claim()) {
                    auto const& o = d.offset();
                    std::function<void(euf::enode*, euf::enode*)> consume = [&](auto* a, auto* b) {
                        lits.push_back(~eq_internalize(a, b));
                    };
                    explain_slice(o.v, o.w, o.offset, consume);
                }
                else if (d.is_fixed_claim()) {
                    auto const& f = d.fixed();
                    std::function<void(euf::enode*, euf::enode*)> consume = [&](auto* a, auto* b) {
                        lits.push_back(~eq_internalize(a, b));
                    };
                    explain_fixed(f.v, f.lo, f.hi, f.value, consume);
                }
                else {
                    SASSERT(d.is_axiom());
                }
            }
            else if (std::holds_alternative<signed_constraint>(e))
                lits.push_back(ctx.mk_literal(constraint2expr(*std::get_if<signed_constraint>(&e))));
        }
        for (auto lit : lits)
            if (s().value(lit) == l_true)
                return false;
        s().add_clause(lits.size(), lits.data(), sat::status::th(is_redundant, get_id(), nullptr));
        return true;
    }

    void solver::get_antecedents(literal l, sat::ext_justification_idx idx, literal_vector& r, bool probing) {
        auto& jst = euf::th_explain::from_index(idx);
        ctx.get_th_antecedents(l, jst, r, probing);
    }

    expr_ref solver::constraint2expr(signed_constraint const& sc) { 
        expr_ref result(m);
        switch (sc.op()) {
        case ckind_t::ule_t: {
            auto l = pdd2expr(sc.to_ule().lhs());
            auto h = pdd2expr(sc.to_ule().rhs());
            result = bv.mk_ule(l, h);
            if (sc.sign())
                result = m.mk_not(result);
            return result;           
        }
        case ckind_t::umul_ovfl_t: {
            auto l = pdd2expr(sc.to_umul_ovfl().p());
            auto r = pdd2expr(sc.to_umul_ovfl().q());
            result = bv.mk_bvumul_no_ovfl(l, r);
            if (!sc.sign())
                result = m.mk_not(result);
            return result;
        }
        case ckind_t::smul_fl_t:
        case ckind_t::op_t:
            NOT_IMPLEMENTED_YET();
            break;
        }
        throw default_exception("constraint2expr nyi"); 
    }

    expr_ref solver::pdd2expr(pdd const& p) {
        if (p.is_val()) {
            expr* n = bv.mk_numeral(p.val(), p.power_of_2());
            return expr_ref(n, m);
        }
        auto v = var2enode(m_pddvar2var[p.var()]);
        expr* r = v->get_expr();
        if (!p.hi().is_one())
            r = bv.mk_bv_mul(r, pdd2expr(p.hi()));
        if (!p.lo().is_zero())
            r = bv.mk_bv_add(r, pdd2expr(p.lo()));
        return expr_ref(r, m);
    }
}
