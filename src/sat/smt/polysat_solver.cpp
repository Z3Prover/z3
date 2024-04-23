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
        std::function<void(euf::enode*)> ensure_th_var = [&](euf::enode* n) {
            if (get_th_var(n) != euf::null_theory_var)
                return;
            auto v = mk_var(n);            
            rational val;
            unsigned sz = 0;
            if (bv.is_numeral(n->get_expr(), val, sz))
                internalize_set(v, m_core.value(val, sz));
        };
        m_bv_plugin->set_ensure_th_var(ensure_th_var);
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
        TRACE("euf", s().display(tout));
        switch (m_core.check()) {
        case sat::check_result::CR_DONE:
            return sat::check_result::CR_DONE;
        case sat::check_result::CR_CONTINUE:
            return sat::check_result::CR_CONTINUE;
        case sat::check_result::CR_GIVEUP: 
            return sat::check_result::CR_GIVEUP;
            // return intblast();        
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
        m_core.assign_eh(a->m_index, l.sign());
    }

    void solver::set_conflict(dependency_vector const& deps, char const* hint_info) {
        ++m_stats.m_num_conflicts;
        if (inconsistent())
            return;
        auto [lits, eqs] = explain_deps(deps);
        proof_hint* hint = nullptr;
        if (ctx.use_drat() && hint_info)
            hint = mk_proof_hint(hint_info, lits, eqs);
        auto ex = euf::th_explain::conflict(*this, lits, eqs, hint);
        TRACE("bv", tout << "conflict: " << lits << " ";
                    for (auto [a, b] : eqs) tout << ctx.bpp(a) << " == " << ctx.bpp(b) << " "; 
                    tout << "\n"; s().display(tout));
        validate_conflict(hint_info, lits, eqs);
        ctx.set_conflict(ex);
    }

    void solver::explain_dep(dependency const& d, euf::enode_pair_vector& eqs, sat::literal_vector& core) {
        std::function<void(euf::enode*, euf::enode*)> consume = [&](auto* a, auto* b) {
            eqs.push_back({ a, b });
        };

        if (d.is_axiom())
            ;
        else if (d.is_bool_var()) {
            auto bv = d.bool_var();
            auto lit = sat::literal(bv, s().value(bv) == l_false);
            core.push_back(lit);
        }
        else if (d.is_fixed_claim()) {
            auto const& o = d.fixed();
            explain_fixed(o.parent, o, consume);
        }
        else if (d.is_offset_claim()) {
            auto const& offs = d.offset();
            explain_slice(offs.child, offs.parent, offs.offset, consume);
        }
        else if (d.is_enode_eq()) {
            auto const [n1, n2] = d.enode_eq();
            VERIFY(n1->get_root() == n2->get_root());
            eqs.push_back(euf::enode_pair(n1, n2));
        }
        else {
            auto const [v1, v2] = d.eq();
            euf::enode* const n1 = var2enode(v1);
            euf::enode* const n2 = var2enode(v2);
            VERIFY(n1->get_root() == n2->get_root());
            eqs.push_back(euf::enode_pair(n1, n2));
        }
    }

    std::pair<sat::literal_vector, euf::enode_pair_vector> solver::explain_deps(dependency_vector const& deps) {
        sat::literal_vector core;
        euf::enode_pair_vector eqs;
        for (auto d : deps) 
            explain_dep(d, eqs, core);

        IF_VERBOSE(10,
            verbose_stream() << "explain\n";
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
    lbool solver::add_eq_literal(pvar pvar, rational const& val, dependency& d) {
        auto v = m_pddvar2var[pvar];
        auto n = var2enode(v);
        auto eq = eq_internalize(n->get_expr(), bv.mk_numeral(val, get_bv_size(v)));
        euf::enode* eqn = ctx.bool_var2enode(eq.var());
        if (eqn->get_th_var(get_id()) == euf::null_theory_var)
            mk_var(eqn);
        pdd p = m_core.var(pvar);
        pdd q = m_core.value(val, m_core.size(pvar));
        auto sc = m_core.eq(p, q);
        s().set_phase(eq);
        ctx.mark_relevant(eq);
        d = dependency(eq.var());
        auto value = s().value(eq);
        if (!get_bv2a(eq.var())) {
            auto a = mk_atom(eq.var(), sc);
            if (value == l_false)
                m_core.assign_eh(a->m_index, true);
        }
        return s().value(eq);
    }

    void solver::new_eq_eh(euf::th_eq const& eq) {
        auto v1 = eq.v1(), v2 = eq.v2();
        euf::enode* n = var2enode(v1);
        if (!bv.is_bv(n->get_expr()))
            return;
  
        m_var_eqs.setx(m_var_eqs_head, {v1, v2}, {v1, v2});
        ctx.push(value_trail<unsigned>(m_var_eqs_head));    
        m_var_eqs_head++;
        pdd p = var2pdd(v1);
        pdd q = var2pdd(v2);
        auto d = dependency(v1, v2);
        constraint_id id = eq_constraint(p, q, false, d);
        TRACE("bv", tout << ctx.bpp(n) << " == " << ctx.bpp(var2enode(v2)) << " " << d << "\n");
        m_core.assign_eh(id, false); 

    }

    void solver::new_diseq_eh(euf::th_eq const& ne) {
        euf::theory_var v1 = ne.v1(), v2 = ne.v2();
        euf::enode* n = var2enode(v1);
        if (!bv.is_bv(n->get_expr()))
            return;
        pdd p = var2pdd(v1);
        pdd q = var2pdd(v2);
        sat::literal eq = expr2literal(ne.eq());
        auto d = dependency(eq.var());
        auto id = eq_constraint(p, q, true, d);
        TRACE("bv", tout << eq << " := " << s().value(eq) << " @" << s().scope_lvl() << "\n");
        m_core.assign_eh(id, true);
    }

    // Core uses the propagate callback to add unit propagations to the trail.
    // The polysat::solver takes care of translating signed constraints into expressions, which translate into literals.
    // Everything goes over expressions/literals. polysat::core is not responsible for replaying expressions. 
    
    dependency solver::propagate(signed_constraint sc, dependency_vector const& deps, char const* hint_info) {
        ++m_stats.m_num_propagations;
        TRACE("bv", sc.display(tout << "propagate ") << "\n");
        sat::literal lit = ctx.mk_literal(constraint2expr(sc));        
        if (s().value(lit) == l_true)
            return dependency(lit.var());
        auto [core, eqs] = explain_deps(deps);
        proof_hint* hint = nullptr;
        if (ctx.use_drat() && hint_info) {
            core.push_back(~lit);
            hint = mk_proof_hint(hint_info, core, eqs);
            core.pop_back();
        }
        if (s().value(lit) == l_false) {
            verbose_stream() << "contradictory propagation " << sc << " <- " << deps << "\n";
        }
        auto ex = euf::th_explain::propagate(*this, core, eqs, lit, hint);     
        validate_propagate(hint_info, lit, core, eqs);
        ctx.propagate(lit, ex);
        return dependency(lit.var()); 
    }

    void solver::propagate_eq(pvar pv, rational const& val, dependency const& d) {
        theory_var v = m_pddvar2var[pv];
        auto a = var2enode(v);
        auto bval = bv.mk_numeral(val, get_bv_size(v));
        ctx.internalize(bval);
        auto b = ctx.get_enode(bval);
        if (a->get_root() == b->get_root())
            return;
        proof_hint* hint = nullptr;
        sat::literal_vector core;
        euf::enode_pair_vector eqs;
        explain_dep(d, eqs, core);
        if (ctx.use_drat()) 
            hint = mk_proof_hint("propagate-eq", core, eqs);        
        auto exp = euf::th_explain::propagate(*this, core, eqs, a, b, hint);
        ctx.propagate(a, b, exp);
    }

    unsigned solver::level(dependency const& d) {
        if (d.is_bool_var())
            return s().lvl(d.bool_var());
        sat::literal_vector lits;
        euf::enode_pair_vector eqs;
        explain_dep(d, eqs, lits);
        for (auto [n1, n2] : eqs)
            ctx.get_eq_antecedents(n1, n2, lits);
        unsigned level = 0;
        for (auto lit : lits)
            level = std::max(level, s().lvl(lit));
        return level;
    }

    void solver::propagate(dependency const& d, bool sign, dependency_vector const& deps, char const* hint_info) {
        ++m_stats.m_num_propagations;
        TRACE("bv", tout << "propagate " << d << " " << sign << "\n");
        auto [core, eqs] = explain_deps(deps);
        SASSERT(d.is_bool_var() || d.is_eq() || d.is_axiom());
        proof_hint* hint = nullptr;

        if (d.is_axiom()) {
            if (sign) {
                if (ctx.use_drat() && hint_info)
                    hint = mk_proof_hint(hint_info, core, eqs);
                auto ex = euf::th_explain::conflict(*this, core, eqs, hint);
                validate_conflict(hint_info, core, eqs);
                ctx.set_conflict(ex);
            }
        }
        else if (d.is_bool_var()) {
            auto bv = d.bool_var();
            auto lit = sat::literal(bv, sign);
            if (s().value(lit) == l_true)
                return;
            if (ctx.use_drat() && hint_info) {
                core.push_back(~lit);
                hint = mk_proof_hint(hint_info, core, eqs);
                core.pop_back();
            }
            auto ex = euf::th_explain::propagate(*this, core, eqs, lit, hint);
            validate_propagate(hint_info, lit, core, eqs);
            ctx.propagate(lit, ex);
        }
        else if (sign) {  
            SASSERT(d.is_eq());
            auto const [v1, v2] = d.eq();
            // equalities are always asserted so a negative propagation is a conflict.
            auto n1 = var2enode(v1);
            auto n2 = var2enode(v2);
            eqs.push_back({ n1, n2 });
            if (ctx.use_drat() && hint_info)
                hint = mk_proof_hint(hint_info, core, eqs);
            auto ex = euf::th_explain::conflict(*this, core, eqs, hint);
            validate_conflict(hint_info, core, eqs);
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
        ++m_stats.m_num_axioms;
        if (inconsistent())
            return false;
        TRACE("bv", tout << "add " << name << "\n");
        sat::literal_vector lits;
        euf::enode_pair_vector eqs;
        for (auto it = begin; it != end; ++it) {
            auto const& e = *it;
            if (std::holds_alternative<dependency>(e)) {
                auto d = *std::get_if<dependency>(&e);
                SASSERT(!d.is_null());
                explain_dep(d, eqs, lits);
            }
            else if (std::holds_alternative<signed_constraint>(e))
                lits.push_back(~ctx.mk_literal(constraint2expr(*std::get_if<signed_constraint>(&e))));
        }
        for (auto [n1, n2] : eqs)
            ctx.get_eq_antecedents(n1, n2, lits);  
        proof_hint* hint = nullptr;
        if (ctx.use_drat()) 
            hint = mk_proof_hint(name, lits, {});        
        for (auto& lit : lits)
            lit.neg();
        for (auto lit : lits)
            if (s().value(lit) == l_true) {
                TRACE("bv", tout << "literal is true " << ctx.literal2expr(lit) << "\n");
                return false;
            }
        TRACE("bv", display_clause(name, tout, lits));
        IF_VERBOSE(1, display_clause(name, verbose_stream(), lits));
        validate_axiom(name, lits);
        s().add_clause(lits.size(), lits.data(), sat::status::th(is_redundant, get_id(), hint));
        return true;
    }

    void solver::add_axiom(char const* name, sat::literal const* begin, sat::literal const* end, bool is_redundant) {
        ++m_stats.m_num_axioms;
        sat::literal_vector lits;
        validate_axiom(name, sat::literal_vector(static_cast<unsigned>(end - begin), begin));
        for (auto it = begin; it != end; ++it) {
            auto lit = *it;
            if (s().value(lit) == l_true && s().lvl(lit) == 0)
                return;
            if (s().value(lit) == l_false && s().lvl(lit) == 0)
                continue;
            lits.push_back(lit);
        }
        
        proof_hint* hint = nullptr;
        if (ctx.use_drat()) {
            sat::literal_vector core;
            for (auto lit : lits)
                core.push_back(~lit);
            hint = mk_proof_hint(name, core, {});
        }        
        IF_VERBOSE(3, display_clause(name, verbose_stream(), lits));
        s().add_clause(lits.size(), lits.data(), sat::status::th(is_redundant, get_id(), hint));
    }

    void solver::add_axiom(char const* name, sat::literal_vector const& clause, bool is_redundant) {
        add_axiom(name, clause.begin(), clause.end(), is_redundant);

    }

    void solver::add_axiom(char const* name, std::initializer_list<sat::literal> const& clause) {      
        add_axiom(name, clause.begin(), clause.end(), false);
    }

    void solver::equiv_axiom(char const* name, sat::literal a, sat::literal b) {
        add_axiom(name, { a, ~b });
        add_axiom(name, { ~a, b });
    }

    void solver::get_antecedents(literal l, sat::ext_justification_idx idx, literal_vector& r, bool probing) {
        auto& jst = euf::th_explain::from_index(idx);
        ctx.get_th_antecedents(l, jst, r, probing);
    }

    expr_ref solver::constraint2expr(signed_constraint const& sc) { 
        expr_ref result(m);
        if (sc.is_always_false())
            return expr_ref(m.mk_false(), m);
        if (sc.is_always_true())
            return expr_ref(m.mk_true(), m);

        switch (sc.op()) {
        case ckind_t::ule_t: {            
            auto p = sc.to_ule().lhs();
            auto q = sc.to_ule().rhs();
            pdd x = p;
            if (q.is_zero() && p.has_unit(x)) {
                auto l = pdd2expr(x);
                auto r = pdd2expr(x - p);
                result = m.mk_eq(l, r);
            }
            else {
                auto l = pdd2expr(p);
                auto r = pdd2expr(q);
                if (q.is_zero())
                    result = m.mk_eq(l, r);
                else
                    result = bv.mk_ule(l, r);
            }
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
        case ckind_t::op_t:
            UNREACHABLE();
            break;
        }
        return result;
    }

    expr_ref solver::pdd2expr(pdd const& p) {

        auto mk_num = [&](rational const& c) {
            return bv.mk_numeral(c, p.power_of_2());
        };

        auto mk_var = [&](pvar v) {
            return var2expr(m_pddvar2var[v]);
        };

        if (p.is_val()) 
            return expr_ref(mk_num(p.val()), m);
        
        expr_ref_vector args(m);
        for (auto const& mon : p) {
            rational const& c = mon.coeff;
            if (mon.vars.empty())
                args.push_back(mk_num(c));
            else if (c == 1 && mon.vars.size() == 1)
                args.push_back(mk_var(mon.vars[0]));
            else if (mon.vars.size() == 1)
                args.push_back(bv.mk_bv_mul(mk_num(c), mk_var(mon.vars[0])));
            else {
                expr_ref_vector args2(m);
                for (pvar v : mon.vars)
                    args2.push_back(mk_var(v));
                if (c == 1)
                    args.push_back(bv.mk_bv_mul(args2));
                else
                    args.push_back(bv.mk_bv_mul(mk_num(c), bv.mk_bv_mul(args2)));
            }
        }          
        expr_ref r(m);
        if (args.size() == 1)
            r = args.get(0);
        else
            r = bv.mk_bv_add(args);
        return r;
    }

    expr* solver::proof_hint::get_hint(euf::solver& s) const {
        ast_manager& m = s.get_manager();
        family_id fid = m.get_family_id("bv");
        solver& p = dynamic_cast<solver&>(*s.fid2solver(fid));
        expr_ref_vector args(m);
        args.push_back(m.mk_const(name, m.mk_proof_sort()));
        for (unsigned i = m_lit_head; i < m_lit_tail; ++i)           
            args.push_back(s.literal2expr(p.m_mk_hint.lit(i)));
        for (unsigned i = m_eq_head; i < m_eq_tail; ++i)
            args.push_back(s.mk_eq(p.m_mk_hint.eq(i).first, p.m_mk_hint.eq(i).second));
        return m.mk_app(symbol("polysat"), args.size(), args.data(), m.mk_proof_sort());
    }

    void solver::proof_hint_builder::init(euf::solver& ctx, char const* name) {
        ctx.push(value_trail<unsigned>(m_eq_tail));
        ctx.push(value_trail<unsigned>(m_lit_tail));
        m_name = name;
        reset();
    }

    solver::proof_hint* solver::proof_hint_builder::mk(euf::solver& ctx) {
        return new (ctx.get_region()) proof_hint(m_name, m_lit_head, m_lit_tail, m_eq_head, m_eq_tail);
    }

    solver::proof_hint* solver::mk_proof_hint(char const* name, sat::literal_vector const& lits, euf::enode_pair_vector const& eqs) {
        m_mk_hint.init(ctx, name);
        for (auto lit : lits)
            m_mk_hint.add_lit(lit);
        for (auto [a,b] : eqs)
            m_mk_hint.add_eq(a,b);
        return m_mk_hint.mk(ctx);        
    }
}
