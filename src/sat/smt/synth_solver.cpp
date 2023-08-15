/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    synth_solver.h

Author:

    Petra Hozzova 2023-08-08
    Nikolaj Bjorner (nbjorner) 2020-08-17

--*/

#include "util/heap.h"
#include "ast/for_each_expr.h"
#include "ast/synth_decl_plugin.h"
#include "ast/rewriter/expr_safe_replace.h"
#include "ast/rewriter/th_rewriter.h"
#include "sat/smt/synth_solver.h"
#include "sat/smt/euf_solver.h"
#include "qe/qe_mbi.h"

namespace synth {

    solver::solver(euf::solver& ctx):
        th_euf_solver(ctx, symbol("synth"), ctx.get_manager().mk_family_id("synth")), m_rep(m) {
        std::function<void(euf::enode*, euf::enode*)> _on_merge = 
            [&](euf::enode* root, euf::enode* other) { 
            on_merge_eh(root, other); 
        };
        ctx.get_egraph().set_on_merge(_on_merge);
    }
        
    solver::~solver() {}


    bool solver::is_output(expr * e) const {
        return any_of(m_synth, [&](synth_objective const& a) { return a.output() == e; });
    }

    bool solver::contains_uncomputable(expr* e) {
        return any_of(subterms::all(expr_ref(e, m)), [&](expr* a) { return (is_app(a) && m_uncomputable.contains(to_app(a)->get_decl())) || is_output(a); });
    }

    void solver::add_uncomputable(app* e) {
        for (expr* arg : *e) {
            if (is_app(arg)) {
                func_decl* f = to_app(arg)->get_decl();
                m_uncomputable.insert(f);
                ctx.push(insert_obj_trail(m_uncomputable, f));
            }
        }
    }

    void solver::add_synth_objective(synth_objective const& e) {
        m_synth.push_back(e);
        ctx.push(push_back_vector(m_synth));
        for (auto* arg : e) {
            m_is_computable.reserve(arg->get_id() + 1);
            ctx.push(set_bitvector_trail(m_is_computable, arg->get_id())); // TODO use enode roots instead and test if they are already set.
        }
    }

    void solver::add_specification(app* e, expr* arg) {
	// This assumes that each (assert (constraint (...)) is asserting exactly one app
        sat::literal lit = ctx.mk_literal(arg);
        sat::bool_var bv = ctx.get_si().add_bool_var(e);
        sat::literal lit_e(bv, false);
        ctx.attach_lit(lit_e, e);
        add_clause(~lit_e, lit);
        ctx.push_vec(m_spec, arg);        
    }

    // recognize synthesis objectives here.
    sat::literal solver::internalize(expr* e, bool sign, bool root) {
        internalize(e);
	    sat::literal lit = ctx.expr2literal(e);
        if (sign)
            lit.neg();
        return lit;
    }

    // recognize synthesis objectives here and above
    void solver::internalize(expr* e) {
        SASSERT(is_app(e));
        sat::bool_var bv = ctx.get_si().add_bool_var(e);
        sat::literal lit(bv, false);
        ctx.attach_lit(lit, e);
        synth::util util(m);
        app* a = to_app(e);
        expr* arg = nullptr;
        if (util.is_synthesiz3(e))
            add_synth_objective(synth_objective(m, a));
        else if (util.is_grammar(e))
            add_uncomputable(a);
        else if (util.is_specification(e, arg))
            add_specification(a, arg);
        else {
            IF_VERBOSE(0, verbose_stream() << "unrecognized synthesis objective " << mk_pp(e, m) << "\n");
        }
    }

    sat::check_result solver::check() {
        if (m_synth.empty())
            return sat::check_result::CR_DONE;
        
        for (auto& s : m_synth) {
            if (s.is_solved())
                continue;
            if (synthesize_uninterpreted_sort(s))
                continue;
            if (synthesize_arithmetic(s))
                continue;
            IF_VERBOSE(2, ctx.display(verbose_stream()));
            return sat::check_result::CR_GIVEUP;
        }
        if (compute_solutions())
            return sat::check_result::CR_DONE;

        IF_VERBOSE(2, ctx.display(verbose_stream()));
        return sat::check_result::CR_GIVEUP;
    }

    // display current state (eg. current set of realizers)
    std::ostream& solver::display(std::ostream& out) const {
        for (auto const& e : m_synth)
            out << "synth objective " << mk_pp(e.output(), m) << "\n";            
        return out;
    }

    // create a clone of the solver.
    euf::th_solver* solver::clone(euf::solver& ctx) {
        return alloc(solver, ctx);
    }

    void solver::asserted(sat::literal lit) {
        // lit corresponds to a Boolean output variable.
        // it is asserted.
        // assume that we attach this theory to such Boolean output variables.
    }


    void solver::on_merge_eh(euf::enode* root, euf::enode* other) {

        auto is_computable = [&](euf::enode* n) { return !contains_uncomputable(n->get_expr()) || m_is_computable.get(n->get_root_id(), false); };
        auto is_uncomputable = [&](func_decl* f) { return m_uncomputable.contains(f); };

        IF_VERBOSE(2, verbose_stream() << "merge " << ctx.bpp(root) << " " << is_computable(root) << " == " << ctx.bpp(other) << " " << is_computable(other) << "\n");

        m_is_computable.reserve(root->get_id() + 1);
        
        // if neither contains uncomputable, then we want to make sure that m_is_computable gets set.
        if (!m_is_computable.get(root->get_root_id(), false) && !contains_uncomputable(root->get_expr()))
            ctx.push(set_bitvector_trail(m_is_computable, root->get_id()));
        else if (!m_is_computable.get(root->get_root_id(), false) && !contains_uncomputable(other->get_expr()))
            ctx.push(set_bitvector_trail(m_is_computable, root->get_id()));
        else if (is_computable(root) == is_computable(other))
            return;

        if (!is_computable(root)) 
            ctx.push(set_bitvector_trail(m_is_computable, root->get_id()));

        euf::enode_vector todo;
        todo.push_back(root);
        for (unsigned i = 0; i < todo.size(); ++i) {
            auto * n = todo[i];
            for (auto* p : euf::enode_parents(n)) {
                if (is_uncomputable(p->get_decl()))
                    continue;
                if (is_computable(p))
                    continue;
                if (!all_of(euf::enode_args(p), [&](auto * ch) { return is_computable(ch); }))
                    continue;
                m_is_computable.reserve(p->get_root_id() + 1);
                ctx.push(set_bitvector_trail(m_is_computable, p->get_root_id()));
                todo.push_back(p);
            }
        }

        if (m_is_solved)
            return;

        for (auto& e : m_synth) {
            euf::enode* n = expr2enode(e.output());
            if (is_computable(n) && !e.is_solved()) {
                e.set_solution(nullptr);
                ctx.push(synth_objective::unset_solution(e));
            }
         }
    }

    bool solver::unit_propagate() {
        if (m_is_solved)
            return false;
        if (!all_of(m_synth, [&](synth_objective const& s) { return s.is_solved(); }))
            return false;
        IF_VERBOSE(2, verbose_stream() << "propagate\n");
        ctx.push(value_trail(m_is_solved));
        m_is_solved = true;
        return compute_solutions();
    }

    void solver::compute_rep() {
        m_rep.reset();
        auto is_uncomputable = [&](func_decl* f) { return m_uncomputable.contains(f); };

        struct rep_lt {
            expr_ref_vector const& m_rep;
            rep_lt(expr_ref_vector& m_rep) : m_rep(m_rep) {}
            bool operator()(int v1, int v2) const {
                return get_depth(m_rep.get(v1)) < get_depth(m_rep.get(v2));
            };
        };
        rep_lt lt(m_rep);
        heap<rep_lt> heap(1000, lt);
        euf::enode_vector nodes;
        auto insert_m_rep = [&](euf::enode* n, expr* r) {
            unsigned id = n->get_root_id();
            set_rep(n, r);
            nodes.reserve(id + 1);
            nodes[id] = n->get_root();
            heap.reserve(id + 1);
            heap.insert(id);
            };

        for (auto const& e : m_synth) {
            for (expr* arg : e) {
                auto* narg = expr2enode(arg);
                insert_m_rep(narg, arg);
            }
        }
        // make sure we only insert non-input symbols.
        for (auto* n : ctx.get_egraph().nodes()) {
            if (n->num_args() == 0 && !contains_uncomputable(n->get_expr()) && !has_rep(n))
                insert_m_rep(n, n->get_expr());
        }
        while (!heap.empty()) {
            auto* nn = nodes[heap.erase_min()];
            for (auto* p : euf::enode_parents(nn)) {
                if (is_uncomputable(p->get_decl()))
                    continue;
                if (!all_of(euf::enode_args(p), [&](auto* ch) { return has_rep(ch); }))
                    continue;
                expr* r = get_rep(p);
                if (r) {
                    unsigned depth = get_depth(r);
                    if (any_of(euf::enode_args(p), [&](auto* ch) { return get_depth(get_rep(ch)) >= depth; }))
                        continue;
                    heap.erase(p->get_root_id());
                }
                ptr_buffer<expr> args;
                for (auto* ch : euf::enode_args(p))
                    args.push_back(get_rep(ch));
                expr_ref papp(m.mk_app(p->get_decl(), args), m);
                insert_m_rep(p, papp);
            }
        }
    }

    expr_ref solver::compute_solution(synth_objective const& e) {
        if (e.solution())
            return expr_ref(e.solution(), m);
        auto* n = expr2enode(e.output());
        return expr_ref(m_rep.get(n->get_root_id(), nullptr), m);
    }

    expr_ref solver::compute_condition() {
        expr_ref result(m.mk_and(m_spec), m);
        expr_safe_replace replace(m);
        for (auto const& e : m_synth) 
            replace.insert(e.output(), compute_solution(e));
	IF_VERBOSE(3, verbose_stream() << "spec: " << result << "\n");        
        replace(result);
        th_rewriter rw(m);
        rw(result);
        IF_VERBOSE(4, ctx.display(verbose_stream()));
	IF_VERBOSE(3, verbose_stream() << "simplifying: " << result << "\n");
	result = simplify_condition(result.get());
	IF_VERBOSE(3, verbose_stream() << result << "\n");
        rw(result);
        return result;
    }

    expr_ref solver::simplify_condition(expr* e) {
        ptr_vector<expr> todo;
        todo.push_back(e);
        while (!todo.empty()) {
            expr* a = todo.back();
            if (m_rep.get(a->get_id(), nullptr)) {
                todo.pop_back();
                continue;
            }
            euf::enode* n = expr2enode(a);
            if (n && has_rep(n)) {
                todo.pop_back();
                continue;
            }
            if (!is_app(a)) {
                m_rep.setx(n->get_id(), a);
                todo.pop_back();
                continue;
            }

            func_decl* f = to_app(a)->get_decl();

	    ptr_buffer<expr> args;
            for (expr* arg : *to_app(a)) {
		n = expr2enode(arg);
		expr* r;
		if (n && (r = get_rep(n)))
		    args.push_back(r);
		else if (r = m_rep.get(arg->get_id(), nullptr))
                    args.push_back(r);
                else
                    todo.push_back(arg);
            }
            if (args.size() == to_app(a)->get_num_args()) {
                todo.pop_back();
                expr_ref new_a(m.mk_app(f, args), m);
                n = expr2enode(new_a);
                if (n && has_rep(n)) 
                    m_rep.setx(a->get_id(), get_rep(n));
                else if (m_uncomputable.contains(f) && n->get_root()->value() != l_undef) {
                    if (n->get_root()->value() == l_true)
                        m_rep.setx(a->get_id(), m.mk_true());
                    else
                        m_rep.setx(a->get_id(), m.mk_false());
                }
                else 
                    m_rep.setx(a->get_id(), new_a);
            }
        }
        euf::enode* n = expr2enode(e);
        if (n && has_rep(n))
            return expr_ref(get_rep(n), m);
        SASSERT(m_rep.get(e->get_id(), nullptr));
        return expr_ref(m_rep.get(e->get_id()), m);
    }

    sat::literal solver::synthesize(synth_objective const& synth_objective) {
        expr_ref sol = compute_solution(synth_objective);
        if (!sol)
            return sat::null_literal;

        IF_VERBOSE(0, verbose_stream() << sol << "\n");
        return eq_internalize(synth_objective.output(), sol);
    }

    bool solver::compute_solutions() {
        sat::literal_vector clause;
        compute_rep();

        for (synth_objective const& e : m_synth) {
            expr_ref sol = compute_solution(e);
            if (!sol)
                return false;
            IF_VERBOSE(0, verbose_stream() << sol << "\n");
        }
        expr_ref cond = compute_condition();
        add_unit(~mk_literal(cond));
        IF_VERBOSE(0, verbose_stream() << "if " << cond << "\n");
        return true;
    }

    bool solver::synthesize_uninterpreted_sort(synth_objective& obj) {
        if (!m.is_uninterp(obj.output()->get_sort()))
            return false;
                
        sort* srt = obj.output()->get_sort();
        euf::enode* r = expr2enode(obj.output());
        VERIFY(r);
        if (!r)
            return false;
        euf::enode_vector candidates;
        auto& egraph = ctx.get_egraph();
        for (auto* n : egraph.nodes()) {
            if (n->get_sort() != srt || contains_uncomputable(n->get_expr())) 
                continue;

            // quick check to determine whether n can be used as a candidate
            expr_ref eq(m.mk_eq(r->get_root()->get_expr(), n->get_root()->get_expr()), m);
            euf::enode* eq_n = expr2enode(eq);
            if (eq_n && eq_n->bool_var() != sat::null_bool_var &&
                s().value(eq_n->bool_var()) == l_false)
                continue;
            candidates.push_back(n);
        }
        for (auto* n : candidates) {
            // euf check if n can be used as a candidate
            bool can_use = false;
            egraph.push();
            egraph.merge(r, n, nullptr);
            if (!egraph.propagate())
                can_use = true;
            egraph.pop(1);

            if (can_use) {
                obj.set_solution(n->get_expr());
                ctx.push(synth_objective::unset_solution(obj));
                return true;
            }
        }

        verbose_stream() << "synth-uninterp failed\n";
        return false;
    }

    bool solver::synthesize_arithmetic(synth_objective& obj) {
        arith_util a(m);
        if (!a.is_int_real(obj.output()))
            return false;
        model_ref mdl = alloc(model, m);
        ctx.update_model(mdl, false);
        verbose_stream() << "int-real-objective\n";
        verbose_stream() << *mdl << "\n";

        expr_ref_vector lits(m), core(m);
        for (unsigned i = 0; i < s().trail_size(); ++i) {
            sat::literal l = s().trail_literal(i);
            if (!ctx.is_relevant(l))
                continue;
            expr_ref e = literal2expr(l);
            if (e)
                lits.push_back(e);            
        }
        verbose_stream() << lits << "\n";

        sat::no_drat_params                    no_drat_params;
        ref<::solver> solver = mk_smt2_solver(m, no_drat_params, symbol::null);
        solver->assert_expr(m.mk_not(m.mk_and(m_spec)));
        lbool r = solver->check_sat(lits);
        if (r != l_false)
            return false;
        solver->get_unsat_core(core);
        verbose_stream() << "core " << core << "\n";

        qe::uflia_project proj(m);
        auto& egraph = ctx.get_egraph();
        func_decl_ref_vector shared(m);
        ast_mark visited;
        for (auto* n : egraph.nodes())
            if (is_app(n->get_expr()) && !is_output(n->get_expr()) && !m_uncomputable.contains(n->get_decl()) && !visited.is_marked(n->get_decl())) {
                visited.mark(n->get_decl(), true);
                shared.push_back(n->get_decl());
            }
        verbose_stream() << "shared " << shared << "\n";
        proj.set_shared(shared);
        auto defs = proj.project_solve(mdl, core);

        for (auto const& d : defs) {
            verbose_stream() << d.var << " := " << d.term << "\n";
            if (d.var == obj.output()) {
                obj.set_solution(d.term);
                ctx.push(synth_objective::unset_solution(obj));
                return true;
            }
        }
#if 0
        // - retrieve literal dependencies
        // - difference cert?
        // - split arith?
        // - split_arith, arith_vars, rpoejct, project_euf,
        // produce projection

        add_dcert(mdl, lits);
        expr_ref_vector alits(m), uflits(m);
        split_arith(lits, alits, uflits);
        auto avars = get_arith_vars(lits);
        vector<mbp::def> defs = arith_project(mdl, avars, alits);
        for (auto const& d : defs) uflits.push_back(m.mk_eq(d.var, d.term));
        TRACE("qe", tout << "uflits: " << uflits << "\n";);
        project_euf(mdl, uflits);
        lits.reset();
        lits.append(alits);
        lits.append(uflits);
#endif
        return false;
    }


}
