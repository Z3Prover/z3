/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    synth_solver.h

Author:

    Petra Hozzova 2023-08-08
    Nikolaj Bjorner (nbjorner) 2020-08-17

--*/

#include "ast/for_each_expr.h"
#include "ast/synth_decl_plugin.h"
#include "sat/smt/synth_solver.h"
#include "sat/smt/euf_solver.h"

namespace synth {

    solver::solver(euf::solver& ctx):
        th_euf_solver(ctx, symbol("synth"), ctx.get_manager().mk_family_id("synth")) {
        std::function<void(euf::enode*, euf::enode*)> _on_merge = 
            [&](euf::enode* root, euf::enode* other) { 
            on_merge_eh(root, other); 
        };
        ctx.get_egraph().set_on_merge(_on_merge);
    }
        
    solver::~solver() {}

    bool solver::contains_uncomputable(expr* e) {
        
        auto is_output = [&](expr* e) {
            return any_of(m_synth, [&](app* a) { return a->get_arg(0) == e; });
        };
        return any_of(subterms::all(expr_ref(e, m)), [&](expr* a) { return (is_app(a) && m_uncomputable.contains(to_app(a)->get_decl())) || is_output(a); });
    }

    sat::literal solver::synthesize(app* e) {

        if (e->get_num_args() == 0)
            return sat::null_literal;

        expr_ref sol = compute_solution(e);
        if (!sol)
            return sat::null_literal;

        IF_VERBOSE(0, verbose_stream() << sol << "\n");
        return eq_internalize(e->get_arg(0), sol);
    }

    // block current model using realizer by E-graph (and arithmetic)
    // 
    sat::check_result solver::check() {
        sat::literal_vector clause;
	for (app* e : m_synth) {
	    auto lit = synthesize(e);
            if (lit == sat::null_literal)
                return sat::check_result::CR_GIVEUP;
            clause.push_back(~lit);
        }
        if (clause.empty())
            return sat::check_result::CR_DONE;
        add_clause(clause);
        return sat::check_result::CR_CONTINUE; 
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

    void solver::add_synth_objective(app* e) {
        ctx.push_vec(m_synth, e);
        for (unsigned i = 1; i < e->get_num_args(); ++i) {
            m_is_computable.reserve(e->get_arg(i)->get_id() + 1);
            ctx.push(set_bitvector_trail(m_is_computable, e->get_arg(i)->get_id())); // TODO use enode roots instead and test if they are already set.
        }
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
        if (util.is_synthesiz3(e))
            add_synth_objective(to_app(e));
        if (util.is_grammar(e))
	    add_uncomputable(to_app(e));
    }

    // display current state (eg. current set of realizers)
    std::ostream& solver::display(std::ostream& out) const {
        for (auto * e : m_synth)
            out << "synth objective " << mk_pp(e, m) << "\n";            
        return out;
    }

    // create a clone of the solver.
    euf::th_solver* solver::clone(euf::solver& ctx) {
        return alloc(solver, ctx);
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

        for (app* e : m_synth) {
            euf::enode* n = expr2enode(e->get_arg(0));
            if (is_computable(n)) {
                expr_ref sol = compute_solution(e);
                verbose_stream() << "solution " << sol << "\n";
                ctx.push_vec(m_blockers, ~eq_internalize(sol, n->get_expr()));                
            }
        }
    }

    bool solver::unit_propagate() {
        if (m_blockers_qhead >= m_blockers.size())
            return false;
        IF_VERBOSE(2, verbose_stream() << "propagate " << m_blockers_qhead << " " << m_blockers << "\n");
        ctx.push(value_trail(m_blockers_qhead));
        while (m_blockers_qhead++ < m_blockers.size())
            add_unit(m_blockers[m_blockers_qhead-1]);
        return true;
    }

    expr_ref solver::compute_solution(app* e) {
        auto * n = expr2enode(e->get_arg(0));
	expr_ref_vector repr(m);
        auto get_rep = [&](euf::enode* n) { return repr.get(n->get_root_id(), nullptr); };
        auto has_rep = [&](euf::enode* n) { return !!get_rep(n); };
        auto set_rep = [&](euf::enode* n, expr* e) { repr.setx(n->get_root_id(), e); };
        auto is_uncomputable = [&](func_decl* f) { return m_uncomputable.contains(f); };

	euf::enode_vector todo;                
        
	for (unsigned i = 1; i < e->get_num_args(); ++i) {
	    expr * arg = e->get_arg(i);
	    auto * narg = expr2enode(arg);
	    todo.push_back(narg);
	    set_rep(narg, arg);
        }
	for (unsigned i = 0; i < todo.size() && !has_rep(n); ++i) {
	    auto * nn = todo[i];
            for (auto * p : euf::enode_parents(nn)) {
	        if (has_rep(p))
                    continue;
                if (is_uncomputable(p->get_decl()))
                    continue;
                if (!all_of(euf::enode_args(p), [&](auto * ch) { return has_rep(ch); }))
                    continue;
                ptr_buffer<expr> args;
                for (auto * ch : euf::enode_args(p))
                    args.push_back(get_rep(ch));
                app * papp = m.mk_app(p->get_decl(), args);
                set_rep(p, papp);
                todo.push_back(p);
            }
	}
        return expr_ref(get_rep(n), m);        
    }

}
