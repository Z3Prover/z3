/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    intblast_solver.cpp

Author:

    Nikolaj Bjorner (nbjorner) 2023-12-10

--*/

#include "ast/ast_util.h"
#include "ast/for_each_expr.h"
#include "ast/rewriter/bv_rewriter.h"
#include "params/bv_rewriter_params.hpp"
#include "sat/smt/intblast_solver.h"
#include "sat/smt/euf_solver.h"
#include "sat/smt/arith_value.h"


namespace intblast {

    void translator_trail::push(push_back_vector<expr_ref_vector> const& c) { ctx.push(c); }
    void translator_trail::push(push_back_vector<ptr_vector<app>> const& c) { ctx.push(c); }
    void translator_trail::push_idx(set_vector_idx_trail<expr_ref_vector> const& c) { ctx.push(c); }

    solver::solver(euf::solver& ctx) :
        th_euf_solver(ctx, symbol("intblast"), ctx.get_manager().get_family_id("bv")),
        ctx(ctx),
        s(ctx.s()),
        m(ctx.get_manager()),
        bv(m),
        a(m),
        trail(ctx),
        m_translator(m, trail)
    {}

    euf::theory_var solver::mk_var(euf::enode* n) {
        auto r = euf::th_euf_solver::mk_var(n);
        ctx.attach_th_var(n, this, r);
        TRACE("bv", tout << "mk-var: v" << r << " " << ctx.bpp(n) << "\n";);
        return r;
    }

    sat::literal solver::internalize(expr* e, bool sign, bool root) {
        force_push();
        SASSERT(m.is_bool(e));
        if (!visit_rec(m, e, sign, root))
            return sat::null_literal;
        sat::literal lit = expr2literal(e);
        if (sign)
            lit.neg();
        TRACE("bv", tout << mk_pp(e, m) << " -> " << literal2expr(lit) << "\n");
        return lit;
    }

    void solver::internalize(expr* e) {
        force_push();
        visit_rec(m, e, false, false);
    }

    bool solver::visit(expr* e) {
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
        m_translator.internalize_bv(a);
        return true;
    }

    void solver::eq_internalized(euf::enode* n) {
        m_translator.translate_eq(n->get_expr());
    }

    bool solver::add_bound_axioms() {
        auto const& vars = m_translator.vars();
        if (m_vars_qhead == vars.size())
            return false;
        ctx.push(value_trail(m_vars_qhead));
        for (; m_vars_qhead < vars.size(); ++m_vars_qhead) {
            auto v = vars[m_vars_qhead];
            auto w = m_translator.translated(v);
            auto sz = rational::power_of_two(bv.get_bv_size(v->get_sort()));
            auto lo = ctx.mk_literal(a.mk_ge(w, a.mk_int(0)));
            auto hi = ctx.mk_literal(a.mk_le(w, a.mk_int(sz - 1)));
            ctx.mark_relevant(lo);
            ctx.mark_relevant(hi);
            add_unit(lo);
            add_unit(hi);
        }
        return true;
    }

    bool solver::add_predicate_axioms() {
        auto const& preds = m_translator.preds();
        if (m_preds_qhead == preds.size())
            return false;
        ctx.push(value_trail(m_preds_qhead));
        for (; m_preds_qhead < preds.size(); ++m_preds_qhead) {
            expr* e = preds[m_preds_qhead];
            expr_ref r(m_translator.translated(e), m);
            ctx.get_rewriter()(r);
            auto a = expr2literal(e);
            auto b = mk_literal(r);
            ctx.mark_relevant(b);
//            verbose_stream() << "add-predicate-axiom: " << mk_pp(e, m) << " == " << r << "\n";
            add_equiv(a, b);
        }
        return true;
    }

    bool solver::unit_propagate() {
        return add_bound_axioms() || add_predicate_axioms();
    }    

    lbool solver::check_axiom(sat::literal_vector const& lits) {
        sat::literal_vector core;
        for (auto lit : lits)
            core.push_back(~lit);
        return check_core(core, {});
    }
    lbool solver::check_propagation(sat::literal lit, sat::literal_vector const& lits, euf::enode_pair_vector const& eqs) {
        sat::literal_vector core;
        core.append(lits);
        core.push_back(~lit);
        return check_core(core, eqs);
    }

    lbool solver::check_core(sat::literal_vector const& lits, euf::enode_pair_vector const& eqs) {
        m_is_plugin = false;
        m_translator.reset(false);
        m_solver = mk_smt2_solver(m, s.params(), symbol::null);

        expr_ref_vector es(m), original_es(m);
        for (auto lit : lits)
            es.push_back(ctx.literal2expr(lit));
        for (auto [a, b] : eqs)
            es.push_back(m.mk_eq(a->get_expr(), b->get_expr()));
        
        original_es.append(es);

        lbool r;
        if (false) {
            r = m_solver->check_sat(es);            
        }
        else {
        
            translate(es);
            
            for (auto e : m_translator.vars()) {
                auto v = m_translator.translated(e);
                auto b = rational::power_of_two(bv.get_bv_size(e));
                m_solver->assert_expr(a.mk_le(a.mk_int(0), v));
                m_solver->assert_expr(a.mk_lt(v, a.mk_int(b)));
            }

            for (unsigned i = 0; i < es.size(); ++i) {
                expr_ref tmp(es.get(i), m);
                ctx.get_rewriter()(tmp);
                es[i] = tmp;
            }

            IF_VERBOSE(2, verbose_stream() << "check\n" << original_es << "\n");
            
            IF_VERBOSE(2,
                {
                    m_solver->push();
                    m_solver->assert_expr(es);
                    m_solver->display(verbose_stream()) << "(check-sat)\n";
                    m_solver->pop(1);
                });

            
            r = m_solver->check_sat(es);
        }

        m_solver->collect_statistics(m_stats);

        IF_VERBOSE(2, verbose_stream() << "(sat.intblast :result " << r << ")\n");
        if (r == l_true) {
            IF_VERBOSE(0,
                model_ref mdl;
                m_solver->get_model(mdl);
                verbose_stream() << original_es << "\n";
                verbose_stream() << *mdl << "\n";
                verbose_stream() << es << "\n";
                m_solver->display(verbose_stream()););
            SASSERT(false);
        }

        m_solver = nullptr;

        return r;
    }

    

    lbool solver::check_solver_state() {
        sat::literal_vector literals;
        uint_set selected;
        for (auto const& clause : s.clauses()) {
            if (any_of(*clause, [&](auto lit) { return selected.contains(lit.index()); }))
                continue;
            if (any_of(*clause, [&](auto lit) { return s.value(lit) == l_true && !is_bv(lit); }))
                continue;
            // TBD: if we associate "status" with clauses, we can also remove theory axioms from polysat
            sat::literal selected_lit = sat::null_literal;
            for (auto lit : *clause) {
                if (s.value(lit) != l_true)
                    continue;
                SASSERT(is_bv(lit));
                if (selected_lit == sat::null_literal || s.lvl(selected_lit) > s.lvl(lit))
                    selected_lit = lit;
            }
            if (selected_lit == sat::null_literal) {
                UNREACHABLE();
                return l_undef;
            }
            selected.insert(selected_lit.index());
            literals.push_back(selected_lit);
        }
        unsigned trail_sz = s.init_trail_size();
        for (unsigned i = 0; i < trail_sz; ++i) {
            auto lit = s.trail_literal(i);
            if (selected.contains(lit.index()) || !is_bv(lit))
                continue;
            selected.insert(lit.index());
            literals.push_back(lit);
        }
        svector<std::pair<sat::literal, sat::literal>> bin;
        s.collect_bin_clauses(bin, false, false);
        for (auto [a, b] : bin) {
            if (selected.contains(a.index()))
                continue;
            if (selected.contains(b.index()))
                continue;
            if (s.value(a) == l_true && !is_bv(a))
                continue;
            if (s.value(b) == l_true && !is_bv(b))
                continue;
            if (s.value(a) == l_false)
                std::swap(a, b);
            if (s.value(b) == l_true && s.value(a) == l_true && s.lvl(b) < s.lvl(a))
                std::swap(a, b);
            selected.insert(a.index());
            literals.push_back(a);
        }

        m_core.reset();
        m_is_plugin = false;
        m_solver = mk_smt2_solver(m, s.params(), symbol::null);

        expr_ref_vector es(m);
        for (auto lit : literals)
            es.push_back(ctx.literal2expr(lit));

        translate(es);

        for (auto e : m_translator.vars()) {
            auto v = m_translator.translated(e);
            auto b = rational::power_of_two(bv.get_bv_size(e));
            m_solver->assert_expr(a.mk_le(a.mk_int(0), v));
            m_solver->assert_expr(a.mk_lt(v, a.mk_int(b)));
        }

        IF_VERBOSE(10, verbose_stream() << "check\n";
        m_solver->display(verbose_stream());
        verbose_stream() << es << "\n");

        lbool r = m_solver->check_sat(es);

        m_solver->collect_statistics(m_stats);

        IF_VERBOSE(2, verbose_stream() << "(sat.intblast :result " << r << ")\n");

        if (r == l_false) {
            expr_ref_vector core(m);
            m_solver->get_unsat_core(core);
            obj_map<expr, unsigned> e2index;
            for (unsigned i = 0; i < es.size(); ++i)
                e2index.insert(es.get(i), i);
            for (auto e : core) {
                unsigned idx = e2index[e];
                if (idx < literals.size())
                    m_core.push_back(literals[idx]);
                else
                    m_core.push_back(ctx.mk_literal(e));
            }
        }
        return r;
    };

    bool solver::is_bv(sat::literal lit) {
        expr* e = ctx.bool_var2expr(lit.var());
        if (!e)
            return false;
        if (m.is_and(e) || m.is_or(e) || m.is_not(e) || m.is_implies(e) || m.is_iff(e))
            return false;
        return any_of(subterms::all(expr_ref(e, m)), [&](auto* p) { return bv.is_bv_sort(p->get_sort()); });
    }

    void solver::sorted_subterms(expr_ref_vector& es, ptr_vector<expr>& sorted) {
        expr_fast_mark1 visited;
        for (expr* e : es) {
            if (m_translator.is_translated(e))
                continue;
            if (visited.is_marked(e))
                continue;
            sorted.push_back(e);
            visited.mark(e);
        }
        for (unsigned i = 0; i < sorted.size(); ++i) {
            expr* e = sorted[i];
            if (is_app(e)) {
                app* a = to_app(e);
                for (expr* arg : *a) {
                    if (!visited.is_marked(arg) && !m_translator.is_translated(arg)) {
                        visited.mark(arg);
                        sorted.push_back(arg);
                    }
                }

            }
            else if (is_quantifier(e)) {
                quantifier* q = to_quantifier(e);
                expr* b = q->get_expr();
                if (!visited.is_marked(b) && !m_translator.is_translated(b)) {
                    visited.mark(b);
                    sorted.push_back(b);
                }
            }
        }
        std::stable_sort(sorted.begin(), sorted.end(), [&](expr* a, expr* b) { return get_depth(a) < get_depth(b); });
    }

    void solver::translate(expr_ref_vector& es) {
        ptr_vector<expr> todo;

        sorted_subterms(es, todo);

        for (expr* e : todo)
            m_translator.translate_expr(e);

        TRACE("bv",
            for (expr* e : es)
                tout << mk_pp(e, m) << "\n->\n" << mk_pp(m_translator.translated(e), m) << "\n";
        );

        for (unsigned i = 0; i < es.size(); ++i)
            es[i] = m_translator.translated(es.get(i));
    }

    sat::check_result solver::check() { 
        // ensure that bv2int is injective
        for (auto e : m_translator.bv2int()) {
            euf::enode* n = expr2enode(e);
            euf::enode* r1 = n->get_arg(0)->get_root();
            for (auto sib : euf::enode_class(n)) {
                if (sib == n)
                    continue;
                if (!bv.is_ubv2int(sib->get_expr()))
                    continue;
                if (sib->get_arg(0)->get_root() == r1)
                    continue;
                if (bv.get_bv_size(r1->get_expr()) != bv.get_bv_size(sib->get_arg(0)->get_expr()))
                    continue;
                auto a = eq_internalize(n, sib);
                auto b = eq_internalize(sib->get_arg(0), n->get_arg(0));
                ctx.mark_relevant(a);
                ctx.mark_relevant(b);
                add_clause(~a, b, nullptr);
                return sat::check_result::CR_CONTINUE;
            }
        }
        // ensure that int2bv respects values
        // bv2int(int2bv(x)) = x mod N
        for (auto e : m_translator.int2bv()) {
            auto n = expr2enode(e);
            auto x = n->get_arg(0)->get_expr();
            auto bv2int = bv.mk_ubv2int(e);
            ctx.internalize(bv2int);
            auto N = rational::power_of_two(bv.get_bv_size(e));
            auto xModN = a.mk_mod(x, a.mk_int(N));
            ctx.internalize(xModN);
            auto nBv2int = ctx.get_enode(bv2int);
            auto nxModN = ctx.get_enode(xModN);
            if (nBv2int->get_root() != nxModN->get_root()) {
                auto a = eq_internalize(nBv2int, nxModN);
                ctx.mark_relevant(a);
                add_unit(a);
                return sat::check_result::CR_CONTINUE;
            }
        }
        return sat::check_result::CR_DONE; 
    }

    rational solver::get_value(expr* e) const {
        SASSERT(bv.is_bv(e));
        model_ref mdl;
        m_solver->get_model(mdl);
        expr_ref r(m);
        r = m_translator.translated(e);
        rational val;
        if (!mdl->eval_expr(r, r, true))
            return rational::zero();
        if (!a.is_numeral(r, val))
            return rational::zero();
        return val;
    }

    void solver::add_value(euf::enode* n, model& mdl, expr_ref_vector& values) {
        if (m_is_plugin)
            add_value_plugin(n, mdl, values);
        else
            add_value_solver(n, mdl, values);
    }

    bool solver::add_dep(euf::enode* n, top_sort<euf::enode>& dep) {
        if (!is_app(n->get_expr()))
            return false;
        app* e = to_app(n->get_expr());
        if (n->num_args() == 0) {
            dep.insert(n, nullptr);
            return true;
        }
        if (e->get_family_id() != bv.get_family_id())
            return false;
        for (euf::enode* arg : euf::enode_args(n))
            dep.add(n, arg);
        return true;
    }

    // TODO: handle dependencies properly by using arithmetical model to retrieve values of translated 
    // bit-vectors directly.
    void solver::add_value_solver(euf::enode* n, model& mdl, expr_ref_vector& values) {
        expr* e = n->get_expr();
        SASSERT(bv.is_bv(e));
        if (bv.is_numeral(e)) {
            values.setx(n->get_root_id(), e);
            return;
        }

        rational r, N = rational::power_of_two(bv.get_bv_size(e));
        expr* te = m_translator.translated(e);
        model_ref mdlr;
        m_solver->get_model(mdlr);
        expr_ref value(m);
        if (mdlr->eval_expr(te, value, true) && a.is_numeral(value, r)) {
            values.setx(n->get_root_id(), bv.mk_numeral(mod(r, N), bv.get_bv_size(e)));
            return;
        }
        ctx.s().display(verbose_stream());
        verbose_stream() << "failed to evaluate " << mk_pp(te, m) << " " << value << "\n";
        UNREACHABLE();
    }

    void solver::add_value_plugin(euf::enode* n, model& mdl, expr_ref_vector& values) {
        expr_ref value(m);
        if (n->interpreted())
            value = n->get_expr();
        else if (to_app(n->get_expr())->get_family_id() == bv.get_family_id()) {
            bv_rewriter rw(m);
            expr_ref_vector args(m);
            for (auto arg : euf::enode_args(n))
                args.push_back(values.get(arg->get_root_id()));
            rw.mk_app(n->get_decl(), args.size(), args.data(), value);
        }
        else {
            expr_ref bv2int(bv.mk_ubv2int(n->get_expr()), m);
            euf::enode* b2i = ctx.get_enode(bv2int);
            SASSERT(b2i);
            VERIFY(b2i);
            arith::arith_value av(ctx);
            rational r;
            VERIFY(av.get_value(b2i->get_expr(), r));
            value = bv.mk_numeral(r, bv.get_bv_size(n->get_expr()));
        }
        values.set(n->get_root_id(), value);
        TRACE("model", tout << "add_value " << ctx.bpp(n) << " := " << value << "\n");
    }

    void solver::finalize_model(model& mdl) {
        return;
        for (auto n : ctx.get_egraph().nodes()) {
            auto e = n->get_expr();            
            if (!m_translator.is_translated(e))
                continue;
            if (!bv.is_bv(e))
                continue;
            auto t = m_translator.translated(e);
            
            expr_ref ei(bv.mk_ubv2int(e), m);
            expr_ref ti(a.mk_mod(t, a.mk_int(rational::power_of_two(bv.get_bv_size(e)))), m);
            auto ev = mdl(ei);
            auto tv = mdl(ti);
            if (ev != tv) {
                IF_VERBOSE(0, verbose_stream() << mk_pp(e, m) << " <- " << ev << "\n");
                IF_VERBOSE(0, verbose_stream() << mk_pp(t, m) << " <- " << tv << "\n");
            }
        }
    }

    sat::literal_vector const& solver::unsat_core() {
        return m_core;
    }

    std::ostream& solver::display(std::ostream& out) const {
        if (m_solver)
            m_solver->display(out);
        return out;
    }

    void solver::collect_statistics(statistics& st) const {
        st.copy(m_stats);
    }

}
