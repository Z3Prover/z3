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

    solver::solver(euf::solver& ctx) :
        th_euf_solver(ctx, symbol("intblast"), ctx.get_manager().get_family_id("bv")),
        ctx(ctx),
        s(ctx.s()),
        m(ctx.get_manager()),
        bv(m),
        a(m),
        m_translate(m),
        m_args(m),
        m_pinned(m)
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
        internalize_bv(a);
        return true;
    }

    void solver::eq_internalized(euf::enode* n) {
        expr* e = n->get_expr();
        expr* x = nullptr, * y = nullptr;
        VERIFY(m.is_eq(n->get_expr(), x, y));
        SASSERT(bv.is_bv(x));
        if (!is_translated(e)) {
            ensure_translated(x);
            ensure_translated(y);
            m_args.reset();
            m_args.push_back(a.mk_sub(translated(x), translated(y)));
            set_translated(e, m.mk_eq(umod(x, 0), a.mk_int(0)));
        }
        m_preds.push_back(e);
        TRACE("bv", tout << mk_pp(e, m) << " " << mk_pp(translated(e), m) << "\n");
        ctx.push(push_back_vector(m_preds));
    }

    void solver::set_translated(expr* e, expr* r) { 
        SASSERT(r);
        SASSERT(!is_translated(e));          
        m_translate.setx(e->get_id(), r); 
        ctx.push(set_vector_idx_trail(m_translate, e->get_id()));
    }

    void solver::internalize_bv(app* e) {
        ensure_translated(e);
        if (m.is_bool(e)) {
            m_preds.push_back(e);
            ctx.push(push_back_vector(m_preds));
        }
    }

    bool solver::add_bound_axioms() {
        if (m_vars_qhead == m_vars.size())
            return false;
        ctx.push(value_trail(m_vars_qhead));
        for (; m_vars_qhead < m_vars.size(); ++m_vars_qhead) {
            auto v = m_vars[m_vars_qhead];
            auto w = translated(v);
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
        if (m_preds_qhead == m_preds.size())
            return false;
        ctx.push(value_trail(m_preds_qhead));
        for (; m_preds_qhead < m_preds.size(); ++m_preds_qhead) {
            expr* e = m_preds[m_preds_qhead];
            expr_ref r(translated(e), m);
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
    void solver::ensure_translated(expr* e) {
        if (m_translate.get(e->get_id(), nullptr))
            return;
        ptr_vector<expr> todo;
        ast_fast_mark1 visited;
        todo.push_back(e);
        visited.mark(e);
        for (unsigned i = 0; i < todo.size(); ++i) {
            expr* e = todo[i];
            if (!is_app(e))
                continue;
            app* a = to_app(e);
            if (m.is_bool(e) && a->get_family_id() != bv.get_family_id())
                continue;
            for (auto arg : *a)
                if (!visited.is_marked(arg) && !m_translate.get(arg->get_id(), nullptr)) {
                    visited.mark(arg);
                    todo.push_back(arg);
                }
        }
        std::stable_sort(todo.begin(), todo.end(), [&](expr* a, expr* b) { return get_depth(a) < get_depth(b); });
        for (expr* e : todo)            
            translate_expr(e);
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
        m_core.reset();
        m_vars.reset();
        m_is_plugin = false;
        m_solver = mk_smt2_solver(m, s.params(), symbol::null);

        for (unsigned i = 0; i < m_translate.size(); ++i)
            m_translate[i] = nullptr;

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
            
            for (auto e : m_vars) {
                auto v = translated(e);
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

        for (auto e : m_vars) {
            auto v = translated(e);
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
            if (is_translated(e))
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
                    if (!visited.is_marked(arg) && !is_translated(arg)) {
                        visited.mark(arg);
                        sorted.push_back(arg);
                    }
                }

            }
            else if (is_quantifier(e)) {
                quantifier* q = to_quantifier(e);
                expr* b = q->get_expr();
                if (!visited.is_marked(b) && !is_translated(b)) {
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
            translate_expr(e);

        TRACE("bv",
            for (expr* e : es)
                tout << mk_pp(e, m) << "\n->\n" << mk_pp(translated(e), m) << "\n";
        );

        for (unsigned i = 0; i < es.size(); ++i)
            es[i] = translated(es.get(i));
    }

    sat::check_result solver::check() { 
        // ensure that bv2int is injective
        for (auto e : m_bv2int) {
            euf::enode* n = expr2enode(e);
            euf::enode* r1 = n->get_arg(0)->get_root();
            for (auto sib : euf::enode_class(n)) {
                if (sib == n)
                    continue;
                if (!bv.is_bv2int(sib->get_expr()))
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
        for (auto e : m_int2bv) {
            auto n = expr2enode(e);
            auto x = n->get_arg(0)->get_expr();
            auto bv2int = bv.mk_bv2int(e);
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

    bool solver::is_bounded(expr* x, rational const& N) {
        return any_of(m_vars, [&](expr* v) {
            return is_translated(v) && translated(v) == x && bv_size(v) <= N;
        });
    }

    bool solver::is_non_negative(expr* bv_expr, expr* e) {
        auto N = rational::power_of_two(bv.get_bv_size(bv_expr));
        rational r;
        if (a.is_numeral(e, r))
            return r >= 0;
        if (is_bounded(e, N))
            return true;
        expr* x = nullptr, * y = nullptr;
        if (a.is_mul(e, x, y)) 
            return is_non_negative(bv_expr, x) && is_non_negative(bv_expr, y);
        if (a.is_add(e, x, y))
            return is_non_negative(bv_expr, x) && is_non_negative(bv_expr, y);
        return false;
    }

    expr* solver::umod(expr* bv_expr, unsigned i) {
        expr* x = arg(i);
        rational N = bv_size(bv_expr);
        return amod(bv_expr, x, N);
    }

    expr* solver::smod(expr* bv_expr, unsigned i) {
        expr* x = arg(i);
        auto N = bv_size(bv_expr);
        auto shift = N / 2;
        rational r;
        if (a.is_numeral(x, r))
            return a.mk_int(mod(r + shift, N));
        return amod(bv_expr, add(x, a.mk_int(shift)), N);
    }

    expr_ref solver::mul(expr* x, expr* y) {
        expr_ref _x(x, m), _y(y, m);
        if (a.is_zero(x))
            return _x;
        if (a.is_zero(y))
            return _y;
        if (a.is_one(x))
            return _y;
        if (a.is_one(y))
            return _x;
        rational v1, v2;
        if (a.is_numeral(x, v1) && a.is_numeral(y, v2))
            return expr_ref(a.mk_int(v1 * v2), m);
        _x = a.mk_mul(x, y);
        return _x;
    }

    expr_ref solver::add(expr* x, expr* y) {
        expr_ref _x(x, m), _y(y, m);
        if (a.is_zero(x))
            return _y;
        if (a.is_zero(y))
            return _x;
        rational v1, v2;
        if (a.is_numeral(x, v1) && a.is_numeral(y, v2))
            return expr_ref(a.mk_int(v1 + v2), m);
        _x = a.mk_add(x, y);
        return _x;
    }

    /*
    * Perform simplifications that are claimed sound when the bit-vector interpretations of
    * mod/div always guard the mod and dividend to be non-zero.
    * Potentially shady area is for arithmetic expressions created by int2bv. 
    * They will be guarded by a modulus which does not disappear.
    */
    expr* solver::amod(expr* bv_expr, expr* x, rational const& N) {
        rational v;
        expr* r = nullptr, *c = nullptr, * t = nullptr, * e = nullptr;
        if (m.is_ite(x, c, t, e))
            r = m.mk_ite(c, amod(bv_expr, t, N), amod(bv_expr, e, N));
        else if (a.is_idiv(x, t, e) && a.is_numeral(t, v) && 0 <= v && v < N && is_non_negative(bv_expr, e))
            r = x;
        else if (a.is_mod(x, t, e) && a.is_numeral(t, v) && 0 <= v && v < N)
            r = x;
        else if (a.is_numeral(x, v))
            r = a.mk_int(mod(v, N));
        else if (is_bounded(x, N))
            r = x;
        else 
            r = a.mk_mod(x, a.mk_int(N));
        return r;
    }

    rational solver::bv_size(expr* bv_expr) {
        return rational::power_of_two(bv.get_bv_size(bv_expr->get_sort()));
    }

    void solver::translate_expr(expr* e) {
        if (is_quantifier(e))
            translate_quantifier(to_quantifier(e));
        else if (is_var(e))
            translate_var(to_var(e));
        else {
            app* ap = to_app(e);
            if (m_is_plugin && ap->get_family_id() == basic_family_id && m.is_bool(ap)) {
                set_translated(e, e);
                return;
            }
            m_args.reset();
            for (auto arg : *ap)
                m_args.push_back(translated(arg));

            if (ap->get_family_id() == basic_family_id)
                translate_basic(ap);
            else if (ap->get_family_id() == bv.get_family_id())
                translate_bv(ap);
            else
                translate_app(ap);
        }
    }

    void solver::translate_quantifier(quantifier* q) {
        if (m_is_plugin) {
            set_translated(q, q);
            return;
        }
        if (is_lambda(q))
            throw default_exception("lambdas are not supported in intblaster");
        expr* b = q->get_expr();
        unsigned nd = q->get_num_decls();
        ptr_vector<sort> sorts;
        for (unsigned i = 0; i < nd; ++i) {
            auto s = q->get_decl_sort(i);
            if (bv.is_bv_sort(s)) {
                NOT_IMPLEMENTED_YET();
                sorts.push_back(a.mk_int());
            }
            else
                sorts.push_back(s);
        }
        b = translated(b);
        // TODO if sorts contain integer, then created bounds variables.       
        set_translated(q, m.update_quantifier(q, b));
    }

    void solver::translate_var(var* v) {
        if (bv.is_bv_sort(v->get_sort()))
            set_translated(v, m.mk_var(v->get_idx(), a.mk_int()));
        else
            set_translated(v, v);
    }

    // Translate functions that are not built-in or bit-vectors.
    // Base method uses fresh functions.
    // Other method could use bv2int, int2bv axioms and coercions.
    // f(args) = bv2int(f(int2bv(args'))
    //

    void solver::translate_app(app* e) {

        if (m_is_plugin && m.is_bool(e)) {
            set_translated(e, e);
            return;
        }

        bool has_bv_sort = bv.is_bv(e);
        func_decl* f = e->get_decl();

        for (unsigned i = 0; i < m_args.size(); ++i)
            if (bv.is_bv(e->get_arg(i)))
                m_args[i] = bv.mk_int2bv(bv.get_bv_size(e->get_arg(i)), m_args.get(i));

        if (has_bv_sort)
            m_vars.push_back(e);        
        if (m_is_plugin) {
            expr* r = m.mk_app(f, m_args);
            if (has_bv_sort) {
                ctx.push(push_back_vector(m_vars));
                r = bv.mk_bv2int(r);
            }
            set_translated(e, r);
            return;
        }
        else if (has_bv_sort) {
            if (f->get_family_id() != null_family_id)
                throw default_exception("conversion for interpreted functions is not supported by intblast solver");
            func_decl* g = nullptr;
            if (!m_new_funs.find(f, g)) {
                g = m.mk_fresh_func_decl(e->get_decl()->get_name(), symbol("bv"), f->get_arity(), f->get_domain(), a.mk_int());
                m_new_funs.insert(f, g);
            }
            f = g;
            m_pinned.push_back(f);
        }
        set_translated(e, m.mk_app(f, m_args));        
    }

    void solver::translate_bv(app* e) {

        auto bnot = [&](expr* e) {
            return a.mk_sub(a.mk_int(-1), e);
            };

        auto band = [&](expr_ref_vector const& args) {
            expr* r = arg(0);
            for (unsigned i = 1; i < args.size(); ++i)
                r = a.mk_band(bv.get_bv_size(e), r, arg(i));
            return r;
            };

        auto rotate_left = [&](unsigned n) {
            auto sz = bv.get_bv_size(e);
            n = n % sz;
            expr* r = arg(0);
            if (n != 0 && sz != 1) {
                // r[sz - n - 1 : 0] ++ r[sz - 1 : sz - n]
                // r * 2^(sz - n) + (r div 2^n) mod 2^(sz - n)???
                // r * A + (r div B) mod A
                auto N = bv_size(e);
                auto A = rational::power_of_two(sz - n);
                auto B = rational::power_of_two(n);
                auto hi = mul(r, a.mk_int(A));
                auto lo = amod(e, a.mk_idiv(umod(e, 0), a.mk_int(B)), A);
                r = add(hi, lo);
            }
            return r;
        };

        expr* bv_expr = e;
        expr_ref r(m);
        auto const& args = m_args;
        switch (e->get_decl_kind()) {
        case OP_BADD:
            r = a.mk_add(args);
            break;
        case OP_BSUB:
            r = a.mk_sub(args.size(), args.data());
            break;
        case OP_BMUL:
            r = a.mk_mul(args);
            break;
        case OP_ULEQ:
            bv_expr = e->get_arg(0);
            r = a.mk_le(umod(bv_expr, 0), umod(bv_expr, 1));
            break;
        case OP_UGEQ:
            bv_expr = e->get_arg(0);
            r = a.mk_ge(umod(bv_expr, 0), umod(bv_expr, 1));
            break;
        case OP_ULT:
            bv_expr = e->get_arg(0);
            r = a.mk_lt(umod(bv_expr, 0), umod(bv_expr, 1));
            break;
        case OP_UGT:
            bv_expr = e->get_arg(0);
            r = a.mk_gt(umod(bv_expr, 0), umod(bv_expr, 1));
            break;
        case OP_SLEQ:
            bv_expr = e->get_arg(0);
            r = a.mk_le(smod(bv_expr, 0), smod(bv_expr, 1));
            break;
        case OP_SGEQ:
            bv_expr = e->get_arg(0);
            r = a.mk_ge(smod(bv_expr, 0), smod(bv_expr, 1));
            break;
        case OP_SLT:
            bv_expr = e->get_arg(0);
            r = a.mk_lt(smod(bv_expr, 0), smod(bv_expr, 1));
            break;
        case OP_SGT:
            bv_expr = e->get_arg(0);
            r = a.mk_gt(smod(bv_expr, 0), smod(bv_expr, 1));
            break;
        case OP_BNEG:
            r = a.mk_uminus(arg(0));
            break;
        case OP_CONCAT: {
            unsigned sz = 0;
            expr_ref new_arg(m);
            for (unsigned i = args.size(); i-- > 0;) {
                expr* old_arg = e->get_arg(i);
                new_arg = umod(old_arg, i);
                if (sz > 0) {
                    new_arg = mul(new_arg, a.mk_int(rational::power_of_two(sz)));
                    r = add(r, new_arg);
                }
                else
                    r = new_arg;
                sz += bv.get_bv_size(old_arg->get_sort());
            }
            break;
        }
        case OP_EXTRACT: {
            unsigned lo, hi;
            expr* old_arg;
            VERIFY(bv.is_extract(e, lo, hi, old_arg));
            r = arg(0);
            if (lo > 0)
                r = a.mk_idiv(r, a.mk_int(rational::power_of_two(lo)));
            break;
        }
        case OP_BV_NUM: {
            rational val;
            unsigned sz;
            VERIFY(bv.is_numeral(e, val, sz));
            r = a.mk_int(val);
            break;
        }
        case OP_BUREM:
        case OP_BUREM_I: {
            expr* x = umod(e, 0), * y = umod(e, 1);
            r = if_eq(y, 0, x, a.mk_mod(x, y));
            break;
        }
        case OP_BUDIV:
        case OP_BUDIV_I: {
            expr* x = umod(e, 0), * y = umod(e, 1);
            r = if_eq(y, 0, a.mk_int(-1), a.mk_idiv(x, y));
            break;
        }
        case OP_BUMUL_NO_OVFL: {
            bv_expr = e->get_arg(0);
            r = a.mk_lt(mul(umod(bv_expr, 0), umod(bv_expr, 1)), a.mk_int(bv_size(bv_expr)));
            break;
        }
        case OP_BSHL: {
            if (!a.is_numeral(arg(0)) && !a.is_numeral(arg(1))) 
                r = a.mk_shl(bv.get_bv_size(e), arg(0),arg(1));
            else {
                expr* x = arg(0), * y = umod(e, 1);
                r = a.mk_int(0);
                IF_VERBOSE(2, verbose_stream() << "shl " << mk_bounded_pp(e, m) << " " << bv.get_bv_size(e) << "\n");
                for (unsigned i = 0; i < bv.get_bv_size(e); ++i)
                    r = if_eq(y, i, mul(x, a.mk_int(rational::power_of_two(i))), r);   
            }
            break;
        }
        case OP_BNOT:
            r = bnot(arg(0));
            break;
        case OP_BLSHR: 
            if (!a.is_numeral(arg(0)) && !a.is_numeral(arg(1)))  
                r = a.mk_lshr(bv.get_bv_size(e), arg(0), arg(1));
            else {
                expr* x = arg(0), * y = umod(e, 1);
                r = a.mk_int(0);
                IF_VERBOSE(2, verbose_stream() << "lshr " << mk_bounded_pp(e, m) << " " << bv.get_bv_size(e) << "\n");
                for (unsigned i = 0; i < bv.get_bv_size(e); ++i)
                    r = if_eq(y, i, a.mk_idiv(x, a.mk_int(rational::power_of_two(i))), r);
            }
            break;
        case OP_BASHR: 
            if (!a.is_numeral(arg(1)))
                r = a.mk_ashr(bv.get_bv_size(e), arg(0), arg(1));
            else {
                
                //
                // ashr(x, y)
                // if y = k & x >= 0 -> x / 2^k   
                // if y = k & x < 0  -> (x / 2^k) - 2^{N-k}
                //
                unsigned sz = bv.get_bv_size(e);
                rational N = bv_size(e);
                expr* x = umod(e, 0), *y = umod(e, 1);
                expr* signx = a.mk_ge(x, a.mk_int(N / 2));
                r = m.mk_ite(signx, a.mk_int(- 1), a.mk_int(0));
                IF_VERBOSE(1, verbose_stream() << "ashr " << mk_bounded_pp(e, m) << " " << bv.get_bv_size(e) << "\n");
                for (unsigned i = 0; i < sz; ++i) {
                    expr* d = a.mk_idiv(x, a.mk_int(rational::power_of_two(i)));              
                    r = if_eq(y, i,
                                 m.mk_ite(signx, add(d, a.mk_int(- rational::power_of_two(sz-i))), d),
                                 r);
                }
            }
            break;
        case OP_BOR: 
            // p | q := (p + q) - band(p, q)
            IF_VERBOSE(2, verbose_stream() << "bor " << mk_bounded_pp(e, m) << " " << bv.get_bv_size(e) << "\n");
            r = arg(0);
            for (unsigned i = 1; i < args.size(); ++i)
                r = a.mk_sub(add(r, arg(i)), a.mk_band(bv.get_bv_size(e), r, arg(i)));
            break;        
        case OP_BNAND:
            r = bnot(band(args));
            break;
        case OP_BAND:
            IF_VERBOSE(2, verbose_stream() << "band " << mk_bounded_pp(e, m) << " " << bv.get_bv_size(e) << "\n");
            r = band(args);
            break;
        case OP_BXNOR:
        case OP_BXOR: {
            // p ^ q := (p + q) - 2*band(p, q);
            unsigned sz = bv.get_bv_size(e);
            IF_VERBOSE(2, verbose_stream() << "bxor " << bv.get_bv_size(e) << "\n");
            r = arg(0);
            for (unsigned i = 1; i < args.size(); ++i) {
                expr* q = arg(i);
                r = a.mk_sub(add(r, q), mul(a.mk_int(2), a.mk_band(sz, r, q)));
            }
            if (e->get_decl_kind() == OP_BXNOR)
                r = bnot(r);
            break;
        }
        case OP_ZERO_EXT:
            bv_expr = e->get_arg(0);
            r = umod(bv_expr, 0);
            SASSERT(bv.get_bv_size(e) >= bv.get_bv_size(bv_expr));
            break;
        case OP_SIGN_EXT: {
            bv_expr = e->get_arg(0);
            r = umod(bv_expr, 0);
            SASSERT(bv.get_bv_size(e) >= bv.get_bv_size(bv_expr));
            unsigned arg_sz = bv.get_bv_size(bv_expr);
            //unsigned sz = bv.get_bv_size(e);
            // rational N = rational::power_of_two(sz);
            rational M = rational::power_of_two(arg_sz);
            expr* signbit = a.mk_ge(r, a.mk_int(M / 2));
            r = m.mk_ite(signbit, a.mk_sub(r, a.mk_int(M)), r);
            break;
        }
        case OP_INT2BV:
            m_int2bv.push_back(e);
            ctx.push(push_back_vector(m_int2bv));
            r = arg(0);
            break;
        case OP_BV2INT:
            m_bv2int.push_back(e);
            ctx.push(push_back_vector(m_bv2int));
            r = umod(e->get_arg(0), 0);
            break;
        case OP_BCOMP:
            bv_expr = e->get_arg(0);
            r = m.mk_ite(m.mk_eq(umod(bv_expr, 0), umod(bv_expr, 1)), a.mk_int(1), a.mk_int(0));
            break;
        case OP_BSMOD_I:
        case OP_BSMOD: {            
            expr* x = umod(e, 0), *y = umod(e, 1);
            rational N = bv_size(e); 
            expr* signx = a.mk_ge(x, a.mk_int(N/2));
            expr* signy = a.mk_ge(y, a.mk_int(N/2));
            expr* u = a.mk_mod(x, y);
            // u = 0 ->  0
            // y = 0 ->  x
            // x < 0, y < 0 ->  -u
            // x < 0, y >= 0 ->  y - u
            // x >= 0, y < 0 ->  y + u
            // x >= 0, y >= 0 ->  u
            r = a.mk_uminus(u);   
            r = m.mk_ite(m.mk_and(m.mk_not(signx), signy), add(u, y), r);
            r = m.mk_ite(m.mk_and(signx, m.mk_not(signy)), a.mk_sub(y, u), r);
            r = m.mk_ite(m.mk_and(m.mk_not(signx), m.mk_not(signy)), u, r);
            r = if_eq(u, 0, a.mk_int(0), r);
            r = if_eq(y, 0, x, r);
            break;
        } 
        case OP_BSDIV_I:
        case OP_BSDIV: {
            // d = udiv(abs(x), abs(y))
            // y = 0, x > 0 -> 1
            // y = 0, x <= 0 -> -1
            // x = 0, y != 0 -> 0
            // x > 0, y < 0 -> -d
            // x < 0, y > 0 -> -d
            // x > 0, y > 0 -> d
            // x < 0, y < 0 -> d
            expr* x = umod(e, 0), * y = umod(e, 1);
            rational N = bv_size(e);
            expr* signx = a.mk_ge(x, a.mk_int(N / 2));
            expr* signy = a.mk_ge(y, a.mk_int(N / 2));
            x = m.mk_ite(signx, a.mk_sub(a.mk_int(N), x), x);
            y = m.mk_ite(signy, a.mk_sub(a.mk_int(N), y), y);
            expr* d = a.mk_idiv(x, y);
            r = m.mk_ite(m.mk_iff(signx, signy), d, a.mk_uminus(d));
            r = if_eq(y, 0, m.mk_ite(signx, a.mk_int(1), a.mk_int(-1)), r);
            break;
        }
        case OP_BSREM_I:
        case OP_BSREM: {
            // y = 0 -> x
            // else x - sdiv(x, y) * y
            expr* x = umod(e, 0), * y = umod(e, 1);
            rational N = bv_size(e);
            expr* signx = a.mk_ge(x, a.mk_int(N / 2));
            expr* signy = a.mk_ge(y, a.mk_int(N / 2));
            expr* absx = m.mk_ite(signx, a.mk_sub(a.mk_int(N), x), x);
            expr* absy = m.mk_ite(signy, a.mk_sub(a.mk_int(N), y), y);
            expr* d = a.mk_idiv(absx, absy);
            d = m.mk_ite(m.mk_iff(signx, signy), d, a.mk_uminus(d));
            r = a.mk_sub(x, mul(d, y));
            r = if_eq(y, 0, x, r);
            break;  
        }
        case OP_ROTATE_LEFT: {
            auto n = e->get_parameter(0).get_int();
            r = rotate_left(n);
            break;
        }
        case OP_ROTATE_RIGHT: {
            unsigned sz = bv.get_bv_size(e);
            auto n = e->get_parameter(0).get_int();
            r = rotate_left(sz - n);
            break;
        }
        case OP_EXT_ROTATE_LEFT:  {
            unsigned sz = bv.get_bv_size(e);
            expr* y = umod(e, 1);
            r = a.mk_int(0);
            for (unsigned i = 0; i < sz; ++i) 
                r = if_eq(y, i, rotate_left(i), r);
            break;
        }
        case OP_EXT_ROTATE_RIGHT: {
            unsigned sz = bv.get_bv_size(e);
            expr* y = umod(e, 1);
            r = a.mk_int(0);
            for (unsigned i = 0; i < sz; ++i) 
                r = if_eq(y, i, rotate_left(sz - i), r);
            break;
        }
        case OP_REPEAT: {
            unsigned n = e->get_parameter(0).get_int();
            expr* x = umod(e->get_arg(0), 0);
            r = x;
            rational N = bv_size(e->get_arg(0));
            rational N0 = N;
            for (unsigned i = 1; i < n; ++i)
                r = add(mul(a.mk_int(N), x), r), N *= N0;
            break;
        }            
        case OP_BREDOR: {
            r = umod(e->get_arg(0), 0);
            r = m.mk_not(m.mk_eq(r, a.mk_int(0)));
            break;
        }
        case OP_BREDAND: {
            rational N = bv_size(e->get_arg(0));
            r = umod(e->get_arg(0), 0);
            r = m.mk_not(m.mk_eq(r, a.mk_int(N - 1)));
            break;
        }
        default:
            verbose_stream() << mk_pp(e, m) << "\n";
            NOT_IMPLEMENTED_YET();
        }
        set_translated(e, r);
    }

    expr_ref solver::if_eq(expr* n, unsigned k, expr* th, expr* el) {
        rational r;
        expr_ref _th(th, m), _el(el, m);
        if (bv.is_numeral(n, r)) {
            if (r == k)
                return expr_ref(th, m);
            else
                return expr_ref(el, m);
        }
        return expr_ref(m.mk_ite(m.mk_eq(n, a.mk_int(k)), th, el), m);
    }

    void solver::translate_basic(app* e) {
        if (m.is_eq(e)) {
            bool has_bv_arg = any_of(*e, [&](expr* arg) { return bv.is_bv(arg); });
            if (has_bv_arg) {
                expr* bv_expr = e->get_arg(0);
                rational N = rational::power_of_two(bv.get_bv_size(bv_expr));
                if (a.is_numeral(arg(0)) || a.is_numeral(arg(1)) || 
                    is_bounded(arg(0), N) || is_bounded(arg(1), N)) {
                    set_translated(e, m.mk_eq(umod(bv_expr, 0), umod(bv_expr, 1)));
                }
                else {
                    m_args[0] = a.mk_sub(arg(0), arg(1));
                    set_translated(e, m.mk_eq(umod(bv_expr, 0), a.mk_int(0)));
                }
            }
            else
                set_translated(e, m.mk_eq(arg(0), arg(1)));
        }
        else if (m.is_ite(e))
            set_translated(e, m.mk_ite(arg(0), arg(1), arg(2)));
        else if (m_is_plugin)
            set_translated(e, e);
        else 
            set_translated(e, m.mk_app(e->get_decl(), m_args));        
    }

    rational solver::get_value(expr* e) const {
        SASSERT(bv.is_bv(e));
        model_ref mdl;
        m_solver->get_model(mdl);
        expr_ref r(m);
        r = translated(e);
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
        expr* te = translated(e);
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
            expr_ref bv2int(bv.mk_bv2int(n->get_expr()), m);
            euf::enode* b2i = ctx.get_enode(bv2int);
            if (!b2i) verbose_stream() << bv2int << "\n";
            SASSERT(b2i);
            VERIFY(b2i);
            arith::arith_value av(ctx);
            rational r;
            VERIFY(av.get_value(b2i->get_expr(), r));
            value = bv.mk_numeral(r, bv.get_bv_size(n->get_expr()));
            verbose_stream() << ctx.bpp(n) << " := " << value << "\n";
        }
        values.set(n->get_root_id(), value);
        TRACE("model", tout << "add_value " << ctx.bpp(n) << " := " << value << "\n");
    }

    void solver::finalize_model(model& mdl) {
        return;
        for (auto n : ctx.get_egraph().nodes()) {
            auto e = n->get_expr();            
            if (!is_translated(e))
                continue;
            if (!bv.is_bv(e))
                continue;
            auto t = translated(e);
            
            expr_ref ei(bv.mk_bv2int(e), m);
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
