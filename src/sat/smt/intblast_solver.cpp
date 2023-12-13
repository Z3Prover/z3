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


namespace intblast {

    solver::solver(euf::solver& ctx) :
        th_euf_solver(ctx, symbol("intblast"), ctx.get_manager().get_family_id("bv")),
        ctx(ctx),
        s(ctx.s()),
        m(ctx.get_manager()),
        bv(m),
        a(m),
        m_translate(m),
        m_args(m)
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
        expr* x, * y;
        VERIFY(m.is_eq(n->get_expr(), x, y));
        m_args.reset();
        m_args.push_back(translated(x));
        m_args.push_back(translated(y));
        add_equiv(expr2literal(e), eq_internalize(umod(x, 0), umod(x, 1)));
    }

    void solver::internalize_bv(app* e) {
        ensure_args(e);
        m_args.reset();
        for (auto arg : *e)
            m_args.push_back(translated(arg));
        translate_bv(e);

        // possibly wait until propagation?
        if (m.is_bool(e))
            add_equiv(expr2literal(e), mk_literal(translated(e)));
        add_bound_axioms();
    }

    void solver::add_bound_axioms() {
        if (m_vars_qhead == m_vars.size())
            return;
        ctx.push(value_trail(m_vars_qhead));
        for (; m_vars_qhead < m_vars.size(); ++m_vars_qhead) {
            auto v = m_vars[m_vars_qhead];
            auto w = translated(v);
            auto sz = rational::power_of_two(bv.get_bv_size(v->get_sort()));
            add_unit(ctx.mk_literal(a.mk_ge(w, a.mk_int(0))));
            add_unit(ctx.mk_literal(a.mk_le(w, a.mk_int(sz - 1))));
        }
    }

    void solver::ensure_args(app* e) {
        ptr_vector<expr> todo;
        ast_fast_mark1 visited;
        for (auto arg : *e) {
            if (!m_translate.get(arg->get_id(), nullptr))
                todo.push_back(arg);
        }
        if (todo.empty())
            return;
        for (unsigned i = 0; i < todo.size(); ++i) {
            expr* e = todo[i];
            if (m.is_bool(e))
                continue;
            else if (is_app(e)) {
                for (auto arg : *to_app(e))
                    if (!visited.is_marked(arg)) {
                        visited.mark(arg);
                        todo.push_back(arg);
                    }
            }
            else if (is_lambda(e))
                throw default_exception("lambdas are not supported in intblaster");
        }

        std::stable_sort(todo.begin(), todo.end(), [&](expr* a, expr* b) { return get_depth(a) < get_depth(b); });
        for (expr* e : todo)
            translate_expr(e);
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
        m_translate.reset();
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
            sorted.push_back(e);
            visited.mark(e);
        }
        for (unsigned i = 0; i < sorted.size(); ++i) {
            expr* e = sorted[i];
            if (is_app(e)) {
                app* a = to_app(e);
                for (expr* arg : *a) {
                    if (!visited.is_marked(arg)) {
                        visited.mark(arg);
                        sorted.push_back(arg);
                    }
                }

                //
                // Add ground equalities to ensure the model is valid with respect to the current case splits.
                // This may cause more conflicts than necessary. Instead could use intblast on the base level, but using literal
                // assignment from complete level.
                // E.g., force the solver to completely backtrack, check satisfiability using the assignment obtained under a complete assignment.
                // If intblast is SAT, then force the model and literal assignment on the rest of the literals.
                // 
                if (!is_ground(e))
                    continue;
                euf::enode* n = ctx.get_enode(e);
                if (!n)
                    continue;
                if (n == n->get_root())
                    continue;
                expr* r = n->get_root()->get_expr();
                es.push_back(m.mk_eq(e, r));
                r = es.back();
                if (!visited.is_marked(r)) {
                    visited.mark(r);
                    sorted.push_back(r);
                }
            }
            else if (is_quantifier(e)) {
                quantifier* q = to_quantifier(e);
                expr* b = q->get_expr();
                if (!visited.is_marked(b)) {
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
                add_clause(~eq_internalize(n, sib), eq_internalize(sib->get_arg(0), n->get_arg(0)), nullptr);
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
                add_unit(eq_internalize(nBv2int, nxModN));
                return sat::check_result::CR_CONTINUE;
            }
        }
        return sat::check_result::CR_DONE; 
    }

    expr* solver::umod(expr* bv_expr, unsigned i) {
        expr* x = arg(i);
        rational r;
        rational N = bv_size(bv_expr);
        if (a.is_numeral(x, r)) {
            if (0 <= r && r < N)
                return x;
            return a.mk_int(mod(r, N));
        }
        if (any_of(m_vars, [&](expr* v) { return translated(v) == x; }))
            return x;
        return to_expr(a.mk_mod(x, a.mk_int(N)));
    }

    expr* solver::smod(expr* bv_expr, unsigned i) {
        expr* x = arg(i);
        auto N = bv_size(bv_expr);
        auto shift = N / 2;
        rational r;
        if (a.is_numeral(x, r))
            return a.mk_int(mod(r + shift, N));
        return a.mk_mod(a.mk_add(x, a.mk_int(shift)), a.mk_int(N));
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
        if (is_lambda(q))
            throw default_exception("lambdas are not supported in intblaster");
        if (m_is_plugin) {
            set_translated(q, q);
            return;
        }
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

        expr* bv_expr = e;
        expr* r = nullptr;
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
            r = a.mk_int(0);
            unsigned sz = 0;
            for (unsigned i = 0; i < args.size(); ++i) {
                expr* old_arg = e->get_arg(i);
                expr* new_arg = umod(old_arg, i);
                if (sz > 0) {
                    new_arg = a.mk_mul(new_arg, a.mk_int(rational::power_of_two(sz)));
                    r = a.mk_add(r, new_arg);
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
            expr* x = arg(0), * y = arg(1);
            r = m.mk_ite(m.mk_eq(y, a.mk_int(0)), x, a.mk_mod(x, y));
            break;
        }
        case OP_BUDIV:
        case OP_BUDIV_I: {
            expr* x = arg(0), * y = arg(1);
            r = m.mk_ite(m.mk_eq(y, a.mk_int(0)), a.mk_int(1), a.mk_idiv(x, umod(bv_expr, 1)));
            break;
        }
        case OP_BUMUL_NO_OVFL: {
            bv_expr = e->get_arg(0);
            r = a.mk_lt(a.mk_mul(umod(bv_expr, 0), umod(bv_expr, 1)), a.mk_int(bv_size(bv_expr)));
            break;
        }
        case OP_BSHL: {
            expr* x = arg(0), * y = arg(1);
            r = a.mk_int(0);
            for (unsigned i = 0; i < bv.get_bv_size(e); ++i)
                r = m.mk_ite(a.mk_eq(y, a.mk_int(i)), a.mk_mul(x, a.mk_int(rational::power_of_two(i))), r);
            break;
        }
        case OP_BNOT:
            r = bnot(arg(0));
            break;
        case OP_BLSHR: {
            expr* x = arg(0), * y = arg(1);
            r = a.mk_int(0);
            for (unsigned i = 0; i < bv.get_bv_size(e); ++i)
                r = m.mk_ite(a.mk_eq(y, a.mk_int(i)), a.mk_idiv(x, a.mk_int(rational::power_of_two(i))), r);
            break;
        }
                     // Or use (p + q) - band(p, q)?
        case OP_BOR: {
            r = arg(0);
            for (unsigned i = 1; i < args.size(); ++i)
                r = a.mk_sub(a.mk_add(r, arg(i)), a.mk_band(bv.get_bv_size(e), r, arg(i)));
            break;
        }
        case OP_BNAND:
            r = bnot(band(args));
            break;
        case OP_BAND:
            r = band(args);
            break;
            // From "Hacker's Delight", section 2-2. Addition Combined with Logical Operations;
            // found via Int-Blasting paper; see https://doi.org/10.1007/978-3-030-94583-1_24
            // (p + q) - 2*band(p, q);
        case OP_BXNOR:
        case OP_BXOR: {
            unsigned sz = bv.get_bv_size(e);
            r = arg(0);
            for (unsigned i = 1; i < args.size(); ++i) {
                expr* q = arg(i);
                r = a.mk_sub(a.mk_add(r, q), a.mk_mul(a.mk_int(2), a.mk_band(sz, r, q)));
            }
            if (e->get_decl_kind() == OP_BXNOR)
                r = bnot(r);
            break;
        }
        case OP_BASHR: {
            //
            // ashr(x, y)
            // if y = k & x >= 0 -> x / 2^k   
            // if y = k & x < 0  -> - (x / 2^k) 
            //
            rational N = rational::power_of_two(bv.get_bv_size(e));
            expr* x = umod(e, 0);
            expr* y = umod(e, 1);
            expr* signbit = a.mk_ge(x, a.mk_int(N / 2));
            r = m.mk_ite(signbit, a.mk_int(N - 1), a.mk_int(0));
            for (unsigned i = 0; i < bv.get_bv_size(e); ++i) {
                expr* d = a.mk_idiv(x, a.mk_int(rational::power_of_two(i)));
                r = m.mk_ite(a.mk_eq(y, a.mk_int(i)),
                    m.mk_ite(signbit, a.mk_uminus(d), d),
                    r);
            }
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
            unsigned sz = bv.get_bv_size(e);
            rational N = rational::power_of_two(sz);
            rational M = rational::power_of_two(arg_sz);
            expr* signbit = a.mk_ge(r, a.mk_int(M / 2));
            r = m.mk_ite(signbit, a.mk_uminus(r), r);
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
        case OP_BSMOD: {
            bv_expr = e;
            expr* x = umod(bv_expr, 0), *y = umod(bv_expr, 0);
            rational N = rational::power_of_two(bv.get_bv_size(bv_expr));
            expr* signx = a.mk_ge(x, a.mk_int(N/2));
            expr* signy = a.mk_ge(y, a.mk_int(N/2));
            expr* u = a.mk_mod(x, y);
            // x < 0, y < 0 -> r = -u
            // x < 0, y >= 0 -> r = y - u
            // x >= 0, y < 0 -> r = y + u
            // x >= 0, y >= 0 -> r = u
            // u = 0 -> r = 0
            // y = 0 -> r = x
            r = a.mk_uminus(u);   
            r = m.mk_ite(m.mk_and(m.mk_not(signx), signy), a.mk_add(u, y), r);
            r = m.mk_ite(m.mk_and(signx, m.mk_not(signy)), a.mk_sub(y, u), r);
            r = m.mk_ite(m.mk_and(m.mk_not(signx), m.mk_not(signy)), u, r);
            r = m.mk_ite(m.mk_eq(u, a.mk_int(0)), a.mk_int(0), r);
            r = m.mk_ite(m.mk_eq(y, a.mk_int(0)), x, r);
            break;
        } 
        case OP_BSDIV: {
            // y = 0, x > 0 -> 1
            // y = 0, x <= 0 -> -1
            // y != 0 -> machine_div(x, y)
#if 0

#endif
        }

        case OP_ROTATE_LEFT:
        case OP_ROTATE_RIGHT:
        case OP_EXT_ROTATE_LEFT:
        case OP_EXT_ROTATE_RIGHT:
        case OP_REPEAT:
        case OP_BREDOR:
        case OP_BREDAND:
        case OP_BSREM:
            verbose_stream() << mk_pp(e, m) << "\n";
            NOT_IMPLEMENTED_YET();
            break;
        default:
            verbose_stream() << mk_pp(e, m) << "\n";
            NOT_IMPLEMENTED_YET();
        }
        set_translated(e, r);
    }

    void solver::translate_basic(app* e) {
        if (m.is_eq(e)) {
            bool has_bv_arg = any_of(*e, [&](expr* arg) { return bv.is_bv(arg); });
            if (has_bv_arg) {
                expr* bv_expr = e->get_arg(0);
                set_translated(e, m.mk_eq(umod(bv_expr, 0), umod(bv_expr, 1)));
            }
            else
                set_translated(e, m.mk_eq(arg(0), arg(1)));
        }
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
        // bv2int 
        auto e = ctx.get_enode(translated(n->get_expr()));
        if (!e)
            return false;
        dep.add(n, e);
        return true;
    }

    // TODO: handle dependencies properly by using arithmetical model to retrieve values of translated 
    // bit-vectors directly.
    void solver::add_value_plugin(euf::enode* n, model& mdl, expr_ref_vector& values) {
        SASSERT(bv.is_bv(n->get_expr()));
        rational N = rational::power_of_two(bv.get_bv_size(n->get_expr()));
        auto e = ctx.get_enode(translated(n->get_expr()));
        expr_ref value(m);
        value = values.get(e->get_root_id());        
        values.setx(n->get_root_id(), value);
    }

    void solver::add_value_solver(euf::enode* n, model& mdl, expr_ref_vector& values) {
        expr_ref value(m);
        if (n->interpreted())
            value = n->get_expr();
        else if (to_app(n->get_expr())->get_family_id() == bv.get_family_id()) {
            bv_rewriter rw(m);
            expr_ref_vector args(m);
            for (auto arg : euf::enode_args(n))
                args.push_back(values.get(arg->get_root_id()));
            rw.mk_app(n->get_decl(), args.size(), args.data(), value);
            VERIFY(value);
        }
        else {
            rational r = get_value(n->get_expr());
            verbose_stream() << ctx.bpp(n) << " := " << r << "\n";
            value = bv.mk_numeral(r, bv.get_bv_size(n->get_expr()));
        }
        values.set(n->get_root_id(), value);
        TRACE("model", tout << "add_value " << ctx.bpp(n) << " := " << value << "\n");
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
