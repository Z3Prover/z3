/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    intblast_solver.cpp

Author:

    Nikolaj Bjorner (nbjorner) 2023-12-10

--*/

#include "ast/ast_util.h"
#include "ast/for_each_expr.h"
#include "sat/smt/intblast_solver.h"
#include "sat/smt/euf_solver.h"


namespace intblast {

    solver::solver(euf::solver& ctx): 
        ctx(ctx), 
        s(ctx.s()),
        m(ctx.get_manager()),
        bv(m),
        a(m),
        m_trail(m)
    {}
    
    lbool solver::check() {
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
        m_vars.reset();
        m_trail.reset();
        m_new_funs.reset();
        m_solver = mk_smt2_solver(m, s.params(), symbol::null);

        expr_ref_vector es(m);
        for (auto lit : literals)
            es.push_back(ctx.literal2expr(lit));

        translate(es);

        for (auto const& [src, vi] : m_vars) {
            auto const& [v, b] = vi;
            m_solver->assert_expr(a.mk_le(a.mk_int(0), v));
            m_solver->assert_expr(a.mk_lt(v, a.mk_int(b)));
        }

        IF_VERBOSE(10, verbose_stream() << "check\n";
            m_solver->display(verbose_stream());
            verbose_stream() << es << "\n");
               
        lbool r = m_solver->check_sat(es);

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
        obj_map<expr, expr*> translated;        
        expr_ref_vector args(m);
        
        sorted_subterms(es, todo);

        for (expr* e : todo) {
            if (is_quantifier(e)) {
                quantifier* q = to_quantifier(e);
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
                b = translated[b];
                // TODO if sorts contain integer, then created bounds variables.
                m_trail.push_back(m.update_quantifier(q, b));
                translated.insert(e, m_trail.back());
                continue;
            }
            if (is_var(e)) {
                if (bv.is_bv_sort(e->get_sort())) {
                    expr* v = m.mk_var(to_var(e)->get_idx(), a.mk_int());
                    m_trail.push_back(v);
                    translated.insert(e, m_trail.back());
                }
                else {
                    m_trail.push_back(e);
                    translated.insert(e, m_trail.back());
                }
                continue;
            }
            app* ap = to_app(e);
            expr* bv_expr = e;
            args.reset();
            for (auto arg : *ap)
                args.push_back(translated[arg]);

            auto bv_size = [&]() { return rational::power_of_two(bv.get_bv_size(bv_expr->get_sort())); };

            auto mk_mod = [&](expr* x) {
                if (m_vars.contains(x))
                    return x;
                return to_expr(a.mk_mod(x, a.mk_int(bv_size())));
            };

            auto mk_smod = [&](expr* x) {
                auto shift = bv_size() / 2;
                return a.mk_mod(a.mk_add(x, a.mk_int(shift)), a.mk_int(bv_size()));
            };           

            if (m.is_eq(e)) {
                bool has_bv_arg = any_of(*ap, [&](expr* arg) { return bv.is_bv(arg); });
                if (has_bv_arg) {
                    bv_expr = ap->get_arg(0);
                    m_trail.push_back(m.mk_eq(mk_mod(args.get(0)), mk_mod(args.get(1))));
                    translated.insert(e, m_trail.back());
                }
                else {
                    m_trail.push_back(m.mk_eq(args.get(0), args.get(1)));
                    translated.insert(e, m_trail.back());
                }
                continue;
            }
            
            if (m.is_ite(e)) {
                m_trail.push_back(m.mk_ite(args.get(0), args.get(1), args.get(2)));
                translated.insert(e, m_trail.back());
                continue;
            }

            if (ap->get_family_id() != bv.get_family_id()) {
                bool has_bv_arg = any_of(*ap, [&](expr* arg) { return bv.is_bv(arg); });
                bool has_bv_sort = bv.is_bv(e);
                func_decl* f = ap->get_decl();
                if (has_bv_arg) {
                    verbose_stream() << mk_pp(ap, m) << "\n";
                    // need to update args with mod where they are bit-vectors.
                    NOT_IMPLEMENTED_YET();
                }

                if (has_bv_arg || has_bv_sort) {
                    ptr_vector<sort> domain;
                    for (auto* arg : *ap) {
                        sort* s = arg->get_sort();
                        domain.push_back(bv.is_bv_sort(s) ? a.mk_int() : s);
                    }
                    sort* range = bv.is_bv(e) ? a.mk_int() : e->get_sort();
                    func_decl* g = nullptr;
                    if (!m_new_funs.find(f, g)) {
                        g = m.mk_fresh_func_decl(ap->get_decl()->get_name(), symbol("bv"), domain.size(), domain.data(), range);
                        m_new_funs.insert(f, g);
                    }
                    f = g;
                }
                
                m_trail.push_back(m.mk_app(f, args));
                translated.insert(e, m_trail.back());

                if (has_bv_sort) 
                    m_vars.insert(e, { m_trail.back(), bv_size() });
                
                continue;
            }

            switch (ap->get_decl_kind()) {
                case OP_BADD:
                    m_trail.push_back(a.mk_add(args));
                    break;
                case OP_BSUB:
                    m_trail.push_back(a.mk_sub(args.size(), args.data()));
                    break;
                case OP_BMUL:
                    m_trail.push_back(a.mk_mul(args));
                    break;
                case OP_ULEQ:
                    bv_expr = ap->get_arg(0);
                    m_trail.push_back(a.mk_le(mk_mod(args.get(0)), mk_mod(args.get(1))));
                    break;
                case OP_UGEQ:
                    bv_expr = ap->get_arg(0);
                    m_trail.push_back(a.mk_ge(mk_mod(args.get(0)), mk_mod(args.get(1))));
                    break;
                case OP_ULT:
                    bv_expr = ap->get_arg(0);
                    m_trail.push_back(a.mk_lt(mk_mod(args.get(0)), mk_mod(args.get(1))));
                    break;
                case OP_UGT:
                    bv_expr = ap->get_arg(0);
                    m_trail.push_back(a.mk_gt(mk_mod(args.get(0)), mk_mod(args.get(1))));
                    break;
                case OP_SLEQ: 
                    bv_expr = ap->get_arg(0);
                    m_trail.push_back(a.mk_le(mk_smod(args.get(0)), mk_smod(args.get(1))));
                    break;
                case OP_SGEQ:
                    m_trail.push_back(a.mk_ge(mk_smod(args.get(0)), mk_smod(args.get(1))));
                    break;
                case OP_SLT:
                    bv_expr = ap->get_arg(0);
                    m_trail.push_back(a.mk_lt(mk_smod(args.get(0)), mk_smod(args.get(1))));
                    break;
                case OP_SGT:
                    bv_expr = ap->get_arg(0);
                    m_trail.push_back(a.mk_gt(mk_smod(args.get(0)), mk_smod(args.get(1))));
                    break;
                case OP_BNEG:
                    m_trail.push_back(a.mk_uminus(args.get(0)));
                    break;
                case OP_CONCAT: {
                    expr_ref r(a.mk_int(0), m);
                    unsigned sz = 0;
                    for (unsigned i = 0; i < args.size(); ++i) {
                        expr* old_arg = ap->get_arg(i);
                        expr* new_arg = args.get(i);
                        bv_expr = old_arg;
                        new_arg = mk_mod(new_arg);
                        if (sz > 0) {
                            new_arg = a.mk_mul(new_arg, a.mk_int(rational::power_of_two(sz)));
                            r = a.mk_add(r, new_arg);
                        }
                        else 
                            r = new_arg;                        
                        sz += bv.get_bv_size(old_arg->get_sort());
                    }
                    m_trail.push_back(r);
                    break;
                }
                case OP_EXTRACT: {
                    unsigned lo, hi;
                    expr* old_arg;
                    VERIFY(bv.is_extract(e, lo, hi, old_arg));
                    unsigned sz = hi - lo + 1;
                    expr* new_arg = args.get(0);
                    if (lo > 0)
                        new_arg = a.mk_idiv(new_arg, a.mk_int(rational::power_of_two(lo)));
                    m_trail.push_back(new_arg);
                    break;
                }   
                case OP_BV_NUM: {
                    rational val;
                    unsigned sz;
                    VERIFY(bv.is_numeral(e, val, sz));
                    m_trail.push_back(a.mk_int(val));
                    break;
                }
                case OP_BUREM_I: {
                    expr* x = args.get(0), * y = args.get(1);
                    m_trail.push_back(m.mk_ite(m.mk_eq(y, a.mk_int(0)), a.mk_int(0), a.mk_mod(x, y)));
                    break;
                }
                case OP_BUDIV_I: {
                    expr* x = args.get(0), * y = args.get(1);
                    m_trail.push_back(m.mk_ite(m.mk_eq(y, a.mk_int(0)), a.mk_int(0), a.mk_idiv(x, y)));
                    break;
                }
                case OP_BUMUL_NO_OVFL: {
                    expr* x = args.get(0), * y = args.get(1);
                    bv_expr = ap->get_arg(0);
                    m_trail.push_back(a.mk_lt(a.mk_mul(mk_mod(x), mk_mod(y)), a.mk_int(bv_size())));
                    break;
                }
                case OP_BNOT:
                case OP_BNAND:
                case OP_BNOR:
                case OP_BXOR:
                case OP_BXNOR:
                case OP_BCOMP:
                case OP_BSHL:
                case OP_BLSHR:
                case OP_BASHR:
                case OP_ROTATE_LEFT:
                case OP_ROTATE_RIGHT:
                case OP_EXT_ROTATE_LEFT:
                case OP_EXT_ROTATE_RIGHT:
                case OP_REPEAT:
                case OP_ZERO_EXT:
                case OP_SIGN_EXT:
                case OP_BREDOR:
                case OP_BREDAND:
                case OP_BUDIV:
                case OP_BSDIV:
                case OP_BUREM:
                case OP_BSREM:
                case OP_BSMOD:
                case OP_BAND:
                    verbose_stream() << mk_pp(e, m) << "\n";
                    NOT_IMPLEMENTED_YET();
                    break;
                default:
                    verbose_stream() << mk_pp(e, m) << "\n";
                    NOT_IMPLEMENTED_YET();
            }            
            translated.insert(e, m_trail.back());
        }

        TRACE("bv",
            for (expr* e : es)
                tout << mk_pp(e, m) << "\n->\n" << mk_pp(translated[e], m) << "\n";
        );

        for (unsigned i = 0; i < es.size(); ++i) 
            es[i] = translated[es.get(i)];


    }

    rational solver::get_value(expr* e) const {
        SASSERT(bv.is_bv(e));
        model_ref mdl;
        m_solver->get_model(mdl);
        expr_ref r(m);
        var_info vi;
        rational val;       
        if (!m_vars.find(e, vi))
            return rational::zero();
        if (!mdl->eval_expr(vi.dst, r, true))
            return rational::zero();
        if (!a.is_numeral(r, val))
            return rational::zero();
        return val;
    }

    sat::literal_vector const& solver::unsat_core() {
        return m_core;
    }

    std::ostream& solver::display(std::ostream& out) const {
        if (m_solver)
            m_solver->display(out);
        return out;
    }

}
