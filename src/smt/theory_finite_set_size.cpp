
/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    theory_finite_set_size.cpp

Abstract:

    Theory solver for finite sets.
    Implements axiom schemas for finite set operations.

--*/

#include "smt/theory_finite_set.h"
#include "smt/theory_finite_set_size.h"
#include "smt/smt_context.h"
#include "smt/smt_model_generator.h"
#include "smt/smt_arith_value.h"
#include "ast/ast_pp.h"

namespace smt {

    theory_finite_set_size::theory_finite_set_size(theory_finite_set& th): 
        m(th.m), ctx(th.ctx), th(th), u(m), bs(m), m_assumption(m) {}

    void theory_finite_set_size::add_set_size(func_decl* f) {
        if (!m_set_size_decls.contains(f)) {
            m_set_size_decls.push_back(f);
            ctx.push_trail(push_back_trail(m_set_size_decls));
        }
    }

    void theory_finite_set_size::initialize_solver() {
        struct clear_solver : public trail {
            theory_finite_set_size &s;
        public:
            clear_solver(theory_finite_set_size &s) : s(s) {}
            void undo() override {
                s.m_solver = nullptr;
                s.n2b.reset();
                s.m_assumptions.reset();
                s.bs.reset();
            }
        };
        ctx.push_trail(clear_solver(*this));
        m_solver = alloc(context, m, ctx.get_fparams(), ctx.get_params());
        // collect all expressons that use cardinality constraints
        // collect cone of influence of sets terminals used in cardinality constraints
        // for every visited uninterpreted set variable add a Boolean variable
        // for every visited set expression add definitions as constraints to m_cardinality solver
        // introduce fresh variables for set membership constraints
        // assume that distinct enodes in set memberships produce different sets
        // assert added disequalities
        // assert equalities based on union-find equalities
        // assert set membership constraints by in

        enode_vector ns;
        collect_subexpressions(ns);

        //
        // we now got all subexpressions from equalities, disequalities, set.in
        //        
        // associate a Boolean variable with every set enode
        for (auto n : ns) {
            std::ostringstream strm;
            strm << "|" << enode_pp(n, ctx) << "|";
            symbol name = symbol(strm.str());
            expr_ref b(m.mk_const(name, m.mk_bool_sort()), m);
            bs.push_back(b);
            n2b.insert(n, b);
            TRACE(finite_set, tout << "assoc " << name << " to " << enode_pp(n, ctx) << " " << enode_pp(n->get_root(), ctx) << "\n";);
        }

        add_def_axioms(ns);
        add_singleton_axioms(ns); // (set.in x s) -> |{x}| = 1
        add_diseq_axioms(ns);     // |x\y| > 0 or |y\x| > 0
        add_not_in_axioms(ns);    // not (x in s) -> |{x}\s| = 1
        add_eq_axioms(ns);

        TRACE(finite_set, display(tout));
    }

    /**
    * For every (supported) set expression ensure associated Boolean expressions follow semantics
    */
    void theory_finite_set_size::add_def_axioms(enode_vector const& ns) {
        for (auto n : ns) {
            expr *e = n->get_expr();
            if (u.is_union(e)) {
                auto a = n2b[n->get_arg(0)];
                auto b = n2b[n->get_arg(1)];
                m_solver->assert_expr(m.mk_iff(n2b[n], m.mk_or(a, b)));
            }
            else if (u.is_intersect(e)) {
                auto a = n2b[n->get_arg(0)];
                auto b = n2b[n->get_arg(1)];
                m_solver->assert_expr(m.mk_iff(n2b[n], m.mk_and(a, b)));
            }
            else if (u.is_difference(e)) {
                auto a = n2b[n->get_arg(0)];
                auto not_b = m.mk_not(n2b[n->get_arg(1)]);
                m_solver->assert_expr(m.mk_iff(n2b[n], m.mk_and(a, not_b)));
            }
        }
    }

    enode* theory_finite_set_size::mk_singleton(enode* n) {
        expr_ref s(u.mk_singleton(n->get_expr()), m);
        ctx.ensure_internalized(s);
        ctx.mark_as_relevant(s.get());
        return ctx.get_enode(s);
    }

    enode* theory_finite_set_size::mk_diff(enode* a, enode* b) {
        expr_ref d(u.mk_difference(a->get_expr(), b->get_expr()), m);
        ctx.ensure_internalized(d);
        ctx.mark_as_relevant(d.get());
        return ctx.get_enode(d);
    }

    /**
     * For every set membership (set.in x s) add axiom for (set.subset (set.singleton x) s)
     */

    void theory_finite_set_size::add_singleton_axioms(enode_vector const &ns) {
        for (auto n : ns) {
            for (auto p : enode::parents(n)) {
                if (!u.is_in(p->get_expr()))
                    continue;
                if (!ctx.is_relevant(p))
                    continue;
                auto v = ctx.get_assignment(p);
                if (v != l_true)
                    continue;
                auto e = p->get_arg(0)->get_root();
                TRACE(finite_set, tout << "singleton axiom for " << enode_pp(e, ctx) << " in " << enode_pp(p, ctx) 
                      << " is " << v << "\n";);
                auto s = mk_singleton(e);
                SASSERT(n2b.contains(p->get_arg(1)));
                SASSERT(n2b.contains(s));
                auto is_in = m.mk_implies(n2b[s], n2b[p->get_arg(1)]);
                in lit(p, v == l_true);
                std::ostringstream strm;
                strm << "|" << enode_pp(p, ctx) << "|";
                symbol name = symbol(strm.str());
                expr* t = m.mk_const(name, m.mk_bool_sort());
                bs.push_back(t);
                m_assumptions.insert(t, lit);
                m_solver->assert_expr(m.mk_implies(t, is_in));
            }
        }
    }

    /*
     * For every x not in S include the assertion
     * x in S or |{x} \ S| = 1
     */
    void theory_finite_set_size::add_not_in_axioms(enode_vector const &ns) {
        for (auto n : ns) {
            for (auto p : enode::parents(n)) {
                if (!u.is_in(p->get_expr()))
                    continue;
                auto v = ctx.get_assignment(p);
                if (v != l_false)
                    continue;
                arith_util a(m);
                auto x = p->get_arg(0);
                auto S = p->get_arg(1);
                auto X = mk_singleton(x);
                auto X_minus_S = mk_diff(X, S);
                auto l1 = th.mk_literal(p->get_expr());
                auto l2 = th.mk_literal(m.mk_eq(u.mk_size(X_minus_S->get_expr()), a.mk_int(1)));
                ctx.mk_th_axiom(th.get_id(), l1, l2);
            }
        }
    }

    /**
    * For every asserted equality ensure equivalence
    */
    void theory_finite_set_size::add_eq_axioms(enode_vector const &ns) {
        for (auto [a, b] : th.m_eqs) {
            auto x = th.get_enode(a);
            auto y = th.get_enode(b);
            if (n2b.contains(x) && n2b.contains(y)) {
                eq e = {a, b};
                std::ostringstream strm;
                strm << "|" << enode_pp(x, ctx) << " == " << enode_pp(y, ctx) << "|";
                symbol name = symbol(strm.str());
                auto t = m.mk_const(name, m.mk_bool_sort());
                bs.push_back(t);
                m_assumptions.insert(t, e);
                m_solver->assert_expr(m.mk_implies(t, m.mk_iff(n2b[x], n2b[y])));
            }
        }
    }

    /*
    * For every disequality include the assertions x = y or |x\y| >= 1 or |y\z| >= 1
    * The expressions x\y and y\x are created when ns is created.
    */
    void theory_finite_set_size::add_diseq_axioms(enode_vector const &ns) {
        for (auto [a, b] : th.m_diseqs) {
            auto x = th.get_enode(a);
            auto y = th.get_enode(b);
            diseq d = {a, b};
            if (n2b.contains(x) && n2b.contains(y)) {
                arith_util a(m);
                auto d1 = mk_diff(x, y);
                auto d2 = mk_diff(y, x);
                expr_ref sz1(u.mk_size(d1->get_expr()), m);
                expr_ref sz2(u.mk_size(d2->get_expr()), m);
                literal l_eq = th.mk_literal(m.mk_eq(x->get_expr(), y->get_expr()));
                literal l1 = th.mk_literal(a.mk_ge(sz1, a.mk_int(1)));
                literal l2 = th.mk_literal(a.mk_ge(sz2, a.mk_int(1)));
                ctx.mk_th_axiom(th.get_id(), l_eq, l1, l2);
            }
        }
    }



    /**
    * Walk the cone of influence of expresions that depend on ns
    */
    void theory_finite_set_size::collect_subexpressions(enode_vector &ns) {
        // initialize disequality watch list
        u_map<unsigned_vector> v2diseqs, v2eqs;
        for (auto [a, b] : th.m_diseqs) {
            v2diseqs.insert_if_not_there(a, unsigned_vector()).push_back(b);
            v2diseqs.insert_if_not_there(b, unsigned_vector()).push_back(a);
        }
        for (auto [a, b] : th.m_eqs) {
            v2eqs.insert_if_not_there(a, unsigned_vector()).push_back(b);
            v2eqs.insert_if_not_there(b, unsigned_vector()).push_back(a);
        }

        auto add_expression = [&](enode *e) {
            if (!ctx.is_relevant(e))
                return;
            if (e->is_marked())
                return;
            e->set_mark();
            ns.push_back(e);
        };

        auto is_setop = [&](enode *n) {
            auto e = n->get_expr();
            return u.is_union(e) || u.is_intersect(e) || u.is_difference(e);
        };

        for (auto f : m_set_size_decls) {
            for (auto n : ctx.enodes_of(f)) {
                SASSERT(u.is_size(n->get_expr()));
                add_expression(n->get_arg(0));
            }
        }
        for (unsigned i = 0; i < ns.size(); ++i) {
            auto n = ns[i];
            // add children under set operations
            if (is_setop(n))
                for (auto arg : enode::args(n))
                    add_expression(arg);
            // add parents that are operations and use n
            for (auto p : enode::parents(n))
                if (is_setop(p) && any_of(enode::args(p), [n](auto a) { return a == n; }))
                    add_expression(p);
            // add equalities and disequalities
            auto v = th.get_th_var(n);
            if (v2eqs.contains(v)) {
                auto const &other = v2eqs[v];
                for (auto w : other)
                    add_expression(th.get_enode(w));
            }
            if (v2diseqs.contains(v)) {
                auto const &other = v2diseqs[v];
                for (auto w : other) {
                    auto n2 = th.get_enode(w);
                    add_expression(n2);
                    auto D1 = mk_diff(n, n2);
                    auto D2 = mk_diff(n2, n);
                    ctx.mark_as_relevant(D1->get_expr());
                    ctx.mark_as_relevant(D2->get_expr());
                    add_expression(D1);
                    add_expression(D2);
                }
            }
            for (auto p : enode::parents(n)) {
                if (!u.is_in(p->get_expr()))
                    continue;
                if (!ctx.is_relevant(p))
                    continue;
                if (ctx.get_assignment(p) != l_false)
                    continue;
                auto x = p->get_arg(0)->get_root();
                auto X = mk_singleton(x);
                ctx.mark_as_relevant(X->get_expr());
                add_expression(X);
                auto D = mk_diff(X, p->get_arg(1));
                ctx.mark_as_relevant(D);
                add_expression(D);
            }
        }
        for (auto n : ns)
            n->unset_mark();
    }
    

    /**
    * Base implementation:
    *    Enumerate all satisfying assignments to m_solver for atoms based on |s|
    *    Extract Core from enumeration
    *    Assert Core => |s_i| = sum_ij n_ij for each |s_i| cardinality expression
    *    NB. Soundness of using Core has not been rigorously established.    
    * Incremental algorithm:
    *    Enumerate N assignments at a time. 
    *    Associate tracking literal C_i with current assignment.
    *    Assume C_i
    *    Assert !C_0, .. , !C_{i-1}, C_i => /\_i |s_i| = sum_j n_ij and /\ n_j >= 0
    * Incremental algorithm with blocking clauses
    *    Enumerate N assignments at a time.
    *    use smt_arith_value::check_lp_feasiable to check if current assignment is feasible.
    *    if it is, then yield the current assignment. Assume there is a filter that avoids future
    *      calls to find more models if the current model satisfies all cardinality terms.
    *      In other words, for every |s| the model produces a set with |s| elements, 
    *      where |s| is the value assigned by the arithmetic solver.
    *   if it is not feasible, extract the infeasible core from call:
    *     - card_core: a set of cardinality atoms
    *     - lit_core:  a set of literals asserted into the arithmetic solver
    *     - eq_core:  a set of equations asserte into the arithmetic solver
    *   First take the card_core atoms and enumerate Boolean models for m_solver that 
    *   satisfy the disjunction of those atoms.
    *   - Infeasibility of the current model meant that there was no linear assignment to
    *     the subset in card_core that satisfied lit_core & eq_core. So the query to extend the
    *     set of assignments is to fix this.
     *   If there is some model for the disjunction of card_core atoms, then
     *     add new slacks for the models an continue, possibly querying the arithmetic solver if the new set of 
     *     linear relaxation to the subset is feasible.
     *   If there is no model to the disjunction of card_core atoms, then
     *     it means that size_core & lit_core & eq_core is unsat.
     *     where size_core is the unsat core for m_solver.
    */
    lbool theory_finite_set_size::run_solver() {
        expr_ref_vector asms(m);
        for (auto [k, v] : m_assumptions)
            asms.push_back(k);

        expr_ref_vector slack_exprs(m);
        obj_map<expr, expr *> slack_sums;
        arith_util a(m);
        expr_ref z(a.mk_int(0), m);
        for (auto f : m_set_size_decls) 
            for (auto n : ctx.enodes_of(f)) 
                slack_sums.insert(n->get_expr(), z);
                   
        while (true) {
            lbool r = m_solver->check(asms.size(), asms.data());
            if (r == l_false) {
                auto const& core = m_solver->unsat_core();
                literal_vector lits;
                for (auto c : core) {
                    auto exp = m_assumptions[c];
                    if (std::holds_alternative<eq>(exp)) {
                        auto [a, b] = std::get<eq>(exp);
                        expr_ref eq(m.mk_eq(th.get_expr(a), th.get_expr(b)), m);
                        lits.push_back(~th.mk_literal(eq));
                    }
                    else if (std::holds_alternative<diseq>(exp)) {
                        auto [a, b] = std::get<diseq>(exp);
                        expr_ref eq(m.mk_eq(th.get_expr(a), th.get_expr(b)), m);
                        lits.push_back(th.mk_literal(eq));
                    }
                    else if (std::holds_alternative<in>(exp)) {
                        auto [n, is_pos] = std::get<in>(exp);
                        auto lit = th.mk_literal(n->get_expr());
                        lits.push_back(is_pos ? ~lit : lit);
                    }
                }
                for (auto f : m_set_size_decls) {
                    for (auto n : ctx.enodes_of(f)) {
                        expr_ref eq(m.mk_eq(n->get_expr(), slack_sums[n->get_expr()]), m);
                        auto lit = th.mk_literal(eq);
                        literal_vector lemma(lits);
                        lemma.push_back(lit);
                        TRACE(finite_set, tout << "Asserting cardinality lemma\n";
                              for (auto lit : lemma) tout << ctx.literal2expr(lit) << "\n";);
                        ctx.mk_th_axiom(th.get_id(), lemma);
                    }
                }
                ctx.push_trail(value_trail(m_solver_ran));
                TRACE(finite_set, ctx.display(tout << "Core " << core << "\n"));
                m_solver_ran = true;
                return l_false;
            }
            if (r != l_true)
                return r;

            expr_ref slack(m.mk_fresh_const(symbol("slack"), a.mk_int()), m);
            ctx.mk_th_axiom(th.get_id(), th.mk_literal(a.mk_ge(slack, a.mk_int(0))));  // slack is non-negative
            model_ref mdl;
            m_solver->get_model(mdl);

            expr_ref_vector props(m);
            for (auto f : m_set_size_decls) {
                for (auto n : ctx.enodes_of(f)) {
                    auto arg = n->get_arg(0);
                    auto b = n2b[arg];
                    auto b_is_true = mdl->is_true(b);
                    props.push_back(b_is_true ? b : m.mk_not(b));
                    if (b_is_true) {
                        auto s = slack_sums[n->get_expr()];
                        s = s == z ? slack : a.mk_add(s, slack);
                        slack_exprs.push_back(s);
                        slack_sums.insert(n->get_expr(), s);
                    }
                }
            }
            TRACE(finite_set, tout << *mdl << "\nPropositional model:\n" << props << "\n");
            m_solver->assert_expr(m.mk_not(m.mk_and(props)));           
        }
        return l_undef;
    }

    lbool theory_finite_set_size::final_check() {
        if (m_set_size_decls.empty())
            return l_true;
        if (!m_solver) {
            initialize_solver();
            return l_false;
        }
        if (!m_solver_ran)
            return run_solver();

        // at this point we assume that 
        // cardinality constraints are satisfied 
        // by arithmetic solver.
        // 
        // a refinement checks if this is really necessary
        //
        return l_true;
    }

    /**
    * Placeholder to introduce an assumption literal to manage incremental search for solutions
    */
    void theory_finite_set_size::add_theory_assumptions(expr_ref_vector &assumptions) {
        
    }

    bool theory_finite_set_size::should_research(expr_ref_vector& unsat_core) {
        return false;
    }

    std::ostream& theory_finite_set_size::display(std::ostream& out) const {
        if (m_solver)
            m_solver->display(out << "set.size-solver\n");
        return out;
    }
}  // namespace smt