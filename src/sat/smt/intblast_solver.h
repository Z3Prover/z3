/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    intblast_solver.h

Abstract:

    Int-blast solver.

    check_solver_state assumes a full assignment to literals in 
    irredundant clauses. 
    It picks a satisfying Boolean assignment and 
    checks if it is feasible for bit-vectors using
    an arithmetic solver.

    The solver plugin is self-contained.

    Internalize:
    - internalize bit-vector terms bottom-up by updating m_translate.
    - add axioms of the form:
      - ule(b,a) <=> translate(ule(b, a))
      - let arithmetic solver handle bit-vector constraints.
    - For shared b
      - Ensure: int2bv(translate(b)) = b
      - but avoid bit-blasting by ensuring int2bv is injective (mod N) during final check

Author:

    Nikolaj Bjorner (nbjorner) 2023-12-10

--*/
#pragma once

#include "ast/arith_decl_plugin.h"
#include "ast/bv_decl_plugin.h"
#include "solver/solver.h"
#include "sat/smt/sat_th.h"
#include "util/statistics.h"

namespace euf {
    class solver;
}

namespace intblast {

    class solver : public euf::th_euf_solver {
        euf::solver& ctx;
        sat::solver& s;
        ast_manager& m;
        bv_util bv;
        arith_util a;
        scoped_ptr<::solver> m_solver;
        obj_map<func_decl, func_decl*> m_new_funs;
        expr_ref_vector m_translate, m_args;
        ast_ref_vector m_pinned;
        sat::literal_vector m_core;
        ptr_vector<app> m_bv2int, m_int2bv;
        statistics m_stats;
        bool m_is_plugin = true;        // when the solver is used as a plugin, then do not translate below quantifiers.        

        bool is_bv(sat::literal lit);
        void translate(expr_ref_vector& es);
        void sorted_subterms(expr_ref_vector& es, ptr_vector<expr>& sorted);



        bool is_translated(expr* e) const { return !!m_translate.get(e->get_id(), nullptr); }
        expr* translated(expr* e) const { expr* r = m_translate.get(e->get_id(), nullptr); SASSERT(r); return r; }
        void set_translated(expr* e, expr* r);
        expr* arg(unsigned i) { return m_args.get(i); }

        expr* umod(expr* bv_expr, unsigned i);
        expr* smod(expr* bv_expr, unsigned i);
        bool is_bounded(expr* v, rational const& N);
        bool is_non_negative(expr* bv_expr, expr* e);
        expr_ref mul(expr* x, expr* y);
        expr_ref add(expr* x, expr* y);
        expr_ref if_eq(expr* n, unsigned k, expr* th, expr* el);
        expr* amod(expr* bv_expr, expr* x, rational const& N);
        rational bv_size(expr* bv_expr);

        void translate_expr(expr* e);
        void translate_bv(app* e);
        void translate_basic(app* e);
        void translate_app(app* e);
        void translate_quantifier(quantifier* q);
        void translate_var(var* v);

        void ensure_translated(expr* e);
        void internalize_bv(app* e);

        unsigned m_vars_qhead = 0, m_preds_qhead = 0;
        ptr_vector<expr> m_vars, m_preds;
        bool add_bound_axioms();
        bool add_predicate_axioms();

        euf::theory_var mk_var(euf::enode* n) override;

        void add_value_plugin(euf::enode* n, model& mdl, expr_ref_vector& values);
        void add_value_solver(euf::enode* n, model& mdl, expr_ref_vector& values);

    public:
        solver(euf::solver& ctx);

        lbool check_axiom(sat::literal_vector const& lits);
        lbool check_core(sat::literal_vector const& lits, euf::enode_pair_vector const& eqs);
        lbool check_propagation(sat::literal lit, sat::literal_vector const& lits, euf::enode_pair_vector const& eqs);

        lbool check_solver_state();

        sat::literal_vector const& unsat_core();

        void add_value(euf::enode* n, model& mdl, expr_ref_vector& values) override;

        bool add_dep(euf::enode* n, top_sort<euf::enode>& dep) override;

        std::ostream& display(std::ostream& out) const override;

        void collect_statistics(statistics& st) const override;

        bool unit_propagate() override;

        void get_antecedents(sat::literal l, sat::ext_justification_idx idx, sat::literal_vector& r, bool probing) override {}

        sat::check_result check() override;

        std::ostream& display_justification(std::ostream& out, sat::ext_justification_idx idx) const override { return out; }

        std::ostream& display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const override { return out; }

        euf::th_solver* clone(euf::solver& ctx) override { return alloc(solver, ctx); }

        void internalize(expr* e) override;

        bool visited(expr* e) override;

        bool post_visit(expr* e, bool sign, bool root) override;

        bool visit(expr* e) override;

        sat::literal internalize(expr* e, bool, bool) override;

        void eq_internalized(euf::enode* n) override;

        rational get_value(expr* e) const;

        void finalize_model(model& mdl) override;
    };

}
