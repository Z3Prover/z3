/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    opt_pareto_solver.cpp

Abstract:

    Keep nlsat clauses and expression mappings across Pareto improvement
    checks. Scope-local assertions and their learned consequences carry
    an opaque assumption tag and are retracted together.

--*/
#include "opt/opt_pareto_solver.h"
#include "opt/opt_params.hpp"
#include "ast/arith_decl_plugin.h"
#include "ast/expr2var.h"
#include "ast/for_each_expr.h"
#include "nlsat/nlsat_solver.h"
#include "nlsat/tactic/goal2nlsat.h"
#include "solver/solver_na2as.h"
#include "tactic/arith/purify_arith_tactic.h"
#include "tactic/core/elim_term_ite_tactic.h"
#include "tactic/core/simplify_tactic.h"
#include "tactic/core/tseitin_cnf_tactic.h"
#include "tactic/tactical.h"

namespace opt {

    bool can_reuse_nlsat_solver(expr_ref_vector const& terms) {
        ast_manager& m = terms.m();
        arith_util a(m);
        for (expr* e : subterms::all(terms)) {
            if (!is_app(e))
                return false;
            app* n = to_app(e);
            if (!m.is_bool(e) && !a.is_real(e) && !a.is_numeral(e))
                return false;
            if (is_uninterp_const(e) || n->get_family_id() == m.get_basic_family_id())
                continue;
            if (n->get_family_id() != a.get_family_id())
                return false;
            rational r;
            switch (n->get_decl_kind()) {
            case OP_NUM: case OP_IRRATIONAL_ALGEBRAIC_NUM:
            case OP_LE: case OP_GE: case OP_LT: case OP_GT:
            case OP_ADD: case OP_SUB: case OP_UMINUS: case OP_MUL:
                break;
            case OP_DIV:
                if (!a.is_numeral(n->get_arg(1), r) || r.is_zero())
                    return false;
                break;
            case OP_POWER:
                if (!a.is_numeral(n->get_arg(1), r) || !r.is_unsigned() || r.is_zero())
                    return false;
                break;
            default:
                return false;
            }
        }
        return true;
    }

    namespace {

    params_ref incremental_params(params_ref const& p) {
        params_ref result(p);
        // Keep root atoms and external variable IDs stable, also on cancellation.
        result.set_bool("reorder", false);
        result.set_bool("shuffle_vars", false);
        result.set_uint("variable_ordering_strategy", 0);
        return result;
    }

    tactic* mk_preprocessor(ast_manager& m, params_ref const& p) {
        params_ref simp(p), purify(p);
        simp.set_bool("elim_and", true);
        simp.set_bool("blast_distinct", true);
        simp.set_bool("expand_power", true);
        purify.set_bool("complete", false);
        // No solve-eqs or unconstrained-variable elimination: later assertions
        // must still refer to the same original constants.
        return and_then(
            using_params(mk_simplify_tactic(m, p), simp),
            using_params(mk_purify_arith_tactic(m, p), purify),
            mk_elim_term_ite_tactic(m, p),
            using_params(mk_purify_arith_tactic(m, p), purify),
            using_params(mk_simplify_tactic(m, p), simp),
            mk_tseitin_cnf_core_tactic(m, p),
            using_params(mk_simplify_tactic(m, p), simp));
    }

    class pareto_nlsat_solver : public solver_na2as {
        expr_ref_vector m_assertions;
        expr_ref_vector m_tags;
        expr_ref_vector m_scope_tags;
        unsigned_vector m_limits;
        unsigned m_head = 0;
        mutable nlsat::solver m_nlsat;
        expr2var m_a2b, m_t2x;
        tactic_ref m_preprocessor;
        model_ref m_model;
        expr_ref_vector m_core;
        std::string m_unknown;
        unsigned m_checks = 0, m_retractions = 0, m_retained_lemmas = 0;

        void invalidate() {
            m_model = nullptr;
            m_core.reset();
        }

        void internalize() {
            while (m_head < m_assertions.size()) {
                expr* tag = m_tags.get(m_head);
                unsigned end = m_head + 1;
                while (end < m_assertions.size() && m_tags.get(end) == tag)
                    ++end;
                goal_ref g = alloc(goal, m, false, false, false);
                for (unsigned i = m_head; i < end; ++i)
                    g->assert_expr(m_assertions.get(i));
                goal_ref_buffer result;
                m_preprocessor->cleanup();
                (*m_preprocessor)(g, result);
                if (result.size() != 1)
                    throw tactic_exception("Pareto nlsat preprocessing requires a single goal");
                if (result[0]->inconsistent())
                    m_nlsat.mk_clause(0, nullptr, tag);
                else {
                    goal2nlsat g2n;
                    g2n(*result[0], get_params(), m_nlsat, m_a2b, m_t2x, tag);
                }
                m_head = end;
            }
        }

        void extract_model() {
            arith_util a(m);
            m_model = alloc(model, m);
            // Preprocessing only introduces auxiliaries; projecting onto the
            // original constants hides them without scope-sensitive converters.
            for (expr* e : subterms::all(m_assertions)) {
                if (!is_uninterp_const(e))
                    continue;
                if (m_t2x.is_var(e)) {
                    expr_ref value(a.mk_numeral(m_nlsat.am(), m_nlsat.value(m_t2x.to_var(e)), false), m);
                    m_model->register_decl(to_app(e)->get_decl(), value);
                }
                else if (m_a2b.is_var(e)) {
                    lbool value = m_nlsat.bvalue(m_a2b.to_var(e));
                    if (value != l_undef)
                        m_model->register_decl(to_app(e)->get_decl(), value == l_true ? m.mk_true() : m.mk_false());
                }
            }
        }

        lbool check() {
            ++m_checks;
            m_unknown.clear();
            try {
                internalize();
                lbool result = m_nlsat.check();
                if (result == l_true)
                    extract_model();
                else if (result == l_undef)
                    m_unknown = "incomplete nlsat search";
                return result;
            }
            catch (tactic_exception& ex) {
                m_unknown = ex.what();
            }
            catch (nlsat::solver_exception& ex) {
                m_unknown = ex.what();
            }
            IF_VERBOSE(2, verbose_stream() << "(opt.pareto nlsat: " << m_unknown << ")\n");
            return l_undef;
        }

    public:
        pareto_nlsat_solver(ast_manager& m, params_ref const& p):
            solver_na2as(m), m_assertions(m), m_tags(m), m_scope_tags(m),
            m_nlsat(m.limit(), incremental_params(p), true), m_a2b(m), m_t2x(m),
            m_preprocessor(mk_preprocessor(m, p)), m_core(m) {
            solver::updt_params(p);
        }

        solver* translate(ast_manager& m, params_ref const& p) override {
            throw default_exception("the private Pareto nlsat solver cannot be translated");
        }

        ast_manager& get_manager() const override { return m; }

        void updt_params(params_ref const& p) override {
            solver::updt_params(p);
            m_nlsat.updt_params(incremental_params(get_params()));
            m_preprocessor->updt_params(get_params());
        }

        void collect_param_descrs(param_descrs& r) override {
            solver::collect_param_descrs(r);
            m_preprocessor->collect_param_descrs(r);
            nlsat::solver::collect_param_descrs(r);
        }

        void assert_expr_core(expr* e) override {
            m_assertions.push_back(e);
            m_tags.push_back(m_scope_tags.empty() ? nullptr : m_scope_tags.back());
            invalidate();
        }

        void push_core() override {
            m_limits.push_back(m_assertions.size());
            m_scope_tags.push_back(m.mk_fresh_const("pareto.nlsat.scope", m.mk_bool_sort()));
            invalidate();
        }

        void pop_core(unsigned n) override {
            SASSERT(n <= m_limits.size());
            if (!n)
                return;
            unsigned level = m_limits.size() - n;
            unsigned limit = m_limits[level];
            opt_params optp(get_params());
            for (unsigned i = m_limits.size(); i-- > level;) {
                m_nlsat.retract(m_scope_tags.get(i), optp.pareto_nlsat_max_lemmas());
                ++m_retractions;
                m_retained_lemmas += m_nlsat.get_lemmas().size();
            }
            m_assertions.shrink(limit);
            m_tags.shrink(limit);
            m_head = std::min(m_head, limit);
            m_limits.shrink(level);
            m_scope_tags.shrink(level);
            invalidate();
        }

        lbool check_sat_core2(unsigned n, expr* const* assumptions) override {
            invalidate();
            if (!n)
                return check();
            lbool result;
            model_ref model;
            {
                solver::scoped_push scope(*this);
                for (unsigned i = 0; i < n; ++i)
                    assert_expr(assumptions[i]);
                result = check();
                model = m_model;
            }
            m_model = model;
            if (result == l_false)
                m_core.append(n, assumptions);
            return result;
        }

        unsigned get_num_assertions() const override { return m_assertions.size(); }
        expr* get_assertion(unsigned i) const override { return m_assertions.get(i); }
        void get_model_core(model_ref& model) override { model = m_model; }
        void get_unsat_core(expr_ref_vector& core) override { core.append(m_core); }
        proof* get_proof_core() override { return nullptr; }
        void get_labels(svector<symbol>& labels) override { labels.reset(); }
        std::string reason_unknown() const override { return m_unknown; }
        void set_reason_unknown(char const* msg) override { m_unknown = msg; }

        void collect_statistics_core(statistics& st) const override {
            m_nlsat.collect_statistics(st);
            st.update("pareto nlsat checks", m_checks);
            st.update("pareto nlsat retractions", m_retractions);
            st.update("pareto nlsat retained lemmas", m_retained_lemmas);
        }

        void set_progress_callback(progress_callback*) override {}
        void set_phase(expr*) override {}
        phase* get_phase() override { return nullptr; }
        void set_phase(phase*) override {}
        void move_to_front(expr*) override {}
        expr* congruence_root(expr* e) override { return e; }
        expr* congruence_next(expr* e) override { return e; }
        expr_ref congruence_explain(expr* a, expr* b) override { return expr_ref(m.mk_eq(a, b), m); }
        expr_ref_vector cube(expr_ref_vector&, unsigned) override {
            throw default_exception("cubing is not supported by the private Pareto nlsat solver");
        }
        void get_levels(ptr_vector<expr> const&, unsigned_vector&) override {
            throw default_exception("levels are not supported by the private Pareto nlsat solver");
        }
        expr_ref_vector get_trail(unsigned) override {
            throw default_exception("trails are not supported by the private Pareto nlsat solver");
        }
    };

    }

    solver* mk_pareto_nlsat_solver(ast_manager& m, params_ref const& p) {
        return alloc(pareto_nlsat_solver, m, p);
    }
}
