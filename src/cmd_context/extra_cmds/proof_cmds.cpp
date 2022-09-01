/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    proof_cmds.cpp

Abstract:

    Commands for reading and checking proofs.

Author:

    Nikolaj Bjorner (nbjorner) 2022-8-26

Notes:

Proof checker for clauses created during search.
1. Clauses annotated by RUP (reverse unit propagation)
   are checked to be inferrable using reverse unit propagation
   based on previous clauses.
2. Clauses annotated by supported proof rules (proof hints)
   are checked by custom proof checkers. There is a proof checker
   for each proof rule. Main proof checkers just have a single step
   but the framework allows to compose proof rules, each inference
   is checked for correctness by a plugin. 
3. When there are no supported plugin to justify the derived
   clause, or a custom check fails, the fallback is to check that the
   derived clause is a consequence of the input clauses using SMT.
   The last approach is a bail-out and offers a weaker notion of
   self-validation. It is often (but not always) sufficient for using proof
   checking for debugging, as the root-cause for an unsound inference in z3
   does not necessarily manifest when checking the conclusion of the
   inference. An external proof checker that uses such fallbacks could
   use several solvers, or bootstrap from a solver that can generate certificates
   when z3 does not.
   



--*/

#include "util/small_object_allocator.h"
#include "ast/ast_util.h"
#include "smt/smt_solver.h"
#include "sat/sat_solver.h"
#include "sat/sat_drat.h"
#include "sat/smt/euf_proof_checker.h"
#include "cmd_context/cmd_context.h"
#include <iostream>

class smt_checker {
    ast_manager& m;
    params_ref   m_params;

    // for checking proof rules (hints)
    euf::proof_checker m_checker;

    // for fallback SMT checker
    scoped_ptr<solver> m_solver;

    // for RUP
    symbol       m_rup;
    sat::solver  m_sat_solver;
    sat::drat    m_drat;
    sat::literal_vector m_units;
    sat::literal_vector m_clause;

    void add_units() {
        auto const& units = m_drat.units();
        for (unsigned i = m_units.size(); i < units.size(); ++i)
            m_units.push_back(units[i].first);
    }

public:
    smt_checker(ast_manager& m):
        m(m),
        m_checker(m),
        m_sat_solver(m_params, m.limit()), 
        m_drat(m_sat_solver) 
    {
        m_params.set_bool("drat.check_unsat", true);
        m_sat_solver.updt_params(m_params);
        m_drat.updt_config();
        m_solver = mk_smt_solver(m, m_params, symbol());
        m_rup = symbol("rup");
    }

    bool is_rup(app* proof_hint) {
        return
            proof_hint &&
            proof_hint->get_name() == m_rup;        
    }

    void mk_clause(expr_ref_vector const& clause) {
        m_clause.reset();
        for (expr* e : clause) {
            bool sign = false;
            while (m.is_not(e, e))
                sign = !sign;
            m_clause.push_back(sat::literal(e->get_id(), sign));
        }
    }

    void mk_clause(expr* e) {
        m_clause.reset();
        bool sign = false;
        while (m.is_not(e, e))
            sign = !sign;
        m_clause.push_back(sat::literal(e->get_id(), sign));
    }
    
    bool check_rup(expr_ref_vector const& clause) {
        add_units();
        mk_clause(clause);
        return m_drat.is_drup(m_clause.size(), m_clause.data(), m_units);
    }

    bool check_rup(expr* u) {
        add_units();
        mk_clause(u);
        return m_drat.is_drup(m_clause.size(), m_clause.data(), m_units);
    }

    void add_clause(expr_ref_vector const& clause) {
        mk_clause(clause);
        m_drat.add(m_clause, sat::status::input());
    }

    void check(expr_ref_vector& clause, app* proof_hint) {
        
        if (is_rup(proof_hint) && check_rup(clause)) {
            std::cout << "(verified-rup)\n";
            return;
        }

        expr_ref_vector units(m);
        if (m_checker.check(clause, proof_hint, units)) {
            bool units_are_rup = true;
            for (expr* u : units) {
                if (!check_rup(u)) {
                    std::cout << "unit " << mk_pp(u, m) << " is not rup\n";
                    units_are_rup = false;
                }
            }
            if (units_are_rup) {
                std::cout << "(verified-" << proof_hint->get_name() << ")\n";
                add_clause(clause);
                return;
            }
        }

        m_solver->push();
        for (expr* lit : clause)
            m_solver->assert_expr(m.mk_not(lit));
        lbool is_sat = m_solver->check_sat();
        if (is_sat != l_false) {
            std::cout << "did not verify: " << is_sat << " " << clause << "\n\n";
            m_solver->display(std::cout);
            if (is_sat == l_true) {
                model_ref mdl;
                m_solver->get_model(mdl);
                std::cout << *mdl << "\n";
            }                
            exit(0);
        }
        m_solver->pop(1);
        std::cout << "(verified-smt)\n";
        if (proof_hint)
            std::cout << "(missed-hint " << mk_pp(proof_hint, m) << ")\n";
        add_clause(clause);
    }

    void assume(expr_ref_vector const& clause) {
        add_clause(clause);
        m_solver->assert_expr(mk_or(clause));
    }
};

class proof_cmds_imp : public proof_cmds {
    ast_manager&    m;
    expr_ref_vector m_lits;
    app_ref         m_proof_hint;
    smt_checker     m_checker;
public:
    proof_cmds_imp(ast_manager& m): m(m), m_lits(m), m_proof_hint(m), m_checker(m) {}

    void add_literal(expr* e) override {
        if (m.is_proof(e))
            m_proof_hint = to_app(e);
        else
            m_lits.push_back(e);
    }

    void end_assumption() override {
        m_checker.assume(m_lits);
        m_lits.reset();
        m_proof_hint.reset();
    }

    void end_learned() {
        m_checker.check(m_lits, m_proof_hint);
        m_lits.reset();
        m_proof_hint.reset();
    }

    void end_deleted() {
        m_lits.reset();
        m_proof_hint.reset();
    }
};


static proof_cmds& get(cmd_context& ctx) {
    if (!ctx.get_proof_cmds())
        ctx.set_proof_cmds(alloc(proof_cmds_imp, ctx.m()));
    return *ctx.get_proof_cmds();
}

// assumption
class assume_cmd : public cmd {
public:
    assume_cmd():cmd("assume") {}
    char const* get_usage() const override { return "<expr>+"; }
    char const * get_descr(cmd_context& ctx) const override { return "proof command for adding assumption (input assertion)"; }
    unsigned get_arity() const override { return VAR_ARITY; }
    void prepare(cmd_context & ctx) override {}
    void finalize(cmd_context & ctx) override {}
    void failure_cleanup(cmd_context & ctx) override {}
    cmd_arg_kind next_arg_kind(cmd_context & ctx) const override { return CPK_EXPR; }    
    void set_next_arg(cmd_context & ctx, expr * arg) override { get(ctx).add_literal(arg); }
    void execute(cmd_context& ctx) override { get(ctx).end_assumption(); }
};

// deleted clause
class del_cmd : public cmd {
public:
    del_cmd():cmd("del") {}
    char const* get_usage() const override { return "<expr>+"; }
    char const * get_descr(cmd_context& ctx) const override { return "proof command for clause deletion"; }
    unsigned get_arity() const override { return VAR_ARITY; }
    void prepare(cmd_context & ctx) override {}
    void finalize(cmd_context & ctx) override {}
    void failure_cleanup(cmd_context & ctx) override {}
    cmd_arg_kind next_arg_kind(cmd_context & ctx) const override { return CPK_EXPR; }    
    void set_next_arg(cmd_context & ctx, expr * arg) override { get(ctx).add_literal(arg); }
    void execute(cmd_context& ctx) override { get(ctx).end_deleted(); }
};

// learned/redundant clause
class learn_cmd : public cmd {
public:
    learn_cmd():cmd("learn") {}
    char const* get_usage() const override { return "<expr>+"; }
    char const* get_descr(cmd_context& ctx) const override { return "proof command for learned (redundant) clauses"; }
    unsigned get_arity() const override { return VAR_ARITY; }
    void prepare(cmd_context & ctx) override {}
    void finalize(cmd_context & ctx) override {}
    void failure_cleanup(cmd_context & ctx) override {}
    cmd_arg_kind next_arg_kind(cmd_context & ctx) const override { return CPK_EXPR; }    
    void set_next_arg(cmd_context & ctx, expr * arg) override { get(ctx).add_literal(arg); }
    void execute(cmd_context& ctx) override { get(ctx).end_learned(); }
};

void install_proof_cmds(cmd_context & ctx) {
    ctx.insert(alloc(del_cmd));
    ctx.insert(alloc(learn_cmd));
    ctx.insert(alloc(assume_cmd));
}
