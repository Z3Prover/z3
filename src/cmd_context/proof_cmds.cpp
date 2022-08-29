/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    proof_cmds.cpp

Abstract:

    Commands for reading and checking proofs.

Author:

    Nikolaj Bjorner (nbjorner) 2022-8-26

Notes:

- add theory hint bypass using proof checker plugins of SMT
  - arith_proof_checker.h is currently
- could use m_drat for drup premises.

--*/

#include "util/small_object_allocator.h"
#include "ast/ast_util.h"
#include "cmd_context/cmd_context.h"
#include "smt/smt_solver.h"
#include "sat/sat_solver.h"
#include "sat/sat_drat.h"
#include "sat/smt/euf_proof_checker.h"
#include <iostream>

class smt_checker {
    ast_manager& m;
    params_ref   m_params;
    euf::proof_checker m_checker;

    scoped_ptr<solver> m_solver;

#if 0
    sat::solver  sat_solver;
    sat::drat    m_drat;
    sat::literal_vector m_units;
    sat::literal_vector m_drup_units;

    void add_units() {
        auto const& units = m_drat.units();
        for (unsigned i = m_units.size(); i < units.size(); ++i)
            m_units.push_back(units[i].first);
    }
#endif

public:
    smt_checker(ast_manager& m):
        m(m),
        m_checker(m)
        // sat_solver(m_params, m.limit()), 
        // m_drat(sat_solver) 
    {
        m_solver = mk_smt_solver(m, m_params, symbol());
    }

    void check(expr_ref_vector const& clause, expr* proof_hint) {

        if (m_checker.check(clause, proof_hint)) {
            if (is_app(proof_hint))
                std::cout << "(verified-" << to_app(proof_hint)->get_name() << ")\n";
            else
                std::cout << "(verified-checker)\n";
            return;
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
        // assume(clause);
    }

    void assume(expr_ref_vector const& clause) {
        m_solver->assert_expr(mk_or(clause));
    }
};

class proof_cmds::imp {
    ast_manager& m;
    expr_ref_vector m_lits;
    expr_ref m_proof_hint;
    smt_checker m_checker;
public:
    imp(ast_manager& m): m(m), m_lits(m), m_proof_hint(m), m_checker(m) {}

    void add_literal(expr* e) {
        if (m.is_proof(e))
            m_proof_hint = e;
        else
            m_lits.push_back(e);
    }

    void end_assumption() {
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

proof_cmds* proof_cmds::mk(ast_manager& m) {
    return alloc(proof_cmds, m);
}

proof_cmds::proof_cmds(ast_manager& m) {
    m_imp = alloc(imp, m);
}

proof_cmds::~proof_cmds() {
    dealloc(m_imp);
}

void proof_cmds::add_literal(expr* e) {
    m_imp->add_literal(e);
}

void proof_cmds::end_assumption() {
    m_imp->end_assumption();
}

void proof_cmds::end_learned() {
    m_imp->end_learned();
}

void proof_cmds::end_deleted() {
    m_imp->end_deleted();
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
    void set_next_arg(cmd_context & ctx, expr * arg) override { ctx.get_proof_cmds().add_literal(arg); }
    void execute(cmd_context& ctx) override { ctx.get_proof_cmds().end_assumption(); }
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
    void set_next_arg(cmd_context & ctx, expr * arg) override { ctx.get_proof_cmds().add_literal(arg); }
    void execute(cmd_context& ctx) override { ctx.get_proof_cmds().end_deleted(); }
};

// learned/redundant clause
class learn_cmd : public cmd {
public:
    learn_cmd():cmd("learn") {}
    char const* get_usage() const override { return "<expr>+"; }
    char const * get_descr(cmd_context& ctx) const override { return "proof command for learned (redundant) clauses"; }
    unsigned get_arity() const override { return VAR_ARITY; }
    void prepare(cmd_context & ctx) override {}
    void finalize(cmd_context & ctx) override {}
    void failure_cleanup(cmd_context & ctx) override {}
    cmd_arg_kind next_arg_kind(cmd_context & ctx) const override { return CPK_EXPR; }    
    void set_next_arg(cmd_context & ctx, expr * arg) override { ctx.get_proof_cmds().add_literal(arg); }
    void execute(cmd_context& ctx) override { ctx.get_proof_cmds().end_learned(); }
};

void install_proof_cmds(cmd_context & ctx) {
    ctx.insert(alloc(del_cmd));
    ctx.insert(alloc(learn_cmd));
    ctx.insert(alloc(assume_cmd));
}
