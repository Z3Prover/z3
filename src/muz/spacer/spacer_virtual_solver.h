/**
Copyright (c) 2017 Arie Gurfinkel

Module Name:

    spacer_virtual_solver.h

Abstract:

   multi-solver view of a single solver

Author:

    Arie Gurfinkel

Notes:

--*/
#ifndef SPACER_VIRTUAL_SOLVER_H_
#define SPACER_VIRTUAL_SOLVER_H_
#include"ast/ast.h"
#include"util/params.h"
#include"solver/solver_na2as.h"
#include"smt/params/smt_params.h"
#include"util/stopwatch.h"
namespace spacer {
class virtual_solver_factory;

class virtual_solver : public solver_na2as {
    friend class virtual_solver_factory;

private:
    virtual_solver_factory &m_factory;
    ast_manager &m;
    solver &m_context;
    app_ref m_pred;

    bool m_virtual;
    expr_ref_vector m_assertions;
    unsigned m_head;
    // temporary to flatten conjunction
    expr_ref_vector m_flat;

    bool m_pushed;
    bool m_in_delay_scope;
    bool m_dump_benchmarks;
    unsigned m_dump_counter;

    proof_ref m_proof;

    virtual_solver(virtual_solver_factory &factory, app* pred);

    bool is_aux_predicate(expr *p);
    void internalize_assertions();
    void to_smt2_benchmark(std::ostream &out,
                           solver &context,
                           unsigned num_assumptions,
                           expr * const * assumptions,
                           char const * name = "benchmarks",
                           symbol const &logic = symbol::null,
                           char const * status = "unknown",
                           char const * attributes = "");

public:
    ~virtual_solver() override;
    unsigned get_num_assumptions() const override
    {
        unsigned sz = solver_na2as::get_num_assumptions();
        return m_virtual ? sz - 1 : sz;
    }
    expr* get_assumption(unsigned idx) const override
    {
        if(m_virtual) { idx++; }
        return solver_na2as::get_assumption(idx);
    }


    void get_unsat_core(ptr_vector<expr> &r) override;
    void assert_expr_core(expr *e) override;
    void collect_statistics(statistics &st) const override {m_context.collect_statistics(st);}
    void get_model_core(model_ref &m) override {m_context.get_model(m);}
    proof* get_proof() override;
    std::string reason_unknown() const override
    {return m_context.reason_unknown();}
    void set_reason_unknown(char const *msg) override
    {m_context.set_reason_unknown(msg);}
    ast_manager& get_manager() const override {return m;}
    void get_labels(svector<symbol> &r) override;
    void set_produce_models(bool f) override;
    smt_params &fparams();
    expr_ref_vector cube(expr_ref_vector&, unsigned) override { return expr_ref_vector(m); }
    void set_progress_callback(progress_callback *callback) override {UNREACHABLE();}

    solver *translate(ast_manager &m, params_ref const &p) override;

    void updt_params(params_ref const &p) override;
    void reset_params(params_ref const& p) override;
    params_ref const& get_params() const override;
    void collect_param_descrs(param_descrs &r) override;
    void push_params() override;
    void pop_params() override;


protected:
    lbool check_sat_core(unsigned num_assumptions, expr *const * assumptions) override;
    void push_core() override;
    void pop_core(unsigned n) override;
};

/// multi-solver abstraction on top of a single solver
class virtual_solver_factory {
    friend class virtual_solver;
private:
    ast_manager &m;
    solver &m_context;
    /// solvers managed by this factory
    ptr_vector<virtual_solver> m_solvers;

    struct stats {
        unsigned m_num_smt_checks;
        unsigned m_num_sat_smt_checks;
        unsigned m_num_undef_smt_checks;
        stats() { reset(); }
        void reset() { memset(this, 0, sizeof(*this)); }
    };

    stats m_stats;
    stopwatch m_check_watch;
    stopwatch m_check_sat_watch;
    stopwatch m_check_undef_watch;
    stopwatch m_proof_watch;


    solver &get_base_solver() {return m_context;}
    ast_manager &get_manager() {return m;}

public:
    virtual_solver_factory(solver &base);
    virtual ~virtual_solver_factory();
    virtual_solver* mk_solver();
    void collect_statistics(statistics &st) const;
    void reset_statistics();
    void updt_params(params_ref const &p) {m_context.updt_params(p);}
    void collect_param_descrs(param_descrs &r) {m_context.collect_param_descrs(r);}
};

}


#endif
