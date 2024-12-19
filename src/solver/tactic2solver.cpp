/*++ Copyright (c) 2012 Microsoft Corporation

Module Name:

    tactic2solver.cpp

Abstract:

    Wrapper for implementing the solver interface
    using a tactic.

    This is a light version of the strategic solver.

Author:

    Leonardo (leonardo) 2012-01-23

Notes:

--*/
#include "ast/ast_translation.h"
#include "ast/ast_pp.h"
#include "tactic/tactic.h"
#include "solver/tactic2solver.h"
#include "solver/solver_na2as.h"
#include "solver/mus.h"
#include "smt/params/smt_params.h"
#include "smt/params/smt_params_helper.hpp"


/**
   \brief Simulates the incremental solver interface using a tactic.

   Every query will be solved from scratch.  So, this is not a good
   option for applications trying to solve many easy queries that a
   similar to each other.
*/

namespace {
class tactic2solver : public solver_na2as {
    expr_ref_vector              m_assertions;
    expr_ref_vector              m_last_assertions;
    unsigned                     m_last_assertions_valid;
    unsigned_vector              m_scopes;
    ref<simple_check_sat_result> m_result;
    tactic_ref                   m_tactic;
    ref<model_converter>         m_mc;
    symbol                       m_logic;
    bool                         m_produce_models;
    bool                         m_produce_proofs;
    bool                         m_produce_unsat_cores;
    statistics                   m_stats;
    bool                         m_minimizing = false;
    
public:
    tactic2solver(ast_manager & m, tactic * t, params_ref const & p, bool produce_proofs, bool produce_models, bool produce_unsat_cores, symbol const & logic);
    ~tactic2solver() override;

    solver* translate(ast_manager& m, params_ref const& p) override;

    void updt_params(params_ref const & p) override;
    void collect_param_descrs(param_descrs & r) override;

    void set_produce_models(bool f) override { m_produce_models = f; }

    void assert_expr_core(expr * t) override;
    ast_manager& get_manager() const override;

    void push_core() override;
    void pop_core(unsigned n) override;
    lbool check_sat_core2(unsigned num_assumptions, expr * const * assumptions) override;

    void collect_statistics(statistics & st) const override;
    void get_unsat_core(expr_ref_vector & r) override;
    void get_model_core(model_ref & m) override;
    proof * get_proof_core() override;
    std::string reason_unknown() const override;
    void set_reason_unknown(char const* msg) override;
    void get_labels(svector<symbol> & r) override {}

    void set_progress_callback(progress_callback * callback) override {}

    unsigned get_num_assertions() const override;
    expr * get_assertion(unsigned idx) const override;
    void set_phase(expr* e) override { }
    phase* get_phase() override { return nullptr; }
    void set_phase(phase* p) override { }
    void move_to_front(expr* e) override { }

    void register_on_clause(void* ctx, user_propagator::on_clause_eh_t& on_clause) override {
        m_tactic->register_on_clause(ctx, on_clause);
    }

    void user_propagate_init(
        void* ctx,
        user_propagator::push_eh_t& push_eh,
        user_propagator::pop_eh_t& pop_eh,
        user_propagator::fresh_eh_t& fresh_eh) override {
        m_tactic->user_propagate_init(ctx, push_eh, pop_eh, fresh_eh);
    }

    void user_propagate_register_fixed(user_propagator::fixed_eh_t& fixed_eh) override {
        m_tactic->user_propagate_register_fixed(fixed_eh);
    }

    void user_propagate_register_final(user_propagator::final_eh_t& final_eh) override {
        m_tactic->user_propagate_register_final(final_eh);
    }

    void user_propagate_register_eq(user_propagator::eq_eh_t& eq_eh) override {
        m_tactic->user_propagate_register_eq(eq_eh);
    }

    void user_propagate_register_diseq(user_propagator::eq_eh_t& diseq_eh) override {
        m_tactic->user_propagate_register_diseq(diseq_eh);
    }

    void user_propagate_register_expr(expr* e) override {
        m_tactic->user_propagate_register_expr(e);
    }
    
    void user_propagate_initialize_value(expr* var, expr* value) override {
        m_tactic->user_propagate_initialize_value(var, value);
    }

    void user_propagate_register_created(user_propagator::created_eh_t& created_eh) override {
        m_tactic->user_propagate_register_created(created_eh);
    }

    void user_propagate_register_decide(user_propagator::decide_eh_t& decide_eh) override {
        m_tactic->user_propagate_register_decide(decide_eh);
    }

    void user_propagate_clear() override {
        if (m_tactic)
            m_tactic->user_propagate_clear();
    }


    expr_ref_vector cube(expr_ref_vector& vars, unsigned ) override {
        set_reason_unknown("cubing is not supported on tactics");
        IF_VERBOSE(1, verbose_stream() << "cubing is not supported on tactics\n");
        return expr_ref_vector(get_manager());
    }

    expr* congruence_next(expr* e) override { return e; }
    expr* congruence_root(expr* e) override { return e; }
    expr_ref congruence_explain(expr* a, expr* b) override { return expr_ref(get_manager().mk_eq(a, b), get_manager()); }

    model_converter_ref get_model_converter() const override { return m_mc; }

    void get_levels(ptr_vector<expr> const& vars, unsigned_vector& depth) override {
        throw default_exception("cannot retrieve depth from solvers created using tactics");
    }

    expr_ref_vector get_trail(unsigned max_level) override {
        throw default_exception("cannot retrieve trail from solvers created using tactics");
    }
};

ast_manager& tactic2solver::get_manager() const { return m_assertions.get_manager(); }

tactic2solver::tactic2solver(ast_manager & m, tactic * t, params_ref const & p, bool produce_proofs, bool produce_models, bool produce_unsat_cores, symbol const & logic):
    solver_na2as(m),
    m_assertions(m),
    m_last_assertions(m),
    m_last_assertions_valid(false) {

    m_tactic = t;
    m_logic  = logic;
    solver::updt_params(p);
    
    m_produce_models      = produce_models;
    m_produce_proofs      = produce_proofs;
    m_produce_unsat_cores = produce_unsat_cores;
}

tactic2solver::~tactic2solver() {
    user_propagate_clear();
}

void tactic2solver::updt_params(params_ref const & p) {
    solver::updt_params(p);
    m_produce_unsat_cores |= p.get_bool("unsat_core", false);
}

void tactic2solver::collect_param_descrs(param_descrs & r) {
    solver::collect_param_descrs(r);
    if (m_tactic.get())
        m_tactic->collect_param_descrs(r);
}

void tactic2solver::assert_expr_core(expr * t) {
    m_last_assertions_valid = false;
    m_assertions.push_back(t);
    m_result = nullptr;
}


void tactic2solver::push_core() {
    m_last_assertions_valid = false;
    m_scopes.push_back(m_assertions.size());
    m_result = nullptr;
    TRACE("pop", tout << m_scopes.size() << "\n";);
}

void tactic2solver::pop_core(unsigned n) {
    m_last_assertions_valid = false;
    TRACE("pop", tout << m_scopes.size() << " " << n << "\n";);
    n = std::min(m_scopes.size(), n);
    unsigned new_lvl = m_scopes.size() - n;
    unsigned old_sz  = m_scopes[new_lvl];
    m_assertions.shrink(old_sz);
    m_scopes.shrink(new_lvl);
    m_result = nullptr;
}

lbool tactic2solver::check_sat_core2(unsigned num_assumptions, expr * const * assumptions) {
    if (m_tactic.get() == nullptr)
        return l_false;
    m_last_assertions_valid = false;
    ast_manager & m = m_assertions.m();
    m_result = alloc(simple_check_sat_result, m);
    m_tactic->cleanup();
    m_tactic->set_logic(m_logic);
    m_tactic->updt_params(get_params()); // parameters are allowed to overwrite logic.
    goal_ref g = alloc(goal, m, m_produce_proofs, m_produce_models, m_produce_unsat_cores);

    for (expr* e : m_assertions) {
        g->assert_expr(e);
    }
    for (unsigned i = 0; i < num_assumptions; i++) {
        proof_ref pr(m.mk_asserted(assumptions[i]), m);
        expr_dependency_ref ans(m.mk_leaf(assumptions[i]), m);    
        g->assert_expr(assumptions[i], pr, ans);
    }

    model_ref           md;
    proof_ref           pr(m);    
    expr_dependency_ref core(m);
    std::string         reason_unknown = "unknown";
    labels_vec labels;
    TRACE("tactic", g->display(tout););
    try {
        switch (::check_sat(*m_tactic, g, md, labels, pr, core, reason_unknown)) {
        case l_true: 
            m_result->set_status(l_true);
            break;
        case l_false: 
            m_result->set_status(l_false);
            break;
        default: 
            m_result->set_status(l_undef);
            if (!reason_unknown.empty())
                m_result->m_unknown = reason_unknown;
            if (num_assumptions == 0 && m_scopes.empty()) {
                m_last_assertions.reset();
                g->get_formulas(m_last_assertions);
                m_last_assertions_valid = true;
            }
            break;
        }
        CTRACE("tactic", md.get(), tout << *md.get() << "\n";);
        TRACE("tactic", 
              if (m_mc) m_mc->display(tout << "mc:\n");
              if (g->mc()) g->mc()->display(tout << "\ng:\n");
              if (md) tout << "\nmodel:\n" << *md.get() << "\n";
              );
        m_mc = g->mc();

    }
    catch (z3_error & ex) {
        TRACE("tactic2solver", tout << "exception: " << ex.what() << "\n";);
        m_result->m_proof = pr;
        throw ex;
    }
    catch (z3_exception & ex) {
        TRACE("tactic2solver", tout << "exception: " << ex.what() << "\n";);
        m_result->set_status(l_undef);
        m_result->m_unknown = ex.what();
        m_result->m_proof = pr;
    }
    m_tactic->collect_statistics(m_result->m_stats);
    m_tactic->collect_statistics(m_stats);
    m_result->m_model = md;
    m_result->m_proof = pr;
    if (m_produce_unsat_cores) {
        ptr_vector<expr> core_elems;
        m.linearize(core, core_elems);
        m_result->m_core.append(core_elems.size(), core_elems.data());
    }
    m_tactic->cleanup();
    return m_result->status();
}


solver* tactic2solver::translate(ast_manager& m, params_ref const& p) {
    tactic* t = m_tactic->translate(m);
    tactic2solver* r = alloc(tactic2solver, m, t, p, m_produce_proofs, m_produce_models, m_produce_unsat_cores, m_logic);
    r->m_result = nullptr;
    ast_translation tr(m_assertions.get_manager(), m, false);
    
    for (unsigned i = 0; i < get_num_assertions(); ++i) {
        r->m_assertions.push_back(tr(get_assertion(i)));
    }
    return r;
}


void tactic2solver::collect_statistics(statistics & st) const {    
    st.copy(m_stats);
    //SASSERT(m_stats.size() > 0);
}

void tactic2solver::get_unsat_core(expr_ref_vector & r) {
    if (m_result.get()) {
        m_result->get_unsat_core(r);
        if (!m_minimizing && smt_params_helper(get_params()).core_minimize()) {
            flet<bool> minimizing(m_minimizing, true);
            mus mus(*this);
            mus.add_soft(r.size(), r.data());
            expr_ref_vector r2(m);
            if (l_true == mus.get_mus(r2)) {
                r.reset();
                r.append(r2);
            }
        }
    }
}

void tactic2solver::get_model_core(model_ref & m) {
    if (m_result.get()) {
        m_result->get_model_core(m);
    }
}

proof * tactic2solver::get_proof_core() {
    if (m_result.get())
        return m_result->get_proof_core();
    else
        return nullptr;
}

std::string tactic2solver::reason_unknown() const {
    if (m_result.get())
        return m_result->reason_unknown();
    else
        return std::string("unknown");
}

void tactic2solver::set_reason_unknown(char const* msg) {
    if (m_result.get()) {
        m_result->set_reason_unknown(msg);
    }
}

unsigned tactic2solver::get_num_assertions() const {
    return m_last_assertions_valid ? m_last_assertions.size() : m_assertions.size();
}

expr * tactic2solver::get_assertion(unsigned idx) const {
    return m_last_assertions_valid ? m_last_assertions.get(idx) : m_assertions.get(idx);
}
}


solver * mk_tactic2solver(ast_manager & m, 
                          tactic * t, 
                          params_ref const & p,
                          bool produce_proofs,
                          bool produce_models,
                          bool produce_unsat_cores,
                          symbol const & logic) {
    return alloc(tactic2solver, m, t, p, produce_proofs, produce_models, produce_unsat_cores, logic);
}

namespace {
class tactic2solver_factory : public solver_factory {
    ref<tactic> m_tactic;
public:
    tactic2solver_factory(tactic * t):m_tactic(t) {
    }

    solver * operator()(ast_manager & m, params_ref const & p, bool proofs_enabled, bool models_enabled, bool unsat_core_enabled, symbol const & logic) override {
        return mk_tactic2solver(m, m_tactic.get(), p, proofs_enabled, models_enabled, unsat_core_enabled, logic);
    }
};

class tactic_factory2solver_factory : public solver_factory {
    tactic_factory m_factory;
public:
    tactic_factory2solver_factory(tactic_factory f):m_factory(f) {
    }
    
    solver * operator()(ast_manager & m, params_ref const & p, bool proofs_enabled, bool models_enabled, bool unsat_core_enabled, symbol const & logic) override {
        tactic * t = (*m_factory)(m, p);
        return mk_tactic2solver(m, t, p, proofs_enabled, models_enabled, unsat_core_enabled, logic);
    }
};
}

solver_factory * mk_tactic2solver_factory(tactic * t) {
    return alloc(tactic2solver_factory, t);
}

solver_factory * mk_tactic_factory2solver_factory(tactic_factory f) {
    return alloc(tactic_factory2solver_factory, f);
}


