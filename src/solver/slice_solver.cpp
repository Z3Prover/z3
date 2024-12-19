/*++
Copyright (c) 2023 Microsoft Corporation

Module Name:

    slice_solver.cpp

Abstract:

    Implements a solver that slices assertions based on the query.
    
Author:

    Nikolaj Bjorner (nbjorner) 2024-10-07

--*/

#include "solver/solver.h"
#include "solver/slice_solver.h"
#include "ast/for_each_ast.h"
#include "ast/ast_pp.h"
#include "params/solver_params.hpp"

class slice_solver : public solver {

    struct fml_t {
        expr_ref formula;
        expr_ref assumption;
        bool     active;
        unsigned level;       
    };
    ast_manager& m;
    solver_ref s;
    vector<fml_t>    m_assertions;
    unsigned_vector  m_assertions_lim;
    obj_map<func_decl, unsigned_vector> m_occurs;
    ptr_vector<func_decl> m_occurs_trail;
    unsigned_vector       m_occurs_lim;
    obj_hashtable<func_decl> m_used_funs;
    ptr_vector<func_decl>    m_used_funs_trail;
    unsigned_vector          m_used_funs_lim;
    bool m_has_query = false;

    ast_mark m_mark;

    void add_occurs(unsigned i, expr* e) {
        struct visit {
            slice_solver& s;
            unsigned i;
            visit(slice_solver& s, unsigned i):s(s), i(i) {}
            
            void operator()(func_decl* f) {
                if (is_uninterp(f)) {
                    s.m_occurs.insert_if_not_there(f, unsigned_vector()).push_back(i);
                    s.m_occurs_trail.push_back(f);
                }
            }
            
            void operator()(ast* a) {}
        };
        m_mark.reset();
        visit visitor(*this, i);
        ptr_buffer<expr> args;

        if (m.is_and(e))
            args.append(to_app(e)->get_num_args(), to_app(e)->get_args());
        else
            args.push_back(e);
        bool has_quantifier = any_of(args, [&](expr* arg) { return is_quantifier(arg); });
        for (expr* arg : args) {
            if (is_quantifier(arg)) {
                auto q = to_quantifier(arg);
                // all symbols in pattern must be present for quantifier to be considered relevant.
                for (unsigned j = 0; j < q->get_num_patterns(); ++j)
                    for_each_ast(visitor, m_mark, q->get_pattern(j));
            }
            else if (!has_quantifier)
                for_each_ast(visitor, m_mark, arg);
        }
    }

    void flush() {
        for (unsigned idx = 0; idx < m_assertions.size(); ++idx) {
            auto& f = m_assertions[idx];
            if (!f.active) {
                f.active = true;
                m_new_idx.push_back(idx);
            }
        }
        activate_indices();
        m_new_idx.reset();
    }

    unsigned_vector m_new_idx;
    void activate(unsigned idx, expr* e) {
        struct visit {
            slice_solver& s;
            visit(slice_solver& s): s(s) {}
            void operator()(func_decl* f) {
                if (!s.m_used_funs.contains(f)) {
                    s.m_used_funs_trail.push_back(f);
                    s.m_used_funs.insert(f);
                }
            }
            void operator()(ast* a) {}
        };
        SASSERT(m_new_idx.empty());
        visit visitor(*this);
        m_mark.reset();
        for_each_ast(visitor, m_mark, e);
        consume_used_funs();
        for (unsigned i = 0; m.inc() && i < m_new_idx.size(); ++i) {
            auto& f = m_assertions[m_new_idx[i]];
            expr* e = f.formula;
            ptr_buffer<expr> args;
            if (m.is_and(e))
                args.append(to_app(e)->get_num_args(), to_app(e)->get_args());
            else
                args.push_back(e);

            for (expr* arg : args) {
                if (is_quantifier(arg)) {
                    for_each_ast(visitor, m_mark, arg);
                    consume_used_funs();
                }
            }
        }
        std::sort(m_new_idx.begin(), m_new_idx.end());
        activate_indices();
        m_new_idx.reset();

        IF_VERBOSE(2, log_active(verbose_stream()););
    }

    void log_active(std::ostream& out) {
        unsigned num_passive = 0, num_active = 0;
        for (auto const& f : m_assertions)
            if (f.active)
                ++num_active;
            else
                ++num_passive;
        out << "passive " << num_passive << " active " << num_active << "\n";
    }
 
    unsigned m_qhead = 0;
    void consume_used_funs() {
        for (; m_qhead < m_used_funs_trail.size(); ++m_qhead) {
            func_decl* f = m_used_funs_trail[m_qhead];
            auto* e = m_occurs.find_core(f);
            if (!e)
                continue;
            for (unsigned idx : e->get_data().m_value) {
                if (!should_activate(idx))
                    continue;
                m_new_idx.push_back(idx);
                m_assertions[idx].active = true;
            }
        }
    }

    bool should_activate(unsigned idx) {
        auto& f = m_assertions[idx];
        return !f.active && should_activate(f.formula.get());
    }

    bool should_activate(expr* f) {
        if (is_ground(f))
            return true;

        if (m.is_and(f))
            for (expr* arg : *to_app(f))
                if (is_forall(arg) && should_activate(arg))
                    return true;

        if (!is_forall(f))
            return true;
        
        auto q = to_quantifier(f);
        return should_activiate_quantifier(q);
    }

    bool should_activiate_quantifier(quantifier* q) {
        struct visit {
            slice_solver& s;
            bool m_all_visited = true;
            visit(slice_solver& s) : s(s) {}
            void operator()(func_decl* f) {
                if (is_uninterp(f))
                    m_all_visited &= s.m_used_funs.contains(f);
            }
            void operator()(ast* a) {}
        };
        m_mark.reset();
        visit visitor(*this);
        for (unsigned i = 0; i < q->get_num_patterns(); ++i)
            for_each_ast(visitor, m_mark, q->get_pattern(i));
        return visitor.m_all_visited;
    }
 
    void assert_expr(fml_t const & f) {
        if (f.assumption)
            s->assert_expr(f.formula, f.assumption);
        else
            s->assert_expr(f.formula);
    }

    void activate_indices() {
        if (m_new_idx.empty())
            return;
        unsigned idx = m_new_idx[0];
        auto const& f0 = m_assertions[idx];
        if (f0.level < s->get_scope_level()) {
            
            // pop to f.level
            // add m_new_idx within f.level
            // replay push and assertions above f.level
            s->pop(s->get_scope_level() - f0.level);
            unsigned last_idx = idx;
            for (unsigned idx : m_new_idx) {
                // add only new assertions within lowest scope level.
                auto const& f = m_assertions[idx];
                if (s->get_scope_level() != f.level)
                    break;
                last_idx = idx;
                assert_expr(f);
            }
            for (unsigned i = last_idx + 1; i < m_assertions.size(); ++i) {
                // add all active assertions within other scope levels.
                auto const& f = m_assertions[i];
                if (f0.level == f.level)
                    continue;
                while (f.level > s->get_scope_level()) 
                    s->push();
                
                if (f.active) 
                    assert_expr(f);                
            }
        }
        else {
            for (unsigned idx : m_new_idx) {
                auto const& f = m_assertions[idx];
                while (f.level > s->get_scope_level()) 
                    s->push();
                assert_expr(f);
            }
        }
    }

    bool is_query(expr* a) {
        return is_uninterp_const(a) && to_app(a)->get_decl()->get_name() == "@query";
    }
    
public:

    slice_solver(solver* s) :
        solver(s->get_manager()),
        m(s->get_manager()),
        s(s) {
    }

    void assert_expr_core2(expr* t, expr* a) override {
        if (!a)
            assert_expr_core(t);
        else {
            unsigned i = m_assertions.size();
            m_assertions.push_back({expr_ref(t, m), expr_ref(a, m), false, m_assertions_lim.size()});
            add_occurs(i, t);
            add_occurs(i, a);
            if (is_query(a)) {
                activate(i, t);
                m_has_query = true;
            }
        }
    }

    void assert_expr_core(expr* t) override {
        unsigned i = m_assertions.size();
        m_assertions.push_back({expr_ref(t, m), expr_ref(nullptr, m), false, m_assertions_lim.size()});
        add_occurs(i, t);
    }

    void push() override {
        m_assertions_lim.push_back(m_assertions.size());
        m_occurs_lim.push_back(m_occurs_trail.size());
        m_used_funs_lim.push_back(m_used_funs_trail.size());
    }

    void pop(unsigned n) override {
        unsigned old_sz = m_assertions_lim[m_assertions_lim.size() - n];
        for (unsigned i = m_assertions.size(); i-- > old_sz; ) {
            auto const& f = m_assertions[i];
            if (f.level < s->get_scope_level()) 
                s->pop(s->get_scope_level() - f.level);
        }
        m_assertions_lim.shrink(m_assertions_lim.size() - n);
        m_assertions.shrink(old_sz);
        old_sz = m_occurs_lim[m_occurs_lim.size() - n];
        for (unsigned i = m_occurs_trail.size(); i-- > old_sz; ) {
            auto f = m_occurs_trail[i];
            m_occurs[f].pop_back();
        }
        m_occurs_lim.shrink(m_occurs_lim.size() - n);
        m_occurs_trail.shrink(old_sz);

        old_sz = m_used_funs_lim[m_used_funs_lim.size() - n];
        for (unsigned i = m_used_funs_trail.size(); i-- > old_sz; ) {
            auto f = m_used_funs_trail[i];
            m_used_funs.erase(f);
        }
        m_used_funs_lim.shrink(m_used_funs_lim.size() - n);
        m_used_funs_trail.shrink(old_sz);
        m_qhead = 0;
        m_has_query = false;
    }

    lbool check_sat_core(unsigned num_assumptions, expr* const* assumptions) override {
        if (!m_has_query || num_assumptions > 0)
            flush();
        return s->check_sat_core(num_assumptions, assumptions);
    }

    void collect_statistics(statistics& st) const override { s->collect_statistics(st); }

    void get_model_core(model_ref& mdl) override { s->get_model_core(mdl); }

    proof* get_proof_core() override { return s->get_proof(); }

    solver* translate(ast_manager& m, params_ref const& p) override { 
        solver* new_s = s->translate(m, p);
        solver* new_slice = alloc(slice_solver, new_s);
        unsigned level = 0;
        ast_translation tr(get_manager(), m);
        for (auto & f : m_assertions) {
            while (f.level > level) {
                new_slice->push();
                ++level;
            }
            new_slice->assert_expr(tr(f.formula.get()), tr(f.assumption.get()));
        }
        return new_slice;
    }    

    void updt_params(params_ref const& p) override { s->updt_params(p); }

    model_converter_ref get_model_converter() const override { return s->get_model_converter(); }

    unsigned get_num_assertions() const override { return s->get_num_assertions(); }
    expr* get_assertion(unsigned idx) const override { return s->get_assertion(idx); }
    std::string reason_unknown() const override { return s->reason_unknown(); }
    void set_reason_unknown(char const* msg) override { s->set_reason_unknown(msg); }
    void get_labels(svector<symbol>& r) override { s->get_labels(r); }
    void get_unsat_core(expr_ref_vector& r) override { s->get_unsat_core(r); }
    ast_manager& get_manager() const override { return s->get_manager(); }    
    void reset_params(params_ref const& p) override { s->reset_params(p); }
    params_ref const& get_params() const override { return s->get_params(); }
    void collect_param_descrs(param_descrs& r) override { s->collect_param_descrs(r); }
    void push_params() override { s->push_params(); }
    void pop_params() override { s->pop_params(); }
    void set_produce_models(bool f) override { s->set_produce_models(f); }
    void set_phase(expr* e) override { s->set_phase(e); }
    void move_to_front(expr* e) override { s->move_to_front(e); }
    phase* get_phase() override { return s->get_phase(); }
    void set_phase(phase* p) override { s->set_phase(p); }
    unsigned get_num_assumptions() const override { return s->get_num_assumptions(); }
    expr* get_assumption(unsigned idx) const override { return s->get_assumption(idx); }
    unsigned get_scope_level() const override { return s->get_scope_level(); }
    void set_progress_callback(progress_callback* callback) override { s->set_progress_callback(callback); }

    lbool get_consequences(expr_ref_vector const& asms, expr_ref_vector const& vars, expr_ref_vector& consequences) override {
        flush();
        return s->get_consequences(asms, vars, consequences);
    }

    lbool check_sat_cc(expr_ref_vector const& cube, vector<expr_ref_vector> const& clauses) override {
        flush();
        return s->check_sat_cc(cube, clauses);
    }

    lbool find_mutexes(expr_ref_vector const& vars, vector<expr_ref_vector>& mutexes) override {
        flush();
        return s->find_mutexes(vars, mutexes);
    }

    lbool preferred_sat(expr_ref_vector const& asms, vector<expr_ref_vector>& cores) override {
        flush();
        return s->preferred_sat(asms, cores);
    }
    
    expr_ref_vector cube(expr_ref_vector& vars, unsigned backtrack_level) override {
        flush();
        return s->cube(vars, backtrack_level); 
    }

    expr* congruence_root(expr* e) override { return s->congruence_root(e); }
    expr* congruence_next(expr* e) override { return s->congruence_next(e); }
    expr_ref congruence_explain(expr* a, expr* b) override { return s->congruence_explain(a, b); }
    std::ostream& display(std::ostream& out, unsigned n, expr* const* assumptions) const override {
        return s->display(out, n, assumptions);
    }
    void get_units_core(expr_ref_vector& units) override { s->get_units_core(units); }
    expr_ref_vector get_trail(unsigned max_level) override { return s->get_trail(max_level); }
    void get_levels(ptr_vector<expr> const& vars, unsigned_vector& depth) override { s->get_levels(vars, depth); }

    void register_on_clause(void* ctx, user_propagator::on_clause_eh_t& on_clause) override {
        s->register_on_clause(ctx, on_clause);
    }
    
    void user_propagate_init(
        void*                ctx, 
        user_propagator::push_eh_t&   push_eh,
        user_propagator::pop_eh_t&    pop_eh,
        user_propagator::fresh_eh_t&  fresh_eh) override {
        s->user_propagate_init(ctx, push_eh, pop_eh, fresh_eh);
    }        
    void user_propagate_register_fixed(user_propagator::fixed_eh_t& fixed_eh) override { s->user_propagate_register_fixed(fixed_eh); }    
    void user_propagate_register_final(user_propagator::final_eh_t& final_eh) override { s->user_propagate_register_final(final_eh); }
    void user_propagate_register_eq(user_propagator::eq_eh_t& eq_eh) override { s->user_propagate_register_eq(eq_eh); }    
    void user_propagate_register_diseq(user_propagator::eq_eh_t& diseq_eh) override { s->user_propagate_register_diseq(diseq_eh); }    
    void user_propagate_register_expr(expr* e) override { s->user_propagate_register_expr(e); }
    void user_propagate_register_created(user_propagator::created_eh_t& r) override { s->user_propagate_register_created(r); }
    void user_propagate_register_decide(user_propagator::decide_eh_t& r) override { s->user_propagate_register_decide(r); }
    void user_propagate_initialize_value(expr* var, expr* value) override { s->user_propagate_initialize_value(var, value); }    
};

solver * mk_slice_solver(solver * s) {
    solver_params sp(s->get_params());
    if (sp.slice())
        return alloc(slice_solver, s);
    else
        return s;
}

