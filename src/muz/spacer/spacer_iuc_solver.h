/**
Copyright (c) 2017 Arie Gurfinkel

Module Name:

    spacer_iuc_solver.h

Abstract:

   A solver that produces interpolated unsat cores

Author:

    Arie Gurfinkel

Notes:

--*/
#ifndef SPACER_IUC_SOLVER_H_
#define SPACER_IUC_SOLVER_H_

#include"solver/solver.h"
#include"ast/expr_substitution.h"
#include"util/stopwatch.h"
namespace spacer {
class iuc_solver : public solver {
private:
    struct def_manager {
        iuc_solver &        m_parent;
        expr_ref_vector     m_defs;
        obj_map<expr, app*> m_expr2proxy;
        obj_map<app, app*>  m_proxy2def;

        def_manager(iuc_solver &parent) :
            m_parent(parent), m_defs(m_parent.m)
        {}

        bool is_proxy(app *k, app_ref &v);
        app* mk_proxy(expr *v);
        void reset();
        bool is_proxy_def(expr *v);

    };

    friend struct def_manager;
    ast_manager&        m;
    solver&             m_solver;
    app_ref_vector      m_proxies;
    unsigned            m_num_proxies;
    vector<def_manager> m_defs;
    def_manager         m_base_defs;
    expr_ref_vector     m_assumptions;
    unsigned            m_first_assumption;
    bool                m_is_proxied;

    stopwatch m_iuc_sw;
    stopwatch m_hyp_reduce1_sw;
    stopwatch m_hyp_reduce2_sw;
    stopwatch m_learn_core_sw;

    expr_substitution m_elim_proxies_sub;
    bool m_split_literals;
    unsigned m_iuc;
    unsigned m_iuc_arith;
    bool m_print_farkas_stats;
    bool m_old_hyp_reducer;
    bool is_proxy(expr *e, app_ref &def);
    void undo_proxies_in_core(expr_ref_vector &v);
    app* mk_proxy(expr *v);
    app* fresh_proxy();
    void elim_proxies(expr_ref_vector &v);
public:
    iuc_solver(solver &solver, unsigned iuc, unsigned iuc_arith,
               bool print_farkas_stats, bool old_hyp_reducer,
               bool split_literals = false) :
        m(solver.get_manager()),
        m_solver(solver),
        m_proxies(m),
        m_num_proxies(0),
        m_base_defs(*this),
        m_assumptions(m),
        m_first_assumption(0),
        m_is_proxied(false),
        m_elim_proxies_sub(m, false, true),
        m_split_literals(split_literals),
        m_iuc(iuc),
        m_iuc_arith(iuc_arith),
        m_print_farkas_stats(print_farkas_stats),
        m_old_hyp_reducer(old_hyp_reducer)
    {}

    ~iuc_solver() override {}

    /* iuc solver specific */
    virtual void get_iuc(expr_ref_vector &core);
    void set_split_literals(bool v) { m_split_literals = v; }
    bool mk_proxies(expr_ref_vector &v, unsigned from = 0);
    void undo_proxies(expr_ref_vector &v);

    void push_bg(expr *e);
    void pop_bg(unsigned n);
    unsigned get_num_bg();

    void get_full_unsat_core(ptr_vector<expr> &core) {
        expr_ref_vector _core(m);
        m_solver.get_unsat_core(_core);
        core.append(_core.size(), _core.c_ptr());
    }

    /* solver interface */

    solver* translate(ast_manager &m, params_ref const &p) override  {
        return m_solver.translate(m, p);
    }
    void updt_params(params_ref const &p) override   { m_solver.updt_params(p); }
    void reset_params(params_ref const &p) override  { m_solver.reset_params(p); }
    const params_ref &get_params() const override { return m_solver.get_params(); }
    void push_params() override { m_solver.push_params(); }
    void pop_params() override { m_solver.pop_params(); }
    void collect_param_descrs(param_descrs &r) override  { m_solver.collect_param_descrs(r); }
    void set_produce_models(bool f) override  { m_solver.set_produce_models(f); }
    void assert_expr_core(expr *t) override  { m_solver.assert_expr(t); }
    void assert_expr_core2(expr *t, expr *a) override   { NOT_IMPLEMENTED_YET(); }
    expr_ref_vector cube(expr_ref_vector&, unsigned) override { return expr_ref_vector(m); }

    void push() override;
    void pop(unsigned n) override;
    unsigned get_scope_level() const override { return m_solver.get_scope_level(); }

    lbool check_sat(unsigned num_assumptions, expr * const *assumptions) override;
    lbool check_sat_cc(const expr_ref_vector &cube, vector<expr_ref_vector> const & clauses) override;
    void set_progress_callback(progress_callback *callback) override {
        m_solver.set_progress_callback(callback);
    }
    unsigned get_num_assertions() const override { return m_solver.get_num_assertions(); }
    expr * get_assertion(unsigned idx) const override { return m_solver.get_assertion(idx); }
    unsigned get_num_assumptions() const override { return m_solver.get_num_assumptions(); }
    expr * get_assumption(unsigned idx) const override { return m_solver.get_assumption(idx); }
    std::ostream &display(std::ostream &out, unsigned n, expr* const* es) const override {
        return m_solver.display(out, n, es);
    }

    /* check_sat_result interface */

    void collect_statistics(statistics &st) const override ;
    virtual void reset_statistics();

    void get_unsat_core(expr_ref_vector &r) override;
    void get_model_core(model_ref &m) override {m_solver.get_model(m);}
    proof *get_proof() override {return m_solver.get_proof();}
    std::string reason_unknown() const override { return m_solver.reason_unknown(); }
    void set_reason_unknown(char const* msg) override { m_solver.set_reason_unknown(msg); }
    void get_labels(svector<symbol> &r) override { m_solver.get_labels(r); }
    ast_manager& get_manager() const override { return m; }

    virtual void refresh();

    class scoped_mk_proxy {
        iuc_solver &m_s;
        expr_ref_vector &m_v;
    public:
        scoped_mk_proxy(iuc_solver &s, expr_ref_vector &v) : m_s(s), m_v(v) {
            m_s.mk_proxies(m_v);
        }
        ~scoped_mk_proxy() { m_s.undo_proxies(m_v); }
    };

    class scoped_bg {
        iuc_solver &m_s;
        unsigned m_bg_sz;
    public:
        scoped_bg(iuc_solver &s) : m_s(s), m_bg_sz(m_s.get_num_bg()) {}
        ~scoped_bg() {
            if (m_s.get_num_bg() > m_bg_sz) {
                m_s.pop_bg(m_s.get_num_bg() - m_bg_sz);
            }
        }
    };
};
}
#endif
