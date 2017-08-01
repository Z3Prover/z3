/**
Copyright (c) 2017 Arie Gurfinkel

Module Name:

    spacer_itp_solver.h

Abstract:

   A solver that produces interpolated unsat cores

Author:

    Arie Gurfinkel

Notes:

--*/
#ifndef SPACER_ITP_SOLVER_H_
#define SPACER_ITP_SOLVER_H_

#include"solver/solver.h"
#include"ast/expr_substitution.h"
#include"util/stopwatch.h"
namespace spacer {
class itp_solver : public solver {
private:
    struct def_manager {
        itp_solver &m_parent;
        obj_map<expr, app*> m_expr2proxy;
        obj_map<app, app*> m_proxy2def;

        expr_ref_vector m_defs;

        def_manager(itp_solver &parent) :
            m_parent(parent), m_defs(m_parent.m)
        {}

        bool is_proxy(app *k, app_ref &v);
        app* mk_proxy(expr *v);
        void reset();
        bool is_proxy_def(expr *v);

    };

    friend struct def_manager;
    ast_manager &m;
    solver &m_solver;
    app_ref_vector m_proxies;
    unsigned m_num_proxies;
    vector<def_manager> m_defs;
    def_manager m_base_defs;
    expr_ref_vector m_assumptions;
    unsigned m_first_assumption;
    bool m_is_proxied;

    stopwatch m_itp_watch;

    expr_substitution m_elim_proxies_sub;
    bool m_split_literals;
    bool m_new_unsat_core;
    bool m_minimize_unsat_core;
    bool m_farkas_optimized;
    bool m_farkas_a_const;

    bool is_proxy(expr *e, app_ref &def);
    void undo_proxies_in_core(ptr_vector<expr> &v);
    app* mk_proxy(expr *v);
    app* fresh_proxy();
    void elim_proxies(expr_ref_vector &v);
public:
    itp_solver(solver &solver, bool new_unsat_core, bool minimize_unsat_core, bool farkas_optimized, bool farkas_a_const, bool split_literals = false) :
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
        m_new_unsat_core(new_unsat_core),
        m_minimize_unsat_core(minimize_unsat_core),
        m_farkas_optimized(farkas_optimized),
        m_farkas_a_const(farkas_a_const)
    {}

    virtual ~itp_solver() {}

    /* itp solver specific */
    virtual void get_unsat_core(expr_ref_vector &core);
    virtual void get_itp_core(expr_ref_vector &core);
    void set_split_literals(bool v) {m_split_literals = v;}
    bool mk_proxies(expr_ref_vector &v, unsigned from = 0);
    void undo_proxies(expr_ref_vector &v);

    void push_bg(expr *e);
    void pop_bg(unsigned n);
    unsigned get_num_bg();

    void get_full_unsat_core(ptr_vector<expr> &core)
    {m_solver.get_unsat_core(core);}

    /* solver interface */

    virtual solver* translate(ast_manager &m, params_ref const &p)
    {return m_solver.translate(m, p);}
    virtual void updt_params(params_ref const &p)
    {m_solver.updt_params(p);}
    virtual void collect_param_descrs(param_descrs &r)
    {m_solver.collect_param_descrs(r);}
    virtual void set_produce_models(bool f)
    {m_solver.set_produce_models(f);}
    virtual void assert_expr(expr *t)
    {m_solver.assert_expr(t);}

    virtual void assert_expr(expr *t, expr *a)
    {NOT_IMPLEMENTED_YET();}

    virtual void push();
    virtual void pop(unsigned n);
    virtual unsigned get_scope_level() const
    {return m_solver.get_scope_level();}

    virtual lbool check_sat(unsigned num_assumptions, expr * const *assumptions);
    virtual void set_progress_callback(progress_callback *callback)
    {m_solver.set_progress_callback(callback);}
    virtual unsigned get_num_assertions() const
    {return m_solver.get_num_assertions();}
    virtual expr * get_assertion(unsigned idx) const
    {return m_solver.get_assertion(idx);}
    virtual unsigned get_num_assumptions() const
    {return m_solver.get_num_assumptions();}
    virtual expr * get_assumption(unsigned idx) const
    {return m_solver.get_assumption(idx);}
    virtual std::ostream &display(std::ostream &out) const
    {m_solver.display(out); return out;}

    /* check_sat_result interface */

    virtual void collect_statistics(statistics &st) const ;
    virtual void reset_statistics();
    virtual void get_unsat_core(ptr_vector<expr> &r);
    virtual void get_model(model_ref &m) {m_solver.get_model(m);}
    virtual proof *get_proof() {return m_solver.get_proof();}
    virtual std::string reason_unknown() const
    {return m_solver.reason_unknown();}
    virtual void set_reason_unknown(char const* msg)
    {m_solver.set_reason_unknown(msg);}
    virtual void get_labels(svector<symbol> &r)
    {m_solver.get_labels(r);}
    virtual ast_manager &get_manager() const {return m;}

    virtual void refresh();

    class scoped_mk_proxy {
        itp_solver &m_s;
        expr_ref_vector &m_v;
    public:
        scoped_mk_proxy(itp_solver &s, expr_ref_vector &v) : m_s(s), m_v(v)
        {m_s.mk_proxies(m_v);}
        ~scoped_mk_proxy()
        {m_s.undo_proxies(m_v);}
    };

    class scoped_bg {
        itp_solver &m_s;
        unsigned m_bg_sz;
    public:
        scoped_bg(itp_solver &s) : m_s(s), m_bg_sz(m_s.get_num_bg()) {}
        ~scoped_bg()
        {if(m_s.get_num_bg() > m_bg_sz) { m_s.pop_bg(m_s.get_num_bg() - m_bg_sz); }}
    };
};
}
#endif
