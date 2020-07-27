/**
Copyright (c) 2017 Arie Gurfinkel

Module Name:

    spacer_prop_solver.h

Abstract:

    SAT solver abstraction for SPACER.

Author:

    Arie Gurfinkel

Revision History:

--*/

#pragma once

#include <map>
#include <string>
#include <utility>

#include "ast/ast.h"
#include "util/obj_hashtable.h"
#include "smt/smt_kernel.h"
#include "util/util.h"
#include "util/vector.h"
#include "solver/solver.h"
#include "muz/spacer/spacer_iuc_solver.h"
#include "muz/spacer/spacer_util.h"

struct fp_params;

namespace spacer {
typedef ptr_vector<func_decl> decl_vector;

class prop_solver {

private:
    ast_manager&        m;
    symbol              m_name;
    ref<solver>         m_solvers[2];
    scoped_ptr<iuc_solver>  m_contexts[2];
    iuc_solver *            m_ctx;
    decl_vector         m_level_preds;
    app_ref_vector      m_pos_level_atoms;  // atoms used to identify level
    app_ref_vector      m_neg_level_atoms;  //
    obj_hashtable<expr> m_level_atoms_set;
    expr_ref_vector*    m_core;
    model_ref*          m_model;
    bool                m_subset_based_core;
    unsigned            m_uses_level;
    /// if true sets the solver into a delta level, enabling only
    /// atoms explicitly asserted in m_current_level
    bool                m_delta_level;
    bool                m_in_level;
    bool                m_use_push_bg;
    unsigned            m_current_level;    // set when m_in_level

    random_gen          m_random;

    void assert_level_atoms(unsigned level);

    void ensure_level(unsigned lvl);

    lbool internal_check_assumptions(expr_ref_vector &hard,
                                     expr_ref_vector &soft,
                                     vector<expr_ref_vector> const & clause);

    lbool maxsmt(expr_ref_vector &hard, expr_ref_vector &soft,
                 vector<expr_ref_vector> const & clauses);
    lbool mss(expr_ref_vector &hard, expr_ref_vector &soft);


public:
    prop_solver(ast_manager &m, solver *solver0, solver* solver1,
                fp_params const& p, symbol const& name);


    void set_core(expr_ref_vector* core) { m_core = core; }
    void set_model(model_ref* mdl) { m_model = mdl; }
    void set_subset_based_core(bool f) { m_subset_based_core = f; }
    bool assumes_level() const { return !is_infty_level(m_uses_level); }
    unsigned uses_level() const {return m_uses_level;}


    void add_level();
    unsigned level_cnt() const;


    void assert_expr(expr * form);
    void assert_expr(expr * form, unsigned level);

    void assert_exprs(const expr_ref_vector &fmls) {
        for (auto *f : fmls) assert_expr(f);
    }
    void assert_exprs(const expr_ref_vector &fmls, unsigned level) {
        for (auto *f : fmls) assert_expr(f, level);
    }

    /**
     * check assumptions with a background formula
     */
    lbool check_assumptions(const expr_ref_vector & hard,
                            expr_ref_vector & soft,
                            const expr_ref_vector &clause,
                            unsigned num_bg = 0,
                            expr * const *bg = nullptr,
                            unsigned solver_id = 0);

    void collect_statistics(statistics& st) const;
    void reset_statistics();

    class scoped_level {
        bool& m_lev;
    public:
        scoped_level(prop_solver& ps, unsigned lvl): m_lev(ps.m_in_level)
        {
            SASSERT(!m_lev);
            m_lev = true;
            ps.m_current_level = lvl;
        }
        ~scoped_level() { m_lev = false; }
    };

    class scoped_subset_core {
        prop_solver &m_ps;
        bool m_subset_based_core;

    public:
        scoped_subset_core(prop_solver &ps, bool subset_core) :
            m_ps(ps), m_subset_based_core(ps.m_subset_based_core)
        {m_ps.set_subset_based_core(subset_core);}

        ~scoped_subset_core()
        {m_ps.set_subset_based_core(m_subset_based_core);}
    };

    class scoped_delta_level : public scoped_level {
        bool &m_delta;
    public:
        scoped_delta_level(prop_solver &ps, unsigned lvl) :
            scoped_level(ps, lvl), m_delta(ps.m_delta_level) {m_delta = true;}
        ~scoped_delta_level() {m_delta = false;}
    };

    class scoped_weakness {
    public:
        solver *sol;
        scoped_weakness(prop_solver &ps, unsigned solver_id, unsigned weakness)
            : sol(nullptr) {
            sol = ps.m_solvers[solver_id == 0 ? 0 :  0 /* 1 */].get();
            if (!sol) return;
            sol->push_params();

            params_ref p;
            p.set_bool("arith.ignore_int", weakness < 1);
            p.set_bool("array.weak",  weakness < 2);
            sol->updt_params(p);
        }
        ~scoped_weakness() {if (sol) {sol->pop_params();}}
    };
};
}


