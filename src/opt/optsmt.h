/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    optsmt.h

Abstract:
   
    Objective optimization method.

Author:

    Anh-Dung Phan (t-anphan) 2013-10-16

Notes:

--*/
#pragma once

#include "opt/opt_solver.h"

namespace opt {
    /**
       Takes solver with hard constraints added.
       Returns an optimal assignment to objective functions.
    */

    class context;

    class optsmt {
        ast_manager&     m;
        context&         m_context;
        opt_solver*      m_s;
        vector<objective_value> m_lower;
        vector<objective_value> m_upper;
        app_ref_vector   m_objs;
        expr_ref_vector  m_lower_fmls;
        svector<smt::theory_var> m_vars;
        symbol           m_optsmt_engine;
        unsigned         m_bisect_rounds = 64;
        bool             m_optsmt_nlsat = true;
        unsigned         m_nlsat_supremum_rlimit = 100000;
        model_ref        m_model, m_best_model;
        svector<symbol>  m_labels;
        sref_vector<model> m_models;
    public:
        optsmt(ast_manager& m, context& ctx): 
            m(m), m_context(ctx), m_s(nullptr), m_objs(m), m_lower_fmls(m) {}

        void setup(opt_solver& solver);

        lbool box();

        lbool lex(unsigned obj_index, bool is_maximize);

        bool is_unbounded(unsigned obj_index, bool is_maximize);

        unsigned add(app* t);

        void updt_params(params_ref& p);

        unsigned get_num_objectives() const { return m_objs.size(); }
        void commit_assignment(unsigned index);
        objective_value get_lower(unsigned index) const;
        objective_value get_upper(unsigned index) const;
        // A finite, unattained limit certified by the nlsat-cell engine.
        bool    has_open_bound(unsigned index) const {
            return m_lower[index].exact_finite() && m_lower[index].has_infinitesimal();
        }
        void    get_model(model_ref& mdl, svector<symbol>& labels);
        model*  get_model(unsigned index) const { return m_models[index]; }


        void update_lower(unsigned idx, inf_eps const& r);

        void update_upper(unsigned idx, inf_eps const& r);

        void reset();

        lbool basic_opt();
        
        bool can_increment_delta(vector<inf_eps> const& lower, unsigned i);

    private:

        inf_eps const& lower(unsigned index) const { return m_lower[index].rational_bound(); }
        inf_eps const& upper(unsigned index) const { return m_upper[index].rational_bound(); }

        lbool geometric_opt();

        lbool symba_opt();

        lbool geometric_search(unsigned idx, bool is_maximize);

        lbool bisect(unsigned idx, bool is_maximize, inf_eps hi);
        lbool nlsat_cells(unsigned idx, bool is_maximize, inf_eps const& hi);
        bool prove_unbounded_above(unsigned idx, unsigned rlimit_budget);

        void set_best(unsigned idx, inf_eps const& v, bool is_maximize);

        void set_max(vector<objective_value>& dst, vector<inf_eps> const& src, expr_ref_vector& fmls);

        expr_ref update_lower();

        void update_lower_lex(unsigned idx, inf_eps const& r, bool is_maximize);

        lbool update_upper();

    };

}
