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
#ifndef OPTSMT_H_
#define OPTSMT_H_

#include "opt_solver.h"

namespace opt {
    /**
       Takes solver with hard constraints added.
       Returns an optimal assignment to objective functions.
    */

    class optsmt {
        ast_manager&     m;
        opt_solver*      m_s;
        vector<inf_eps>  m_lower;
        vector<inf_eps>  m_upper;
        app_ref_vector   m_objs;
        expr_ref_vector  m_lower_fmls;
        svector<smt::theory_var> m_vars;
        symbol           m_optsmt_engine;
        model_ref        m_model;
        svector<symbol>  m_labels;
        sref_vector<model> m_models;
    public:
        optsmt(ast_manager& m): 
            m(m), m_s(0), m_objs(m), m_lower_fmls(m) {}

        void setup(opt_solver& solver);

        lbool box();

        lbool lex(unsigned obj_index, bool is_maximize);

        unsigned add(app* t);

        void updt_params(params_ref& p);

        unsigned get_num_objectives() const { return m_objs.size(); }
        void commit_assignment(unsigned index);
        inf_eps get_lower(unsigned index) const;
        inf_eps get_upper(unsigned index) const;
        bool objective_is_model_valid(unsigned index) const;
        void    get_model(model_ref& mdl, svector<symbol>& labels);
        model*  get_model(unsigned index) const { return m_models[index]; }


        void update_lower(unsigned idx, inf_eps const& r);

        void update_upper(unsigned idx, inf_eps const& r);

        void reset();
        
    private:

        bool get_max_delta(vector<inf_eps> const& lower, unsigned& idx);
        
        lbool basic_opt();

        lbool geometric_opt();

        lbool symba_opt();

        lbool basic_lex(unsigned idx, bool is_maximize);

        lbool geometric_lex(unsigned idx, bool is_maximize);

        lbool farkas_opt();

        void set_max(vector<inf_eps>& dst, vector<inf_eps> const& src, expr_ref_vector& fmls);

        expr_ref update_lower();

        void update_lower_lex(unsigned idx, inf_eps const& r, bool is_maximize);


        lbool update_upper();


    };

};

#endif
