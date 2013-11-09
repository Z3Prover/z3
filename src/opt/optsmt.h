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
#ifndef _OPTSMT_H_
#define _OPTSMT_H_

#include "opt_solver.h"

namespace opt {
    /**
       Takes solver with hard constraints added.
       Returns an optimal assignment to objective functions.
    */

    class optsmt {
        ast_manager&     m;
        opt_solver*      s;
        volatile bool    m_cancel;
        vector<inf_eps>  m_lower;
        vector<inf_eps>  m_upper;
        app_ref_vector   m_objs;
        svector<bool>    m_is_max;
        svector<smt::theory_var> m_vars;
        symbol           m_engine;
    public:
        optsmt(ast_manager& m): m(m), s(0), m_cancel(false), m_objs(m) {}

        lbool operator()(opt_solver& s);

        void add(app* t, bool is_max);

        void set_cancel(bool f);

        void updt_params(params_ref& p);

        void display_assignment(std::ostream& out) const;
        void display_range_assignment(std::ostream& out) const;

        unsigned get_num_objectives() const { return m_vars.size(); }
        void commit_assignment(unsigned index);
        inf_eps get_value(unsigned index) const;
        inf_eps get_lower(unsigned index) const;
        inf_eps get_upper(unsigned index) const;
        
    private:
        
        std::ostream& display_objective(std::ostream& out, unsigned i) const;

        lbool basic_opt();

        lbool farkas_opt();

        void set_max(vector<inf_eps>& dst, vector<inf_eps> const& src);

        void update_lower();

        lbool update_upper();

    };

};

#endif
