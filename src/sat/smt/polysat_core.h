/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    polysat_core.h

Abstract:

    Core solver for polysat

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-30
    Jakob Rath 2021-04-06

--*/
#pragma once

#include "util/dependency.h"
#include "math/dd/dd_pdd.h"
#include "sat/smt/sat_th.h"
#include "sat/smt/polysat_types.h"
#include "sat/smt/polysat_constraints.h"
#include "sat/smt/polysat_viable.h"
#include "sat/smt/polysat_assignment.h"

namespace polysat {

    class core;
    class solver;

    class core {
        class mk_add_var;
        class mk_dqueue_var;
        class mk_assign_var;
        class mk_add_watch;
        typedef svector<std::pair<unsigned, unsigned>> activity;
        friend class viable;
        friend class constraints;
        friend class assignment;

        solver& s;
        viable m_viable;
        constraints m_constraints;
        assignment m_assignment;
        unsigned m_qhead = 0, m_vqhead = 0;
        svector<dependent_constraint> m_prop_queue;
        stacked_dependency_manager<dependency>     m_dep;
        mutable scoped_ptr_vector<dd::pdd_manager> m_pdd;
        dependency_vector m_unsat_core;


        // attributes associated with variables
        vector<pdd>            m_vars;                       // for each variable a pdd
        vector<rational>       m_values;                     // current value of assigned variable
        ptr_vector<stacked_dependency>     m_justification;  // justification for assignment
        activity                m_activity;                  // activity of variables
        var_queue<activity>     m_var_queue;                 // priority queue of variables to assign
        vector<unsigned_vector> m_watch;                     // watch lists for variables for constraints on m_prop_queue where they occur

        // values to split on
        rational    m_value;
        pvar        m_var = 0;

        dd::pdd_manager& sz2pdd(unsigned sz) const;
        dd::pdd_manager& var2pdd(pvar v) const;
        unsigned size(pvar v) const { return var2pdd(v).power_of_2(); }
        void del_var();

        bool is_assigned(pvar v) { return nullptr != m_justification[v]; }
        void propagate_constraint(unsigned idx, dependent_constraint& dc);
        void propagate_value(unsigned idx, dependent_constraint const& dc);
        void propagate_assignment(pvar v, rational const& value, stacked_dependency* dep);
        bool propagate_unsat_core();

        void add_watch(unsigned idx, signed_constraint& sc);
        void add_watch(unsigned idx, unsigned var);

        lbool eval(signed_constraint sc) { throw default_exception("nyi"); }
        dependency_vector explain_eval(dependent_constraint const& dc) { throw default_exception("nyi"); }

    public:
        core(solver& s);

        sat::check_result check();

        bool propagate();
        void assign_eh(signed_constraint const& sc, dependency const& dep);

        expr_ref constraint2expr(signed_constraint const& sc) const { throw default_exception("nyi"); }

        pdd value(rational const& v, unsigned sz);

        signed_constraint eq(pdd const& p) { return m_constraints.eq(p); }
        signed_constraint eq(pdd const& p, pdd const& q) { return m_constraints.eq(p - q); }
        signed_constraint ule(pdd const& p, pdd const& q) { return m_constraints.ule(p, q); }
        signed_constraint sle(pdd const& p, pdd const& q) { return m_constraints.sle(p, q); }
        signed_constraint umul_ovfl(pdd const& p, pdd const& q) { return m_constraints.umul_ovfl(p, q); }
        signed_constraint smul_ovfl(pdd const& p, pdd const& q) { return m_constraints.smul_ovfl(p, q); }
        signed_constraint smul_udfl(pdd const& p, pdd const& q) { return m_constraints.smul_udfl(p, q); }
        signed_constraint bit(pdd const& p, unsigned i) { return m_constraints.bit(p, i); }


        pdd lshr(pdd a, pdd b) { throw default_exception("nyi"); }
        pdd ashr(pdd a, pdd b) { throw default_exception("nyi"); }
        pdd shl(pdd a, pdd b) { throw default_exception("nyi"); }
        pdd band(pdd a, pdd b) { throw default_exception("nyi"); }
        pdd bxor(pdd a, pdd b) { throw default_exception("nyi"); }
        pdd bor(pdd a, pdd b) { throw default_exception("nyi"); }
        pdd bnand(pdd a, pdd b) { throw default_exception("nyi"); }
        pdd bxnor(pdd a, pdd b) { throw default_exception("nyi"); }
        pdd bnor(pdd a, pdd b) { throw default_exception("nyi"); }
        pdd bnot(pdd a) { throw default_exception("nyi"); }
        std::pair<pdd, pdd> quot_rem(pdd const& n, pdd const& d) { throw default_exception("nyi"); }
        pdd zero_ext(pdd a, unsigned sz) { throw default_exception("nyi"); }
        pdd sign_ext(pdd a, unsigned sz) { throw default_exception("nyi"); }
        pdd extract(pdd src, unsigned hi, unsigned lo) { throw default_exception("nyi"); }
        pdd concat(unsigned n, pdd const* args) { throw default_exception("nyi"); }
        pvar add_var(unsigned sz);
        pdd var(pvar p) { return m_vars[p]; }

        std::ostream& display(std::ostream& out) const { throw default_exception("nyi"); }
    };

}
