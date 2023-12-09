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
#include "sat/smt/polysat/polysat_types.h"
#include "sat/smt/polysat/polysat_constraints.h"
#include "sat/smt/polysat/polysat_viable.h"
#include "sat/smt/polysat/polysat_assignment.h"

namespace polysat {

    class core;
    class solver_interface;

    class core {
        class mk_add_var;
        class mk_dqueue_var;
        class mk_assign_var;
        class mk_add_watch;
        typedef svector<std::pair<unsigned, unsigned>> activity;
        typedef std::tuple<unsigned, bool, dependency> prop_item;
        friend class viable;
        friend class constraints;
        friend class assignment;

        struct constraint_info {
            signed_constraint sc;
            dependency d;
        };
        solver_interface& s;
        viable m_viable;
        constraints m_constraints;
        assignment m_assignment;
        unsigned m_qhead = 0, m_vqhead = 0;
        svector<prop_item> m_prop_queue;
        svector<constraint_info> m_constraint_trail;  // index of constraints
        mutable scoped_ptr_vector<dd::pdd_manager> m_pdd;
        dependency_vector m_unsat_core;


        // attributes associated with variables
        vector<pdd>             m_vars;                       // for each variable a pdd
        vector<rational>        m_values;                     // current value of assigned variable
        svector<dependency>     m_justification;  // justification for assignment
        activity                m_activity;                  // activity of variables
        var_queue<activity>     m_var_queue;                 // priority queue of variables to assign
        vector<unsigned_vector> m_watch;                     // watch lists for variables for constraints on m_prop_queue where they occur

        // values to split on
        rational    m_value;
        pvar        m_var = 0;

        dd::pdd_manager& sz2pdd(unsigned sz) const;
        dd::pdd_manager& var2pdd(pvar v) const;

        void del_var();

        bool is_assigned(pvar v) { return !m_justification[v].is_null(); }
        void propagate_value(prop_item const& dc);
        void propagate_assignment(prop_item& dc);
        void propagate_assignment(pvar v, rational const& value, dependency dep);
        void propagate_unsat_core();

        void get_bitvector_prefixes(pvar v, pvar_vector& out);
        void get_fixed_bits(pvar v, svector<justified_fixed_bits>& fixed_bits);
        bool inconsistent() const;
        

        void add_watch(unsigned idx, unsigned var);

        signed_constraint get_constraint(unsigned idx, bool sign);

        lbool eval(signed_constraint const& sc);
        dependency_vector explain_eval(signed_constraint const& sc);

    public:
        core(solver_interface& s);

        sat::check_result check();        
        unsigned register_constraint(signed_constraint& sc, dependency d);
        bool propagate();
        void assign_eh(unsigned idx, bool sign, dependency const& d);

        pdd value(rational const& v, unsigned sz);
        pdd subst(pdd const&);

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
        unsigned size(pvar v) const { return var2pdd(v).power_of_2(); }

        constraints& cs() { return m_constraints; }
        trail_stack& trail();

        std::ostream& display(std::ostream& out) const { throw default_exception("nyi"); }
    };

}
