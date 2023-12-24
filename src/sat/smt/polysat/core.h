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

#include "util/var_queue.h"
#include "util/dependency.h"
#include "math/dd/dd_pdd.h"
#include "sat/sat_extension.h"
#include "sat/smt/polysat/types.h"
#include "sat/smt/polysat/constraints.h"
#include "sat/smt/polysat/viable.h"
#include "sat/smt/polysat/assignment.h"

namespace polysat {

    class core;
    class solver_interface;



    class core {
        class mk_add_var;
        class mk_dqueue_var;
        class mk_assign_var;
        class mk_add_watch;
        typedef svector<std::pair<unsigned, unsigned>> activity;
        friend class viable;
        friend class constraints;
        friend class assignment;

        struct constraint_info {
            signed_constraint sc;        // signed constraint representation
            dependency d;                // justification for constraint
            lbool      value;            // value assigned by solver
        };
        solver_interface& s;
        mutable scoped_ptr_vector<dd::pdd_manager> m_pdd;
        viable m_viable;
        constraints m_constraints;
        assignment m_assignment;
        unsigned m_qhead = 0;
        constraint_id_vector m_prop_queue;
        svector<constraint_info> m_constraint_index;  // index of constraints
        constraint_id_vector m_unsat_core;
        random_gen           m_rand;


        // attributes associated with variables
        vector<pdd>             m_vars;                       // for each variable a pdd
        vector<rational>        m_values;                     // current value of assigned variable
        constraint_id_vector    m_justification;              // justification for assignment
        activity                m_activity;                   // activity of variables
        var_queue<activity>     m_var_queue;                  // priority queue of variables to assign
        vector<unsigned_vector> m_watch;                      // watch lists for variables for constraints on m_prop_queue where they occur

        // values to split on
        rational    m_value;
        pvar        m_var = 0;

        dd::pdd_manager& sz2pdd(unsigned sz) const;
        dd::pdd_manager& var2pdd(pvar v) const;

        void del_var();

        bool is_assigned(pvar v) { return !m_justification[v].is_null(); }
        void propagate_assignment(constraint_id idx);
        void propagate_eval(constraint_id idx);
        void propagate_assignment(pvar v, rational const& value, constraint_id dep);
        void propagate_unsat_core();
        void propagate(constraint_id id, signed_constraint& sc, lbool value, dependency const& d);




        void add_watch(unsigned idx, unsigned var);



        sat::check_result final_check();
        svector<pvar> find_conflict_variables(constraint_id idx);

        void add_axiom(signed_constraint sc);

    public:
        core(solver_interface& s);

        sat::check_result check();        
        constraint_id register_constraint(signed_constraint& sc, dependency d);
        bool propagate();
        void assign_eh(constraint_id idx, bool sign, unsigned level);
        pvar next_var() { return m_var_queue.next_var(); }

        pdd value(rational const& v, unsigned sz);
        pdd subst(pdd const&);
        bool try_eval(pdd const& p, rational& r);

        void collect_statistics(statistics& st) const;

        signed_constraint eq(pdd const& p) { return m_constraints.eq(p); }
        signed_constraint eq(pdd const& p, pdd const& q) { return m_constraints.eq(p - q); }
        signed_constraint ule(pdd const& p, pdd const& q) { return m_constraints.ule(p, q); }
        signed_constraint sle(pdd const& p, pdd const& q) { return m_constraints.sle(p, q); }
        signed_constraint umul_ovfl(pdd const& p, pdd const& q) { return m_constraints.umul_ovfl(p, q); }
        signed_constraint smul_ovfl(pdd const& p, pdd const& q) { return m_constraints.smul_ovfl(p, q); }
        signed_constraint smul_udfl(pdd const& p, pdd const& q) { return m_constraints.smul_udfl(p, q); }
        signed_constraint bit(pdd const& p, unsigned i) { return m_constraints.bit(p, i); }


        void lshr(pdd const& a, pdd const& b, pdd const& r) { add_axiom(m_constraints.lshr(a, b, r)); }
        void ashr(pdd const& a, pdd const& b, pdd const& r) { add_axiom(m_constraints.ashr(a, b, r)); }
        void shl(pdd const& a, pdd const& b, pdd const& r) { add_axiom(m_constraints.shl(a, b, r)); }
        void band(pdd const& a, pdd const& b, pdd const& r) { add_axiom(m_constraints.band(a, b, r)); }

        pdd bnot(pdd p) { return -p - 1; }


        /*
        * Add a named clause. Dependencies are assumed, signed constraints are guaranteeed.
        * In other words, the clause represents the formula /\ d_i -> \/ sc_j
        * Where d_i are logical interpretations of dependencies and sc_j are signed constraints.
        */
        void add_axiom(char const* name, constraint_or_dependency_list const& cs, bool is_redundant);
        void add_axiom(char const* name, constraint_or_dependency const* begin, constraint_or_dependency const* end, bool is_redundant);
        
        pvar add_var(unsigned sz);
        pdd var(pvar p) { return m_vars[p]; }
        unsigned size(pvar v) const { return m_vars[v].power_of_2(); }

        constraints& cs() { return m_constraints; }
        trail_stack& trail();

        std::ostream& display(std::ostream& out) const;

        /*
        * Viable 
        */
        void get_bitvector_suffixes(pvar v, offset_slices& out);
        void get_fixed_bits(pvar v, fixed_bits_vector& fixed_bits);
        void get_subslices(pvar v, offset_slices& out);

        /*
        * Saturation
        */
        signed_constraint get_constraint(constraint_id id);
        constraint_id_vector const& unsat_core() const { return m_unsat_core; }
        constraint_id_vector const& assigned_constraints() const { return m_prop_queue; }
        dependency get_dependency(constraint_id idx) const;
        dependency_vector get_dependencies(constraint_id_vector const& ids) const;
        lbool eval(constraint_id id);
        dependency propagate(signed_constraint const& sc, constraint_id_vector const& ids) { return s.propagate(sc, ids); }
        lbool eval(signed_constraint const& sc);
        constraint_id_vector explain_eval(signed_constraint const& sc);
        bool inconsistent() const;

        /*
        * Constraints
        */
        assignment& get_assignment() { return m_assignment; }
    };

}
