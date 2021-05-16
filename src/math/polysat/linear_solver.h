/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    linear_solver.h

Abstract:

    Fixed-precision unsigned integer linear solver

    This wraps around fixplex and translates polynomials
    into linear form.
    Equalities, Inequalities are converted into rows and slack variables.
    Slack variables are bounded when constraints are activated.
    It also handles backtracking state: bounds that are activated inside one 
    scope are de-activated when exiting the scope.
    
Author:

    Nikolaj Bjorner (nbjorner) 2021-05-14
    Jakob Rath 2021-05-14

--*/

#pragma once

#include "math/polysat/fixplex.h"
#include "math/polysat/constraint.h"
#include "math/polysat/eq_constraint.h"
#include "math/polysat/ule_constraint.h"

namespace polysat {

    class solver;

    class linear_solver {
        enum trail_i {
            inc_level_i,
            add_var_i,
            set_bound_i,
            add_row_i
        };

        solver&                  s;
        scoped_ptr_vector<fixplex_base> m_fix;
        svector<trail_i>         m_trail;
        svector<std::pair<var_t, unsigned>> m_rows; 
        unsigned_vector          m_var2ext;
        unsigned_vector          m_ext2var;

        svector<var_t>           m_vars;
        vector<rational>         m_coeffs;
        svector<std::pair<var_t, var_t>>           m_bool_var2row;
        unsigned_vector          m_sz2num_vars;

        fixplex_base& sz2fixplex(unsigned sz);

        void linearize(pdd const& p);
        var_t fresh_var(unsigned sz);


        var_t internalize_pdd(pdd const& p);
        void new_eq(eq_constraint& eq);
        void new_le(ule_constraint& le);
        void new_bit(var_constraint& vc);
        void assert_eq(eq_constraint& eq);
        void assert_le(ule_constraint& le);
        void assert_bit(var_constraint& vc);

        // bind monomial to variable.
        var_t mono2var(unsigned sz, unsigned_vector const& m);
        var_t pvar2var(unsigned sz, pvar v);
        unsigned_vector var2mono(unsigned sz, var_t v) { throw default_exception("nyi"); }
        //
        // TBD trail object for 
        // removing variables
        // undoing variable bounds bounds
        // removing rows from fixplex
        //
    public:
        linear_solver(solver& s):
            s(s) 
        {}

        void push();
        void pop(unsigned n); 
        void new_constraint(constraint& c);
        void set_value(pvar v, rational const& value);
        void set_bound(pvar v, rational const& lo, rational const& hi);
        void activate_constraint(constraint& c);

        // check integer modular feasibility under current bounds.
        lbool check();
        void unsat_core(unsigned_vector& deps);

        // current value assigned to (linear) variable according to tableau.
        rational value(pvar v);

        std::ostream& display(std::ostream& out) const { return out; }
        void collect_statistics(::statistics & st) const {}

    };



};

