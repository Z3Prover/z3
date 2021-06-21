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

#include "util/hashtable.h"
#include "util/small_object_allocator.h"
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
            add_mono_i,
            set_bound_i,
            add_ineq_i,
            add_row_i
        };

        struct mono_info {
            unsigned  sz { 0 };
            unsigned  num_vars { 0 }; 
            unsigned* vars { nullptr };
            unsigned  var { 0 };            
            mono_info(unsigned sz, unsigned num_vars, unsigned* vars):
                sz(sz),
                num_vars(num_vars),
                vars(vars)
            {}
            mono_info() {}
            struct hash {
                unsigned operator()(mono_info const& i) const {
                    // TODO
                    return 0;
                }
            };
            struct eq {
                 bool operator()(mono_info const& a, mono_info const& b) const {
                     if (a.num_vars != b.num_vars)
                         return false;
                     for (unsigned i = 0; i < a.num_vars; ++i)
                         if (a.vars[i] != b.vars[i])
                             return false;
                     return a.sz == b.sz;
                }
            };
        };

        solver&                  s;
        scoped_ptr_vector<fixplex_base> m_fix;
        svector<trail_i>         m_trail;
        svector<std::pair<var_t, unsigned>> m_rows; 
        unsigned_vector          m_var2ext;
        unsigned_vector          m_ext2var;

        svector<var_t>           m_vars;
        vector<rational>         m_coeffs;
        svector<std::pair<var_t, var_t>> m_bool_var2row;

        hashtable<mono_info, mono_info::hash, mono_info::eq> m_mono2var;
        unsigned_vector          m_sz2num_vars;
        small_object_allocator   m_alloc;
        svector<mono_info>       m_monomials;

        fixplex_base& sz2fixplex(unsigned sz);

        void linearize(pdd const& p);
        var_t fresh_var(unsigned sz);


        var_t internalize_pdd(pdd const& p);
        void new_eq(eq_constraint& eq);
        void new_le(ule_constraint& le);
        void assert_eq(eq_constraint& eq);
        void assert_le(ule_constraint& le);

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
            s(s),
            m_alloc("mononials")
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

