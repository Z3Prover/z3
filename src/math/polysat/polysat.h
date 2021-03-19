/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat

Abstract:

    Polynomial solver for modular arithmetic.

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19

--*/
#pragma once

#include "util/dependency.h"
#include "util/trail.h"
#include "util/math/dd_pdd.h"
#include "util/math/dd_bdd.h"

namespace polysat {

    class poly {
        pdd      m_pdd;
        unsigned m_lidx { UINT_MAX };
    public:
        poly(pdd const& p): m_pdd(p) {}
        poly(pdd const& p, unsigned lidx): m_pdd(p), m_lidx(lidx) {}
    };

    enum ckind_t { eq_t, ule_t, sle_t };

    class constraint {
        ckind_t m_kind;
        poly    m_poly;
        poly    m_other;
        constraint(poly const& p, poly const& q, ckind_t k): m_kind(k), m_poly(p), m_other(q) {}
    public:
        static constraint eq(poly const& p) { return constraint(p, p, ckind_t::eq_t); }
        static constraint ule(poly const& p, poly const& q) { return constraint(p, q, ckind_t::ule_t); }
        ckind_t kind() const { return m_kind; }
        poly const &  p() const { return m_poly; }
        poly const &  lhs() const { return m_poly; }
        poly const &  rhs() const { return m_other; }
    };

    /**
     * linear term is has an offset and is linear addition of variables.
     */
    class linear : public vector<std::pair<unsigned, rational>> {
        rational m_offset;
    public:
        linear(rational const& offset): m_offset(offset) {}
        rational const& offset() const { return m_offset; }
    };

    /**
     * monomial is a list of variables and coefficient.
     */
    clas mono : public unsigned_vector {
        rational m_coeff;
    public:
        linear(rational const& coeff): m_coeff(coeff) {}
        rational const& coeff() const { return m_coeff; }
    };

    class solver {

        trail_stack&         m_trail;
        region&              m_region;
        dd::pdd_manager      m_pdd;
        dd::bdd_manager      m_bdd;
        u_dependency_manager m_dep_manager;

        /**
         * store of linear polynomials. The l_idx points to linear monomials.
         * could also just use pdds.
         */
        vector<linear>           m_linear; 

        // Per constraint state
        vector<u_dependency>     m_cdeps;   // each constraint has set of dependencies
        vector<constraint>       m_constraints

        // Per variable information
        vector<dd::bdd>          m_viable;   // set of viable values.
        vector<u_dependency>     m_vdeps;    // dependencies for viable values
        vector<vector<poly>>     m_pdeps;    // dependencies in polynomial form
        vector<rational>         m_value;    // assigned value
        bool_vector              m_assigned; // whether variable is assigned
        vector<unsigned_vector>  m_watch;    // watch list datastructure into constraints.
        

    public:

        /**
         * to share chronology we pass an external trail stack.
         * every update to the solver is going to be retractable
         * by pushing an undo action on the trail stack.
         */
        solver(trail_stack& s);
        ~solver() {}

        /**
         * Self-contained satisfiability checker.
         * Main mode is to have external solver drive state machine.
         */
        lbool check_sat();

        void push();
        void pop(unsigned n);
        
        /**
         * Add variable with bit-size. 
         */
        unsigned add_var(unsigned sz);

        /**
         * Create polynomial terms
         */
        poly var(unsigned v);
        poly mul(rational cons& r, poly const& p);
        poly num(rational const& r, unsigned sz);
        poly add(poly const& p, poly const& q);

        /**
         * deconstruct polynomials into sum of monomials.
         */
        vector<mono> poly2monos(poly const& p) const;        

        /**
         * Add polynomial constraints
         * Each constraint is tracked by a dependency.
         */
        void add_eq(poly const& p, unsigned dep);
        void add_diseq(poly const& p, unsigned dep);
        void add_ule(poly const& p, poly const& q, unsigned dep);
        void add_sle(poly const& p, poly const& q, unsigned dep);
        

        /**
         * main state transitions.
         */
        bool  can_propagate();
        lbool propagate();

        bool can_decide();
        void decide(rational & val, unsigned& var);
        void assign(unsigned var, rational const& val);
        
        bool is_confict();
        /**
         * Return number of scopes to backtrack and core in the shape of dependencies
         * TBD: External vs. internal mode may need different signatures.
         */
        unsigned resolve_conflict(unsigned_vector& deps);            
        
        bool can_learn();
        void learn(constraint& c, unsigned_vector& deps); 
        void learn(vector<constraint>& cs, unsigned_vector& deps); 


        std::ostream& display(std::ostream& out);



    };
}


