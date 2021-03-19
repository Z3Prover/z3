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
#include "util/lbool.h"
#include "util/var_queue.h"
#include "math/dd/dd_pdd.h"
#include "math/dd/dd_bdd.h"

namespace polysat {

    class solver;
    typedef dd::pdd pdd;
    typedef dd::bdd bdd;

    class poly {
        friend class solver;
        solver&  s;
        pdd      m_pdd;
    public:
        poly(solver& s, pdd const& p): s(s), m_pdd(p) {}
        poly(solver& s, rational const& r, unsigned sz);
        std::ostream& display(std::ostream& out) const;
        unsigned size() const { throw default_exception("nyi query pdd for size"); }
        
        poly operator*(rational const& r);
        poly operator+(poly const& other) { return poly(s, m_pdd + other.m_pdd); }
        poly operator*(poly const& other) { return poly(s, m_pdd * other.m_pdd); }
    };

    inline std::ostream& operator<<(std::ostream& out, poly const& p) { return p.display(out); }

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
        std::ostream& display(std::ostream& out) const;
    };

    inline std::ostream& operator<<(std::ostream& out, constraint const& c) { return c.display(out); }

    /**
     * linear term is has an offset and is linear addition of variables.
     */
    class linear : public vector<std::pair<unsigned, rational>> {
        rational m_offset;
    public:
        linear(rational const& offset): m_offset(offset) {}
        rational const& offset() const { return m_offset; }
        std::ostream& display(std::ostream& out) const;
    };

    inline std::ostream& operator<<(std::ostream& out, linear const& l) { return l.display(out); }

    /**
     * monomial is a list of variables and coefficient.
     */
    class mono : public unsigned_vector {
        rational m_coeff;
    public:
        mono(rational const& coeff): m_coeff(coeff) {}
        rational const& coeff() const { return m_coeff; }
        std::ostream& display(std::ostream& out) const;
    };

    inline std::ostream& operator<<(std::ostream& out, mono const& m) { return m.display(out); }

    /**
     * Justification kind for a variable assignment.
     */
    enum justification_k { unassigned, decision, propagation };

    class justification {
        justification_k m_kind;
        unsigned        m_idx;
        justification(justification_k k, unsigned constraint_idx): m_kind(k), m_idx(constraint_idx) {}
    public:
        justification(): m_kind(justification_k::unassigned), m_idx(0) {}
        static justification unassigned() { return justification(justification_k::unassigned, 0); }
        static justification decision() { return justification(justification_k::decision, 0); }
        static justification propagation(unsigned idx) { return justification(justification_k::propagation, idx); }
        justification_k kind() const { return m_kind; }
        unsigned constraint_index() const { return m_idx; }
        std::ostream& display(std::ostream& out) const;
    };

    inline std::ostream& operator<<(std::ostream& out, justification const& j) { return j.display(out); }

    class solver {
        friend class poly;

        trail_stack&             m_trail;
        region&                  m_region;
        dd::pdd_manager          m_pdd;
        dd::bdd_manager          m_bdd;
        u_dependency_manager     m_dep_manager;
        var_queue                m_free_vars;

        /**
         * store of linear polynomials. The l_idx points to linear monomials.
         * could also just use pdds.
         */
        vector<linear>           m_linear; 

        // Per constraint state
        ptr_vector<u_dependency> m_cdeps;   // each constraint has set of dependencies
        vector<constraint>       m_constraints;

        // Per variable information
        vector<bdd>              m_viable;   // set of viable values.
        ptr_vector<u_dependency> m_vdeps;    // dependencies for viable values
        vector<vector<poly>>     m_pdeps;    // dependencies in polynomial form
        vector<rational>         m_value;    // assigned value
        vector<justification>    m_justification; // justification for variable assignment
        vector<unsigned_vector>  m_watch;    // watch list datastructure into constraints.
        unsigned_vector          m_activity; 
        vector<pdd>              m_vars;

        // search state that lists assigned variables
        unsigned_vector          m_search;
        unsigned                 m_qhead { 0 };

        /**
         * retrieve bit-size associated with polynomial.
         */
        unsigned poly2size(poly const& p) const;

        /**
         * check if value is viable according to m_viable.
         */
        bool is_viable(unsigned var, rational const& val) const;

        /**
         * undo trail operations for backtracking.
         * Each struct is a subclass of trail and implements undo().
         */
        struct del_var;
        struct del_constraint;
        struct var_unassign;

        void do_del_var();
        void do_del_constraint();
        void do_var_unassign();

        /**
         * push / pop are used only in self-contained mode from check_sat.
         */
        void push() { m_trail.push_scope(); }
        void pop(unsigned n) { m_trail.pop_scope(n); }

    public:

        /**
         * to share chronology we pass an external trail stack.
         * every update to the solver is going to be retractable
         * by pushing an undo action on the trail stack.
         */
        solver(trail_stack& s);
        ~solver();

        /**
         * Self-contained satisfiability checker.
         * Main mode is to have external solver drive state machine.
         */
        lbool check_sat();
        
        /**
         * Add variable with bit-size. 
         */
        unsigned add_var(unsigned sz);

        /**
         * Create polynomial terms
         */
        poly var(unsigned v);

        /**
         * deconstruct polynomials into sum of monomials.
         */
        vector<mono> poly2monos(poly const& p) const;        

        /**
         * Add polynomial constraints
         * Each constraint is tracked by a dependency.
         * assign sets the 'index'th bit of var.
         */
        void add_eq(poly const& p, unsigned dep);
        void add_diseq(poly const& p, unsigned dep);
        void add_ule(poly const& p, poly const& q, unsigned dep);
        void add_sle(poly const& p, poly const& q, unsigned dep);
        void assign(unsigned var, unsigned index, bool value, unsigned dep);        

        /**
         * main state transitions.
         */
        bool  can_propagate();
        lbool propagate();

        bool can_decide();
        void decide(rational & val, unsigned& var);
        void assign(unsigned var, rational const& val);
        
        bool is_conflict();
        /**
         * Return number of scopes to backtrack and core in the shape of dependencies
         * TBD: External vs. internal mode may need different signatures.
         */
        unsigned resolve_conflict(unsigned_vector& deps);            
        
        bool can_learn();
        void learn(constraint& c, unsigned_vector& deps); 
        void learn(vector<constraint>& cs, unsigned_vector& deps); 

        std::ostream& display(std::ostream& out) const;

    };

    inline std::ostream& operator<<(std::ostream& out, solver const& s) { return s.display(out); }

}


