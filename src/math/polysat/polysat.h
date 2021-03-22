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
#include "util/scoped_ptr_vector.h"
#include "util/var_queue.h"
#include "math/dd/dd_pdd.h"
#include "math/dd/dd_bdd.h"

namespace polysat {

    class solver;
    typedef dd::pdd pdd;
    typedef dd::bdd bdd;

    enum ckind_t { eq_t, ule_t, sle_t };

    class constraint {
        ckind_t m_kind;
        pdd    m_poly;
        pdd    m_other;
        u_dependency* m_dep;
        unsigned_vector m_vars;
        constraint(pdd const& p, pdd const& q, u_dependency* dep, ckind_t k): 
            m_kind(k), m_poly(p), m_other(q), m_dep(dep) {
            m_vars.append(p.free_vars());
            if (q != p) 
                for (auto v : q.free_vars())
                    m_vars.insert(v);                
        }
    public:
        static constraint* eq(pdd const& p, u_dependency* d) { return alloc(constraint, p, p, d, ckind_t::eq_t); }
        static constraint* ule(pdd const& p, pdd const& q, u_dependency* d) { return alloc(constraint, p, q, d, ckind_t::ule_t); }
        ckind_t kind() const { return m_kind; }
        pdd const &  p() const { return m_poly; }
        pdd const &  lhs() const { return m_poly; }
        pdd const &  rhs() const { return m_other; }
        std::ostream& display(std::ostream& out) const;
        u_dependency* dep() const { return m_dep; }
        unsigned_vector& vars() { return m_vars; }
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
        unsigned        m_level;
        justification(justification_k k, unsigned lvl): m_kind(k), m_level(lvl) {}
    public:
        justification(): m_kind(justification_k::unassigned) {}
        static justification unassigned() { return justification(justification_k::unassigned, 0); }
        static justification decision(unsigned lvl) { return justification(justification_k::decision, lvl); }
        static justification propagation(unsigned lvl) { return justification(justification_k::propagation, lvl); }
        bool is_decision() const { return m_kind == justification_k::decision; }
        bool is_unassigned() const { return m_kind == justification_k::unassigned; }
        bool is_propagation() const { return m_kind == justification_k::propagation; }
        justification_k kind() const { return m_kind; }
        unsigned level() const { return m_level; }
        std::ostream& display(std::ostream& out) const;
    };

    inline std::ostream& operator<<(std::ostream& out, justification const& j) { return j.display(out); }

    class solver {

        typedef ptr_vector<constraint> constraints;

        trail_stack&             m_trail;
        scoped_ptr_vector<dd::pdd_manager> m_pdd;
        dd::bdd_manager          m_bdd;
        u_dependency_manager     m_dep_manager;
        var_queue                m_free_vars;

        // Per constraint state
        scoped_ptr_vector<constraint>   m_constraints;
        // TODO: vector<constraint> m_redundant; // learned constraints

        // Per variable information
        vector<bdd>              m_viable;   // set of viable values.
        ptr_vector<u_dependency> m_vdeps;    // dependencies for viable values
        vector<rational>         m_value;    // assigned value
        vector<justification>    m_justification; // justification for variable assignment
        vector<constraints>      m_cjust;    // constraints used for justification
        vector<constraints>      m_watch;    // watch list datastructure into constraints.
        unsigned_vector          m_activity; 
        vector<pdd>              m_vars;
        unsigned_vector          m_size;     // store size of variables.

        // search state that lists assigned variables
        unsigned_vector          m_search;
        unsigned                 m_qhead { 0 };
        unsigned                 m_level { 0 };

        // conflict state
        constraint* m_conflict { nullptr };

        unsigned size(unsigned var) const { return m_size[var]; }
        /**
         * check if value is viable according to m_viable.
         */
        bool is_viable(unsigned var, rational const& val);

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

        dd::pdd_manager& sz2pdd(unsigned sz);

        void inc_level();

        void assign_core(unsigned var, rational const& val, justification const& j);

        bool is_assigned(unsigned var) const { return !m_justification[var].is_unassigned(); }

        void propagate(unsigned v);
        bool propagate(unsigned v, constraint& c);
        bool propagate_eq(unsigned v, constraint& c);
        void propagate(unsigned var, rational const& val, justification const& j);
        void erase_watch(unsigned v, constraint& c);

        void set_conflict(constraint& c) { m_conflict = &c; }
        void clear_conflict() { m_conflict = nullptr; }

        unsigned_vector m_marks;
        unsigned        m_clock { 0 };
        void reset_marks();
        bool is_marked(unsigned v) const { return m_clock == m_marks[v]; }
        void set_mark(unsigned v) { m_marks[v] = m_clock; }

        pdd isolate(unsigned v);
        pdd resolve(unsigned v, pdd const& p, pdd const& q);

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
        pdd var(unsigned v) { return m_vars[v]; }


        /**
         * Add polynomial constraints
         * Each constraint is tracked by a dependency.
         * assign sets the 'index'th bit of var.
         */
        void add_eq(pdd const& p, unsigned dep);
        void add_diseq(pdd const& p, unsigned dep);
        void add_ule(pdd const& p, pdd const& q, unsigned dep);
        void add_sle(pdd const& p, pdd const& q, unsigned dep);
        void assign(unsigned var, unsigned index, bool value, unsigned dep);        

        /**
         * main state transitions.
         */
        bool can_propagate();
        void propagate();

        bool can_decide() const { return !m_free_vars.empty(); }
        void decide(rational & val, unsigned& var);

        bool is_conflict() const { return nullptr != m_conflict; }
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


