/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat conflict

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

Notes:

    A conflict state is of the form <Vars, Constraints>
    Where Vars are shorthand for the constraints v = value(v) for v in Vars and value(v) is the assignent.
    
    The conflict state is unsatisfiable under background clauses F.
    Dually, the negation is a consequence of F.

    Conflict resolution resolves an assignment in the search stack against the conflict state.

    Assignments are of the form:
  
    lit <- D => lit              - lit is propagated by the clause D => lit
    lit <- ?                     - lit is a decision literal.
    lit <- asserted              - lit is asserted
    lit <- Vars                  - lit is propagated from variable evaluation.

    v = value <- D               - v is assigned value by constraints D
    v = value <- ?               - v is a decision literal.

    - All literals should be assigned in the stack prior to their use.
    
    l <- D => l,       < Vars, { l } u C >   ===>   < Vars, C u D >
    l <- ?,            < Vars, { l } u C >   ===>   ~l <- (C & Vars = value(Vars) => ~l)
    l <- asserted,     < Vars, { l } u C >   ===>   < Vars, { l } u C >
    l <- Vars',        < Vars, { l } u C >   ===>   < Vars u Vars', C >          if all Vars' are propagated
    l <- Vars',        < Vars, { l } u C >   ===>   Mark < Vars, { l } u C > as bailout

    v = value <- D,  < Vars u { v }, C >     ===>   < Vars, D u C >
    v = value <- ?,  < Vars u { v }, C >     ===>   v != value <- (C & Vars = value(Vars) => v != value)
    
    
Example derivations:

Trail:       z <= y  <- asserted 
             xz > xy <- asserted 
             x = a   <- ? 
             y = b   <- ? 
             z = c   <- ?   
Conflict:    < {x, y, z}, xz > xy > when ~O(a,b) and c <= b
Append       x <= a <- { x }
Append       y <= b <- { y }
Conflict:    < {}, y >= z, xz > xy, x <= a, y <= b >
Based on:    z <= y & x <= a & y <= b => xz <= xy
Resolve:     y <= b <- { y }, y is a decision variable.
Bailout:     lemma ~(y >= z & xz > xy & x <= a & y <= b) at decision level of lemma

With overflow predicate:
Append       ~O(x, y) <- { x, y }                  
Conflict:    < {}, y >= z, xz > xy, ~O(x,y) >
Based on     z <= y & ~O(x,y) => xz <= xy
Resolve:     ~O(x, y) <- { x, y } both x, y are decision variables
Lemma:       y < z or xz <= xy or O(x,y)



 
    
--*/
#pragma once
#include "math/polysat/constraint.h"
#include "math/polysat/clause_builder.h"
#include <optional>

namespace polysat {

    class solver;
    class explainer;
    class inference_engine;
    class variable_elimination_engine;
    class conflict_iterator;
    class inference_logger;

    class inference {
    public:
        virtual ~inference() {}
        virtual std::ostream& display(std::ostream& out) const = 0;
    };

    inline std::ostream& operator<<(std::ostream& out, inference const& i) { return i.display(out); }

    class inference_named : public inference {
        char const* m_name;
    public:
        inference_named(char const* name) : m_name(name) { SASSERT(name); }
        std::ostream& display(std::ostream& out) const override { return out << m_name; }
    };

    enum class conflict_kind_t {
        ok,
        bailout_gave_up,
        bailout_lemma,
    };

    /** Conflict state, represented as core (~negation of clause). */
    class conflict {
        solver& s;
        indexed_uint_set m_literals;        // set of boolean literals in the conflict
        unsigned_vector m_var_occurrences;  // for each variable, the number of constraints in m_literals that contain it
        uint_set m_vars;                    // variable assignments used as premises
        uint_set m_bail_vars;

        // If this is not null_var, the conflict was due to empty viable set for this variable.
        // Can be treated like "v = x" for any value x.
        pvar m_conflict_var = null_var;

        /** Whether we are in a bailout state.
         * We enter a bailout state when we give up on proper conflict resolution,
         * or want to learn a lemma without fine-grained backtracking.
         */
        conflict_kind_t m_kind = conflict_kind_t::ok;

        friend class inference_logger;
        scoped_ptr<inference_logger> m_logger;

        bool_vector m_bvar2mark;                  // mark of Boolean variables

        void set_mark(signed_constraint c);
        void unset_mark(signed_constraint c);

        void minimize_vars(signed_constraint c);

        constraint_manager& cm() const;
        scoped_ptr_vector<explainer> ex_engines;
        scoped_ptr_vector<variable_elimination_engine> ve_engines;
        scoped_ptr_vector<inference_engine> inf_engines;

    public:
        conflict(solver& s);
        ~conflict();

        /// Begin next conflict
        void begin_conflict(char const* text);
        /// Log inference at the current state.
        void log_inference(inference const& inf);
        void log_inference(char const* name) { log_inference(inference_named(name)); }
        void log_var(pvar v);
        /// Log relevant part of search state and viable.
        void end_conflict();

        pvar conflict_var() const { return m_conflict_var; }

        bool is_bailout() const { return m_kind != conflict_kind_t::ok; }
        bool is_bailout_lemma() const { return m_kind == conflict_kind_t::bailout_lemma; }
        void set_bailout_gave_up();
        void set_bailout_lemma();

        bool empty() const;
        void reset();

        bool pvar_occurs_in_constraints(pvar v) const { return v < m_var_occurrences.size() && m_var_occurrences[v] > 0; }

        bool contains_pvar(pvar v) const { return m_vars.contains(v) || m_bail_vars.contains(v); }
        bool is_marked(signed_constraint c) const;
        bool is_marked(sat::bool_var b) const;

        /** conflict because the constraint c is false under current variable assignment */
        void set(signed_constraint c);
        /** conflict because there is no viable value for the variable v */
        void set(pvar v);
        /** all literals in clause are false */
        void set(clause const& cl);

        void propagate(signed_constraint c);
        void insert(signed_constraint c);
        void insert_vars(signed_constraint c);
        void insert(signed_constraint c, vector<signed_constraint> const& premises);
        void remove(signed_constraint c);
        void replace(signed_constraint c_old, signed_constraint c_new, vector<signed_constraint> const& c_new_premises);

        bool contains(signed_constraint c) const;
        bool contains(sat::literal lit) const;

        /** Perform boolean resolution with the clause upon variable 'var'.
         * Precondition: core/clause contain complementary 'var'-literals.
         */
        void resolve(sat::literal lit, clause const& cl);

        /** lit was fully evaluated under the assignment up to level 'lvl'.
         */
        void resolve_with_assignment(sat::literal lit, unsigned lvl);

        /** Perform value resolution by applying various inference rules.
         *  Returns true if it was possible to eliminate the variable 'v'.
         */
        bool resolve_value(pvar v);

        /** Convert the core into a lemma to be learned. */
        clause_builder build_lemma();

        bool try_eliminate(pvar v);
        bool try_saturate(pvar v);
        bool try_explain(pvar v);

        using const_iterator = conflict_iterator;
        const_iterator begin() const;
        const_iterator end() const;

        uint_set const& vars() const { return m_vars; }
        uint_set const& bail_vars() const { return m_bail_vars; }

        std::ostream& display(std::ostream& out) const;
    };

    inline std::ostream& operator<<(std::ostream& out, conflict const& c) { return c.display(out); }


    class conflict_iterator {
        friend class conflict;

        using inner_t = indexed_uint_set::iterator;

        constraint_manager* m_cm;
        inner_t m_inner;

        conflict_iterator(constraint_manager& cm, inner_t inner):
            m_cm(&cm), m_inner(inner) {}

        static conflict_iterator begin(constraint_manager& cm, indexed_uint_set const& lits) {
            return {cm, lits.begin()};
        }

        static conflict_iterator end(constraint_manager& cm, indexed_uint_set const& lits) {
            return {cm, lits.end()};
        }

    public:
        using value_type = signed_constraint;
        using difference_type = unsigned;
        using pointer = signed_constraint const*;
        using reference = signed_constraint const&;
        using iterator_category = std::input_iterator_tag;

        conflict_iterator& operator++() {
            ++m_inner;
            return *this;
        }

        signed_constraint operator*() const {
            return m_cm->lookup(sat::to_literal(*m_inner));
        }

        bool operator==(conflict_iterator const& other) const {
            return m_inner == other.m_inner;
        }

        bool operator!=(conflict_iterator const& other) const { return !operator==(other); }
    };


    inline conflict::const_iterator conflict::begin() const { return conflict_iterator::begin(cm(), m_literals); }
    inline conflict::const_iterator conflict::end() const { return conflict_iterator::end(cm(), m_literals); }
}
