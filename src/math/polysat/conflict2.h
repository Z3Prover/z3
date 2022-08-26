/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat conflict

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

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
#include "math/polysat/inference_logger.h"
#include <optional>

namespace polysat {

    class solver;
    class explainer;
    class inference_engine;
    class variable_elimination_engine;
    class conflict_iterator;
    class inference_logger;

    class conflict2 {
        solver& s;
        scoped_ptr<inference_logger> m_logger;

        // current conflict core consists of m_literals and m_vars
        indexed_uint_set m_literals;        // set of boolean literals in the conflict
        uint_set m_vars;                    // variable assignments used as premises, shorthand for literals (x := v)

        unsigned_vector m_var_occurrences;  // for each variable, the number of constraints in m_literals that contain it

        // additional lemmas generated during conflict resolution
        vector<clause_ref> m_lemmas;

        // TODO:
        // conflict resolution plugins
        // - may generate lemma
        // - may force backjumping without further conflict resolution
        // - bailout lemma if no method applies (log these cases in particular because it indicates where we are missing something)

    public:
        conflict2(solver& s);

        inference_logger& logger();

        bool empty() const;
        void reset();

        /** conflict because the constraint c is false under current variable assignment */
        void init(signed_constraint c);
        /** conflict because there is no viable value for the variable v */
        void init(pvar v, bool by_viable_fallback = false);

        bool contains(signed_constraint c) const { SASSERT(c); return contains(c.blit()); }
        bool contains(sat::literal lit) const;

        /**
         * Insert constraint c into conflict state.
         *
         * Skips trivial constraints:
         *  - e.g., constant constraints such as "4 > 1"
         */
        void insert(signed_constraint c);

        /** Insert assigned variables of c */
        void insert_vars(signed_constraint c);

        /** Remove c from core */
        void remove(signed_constraint c);

        std::ostream& display(std::ostream& out) const;
    };

    inline std::ostream& operator<<(std::ostream& out, conflict2 const& c) { return c.display(out); }

}
