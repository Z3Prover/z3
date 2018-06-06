/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    sat_unit_walk.h

Abstract:

    unit walk local search procedure.

Author:

    Nikolaj Bjorner (nbjorner) 2017-12-15.

Revision History:

--*/
#ifndef SAT_UNIT_WALK_H_
#define SAT_UNIT_WALK_H_

#include "sat/sat_solver.h"

namespace sat {

    class unit_walk {
        struct double2 {
            double t, f;
        };
        solver&           s;
        random_gen        m_rand;
        svector<bool>     m_phase;
        svector<double2> m_phase_tf;
        indexed_uint_set  m_freevars;
        unsigned          m_runs;
        unsigned          m_periods;

        // settings
        unsigned          m_max_runs;
        unsigned          m_max_periods;
        unsigned          m_max_conflicts;
        bool              m_sticky_phase;

        unsigned          m_propagations;
        unsigned          m_flips;
        unsigned          m_max_trail;
        unsigned          m_qhead;
        literal_vector    m_trail;
        bool              m_inconsistent;
        literal_vector    m_decisions;
        unsigned          m_conflicts;

        void push();
        void backtrack();
        void init_runs();
        void init_phase();
        void init_propagation();
        void flip_phase(literal l); 
        lbool unit_propagation();
        void propagate();
        void propagate(literal lit);
        literal choose_literal();
        void set_conflict(literal l1, literal l2);
        void set_conflict(literal l1, literal l2, literal l3);
        void set_conflict(clause const& c);
        inline lbool value(literal lit) { return s.value(lit); }
        void log_status();
    public:

        unit_walk(solver& s);
        lbool operator()();
        std::ostream& display(std::ostream& out) const;
        bool inconsistent() const { return m_inconsistent; }
        void set_conflict();
        void assign(literal lit);
    };
};

#endif
