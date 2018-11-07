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
#include "sat_local_search.h"

namespace sat {

    class unit_walk {
        struct double2 {
            double t, f;
        };
        class var_priority {
            svector<bool_var> m_vars;
            unsigned_vector   m_lim;
            unsigned          m_head;
            unsigned          m_depth;
        public:
            var_priority() { m_depth = 0; m_head = 0; }
            void rewind() { m_head = 0; for (unsigned& l : m_lim) l = 0; }
            unsigned depth() const { return m_depth; }
            void inc_depth() { ++m_depth; }
            void dec_depth() { --m_depth; }
            void reset() { m_vars.reset(); m_lim.reset(); m_head = 0; m_depth = 0; }
            void add(bool_var v) { m_vars.push_back(v); }
            bool_var next(solver& s);
            bool_var peek(solver& s);
            void push() { m_lim.push_back(m_head); }
            void pop() { m_head = m_lim.back(); m_lim.pop_back(); }    
            bool_var const* begin() const { return m_vars.begin(); }
            bool_var const* end() const { return m_vars.end(); }
            bool_var* begin() { return m_vars.begin(); }
            bool_var* end() { return m_vars.end(); }
        };

        solver&           s;
        local_search      m_ls;
        random_gen        m_rand;
        svector<bool>     m_phase;
        svector<double2>  m_phase_tf;
        var_priority      m_priorities;

        // settings
        unsigned          m_max_conflicts;
        bool              m_sticky_phase;

        unsigned          m_propagations;
        unsigned          m_flips;
        unsigned          m_max_trail;
        unsigned          m_qhead;
        literal_vector    m_trail;
        bool              m_inconsistent;
        literal_vector    m_decisions;
        unsigned          m_conflict_offset;

        void pop();
        void init_runs();
        lbool update_priority();
        void init_phase();
        void init_propagation();
        void refresh_solver();
        void update_max_trail();
        void flip_phase(literal l); 
        void propagate();
        void propagate(literal lit);
        literal choose_literal();
        void set_conflict(literal l1, literal l2);
        void set_conflict(literal l1, literal l2, literal l3);
        void set_conflict(clause const& c);
        inline lbool value(literal lit) { return s.value(lit); }
        void log_status();
        var_priority& pqueue() { return m_priorities; }
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
