/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    polysat boolean variables

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-6

--*/
#pragma once
#include "math/polysat/types.h"

namespace polysat {

    typedef unsigned bool_var;
    bool_var const null_bool_var = UINT_MAX;


    // 0 ...  x
    // 1 ... ~x
    // 2 ...  y
    // 3 ... ~y
    // :
    // :
    // UINT_MAX-1 ... (invalid)
    // UINT_MAX   ... (invalid; used to represent invalid/missing literals)
    class bool_lit {
        unsigned m_index;

        bool_lit(): m_index(UINT_MAX) {}
        explicit bool_lit(unsigned idx): m_index(idx) { SASSERT(is_valid()); }
        bool_lit(bool_var var, bool is_positive): bool_lit(2*var + !is_positive) {}

    public:
        static bool_lit from_index(unsigned idx) { return bool_lit(idx); }
        static bool_lit from_var(bool_var var, bool is_positive) { return bool_lit(var, is_positive); }
        static bool_lit positive(bool_var var) { return bool_lit(var, true); }
        static bool_lit negative(bool_var var) { return bool_lit(var, false); }
        static bool_lit invalid() { return bool_lit(); }

        bool is_valid() const { return m_index < (UINT_MAX - 1); }

        unsigned index() const { SASSERT(is_valid()); return m_index; }
        bool_var var() const { SASSERT(is_valid()); return m_index / 2; }

        bool is_positive() const { return (m_index & 0x1) == 0; }
        bool is_negative() const { return !is_positive(); }

        bool_lit operator~() const { return bool_lit(m_index ^ 0x1); }
    };

    std::ostream& operator<<(std::ostream& out, bool_lit const& lit);


/* NOTE: currently unused
    class bool_clause {
        unsigned m_level;
        svector<bool_lit> m_literals;

        // TODO: optimization for later
        // unsigned m_num_literals;
        // bool_lit m_literals[0];

        // static size_t object_size(unsigned m_num_literals) {
        //     return sizeof(bool_clause) + m_num_literals * sizeof(bool_lit);
        // }

    public:
        unsigned num_literals() const { return m_literals.size(); }
        bool_lit* literals() const { return m_literals.data(); }
        bool_lit operator[](unsigned i) const { SASSERT(i < num_literals()); return literals()[i]; }

        unsigned level() const { return m_level; }
    };
*/

    class clause;

    class bool_var_manager {
        svector<bool_var>   m_unused;  // previously deleted variables that can be reused by new_var();
        svector<lbool>      m_value;   // current value (indexed by literal)
        svector<unsigned>   m_level;   // level of assignment (indexed by variable)
        svector<clause*>    m_reason;  // propagation reason, NULL for decisions (indexed by variable)

        // For enumerative backtracking we store the lemma we're handling with a certain decision
        svector<clause*>    m_lemma;

        unsigned_vector     m_marks;
        unsigned            m_clock { 0 };

        // allocated size (not the number of active variables)
        unsigned size() const { return m_level.size(); }

    public:
        bool_var new_var();
        void del_var(bool_var var);

        void reset_marks();
        bool is_marked(bool_var var) const { return m_clock == m_marks[var]; }
        void set_mark(bool_var var) { m_marks[var] = m_clock; }

        bool is_assigned(bool_var var) const { return value(var) != l_undef; }
        bool is_assigned(bool_lit lit) const { return value(lit) != l_undef; }
        bool is_decision(bool_var var) const { return is_assigned(var) && !reason(var); }
        // bool is_decision(bool_lit lit) const { return is_decision(lit.var()); }
        bool is_propagation(bool_var var) const { return is_assigned(var) && reason(var); }
        lbool value(bool_var var) const { return value(bool_lit::positive(var)); }
        lbool value(bool_lit lit) const { return m_value[lit.index()]; }
        unsigned level(bool_var var) const { SASSERT(is_assigned(var)); return m_level[var]; }
        // unsigned level(bool_lit lit) const { return level(lit.var()); }
        clause* reason(bool_var var) const { SASSERT(is_assigned(var)); return m_reason[var]; }

        clause* lemma(bool_var var) const { SASSERT(is_decision(var)); return m_lemma[var]; }

        /// Set the given literal to true
        void assign(bool_lit lit, unsigned lvl, clause* reason);
    };

}
