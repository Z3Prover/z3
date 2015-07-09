/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_watched.h

Abstract:

    Element of the SAT solver watchlist.

Author:

    Leonardo de Moura (leonardo) 2011-05-21.

Revision History:

--*/
#ifndef SAT_WATCHED_H_
#define SAT_WATCHED_H_

#include"sat_types.h"
#include"vector.h"

namespace sat {
    /**
       A watched element can be:
       
       1) A literal:               for watched binary clauses
       2) A pair of literals:      for watched ternary clauses
       3) A pair (literal, clause-offset): for watched clauses, where the first element of the pair is a literal of the clause.
       4) A external constraint-idx: for external constraints.

       For binary clauses: we use a bit to store whether the binary clause was learned or not.
       
       Remark: there is not Clause object for binary clauses.
    */
    class watched {
    public:
        enum kind {
            BINARY = 0, TERNARY, CLAUSE, EXT_CONSTRAINT
        };
    private:
        unsigned m_val1;
        unsigned m_val2; 
    public:
        watched(literal l, bool learned):
            m_val1(l.to_uint()),
            m_val2(static_cast<unsigned>(BINARY) + (static_cast<unsigned>(learned) << 2)) {
            SASSERT(is_binary_clause());
            SASSERT(get_literal() == l);
            SASSERT(is_learned() == learned);
            SASSERT(learned || is_binary_non_learned_clause());
        }

        watched(literal l1, literal l2) {
            SASSERT(l1 != l2);
            if (l1.index() > l2.index())
                std::swap(l1, l2);
            m_val1 = l1.to_uint();
            m_val2 = static_cast<unsigned>(TERNARY) + (l2.to_uint() << 2);
            SASSERT(is_ternary_clause());
            SASSERT(get_literal1() == l1);
            SASSERT(get_literal2() == l2);
        }

        watched(literal blocked_lit, clause_offset cls_off):
            m_val1(cls_off), 
            m_val2(static_cast<unsigned>(CLAUSE) + (blocked_lit.to_uint() << 2)) {
            SASSERT(is_clause());
            SASSERT(get_blocked_literal() == blocked_lit);
            SASSERT(get_clause_offset() == cls_off);
        }

        watched(ext_constraint_idx cnstr_idx):
            m_val1(cnstr_idx),
            m_val2(static_cast<unsigned>(EXT_CONSTRAINT)) {
            SASSERT(is_ext_constraint());
            SASSERT(get_ext_constraint_idx() == cnstr_idx);
        }

        kind get_kind() const { return static_cast<kind>(m_val2 & 3); }
       
        bool is_binary_clause() const { return get_kind() == BINARY; }
        literal get_literal() const { SASSERT(is_binary_clause()); return to_literal(m_val1); }
        void set_literal(literal l) { SASSERT(is_binary_clause()); m_val1 = l.to_uint(); }
        bool is_learned() const { SASSERT(is_binary_clause()); return (m_val2 >> 2) == 1; }
        bool is_binary_non_learned_clause() const { return m_val2 == 0; }
        void mark_not_learned() { SASSERT(is_learned()); m_val2 = static_cast<unsigned>(BINARY); SASSERT(!is_learned()); }
        
        bool is_ternary_clause() const { return get_kind() == TERNARY; }
        literal get_literal1() const { SASSERT(is_ternary_clause()); return to_literal(m_val1); }
        literal get_literal2() const { SASSERT(is_ternary_clause()); return to_literal(m_val2 >> 2); }

        bool is_clause() const { return get_kind() == CLAUSE; }
        clause_offset get_clause_offset() const { SASSERT(is_clause()); return m_val1; }
        literal get_blocked_literal() const { SASSERT(is_clause()); return to_literal(m_val2 >> 2); }
        void set_clause_offset(clause_offset c) { SASSERT(is_clause()); m_val1 = c; }
        void set_blocked_literal(literal l) { SASSERT(is_clause()); m_val2 = static_cast<unsigned>(CLAUSE) + (l.to_uint() << 2); }
        void set_clause(literal blocked_lit, clause_offset cls_off) {
            m_val1 = cls_off;
            m_val2 = static_cast<unsigned>(CLAUSE) + (blocked_lit.to_uint() << 2);
        }

        bool is_ext_constraint() const { return get_kind() == EXT_CONSTRAINT; }
        ext_constraint_idx get_ext_constraint_idx() const { SASSERT(is_ext_constraint()); return m_val2; }
        
        bool operator==(watched const & w) const { return m_val1 == w.m_val1 && m_val2 == w.m_val2; }
        bool operator!=(watched const & w) const { return !operator==(w); }
    };

    COMPILE_TIME_ASSERT(0 <= watched::BINARY && watched::BINARY <= 3);
    COMPILE_TIME_ASSERT(0 <= watched::TERNARY && watched::TERNARY <= 3);
    COMPILE_TIME_ASSERT(0 <= watched::CLAUSE && watched::CLAUSE <= 3);
    COMPILE_TIME_ASSERT(0 <= watched::EXT_CONSTRAINT && watched::EXT_CONSTRAINT <= 3);

    struct watched_lt {
        bool operator()(watched const & w1, watched const & w2) const {
            if (w2.is_binary_clause()) return false;
            if (w1.is_binary_clause()) return true;
            if (w2.is_ternary_clause()) return false;
            if (w1.is_ternary_clause()) return true;
            return false;
        }
    };

    typedef vector<watched> watch_list;

    bool erase_clause_watch(watch_list & wlist, clause_offset c);
    inline void erase_ternary_watch(watch_list & wlist, literal l1, literal l2) { wlist.erase(watched(l1, l2)); }

    class clause_allocator;
    void display(std::ostream & out, clause_allocator const & ca, watch_list const & wlist);
};

#endif
