/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    nlsat_clause.h

Abstract:

    Clauses used in the Nonlinear arithmetic satisfiability procedure. 

Author:

    Leonardo de Moura (leonardo) 2012-01-02.

Revision History:

--*/
#pragma once

#include "nlsat/nlsat_types.h"
#include "util/vector.h"

namespace nlsat {

    class clause {
        friend class solver;
        unsigned         m_id;
        unsigned         m_size;
        unsigned         m_capacity:31;
        unsigned         m_learned:1;
        unsigned         m_active:1;
        unsigned         m_removed:1;
        unsigned         m_marked:1;
        unsigned         m_var_hash;
        assumption_set   m_assumptions;
        literal          m_lits[0];
        static size_t get_obj_size(unsigned num_lits) { return sizeof(clause) + num_lits * sizeof(literal); }
        size_t get_size() const { return get_obj_size(m_capacity); }
        clause(unsigned id, unsigned sz, literal const * lits, bool learned, assumption_set as);
    public:
        unsigned size() const { return m_size; }
        unsigned id() const { return m_id; }
        literal & operator[](unsigned idx) { SASSERT(idx < m_size); return m_lits[idx]; }
        literal const & operator[](unsigned idx) const { SASSERT(idx < m_size); return m_lits[idx]; }
        bool is_learned() const { return m_learned; }
        literal * begin() { return m_lits; }
        literal * end() { return m_lits + m_size; }
        literal const * begin() const { return m_lits; }
        literal const * end() const { return m_lits + m_size; }
        literal const * data() const { return m_lits; }
        void set_active(bool b) { m_active = b; }
        bool is_active() const { return m_active; }
        void set_removed() { m_removed = true; }
        bool is_removed() const { return m_removed; }
        unsigned var_hash() const { return m_var_hash; }
        void set_var_hash(unsigned h) { m_var_hash = h; }
        bool is_marked() const { return m_marked; }
        void mark() { m_marked = true; }
        void unmark() { m_marked = false; }
        bool contains(literal l) const;
        bool contains(bool_var v) const;
        void shrink(unsigned num_lits) { SASSERT(num_lits <= m_size); if (num_lits < m_size) { m_size = num_lits; } }
        assumption_set assumptions() const { return m_assumptions; }
    };

    typedef ptr_vector<clause> clause_vector;

};

