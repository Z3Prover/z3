/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_clause.h

Abstract:

    Clauses

Author:

    Leonardo de Moura (leonardo) 2011-05-21.

Revision History:

--*/
#ifndef _SAT_CLAUSE_H_
#define _SAT_CLAUSE_H_

#include"sat_types.h"
#include"small_object_allocator.h"
#include"id_gen.h"

#ifdef _MSC_VER
#pragma warning(disable : 4200)
#pragma warning(disable : 4355)
#endif

namespace sat {

    class clause_allocator;

    class clause {
        friend class clause_allocator;
        friend class tmp_clause;
        unsigned           m_id;
        unsigned           m_size;
        unsigned           m_capacity;
        var_approx_set     m_approx;
        unsigned           m_strengthened:1;
        unsigned           m_removed:1;
        unsigned           m_learned:1;
        unsigned           m_used:1;
        unsigned           m_frozen:1;
        unsigned           m_reinit_stack:1;
        unsigned           m_inact_rounds:8;
        unsigned           m_glue:8; 
        unsigned           m_psm:8;  // transient field used during gc
        literal            m_lits[0];

        static size_t get_obj_size(unsigned num_lits) { return sizeof(clause) + num_lits * sizeof(literal); }
        size_t get_size() const { return get_obj_size(m_capacity); }
        clause(unsigned id, unsigned sz, literal const * lits, bool learned);
    public:
        unsigned id() const { return m_id; }
        unsigned size() const { return m_size; }
        literal & operator[](unsigned idx) { SASSERT(idx < m_size); return m_lits[idx]; }
        literal const & operator[](unsigned idx) const { SASSERT(idx < m_size); return m_lits[idx]; }
        bool is_learned() const { return m_learned; }
        void unset_learned() { SASSERT(is_learned()); m_learned = false; }
        void shrink(unsigned num_lits) { SASSERT(num_lits <= m_size); if (num_lits < m_size) { m_size = num_lits; mark_strengthened(); } }
        bool strengthened() const { return m_strengthened; }
        void mark_strengthened() { m_strengthened = true; update_approx(); }
        void unmark_strengthened() { m_strengthened = false; }
        void elim(literal l);
        bool was_removed() const { return m_removed; }
        void set_removed(bool f) { m_removed = f; }
        var_approx_set approx() const { return m_approx; }
        void update_approx();
        bool check_approx() const; // for debugging
        literal * begin() { return m_lits; }
        literal * end() { return m_lits + m_size; }
        bool contains(literal l) const;
        bool contains(bool_var v) const;
        bool satisfied_by(model const & m) const;
        void mark_used() { m_used = true; }
        void unmark_used() { m_used = false; }
        bool was_used() const { return m_used; }
        void inc_inact_rounds() { m_inact_rounds++; }
        void reset_inact_rounds() { m_inact_rounds = 0; }
        unsigned inact_rounds() const { return m_inact_rounds; }
        bool frozen() const { return m_frozen; }
        void freeze() { SASSERT(is_learned()); SASSERT(!frozen()); m_frozen = true; }
        void unfreeze() { SASSERT(is_learned()); SASSERT(frozen()); m_frozen = false; }
        static var_approx_set approx(unsigned num, literal const * lits);
        void set_glue(unsigned glue) { m_glue = glue > 255 ? 255 : glue; }
        unsigned glue() const { return m_glue; }
        void set_psm(unsigned psm) { m_psm = psm > 255 ? 255 : psm; }
        unsigned psm() const { return m_psm; }

        bool on_reinit_stack() const { return m_reinit_stack; }
        void set_reinit_stack(bool f) { m_reinit_stack = f; }
    };

    std::ostream & operator<<(std::ostream & out, clause const & c);
    std::ostream & operator<<(std::ostream & out, clause_vector const & cs);

    class bin_clause {
        unsigned m_val1;
        unsigned m_val2;
    public:
        bin_clause(literal l1, literal l2, bool learned):m_val1(l1.to_uint()), m_val2((l2.to_uint() << 1) + static_cast<unsigned>(learned)) {}
        literal get_literal1() const { return to_literal(m_val1); }
        literal get_literal2() const { return to_literal(m_val2 >> 1); }
        bool is_learned() const { return (m_val2 & 1) == 1; }
    };

    class tmp_clause {
        clause * m_clause;
    public:
        tmp_clause():m_clause(0) {}
        ~tmp_clause() { if (m_clause) dealloc_svect(m_clause); }
        clause * get() const { return m_clause; }
        void set(unsigned num_lits, literal const * lits, bool learned);
        void set(literal l1, literal l2, bool learned) { literal ls[2] = { l1, l2 }; set(2, ls, learned); }
        void set(bin_clause const & c) { set(c.get_literal1(), c.get_literal2(), c.is_learned()); }
    };

    /**
       \brief Simple clause allocator that allows uint (32bit integers) to be used to reference clauses (even in 64bit machines).
    */
    class clause_allocator {
        small_object_allocator m_allocator;
        id_gen                 m_id_gen;
#ifdef _AMD64_
        unsigned get_segment(size_t ptr);
        static const unsigned  c_cls_alignment = 3; 
        static const unsigned  c_max_segments  = 1 << c_cls_alignment;
        static const size_t    c_aligment_mask = (1ull << c_cls_alignment) - 1ull;
        unsigned               m_num_segments;
        size_t                 m_segments[c_max_segments];
#endif
    public:
        clause_allocator();
        clause *      get_clause(clause_offset cls_off) const;
        clause_offset get_offset(clause const * ptr) const;
        clause *      mk_clause(unsigned num_lits, literal const * lits, bool learned);
        void          del_clause(clause * cls);
    };

    /**
       \brief Wrapper for clauses & binary clauses.
       I do not create clause objects for binary clauses.
       clause_ref wraps a clause object or a pair of literals (i.e., a binary clause). 
    */
    class clause_wrapper {
        union {
            clause * m_cls;
            unsigned m_l1_idx;
        };
        unsigned m_l2_idx;
    public:
        clause_wrapper(literal l1, literal l2):m_l1_idx(l1.to_uint()), m_l2_idx(l2.to_uint()) {}
        clause_wrapper(clause & c):m_cls(&c), m_l2_idx(null_literal.to_uint()) {}

        bool is_binary() const { return m_l2_idx != null_literal.to_uint(); }
        unsigned size() const { return is_binary() ? 2 : m_cls->size(); }
        literal operator[](unsigned idx) const { 
            SASSERT(idx < size());
            if (is_binary())
                return idx == 0 ? to_literal(m_l1_idx) : to_literal(m_l2_idx);
            else
                return m_cls->operator[](idx);
        }

        bool contains(literal l) const;
        bool contains(bool_var v) const;
        clause * get_clause() const { SASSERT(!is_binary()); return m_cls; }
    };

    typedef svector<clause_wrapper> clause_wrapper_vector;

    std::ostream & operator<<(std::ostream & out, clause_wrapper const & c);

};

#endif
