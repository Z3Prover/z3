/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    dl_hassel_diff_table.h

Abstract:

    <abstract>

Revision History:

--*/

#ifndef _DL_HASSEL_DIFF_TABLE_H_
#define _DL_HASSEL_DIFF_TABLE_H_

#include "dl_hassel_common.h"

namespace datalog {

    class hassel_diff_table;

    class ternary_diff_bitvector {
        // pos \ (neg0 \/ ... \/ negn)
        ternary_bitvector m_pos;
        union_ternary_bitvector<ternary_bitvector> m_neg;

    public:
        ternary_diff_bitvector() : m_pos(), m_neg(0) {}
        ternary_diff_bitvector(unsigned size) : m_pos(size), m_neg(size) {}
        ternary_diff_bitvector(unsigned size, bool full);
        ternary_diff_bitvector(uint64 n, unsigned num_bits);
        ternary_diff_bitvector(const ternary_bitvector & tbv);

        bool contains(const ternary_diff_bitvector & other) const;
        bool is_empty() const;

        ternary_diff_bitvector and(const ternary_diff_bitvector& other) const;
        void neg(union_ternary_bitvector<ternary_diff_bitvector>& result) const;

        static bool has_subtract() { return true; }
        void subtract(const union_ternary_bitvector<ternary_diff_bitvector>& other,
            union_ternary_bitvector<ternary_diff_bitvector>& result) const;

        void join(const ternary_diff_bitvector& other, const unsigned_vector& cols1,
            const unsigned_vector& cols2, union_ternary_bitvector<ternary_diff_bitvector>& result) const;

        bool project(const unsigned_vector& delcols, ternary_diff_bitvector& result) const;

        void rename(const unsigned_vector& cyclecols, const unsigned_vector& out_of_cycle_cols,
            const table_information& src_table, const table_information& dst_table,
            ternary_diff_bitvector& result) const;

        unsigned get(unsigned idx);
        void set(unsigned idx, unsigned val);

        void swap(ternary_diff_bitvector & other);
        void reset();

        unsigned size() const { return m_pos.size(); }

        void display(std::ostream & out) const;
        unsigned size_in_bytes() const;

#if Z3DEBUG
        void expand(std::set<bit_vector> & BVs) const;
#endif
    };

    typedef union_ternary_bitvector<ternary_diff_bitvector> union_ternary_diff_bitvector;

    class hassel_diff_table : public common_hassel_table<union_ternary_diff_bitvector> {
    public:
        hassel_diff_table(table_plugin & p, const table_signature & sig) :
            common_hassel_table(p, sig) {}
    };

    class hassel_diff_table_plugin : public common_hassel_table_plugin<hassel_diff_table> {
    public:
        hassel_diff_table_plugin(relation_manager & manager);
    };

}

#endif
