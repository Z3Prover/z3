/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    dl_hassel_common.cpp

Abstract:

    <abstract>

Revision History:

--*/

#include "dl_hassel_common.h"
#include "dl_context.h"

#include <vector>

namespace datalog {

    static void formula_to_dnf_aux(app *and, unsigned idx, std::set<expr*>& conjexpr, std::set<expr*>& toplevel, ast_manager& m) {
        if (idx == and->get_num_args()) {
            std::vector<expr*> v(conjexpr.begin(), conjexpr.end());
            toplevel.insert(m.mk_and((unsigned)v.size(), &v[0]));
            return;
        }

        expr *e = and->get_arg(idx);
        if (is_app(e) && to_app(e)->get_decl_kind() == OP_OR) {
            app *or = to_app(e);
            // quick subsumption test: if any of the elements of the OR is already ANDed, then we skip this OR
            for (unsigned i = 0; i < or->get_num_args(); ++i) {
                if (conjexpr.count(or->get_arg(i))) {
                    formula_to_dnf_aux(and, idx+1, conjexpr, toplevel, m);
                    return;
                }
            }

            for (unsigned i = 0; i < or->get_num_args(); ++i) {
                std::set<expr*> conjexpr2(conjexpr);
                conjexpr2.insert(or->get_arg(i));
                formula_to_dnf_aux(and, idx+1, conjexpr2, toplevel, m);
            }
        } else {
            conjexpr.insert(e);
            formula_to_dnf_aux(and, idx+1, conjexpr, toplevel, m);
        }
    }

    expr_ref formula_to_dnf(expr_ref f) {
        app *a = to_app(f);
        SASSERT(a->get_decl_kind() == OP_AND);
        std::set<expr*> toplevel, conjexpr;
        formula_to_dnf_aux(a, 0, conjexpr, toplevel, f.m());

        if (toplevel.size() > 1) {
            std::vector<expr*> v(toplevel.begin(), toplevel.end());
            return expr_ref(f.m().mk_or((unsigned)v.size(), &v[0]), f.m());
        } else {
            return expr_ref(*toplevel.begin(), f.m());
        }
    }

    bool bit_vector::contains(const bit_vector & other) const {
        unsigned n = num_words();
        if (n == 0)
            return true;

        for (unsigned i = 0; i < n - 1; ++i) {
            if ((m_data[i] & other.m_data[i]) != other.m_data[i])
                return false;
        }
        unsigned bit_rest = m_num_bits % 32;
        unsigned mask = (1 << bit_rest) - 1;
        if (mask == 0) mask = UINT_MAX;
        unsigned other_data = other.m_data[n-1] & mask;
        return (m_data[n-1] & other_data) == other_data;
    }

    bool bit_vector::contains(const bit_vector & other, unsigned idx) const {
        // TODO: optimize this to avoid copy
        return slice(idx, other.size()).contains(other);
    }

    bool bit_vector::contains_consecutive_zeros() const {
        unsigned n = num_words();
        if (n == 0)
            return false;

        for (unsigned i = 0; i < n - 1; ++i) {
            if ((((m_data[i] << 1) | m_data[i]) & 0xAAAAAAAA) != 0xAAAAAAAA)
                return true;
        }
        unsigned bit_rest = m_num_bits % 32;
        unsigned mask = (1 << bit_rest) - 1;
        if (mask == 0) mask = UINT_MAX;
        mask &= 0xAAAAAAAA;
        return ((((m_data[n-1] << 1) | m_data[n-1]) & mask) != mask);
    }

    bit_vector bit_vector::slice(unsigned idx, unsigned length) const {
        bit_vector Res(length);
        // TODO: optimize w/ memcpy when possible
        for (unsigned i = idx; i < idx + length; ++i) {
            Res.push_back(get(i));
        }
        SASSERT(Res.size() == length);
        return Res;
    }

    void bit_vector::append(const bit_vector & other) {
        if (other.empty())
            return;

        if ((m_num_bits % 32) == 0) {
            unsigned prev_num_bits = m_num_bits;
            resize(m_num_bits + other.m_num_bits);
            memcpy(&get_bit_word(prev_num_bits), other.m_data, other.num_words() * sizeof(unsigned));
            return;
        }

        // TODO: optimize the other cases.
        for (unsigned i = 0; i < other.m_num_bits; ++i) {
            push_back(other.get(i));
        }
    }

    uint64 bit_vector::to_number(unsigned idx, unsigned length) const {
        SASSERT(length <= 64);
        uint64 r = 0;
        for (unsigned i = 0; i < length; ++i) {
            r = (r << 1) | (uint64)get(idx+i);
        }
        return r;
    }

    bool bit_vector::operator<(bit_vector const & other) const {
        SASSERT(m_num_bits == other.m_num_bits);
        unsigned n = num_words();
        if (n == 0)
            return false;

        for (unsigned i = 0; i < n - 1; ++i) {
            if (m_data[i] > other.m_data[i])
               return false;
            if (m_data[i] < other.m_data[i])
                return true;
        }

        unsigned bit_rest = m_num_bits % 32;
        unsigned mask = (1 << bit_rest) - 1;
        if (mask == 0) mask = UINT_MAX;
        return (m_data[n-1] & mask) < (other.m_data[n-1] & mask);
    }

    table_information::table_information(table_plugin & p, const table_signature& sig) :
        m_column_info(sig.size()+1),
        m_bv_util(p.get_context().get_manager()),
        m_decl_util(p.get_context().get_manager()) {

        unsigned column = 0;
        for (unsigned i = 0; i < sig.size(); ++i) {
            unsigned num_bits = uint64_log2(sig[i]);
            SASSERT(num_bits == 64 || (1ULL << num_bits) == sig[i]);
            m_column_info[i] = column;
            column += num_bits;
        }
        m_column_info[sig.size()] = column;
    }

    void table_information::expand_column_vector(unsigned_vector& v, const table_information *other) const {
        unsigned_vector orig;
        orig.swap(v);

        for (unsigned i = 0; i < orig.size(); ++i) {
            unsigned col, limit;
            if (orig[i] < get_num_cols()) {
                col = column_idx(orig[i]);
                limit = col + column_num_bits(orig[i]);
            } else {
                unsigned idx = orig[i] - get_num_cols();
                col = get_num_bits() + other->column_idx(idx);
                limit = col + other->column_num_bits(idx);
            }

            for (; col < limit; ++col) {
                v.push_back(col);
            }
        }
    }

    void table_information::display(std::ostream & out) const {
        out << '<';
        for (unsigned i = 0; i < get_num_cols(); ++i) {
            if (i > 0)
                out << ", ";
            out << column_num_bits(i);
        }
        out << ">\n";
    }

    ternary_bitvector::ternary_bitvector(unsigned size, bool full) :
        bit_vector() {
        resize(size, full);
    }

    ternary_bitvector::ternary_bitvector(uint64 n, unsigned num_bits) :
        bit_vector(2 * num_bits) {
        append_number(n, num_bits);
    }

    ternary_bitvector::ternary_bitvector(const table_fact& f, const table_information& t) :
        bit_vector(2 * t.get_num_bits()) {
        for (unsigned i = 0; i < f.size(); ++i) {
            SASSERT(t.column_idx(i) == size());
            append_number(f[i], t.column_num_bits(i));
        }
        SASSERT(size() == t.get_num_bits());
    }

    void ternary_bitvector::fill1() {
        memset(m_data, 0xFF, m_capacity * sizeof(unsigned));
    }

    unsigned ternary_bitvector::get(unsigned idx) const {
        idx *= 2;
        return (bit_vector::get(idx) << 1) | (unsigned)bit_vector::get(idx+1);
    }

    void ternary_bitvector::set(unsigned idx, unsigned val) {
        SASSERT(val == BIT_0 || val == BIT_1 || val == BIT_x);
        idx *= 2;
        bit_vector::set(idx,   (val >> 1) != 0);
        bit_vector::set(idx+1, (val & 1)  != 0);
    }

    void ternary_bitvector::push_back(unsigned val) {
        SASSERT(val == BIT_0 || val == BIT_1 || val == BIT_x);
        bit_vector::push_back((val >> 1) != 0);
        bit_vector::push_back((val & 1)  != 0);
    }

    void ternary_bitvector::append_number(uint64 n, unsigned num_bits) {
        SASSERT(num_bits <= 64);
        for (int bit = num_bits-1; bit >= 0; --bit) {
            if (n & (1ULL << bit)) {
                push_back(BIT_1);
            } else {
                push_back(BIT_0);
            }
        }
    }

    void ternary_bitvector::mk_idx_eq(unsigned idx, ternary_bitvector& val) {
        for (unsigned i = 0; i < val.size(); ++i) {
            set(idx+i, val.get(i));
        }
    }

    ternary_bitvector ternary_bitvector::and(const ternary_bitvector& other) const{
        ternary_bitvector result(*this);
        result &= other;
        return result;
    }

    void ternary_bitvector::neg(union_ternary_bitvector<ternary_bitvector>& result) const {
        ternary_bitvector negated;
        negated.resize(size());

        for (unsigned i = 0; i < size(); ++i) {
            switch (get(i)) {
            case BIT_0:
                negated.fill1();
                negated.set(i, BIT_1);
                break;
            case BIT_1:
                negated.fill1();
                negated.set(i, BIT_0);
                break;
            default:
                continue;
            }
            result.add_fact(negated);
        }
    }

    static void join_fix_eqs(ternary_bitvector& TBV, unsigned idx, unsigned col2_offset,
                             const unsigned_vector& cols1, const unsigned_vector& cols2,
                             union_ternary_bitvector<ternary_bitvector>& result) {
        if (idx == cols1.size()) {
            result.add_fact(TBV);
            return;
        }

        unsigned idx1 = cols1[idx];
        unsigned idx2 = cols2[idx] + col2_offset;
        unsigned v1 = TBV.get(idx1);
        unsigned v2 = TBV.get(idx2);

        if (v1 == BIT_x) {
            if (v2 == BIT_x) {
                // both x: duplicate row
                ternary_bitvector TBV2(TBV);
                TBV2.set(idx1, BIT_0);
                TBV2.set(idx2, BIT_0);
                join_fix_eqs(TBV2, idx+1, col2_offset, cols1, cols2, result);

                TBV.set(idx1, BIT_1);
                TBV.set(idx2, BIT_1);
            } else {
                TBV.set(idx1, v2);
            }
        } else if (v2 == BIT_x) {
            TBV.set(idx2, v1);
        } else if (v1 != v2) {
            // columns don't match
            return;
        }
        join_fix_eqs(TBV, idx+1, col2_offset, cols1, cols2, result);
    }

    void ternary_bitvector::join(const ternary_bitvector& other,
                                 const unsigned_vector& cols1,
                                 const unsigned_vector& cols2,
                                 union_ternary_bitvector<ternary_bitvector>& result) const {
        ternary_bitvector TBV(*this);
        TBV.append(other);
        join_fix_eqs(TBV, 0, size(), cols1, cols2, result);
    }

    bool ternary_bitvector::project(const unsigned_vector& delcols, ternary_bitvector& result) const {
        unsigned *rm_cols = delcols.c_ptr();

        for (unsigned i = 0; i < size(); ++i) {
            if (*rm_cols == i) {
                ++rm_cols;
                continue;
            }
            result.push_back(get(i));
        }
        return true;
    }

    static void copy_column(ternary_bitvector& CopyTo, const ternary_bitvector& CopyFrom,
                            unsigned col_dst, unsigned col_src, const table_information& src_table,
                            const table_information& dst_table) {
        unsigned idx_dst = dst_table.column_idx(col_dst);
        unsigned idx_src = src_table.column_idx(col_src);
        unsigned num_bits = dst_table.column_num_bits(col_dst);
        SASSERT(num_bits == src_table.column_num_bits(col_src));

        for (unsigned i = 0; i < num_bits; ++i) {
            CopyTo.set(idx_dst+i, CopyFrom.get(idx_src+i));
        }
    }

    void ternary_bitvector::rename(const unsigned_vector& cyclecols,
                                   const unsigned_vector& out_of_cycle_cols,
                                   const table_information& src_table,
                                   const table_information& dst_table,
                                   ternary_bitvector& result) const {
        result.resize(dst_table.get_num_bits());

        for (unsigned i = 1; i < cyclecols.size(); ++i) {
            copy_column(result, *this, cyclecols[i-1], cyclecols[i], src_table, dst_table);
        }
        copy_column(result, *this, cyclecols[cyclecols.size()-1], cyclecols[0], src_table, dst_table);

        for (unsigned i = 0; i < out_of_cycle_cols.size(); ++i) {
            unsigned col = out_of_cycle_cols[i];
            copy_column(result, *this, col, col, src_table, dst_table);
        }
    }

    unsigned ternary_bitvector::size_in_bytes() const {
        return sizeof(*this) + m_capacity;
    }

    void ternary_bitvector::display(std::ostream & out) const {
        for (unsigned i = 0; i < size(); ++i) {
            switch (get(i)) {
            case BIT_0:
                out << '0';
                break;
            case BIT_1:
                out << '1';
                break;
            case BIT_x:
                out << 'x';
                break;
            default:
                UNREACHABLE();
            }
        }
    }

#if Z3DEBUG
    void ternary_bitvector::expand(std::set<bit_vector> & BVs) const {
        bit_vector BV(m_num_bits);
        expand(BVs, BV, 0);
    }

    void ternary_bitvector::expand(std::set<bit_vector> & BVs, bit_vector &BV, unsigned idx) const {
        if (idx == size()) {
            BVs.insert(BV);
            return;
        }

        switch (get(idx)) {
        case BIT_0:
            BV.push_back(false);
            expand(BVs, BV, idx+1);
            break;
        case BIT_1:
            BV.push_back(true);
            expand(BVs, BV, idx+1);
            break;
        case BIT_x: { // x: duplicate
            bit_vector BV2(BV);
            BV.push_back(false);
            BV2.push_back(true);
            expand(BVs, BV, idx+1);
            expand(BVs, BV2, idx+1);
            }
            break;
        default:
            UNREACHABLE();
        }
    }
#endif

}
