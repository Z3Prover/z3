/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    dl_hassel_diff_table.cpp

Abstract:

    <abstract>

Revision History:

--*/

#include "ast_printer.h"
#include "dl_context.h"
#include "dl_util.h"
#include "dl_hassel_diff_table.h"


namespace datalog {

    ternary_diff_bitvector::ternary_diff_bitvector(unsigned size, bool full) :
        m_pos(size, full), m_neg(size) { }

    ternary_diff_bitvector::ternary_diff_bitvector(uint64 n, unsigned num_bits) :
        m_pos(n, num_bits), m_neg(num_bits) { }

    ternary_diff_bitvector::ternary_diff_bitvector(const ternary_bitvector & tbv) :
        m_pos(tbv), m_neg(tbv.size()) { }

    bool ternary_diff_bitvector::contains(const ternary_diff_bitvector & other) const {
        return m_pos.contains(other.m_pos) && other.m_neg.contains(m_neg);
    }

    bool ternary_diff_bitvector::is_empty() const {
        if (m_pos.is_empty())
            return true;

        return m_neg.contains(m_pos);
    }

    ternary_diff_bitvector ternary_diff_bitvector::and(const ternary_diff_bitvector& other) const {
        ternary_diff_bitvector result(m_pos.and(other.m_pos));
        result.m_neg.swap(m_neg.or(other.m_neg));
        return result;
    }

    void ternary_diff_bitvector::neg(union_ternary_bitvector<ternary_diff_bitvector>& result) const {
        // not(A\B) <-> (T\A) U B
        ternary_diff_bitvector negated(size(), true);
        negated.m_neg.add_new_fact(m_pos);
        result.add_fact(negated);

        for (union_ternary_bitvector<ternary_bitvector>::const_iterator I = m_neg.begin(),
            E = m_neg.end(); I != E; ++I) {
            result.add_fact(*I);
        }
    }

    void ternary_diff_bitvector::subtract(const union_ternary_bitvector<ternary_diff_bitvector>& other,
        union_ternary_bitvector<ternary_diff_bitvector>& result) const {
        ternary_diff_bitvector newfact(*this);
        for (union_ternary_bitvector<ternary_diff_bitvector>::const_iterator I = other.begin(),
            E = other.end(); I != E; ++I) {
            if (!I->m_neg.empty()) {
                NOT_IMPLEMENTED_YET();
            }
            newfact.m_neg.add_fact(I->m_pos);
        }

        if (!newfact.is_empty())
            result.add_fact(newfact);
    }

    void ternary_diff_bitvector::join(const ternary_diff_bitvector& other,
                                      const unsigned_vector& cols1,
                                      const unsigned_vector& cols2,
                                      union_ternary_bitvector<ternary_diff_bitvector>& result) const {
        unsigned new_size = size() + other.size();
        ternary_diff_bitvector res(new_size);

        res.m_pos = m_pos;
        res.m_pos.append(other.m_pos);

        for (unsigned i = 0; i < cols1.size(); ++i) {
            unsigned idx1 = cols1[i];
            unsigned idx2 = size() + cols2[i];
            unsigned v1 = res.m_pos.get(idx1);
            unsigned v2 = res.m_pos.get(idx2);

            if (v1 == BIT_x) {
                if (v2 == BIT_x) {
                    // add to subtracted TBVs: 1xx0 and 0xx1
                    {
                    ternary_bitvector r(new_size, true);
                    r.set(idx1, BIT_0);
                    r.set(idx2, BIT_1);
                    res.m_neg.add_new_fact(r);
                    }
                    {
                    ternary_bitvector r(new_size, true);
                    r.set(idx1, BIT_1);
                    r.set(idx2, BIT_0);
                    res.m_neg.add_new_fact(r);
                    }
                } else {
                    res.m_pos.set(idx1, v2);
                }
            } else if (v2 == BIT_x) {
                res.m_pos.set(idx2, v1);
            } else if (v1 != v2) {
                // columns don't match
                return;
            }
        }

        // handle subtracted TBVs:  1010 -> 1010xxx
        if (!m_neg.empty()) {
            ternary_bitvector padding(other.size(), true);
            for (union_ternary_bitvector<ternary_bitvector>::const_iterator I = m_neg.begin(),
                E = m_neg.end(); I != E; ++I) {
                ternary_bitvector BV(*I);
                BV.append(padding);
                res.m_neg.add_new_fact(BV);
            }
        }

        if (!other.m_neg.empty()) {
            ternary_bitvector padding(size(), true);
            for (union_ternary_bitvector<ternary_bitvector>::const_iterator I = other.m_neg.begin(),
                E = other.m_neg.end(); I != E; ++I) {
                ternary_bitvector BV(padding);
                BV.append(*I);
                res.m_neg.add_new_fact(BV);
            }
        }

        result.add_fact(res);
    }

    bool ternary_diff_bitvector::project(const unsigned_vector& delcols, ternary_diff_bitvector& result) const {
        m_pos.project(delcols, result.m_pos);
        if (m_neg.empty())
            return true;

        ternary_bitvector newneg;
        for (union_ternary_bitvector<ternary_bitvector>::const_iterator I = m_neg.begin(),
                E = m_neg.end(); I != E; ++I) {
            for (unsigned i = 0; i < delcols.size()-1; ++i) {
                unsigned idx = delcols[i];
                if (I->get(idx) != BIT_x && m_pos.get(idx) == BIT_x)
                    goto skip_row;
            }
            newneg.reset();
            I->project(delcols, newneg);
            result.m_neg.add_fact(newneg);
skip_row:   ;
        }
        return !result.is_empty();
    }

    void ternary_diff_bitvector::rename(const unsigned_vector& cyclecols,
                                        const unsigned_vector& out_of_cycle_cols,
                                        const table_information& src_table,
                                        const table_information& dst_table,
                                        ternary_diff_bitvector& result) const {
        m_pos.rename(cyclecols, out_of_cycle_cols, src_table, dst_table, result.m_pos);
        m_neg.rename(cyclecols, out_of_cycle_cols, src_table, dst_table, result.m_neg);
    }

    unsigned ternary_diff_bitvector::get(unsigned idx) {
        return m_pos.get(idx);
    }

    void ternary_diff_bitvector::set(unsigned idx, unsigned val) {
        m_pos.set(idx, val);
    }

    void ternary_diff_bitvector::swap(ternary_diff_bitvector & other) {
        m_pos.swap(other.m_pos);
        m_neg.swap(other.m_neg);
    }

    void ternary_diff_bitvector::reset() {
        m_pos.reset();
        m_neg.reset();
    }

    void ternary_diff_bitvector::display(std::ostream & out) const {
        m_pos.display(out);
        if (!m_neg.empty()) {
            out << " \\ ";
            if (m_neg.num_disjs() > 1) out << '(';
            m_neg.display(out);
            if (m_neg.num_disjs() > 1) out << ')';
        }
    }

    unsigned ternary_diff_bitvector::size_in_bytes() const {
        return m_pos.size_in_bytes() + m_neg.num_bytes();
    }

#if Z3DEBUG
    void ternary_diff_bitvector::expand(std::set<bit_vector> & BVs) const {
        m_pos.expand(BVs);
        SASSERT(!BVs.empty());

        std::set<bit_vector> NegBVs;
        m_neg.expand(NegBVs);
        BVs.erase(NegBVs.begin(), NegBVs.end());
    }
#endif

    hassel_diff_table_plugin::hassel_diff_table_plugin(relation_manager & manager)
        : common_hassel_table_plugin(symbol("hassel_diff"), manager) {}

}
