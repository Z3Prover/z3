/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    <name>

Abstract:

    <abstract>

Author:

    Lev Nachmanson (levnach)

Revision History:


--*/

#pragma once
#include "util/vector.h"
#include "math/lp/indexed_vector.h"
#include "math/lp/matrix.h"
#include "math/lp/lp_settings.h"
// These matrices appear at the end of the list

namespace lp {
template <typename T, typename X>
class tail_matrix
#ifdef Z3DEBUG
    : public matrix<T, X>
#endif
{
public:
    virtual void apply_from_left_to_T(indexed_vector<T> & w, lp_settings & settings) = 0;
    virtual void apply_from_left(vector<X> & w, lp_settings & settings) = 0;
    virtual void apply_from_right(vector<T> & w) = 0;
    virtual void apply_from_right(indexed_vector<T> & w) = 0;
    virtual ~tail_matrix() {}
    virtual bool is_dense() const = 0;
    struct ref_row {
        const tail_matrix & m_A;
        unsigned m_row;
        ref_row(const tail_matrix& m, unsigned row): m_A(m), m_row(row) {}
        T operator[](unsigned j) const { return m_A.get_elem(m_row, j);}
    };
    ref_row operator[](unsigned i) const { return ref_row(*this, i);}
};
}
