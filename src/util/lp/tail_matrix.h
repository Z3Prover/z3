/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/

#pragma once
#include "util/vector.h"
#include "util/lp/indexed_vector.h"
#include "util/lp/matrix.h"
#include "util/lp/lp_settings.h"
// These matrices appear at the end of the list

namespace lean {
template <typename T, typename X>
class tail_matrix
#ifdef LEAN_DEBUG
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
};
}
