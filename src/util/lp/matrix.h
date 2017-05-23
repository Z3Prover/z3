/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/
#ifdef Z3DEBUG
#pragma once
#include "util/lp/numeric_pair.h"
#include "util/vector.h"
#include <string>
#include "util/lp/lp_settings.h"
namespace lean {
// used for debugging purposes only
template <typename T, typename X>
class matrix {
public:
    virtual T get_elem (unsigned i, unsigned j) const = 0;
    virtual unsigned row_count() const  = 0;
    virtual unsigned column_count() const = 0;
    virtual void set_number_of_rows(unsigned m)  = 0;
    virtual void set_number_of_columns(unsigned n) = 0;

    virtual ~matrix() {}

    bool is_equal(const matrix<T, X>& other);
    bool operator == (matrix<T, X> const & other) {
        return is_equal(other);
    }
    T operator()(unsigned i, unsigned j) const { return get_elem(i, j); }
};

template <typename T, typename X>
void apply_to_vector(matrix<T, X> & m, T * w);



unsigned get_width_of_column(unsigned j, vector<vector<std::string>> & A);
void print_matrix_with_widths(vector<vector<std::string>> & A, vector<unsigned> & ws, std::ostream & out);
void print_string_matrix(vector<vector<std::string>> & A);

template <typename T, typename X>
void print_matrix(matrix<T, X> const * m, std::ostream & out);

}
#endif
