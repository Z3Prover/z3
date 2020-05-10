/*++
Copyright (c) 2017 Microsoft Corporation

Author:

    Lev Nachmanson (levnach)

--*/
#pragma once
#include "math/lp/numeric_pair.h"
#include "util/vector.h"
#include <string>
#include "math/lp/lp_settings.h"
namespace lp {
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
void print_matrix_with_widths(vector<vector<std::string>> & A, vector<unsigned> & ws, std::ostream & out, unsigned blanks = 0);
void print_string_matrix(vector<vector<std::string>> & A, std::ostream &, unsigned blanks_in_front = 0);

template <typename T, typename X>
void print_matrix(matrix<T, X> const * m, std::ostream & out);


template <typename T>
void print_matrix(const vector<vector<T>> & A, std::ostream & out, unsigned blanks_in_front = 0) {
    vector<vector<std::string>> s(A.size());
    for (unsigned i = 0; i < A.size(); i++) {
        for (const auto & v : A[i]) {
            s[i].push_back(T_to_string(v));
        }
    }

    print_string_matrix(s, out, blanks_in_front);
}


}
