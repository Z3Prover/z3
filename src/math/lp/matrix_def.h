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

#include <cmath>
#include <string>
#include "math/lp/matrix.h"
namespace lp {
#ifdef Z3DEBUG
template <typename T, typename X>
bool matrix<T, X>::is_equal(const matrix<T, X>& other) {
    if (other.row_count() != row_count() || other.column_count() != column_count())
        return false;
    for (unsigned i = 0; i < row_count(); i++) {
        for (unsigned j = 0; j < column_count(); j++) {
            auto a = get_elem(i, j);
            auto b = other.get_elem(i, j);
            if (numeric_traits<T>::precise()) {
                if (a != b) return false;
            } else if (fabs(numeric_traits<T>::get_double(a - b)) > 0.000001) {
                // cout << "returning false from operator== of matrix comparison" << endl;
                // cout << "this matrix is " << endl;
                // print_matrix(*this);
                // cout << "other matrix is " << endl;
                // print_matrix(other);
                return false;
            }
        }
    }
    return true;
}

template <typename T, typename X>
void apply_to_vector(matrix<T, X> & m, T * w) {
    // here m is a square matrix
    unsigned dim = m.row_count();

    T * wc = new T[dim];

    for (unsigned i = 0; i < dim; i++) {
        wc[i] = w[i];
    }

    for (unsigned i = 0; i < dim; i++) {
        T t = numeric_traits<T>::zero();
        for (unsigned j = 0; j < dim; j++) {
            t += m(i, j) * wc[j];
        }
        w[i] = t;
    }
    delete [] wc;
}

#endif

unsigned get_width_of_column(unsigned j, vector<vector<std::string>> & A) {
    unsigned r = 0;
    for (unsigned i = 0; i < A.size(); i++) {
        vector<std::string> & t = A[i];
        std::string str = t[j];
        unsigned s = static_cast<unsigned>(str.size());
        if (r < s) {
            r = s;
        }
    }
    return r;
}

void print_matrix_with_widths(vector<vector<std::string>> & A, vector<unsigned> & ws, std::ostream & out, unsigned blanks_in_front) {
    for (unsigned i = 0; i < A.size(); i++) {
        for (unsigned j = 0; j < static_cast<unsigned>(A[i].size()); j++) {
            if (i != 0 && j == 0)
                print_blanks(blanks_in_front, out);
            print_blanks(ws[j] - static_cast<unsigned>(A[i][j].size()), out);
            out << A[i][j] << " ";
        }
        out << std::endl;
    }
}

void print_string_matrix(vector<vector<std::string>> & A, std::ostream & out, unsigned blanks_in_front) {
    vector<unsigned> widths;

    if (!A.empty())
        for (unsigned j = 0; j < A[0].size(); j++) {
            widths.push_back(get_width_of_column(j, A));
        }

    print_matrix_with_widths(A, widths, out, blanks_in_front);
    out << std::endl;
}

template <typename T>
void print_matrix(vector<vector<T>> & A, std::ostream & out, unsigned blanks_in_front = 0) {
    vector<vector<std::string>> s(A.size());
    for (unsigned i = 0; i < A.size(); i++) {
        for (const auto & v : A[i]) {
            s[i].push_back(T_to_string(v));
        }
    }

    print_string_matrix(s, out, blanks_in_front);
}


template <typename T, typename X>
void print_matrix(matrix<T, X> const * m, std::ostream & out) {
    vector<vector<std::string>> A(m->row_count());
    for (unsigned i = 0; i < m->row_count(); i++) {
        for (unsigned j = 0; j < m->column_count(); j++) {
            A[i].push_back(T_to_string(m->get_elem(i, j)));
        }
    }

    print_string_matrix(A, out);
}

}
