#pragma once
/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/
#include <string>
#include "util/lp/linear_combination_iterator.h"
namespace lean {
class column_namer {
public:
    virtual std::string get_column_name(unsigned j) const = 0;
    template <typename T>
    void print_linear_iterator(linear_combination_iterator<T>* it, std::ostream & out) const {
        vector<std::pair<T, unsigned>> coeff;
        T a;
        unsigned i;
        while (it->next(a, i)) {
            coeff.emplace_back(a, i);
        }
        print_linear_combination_of_column_indices(coeff, out);
    }
    template <typename T>
    void print_linear_iterator_indices_only(linear_combination_iterator<T>* it, std::ostream & out) const {
        vector<std::pair<T, unsigned>> coeff;
        T a;
        unsigned i;
        while (it->next(a, i)) {
            coeff.emplace_back(a, i);
        }
        print_linear_combination_of_column_indices_only(coeff, out);
    }
    
    template <typename T>
    void print_linear_combination_of_column_indices_only(const vector<std::pair<T, unsigned>> & coeffs, std::ostream & out) const {
        bool first = true;
        for (const auto & it : coeffs) {
            auto val = it.first;
            if (first) {
                first = false;
            } else {
                if (numeric_traits<T>::is_pos(val)) {
                    out << " + ";
                } else {
                    out << " - ";
                    val = -val;
                }
            }
            if (val == -numeric_traits<T>::one())
                out << " - ";
            else if (val != numeric_traits<T>::one())
                out << T_to_string(val);
        
            out << "_" << it.second;
        }
    }
    
    template <typename T>
    void print_linear_combination_of_column_indices(const vector<std::pair<T, unsigned>> & coeffs, std::ostream & out) const {
        bool first = true;
        for (const auto & it : coeffs) {
            auto val = it.first;
            if (first) {
                first = false;
            } else {
                if (numeric_traits<T>::is_pos(val)) {
                    out << " + ";
                } else {
                    out << " - ";
                    val = -val;
                }
            }
            if (val == -numeric_traits<T>::one())
                out << " - ";
            else if (val != numeric_traits<T>::one())
                out << val;
        
            out << get_column_name(it.second);
        }
    }

};
}
