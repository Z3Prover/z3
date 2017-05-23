/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/

#pragma once

// reads an MPS file reperesenting a Mixed Integer Program
#include <functional>
#include <algorithm>
#include <string>
#include "util/vector.h"
#include <unordered_map>
#include <iostream>
#include <fstream>
#include <locale>
#include "util/lp/lp_primal_simplex.h"
#include "util/lp/lp_dual_simplex.h"
#include "util/lp/lar_solver.h"
#include "util/lp/lp_utils.h"
#include "util/lp/lp_solver.h"
namespace lean {
inline bool my_white_space(const char & a) {
    return a == ' ' || a == '\t';
}
inline size_t number_of_whites(const std::string & s)  {
    size_t i = 0;
    for(;i < s.size(); i++)
        if (!my_white_space(s[i])) return i;
    return i;
}
inline size_t number_of_whites_from_end(const std::string & s)  {
    size_t ret = 0;
    for(int i = static_cast<int>(s.size()) - 1;i >= 0; i--)
        if (my_white_space(s[i])) ret++;else break;
    
    return ret;
}


    // trim from start
inline std::string &ltrim(std::string &s) {
    s.erase(0, number_of_whites(s));
    return s;
}




    // trim from end
inline std::string &rtrim(std::string &s) {
    //       s.erase(std::find_if(s.rbegin(), s.rend(), std::not1(std::ptr_fun<int, int>(std::isspace))).base(), s.end());
    s.erase(s.end() - number_of_whites_from_end(s), s.end());
    return s;
}
    // trim from both ends
inline std::string &trim(std::string &s) {
    return ltrim(rtrim(s));
}

inline std::string trim(std::string const &r) {
        std::string s = r;
        return ltrim(rtrim(s));
}


inline vector<std::string> string_split(const std::string &source, const char *delimiter, bool keep_empty)  {
    vector<std::string> results;
    size_t prev = 0;
    size_t next = 0;
    while ((next = source.find_first_of(delimiter, prev)) != std::string::npos) {
        if (keep_empty || (next - prev != 0)) {
            results.push_back(source.substr(prev, next - prev));
        }
        prev = next + 1;
    }
    if (prev < source.size()) {
        results.push_back(source.substr(prev));
    }
    return results;
}

inline vector<std::string> split_and_trim(std::string line) {
    auto split = string_split(line, " \t", false);
    vector<std::string> ret;
    for (auto s : split) {
        ret.push_back(trim(s));
    }
    return ret;
}

template <typename T, typename X>
class mps_reader {
    enum row_type { Cost, Less_or_equal, Greater_or_equal, Equal };
    struct bound {
        T    m_low;
        T    m_upper;
        bool m_low_is_set;
        bool m_upper_is_set;
        bool m_value_is_fixed;
        T    m_fixed_value;
        bool m_free;
        // constructor
        bound() : m_low(numeric_traits<T>::zero()),
                  m_low_is_set(true),
                  m_upper_is_set(false),
                  m_value_is_fixed(false),
                  m_free(false) {} // it seems all mps files I have seen have the default low value 0 on a variable
    };

    struct column {
        std::string m_name;
        bound * m_bound;
        unsigned m_index;
        column(std::string name, unsigned index): m_name(name),
                                                  m_bound(nullptr),
                                                  m_index(index) {
        }
    };

    struct row {
        row_type m_type;
        std::string m_name;
        std::unordered_map<std::string, T> m_row_columns;
        unsigned m_index;
        T m_right_side;
        T m_range;
        row(row_type type, std::string name, unsigned index) :
            m_type(type),
            m_name(name),
            m_index(index),
            m_right_side(zero_of_type<T>()),
            m_range(zero_of_type<T>())
        {
        }
    };

    bool m_is_OK;
    std::string m_file_name;
    std::unordered_map<std::string, row *> m_rows;
    std::unordered_map<std::string, column *> m_columns;
    std::unordered_map<std::string, unsigned> m_names_to_var_index;
    std::string m_line;
    std::string m_name;
    std::string m_cost_row_name;
    std::ifstream m_file_stream;
    // needed to adjust the index row
    unsigned m_cost_line_count;
    unsigned m_line_number;
    std::ostream * m_message_stream;

    void set_m_ok_to_false() {
        *m_message_stream << "setting m_is_OK to false" << std::endl;
        m_is_OK = false;
    }

    std::string get_string_from_position(unsigned offset) {
        unsigned i = offset;
        for (; i < m_line.size(); i++){
            if (m_line[i] == ' ')
                break;
        }
        lean_assert(m_line.size() >= offset);
        lean_assert(m_line.size() >> i);
        lean_assert(i >= offset);
        return m_line.substr(offset, i - offset);
    }

    void set_boundary_for_column(unsigned col, bound * b, lp_solver<T, X> * solver){
        if (b == nullptr) {
            solver->set_low_bound(col, numeric_traits<T>::zero());
            return;
        }

        if (b->m_free) {
            return;
        }
        if (b->m_low_is_set) {
            solver->set_low_bound(col, b->m_low);
        }
        if (b->m_upper_is_set) {
            solver->set_upper_bound(col, b->m_upper);
        }

        if (b->m_value_is_fixed) {
            solver->set_fixed_value(col, b->m_fixed_value);
        }
    }

    bool all_white_space() {
        for (unsigned i = 0; i < m_line.size(); i++) {
            char c = m_line[i];
            if (c != ' ' && c != '\t') {
                return false;
            }
        }
        return true;
    }

    void read_line() {
        while (m_is_OK) {
            if (!getline(m_file_stream, m_line)) {
                m_line_number++;
                set_m_ok_to_false();
                *m_message_stream << "cannot read from file" << std::endl;
            }
            m_line_number++;
            if (m_line.size() != 0 && m_line[0] != '*' && !all_white_space())
                break;
        }
    }

    void read_name() {
        do {
            read_line();
            if (m_line.find("NAME") != 0) {
                continue;
            }
            m_line = m_line.substr(4);
            m_name = trim(m_line);
            break;
        } while (m_is_OK);
    }

    void read_rows() {
        // look for start of the rows
        read_line();
        do {
            if (static_cast<int>(m_line.find("ROWS")) >= 0) {
                break;
            }
        } while (m_is_OK);
        do {
            read_line();
            if (m_line.find("COLUMNS") == 0) {
                break;
            }
            add_row();
        } while (m_is_OK);
    }

    void read_column_by_columns(std::string column_name, std::string column_data) {
         // uph, let us try to work with columns
        if (column_data.size() >= 22) {
            std::string ss = column_data.substr(0, 8);
            std::string row_name = trim(ss);
            auto t = m_rows.find(row_name);

            if (t == m_rows.end()) {
                *m_message_stream << "cannot find " << row_name << std::endl;
                goto fail;
            } else {
                row * row = t->second;
                row->m_row_columns[column_name] = numeric_traits<T>::from_string(column_data.substr(8));
                if (column_data.size() > 24) {
                    column_data = column_data.substr(25);
                    if (column_data.size() >= 22) {
                        read_column_by_columns(column_name, column_data);
                    }
                }
            }
        } else {
        fail:
            set_m_ok_to_false();
            *m_message_stream << "cannot understand this line" << std::endl;
            *m_message_stream << "line = " << m_line <<  ", line number is " << m_line_number << std::endl;
            return;
        }
    }

    void read_column(std::string column_name, std::string column_data){
        auto tokens = split_and_trim(column_data);
        for (unsigned i = 0; i < tokens.size() - 1; i+= 2) {
            auto row_name = tokens[i];
            if (row_name == "'MARKER'") return; // it is the integrality marker, no real data here
            auto t = m_rows.find(row_name);
            if (t == m_rows.end()) {
                read_column_by_columns(column_name, column_data);
                return;
            }
            row *r = t->second;
            r->m_row_columns[column_name] = numeric_traits<T>::from_string(tokens[i + 1]);
        }
    }

    void read_columns(){
        std::string column_name;
        do {
            read_line();
            if (m_line.find("RHS") == 0) {
                //  cout << "found RHS" << std::endl;
                break;
            }
            if (m_line.size() < 22) {
                (*m_message_stream) << "line is too short for a column" << std::endl;
                (*m_message_stream) << m_line << std::endl;
                (*m_message_stream) << "line number is " << m_line_number << std::endl;
                set_m_ok_to_false();
                return;
            }
            std::string column_name_tmp = trim(m_line.substr(4, 8));
            if (!column_name_tmp.empty()) {
                column_name = column_name_tmp;
            }
            auto col_it = m_columns.find(column_name);
            mps_reader::column * col;
            if (col_it == m_columns.end()) {
                col = new mps_reader::column(column_name, static_cast<unsigned>(m_columns.size()));
                m_columns[column_name] = col;
                // (*m_message_stream) << column_name << '[' << col->m_index << ']'<< std::endl;
            } else {
                col = col_it->second;
            }
            read_column(column_name, m_line.substr(14));
        } while (m_is_OK);
    }

    void read_rhs() {
        do {
            read_line();
            if (m_line.find("BOUNDS") == 0 || m_line.find("ENDATA") == 0 || m_line.find("RANGES") == 0) {
                break;
            }
            fill_rhs();
        } while (m_is_OK);
    }


    void fill_rhs_by_columns(std::string rhsides) {
        // uph, let us try to work with columns
        if (rhsides.size() >= 22) {
            std::string ss = rhsides.substr(0, 8);
            std::string row_name = trim(ss);
            auto t = m_rows.find(row_name);

            if (t == m_rows.end()) {
                (*m_message_stream) << "cannot find " << row_name << std::endl;
                goto fail;
            } else {
                row * row = t->second;
                row->m_right_side = numeric_traits<T>::from_string(rhsides.substr(8));
                if (rhsides.size() > 24) {
                    rhsides = rhsides.substr(25);
                    if (rhsides.size() >= 22) {
                        fill_rhs_by_columns(rhsides);
                    }
                }
            }
        } else {
        fail:
            set_m_ok_to_false();
            (*m_message_stream) << "cannot understand this line" << std::endl;
            (*m_message_stream) << "line = " << m_line <<  ", line number is " << m_line_number << std::endl;
            return;
        }
    }

    void fill_rhs()  {
        if (m_line.size() < 14) {
            (*m_message_stream) << "line is too short" << std::endl;
            (*m_message_stream) << m_line << std::endl;
            (*m_message_stream) << "line number is " << m_line_number << std::endl;
            set_m_ok_to_false();
            return;
        }
        std::string rhsides = m_line.substr(14);
        vector<std::string> splitted_line = split_and_trim(rhsides);

        for (unsigned i = 0; i < splitted_line.size() - 1; i += 2) {
            auto t = m_rows.find(splitted_line[i]);
            if (t == m_rows.end()) {
                fill_rhs_by_columns(rhsides);
                return;
            }
            row * row = t->second;
            row->m_right_side = numeric_traits<T>::from_string(splitted_line[i + 1]);
        }
    }

    void read_bounds() {
        if (m_line.find("BOUNDS") != 0) {
            return;
        }

        do {
            read_line();
            if (m_line[0] != ' ') {
                break;
            }
            create_or_update_bound();
        } while (m_is_OK);
    }

    void read_ranges() {
        if (m_line.find("RANGES") != 0) {
            return;
        }
        do {
            read_line();
            auto sl = split_and_trim(m_line);
            if (sl.size() < 2) {
                break;
            }
            read_range(sl);
        } while (m_is_OK);
    }


    void read_bound_by_columns(std::string colstr) {
        if (colstr.size() < 14) {
            (*m_message_stream) << "line is too short" << std::endl;
            (*m_message_stream) << m_line << std::endl;
            (*m_message_stream) << "line number is " << m_line_number << std::endl;
            set_m_ok_to_false();
            return;
        }
         // uph, let us try to work with columns
        if (colstr.size() >= 22) {
            std::string ss = colstr.substr(0, 8);
            std::string column_name = trim(ss);
            auto t = m_columns.find(column_name);

            if (t == m_columns.end()) {
                (*m_message_stream) << "cannot find " << column_name << std::endl;
                goto fail;
            } else {
                vector<std::string> bound_string;
                bound_string.push_back(column_name);
                if (colstr.size() > 14) {
                    bound_string.push_back(colstr.substr(14));
                }
                mps_reader::column * col = t->second;
                bound * b = col->m_bound;
                if (b == nullptr) {
                    col->m_bound = b = new bound();
                }
                update_bound(b, bound_string);
            }
        } else {
        fail:
            set_m_ok_to_false();
            (*m_message_stream) << "cannot understand this line" << std::endl;
            (*m_message_stream) << "line = " << m_line <<  ", line number is " << m_line_number << std::endl;
            return;
        }
    }

    void update_bound(bound * b, vector<std::string> bound_string) {
        /*
          UP means an upper bound is applied to the variable. A bound of type LO means a lower bound is applied. A bound type of FX ("fixed") means that the variable has upper and lower bounds equal to a single value. A bound type of FR ("free") means the variable has neither lower nor upper bounds and so can take on negative values. A variation on that is MI for free negative, giving an upper bound of 0 but no lower bound. Bound type PL is for a free positive for zero to plus infinity, but as this is the normal default, it is seldom used. There are also bound types for use in MIP models - BV for binary, being 0 or 1. UI for upper integer and LI for lower integer. SC stands for semi-continuous and indicates that the variable may be zero, but if not must be equal to at least the value given.
        */

        std::string bound_type = get_string_from_position(1);
        if (bound_type == "BV") {
            b->m_upper_is_set = true;
            b->m_upper = 1;
            return;
        }

        if (bound_type == "UP" || bound_type == "UI" || bound_type == "LIMITMAX") {
            if (bound_string.size() <= 1){
                set_m_ok_to_false();
                return;
            }
            b->m_upper_is_set = true;
            b->m_upper= numeric_traits<T>::from_string(bound_string[1]);
        } else if (bound_type == "LO" || bound_type == "LI") {
            if (bound_string.size() <= 1){
                set_m_ok_to_false();
                return;
            }

            b->m_low_is_set = true;
            b->m_low = numeric_traits<T>::from_string(bound_string[1]);
        } else if (bound_type == "FR") {
            b->m_free = true;
        } else if (bound_type == "FX") {
            if (bound_string.size() <= 1){
                set_m_ok_to_false();
                return;
            }

            b->m_value_is_fixed = true;
            b->m_fixed_value =  numeric_traits<T>::from_string(bound_string[1]);
        } else if (bound_type == "PL") {
            b->m_low_is_set = true;
            b->m_low = 0;
        } else if (bound_type == "MI") {
            b->m_upper_is_set = true;
            b->m_upper = 0;
        } else {
            (*m_message_stream) << "unexpected bound type " << bound_type << " at line " << m_line_number << std::endl;
            set_m_ok_to_false();
            throw;
        }
    }

    void create_or_update_bound() {
        const unsigned name_offset = 14;
        lean_assert(m_line.size() >= 14);
        vector<std::string> bound_string = split_and_trim(m_line.substr(name_offset, m_line.size()));

        if (bound_string.size() == 0) {
            set_m_ok_to_false();
            (*m_message_stream) << "error at line " << m_line_number << std::endl;
            throw m_line;
        }

        std::string name = bound_string[0];
        auto it = m_columns.find(name);
        if (it == m_columns.end()){
            read_bound_by_columns(m_line.substr(14));
            return;
        }
        mps_reader::column * col = it->second;
        bound * b = col->m_bound;
        if (b == nullptr) {
            col->m_bound = b = new bound();
        }
        update_bound(b, bound_string);
    }



    void read_range_by_columns(std::string rhsides) {
        if (m_line.size() < 14) {
            (*m_message_stream) << "line is too short" << std::endl;
            (*m_message_stream) << m_line << std::endl;
            (*m_message_stream) << "line number is " << m_line_number << std::endl;
            set_m_ok_to_false();
            return;
        }
         // uph, let us try to work with columns
        if (rhsides.size() >= 22) {
            std::string ss = rhsides.substr(0, 8);
            std::string row_name = trim(ss);
            auto t = m_rows.find(row_name);

            if (t == m_rows.end()) {
                (*m_message_stream) << "cannot find " << row_name << std::endl;
                goto fail;
            } else {
                row * row = t->second;
                row->m_range = numeric_traits<T>::from_string(rhsides.substr(8));
                maybe_modify_current_row_and_add_row_for_range(row);
                if (rhsides.size() > 24) {
                    rhsides = rhsides.substr(25);
                    if (rhsides.size() >= 22) {
                        read_range_by_columns(rhsides);
                    }
                }
            }
        } else {
        fail:
            set_m_ok_to_false();
            (*m_message_stream) << "cannot understand this line" << std::endl;
            (*m_message_stream) << "line = " << m_line <<  ", line number is " << m_line_number << std::endl;
            return;
        }
    }


    void read_range(vector<std::string> & splitted_line){
        for (unsigned i = 1; i < splitted_line.size() - 1; i += 2) {
            auto it = m_rows.find(splitted_line[i]);
            if (it == m_rows.end()) {
                read_range_by_columns(m_line.substr(14));
                return;
            }
            row * row = it->second;
            row->m_range = numeric_traits<T>::from_string(splitted_line[i + 1]);
            maybe_modify_current_row_and_add_row_for_range(row);
        }
    }

    void maybe_modify_current_row_and_add_row_for_range(row * row_with_range) {
        unsigned index= static_cast<unsigned>(m_rows.size() - m_cost_line_count);
        std::string row_name = row_with_range->m_name + "_range";
        row * other_bound_range_row;
        switch (row_with_range->m_type) {
        case row_type::Greater_or_equal:
            m_rows[row_name] = other_bound_range_row = new row(row_type::Less_or_equal, row_name, index);
            other_bound_range_row->m_right_side = row_with_range->m_right_side + abs(row_with_range->m_range);
            break;
        case row_type::Less_or_equal:
            m_rows[row_name] = other_bound_range_row = new row(row_type::Greater_or_equal, row_name, index);
            other_bound_range_row->m_right_side = row_with_range->m_right_side - abs(row_with_range->m_range);
            break;
        case row_type::Equal:
            if (row_with_range->m_range > 0) {
                row_with_range->m_type = row_type::Greater_or_equal; // the existing row type change
                m_rows[row_name] = other_bound_range_row = new row(row_type::Less_or_equal, row_name, index);
            } else { // row->m_range < 0;
                row_with_range->m_type = row_type::Less_or_equal; // the existing row type change
                m_rows[row_name] = other_bound_range_row = new row(row_type::Greater_or_equal, row_name, index);
            }
            other_bound_range_row->m_right_side = row_with_range->m_right_side + row_with_range->m_range;
            break;
        default:
            (*m_message_stream) << "unexpected bound type " << row_with_range->m_type << " at line " << m_line_number << std::endl;
            set_m_ok_to_false();
            throw;
        }

        for (auto s : row_with_range->m_row_columns) {
            lean_assert(m_columns.find(s.first) != m_columns.end());
            other_bound_range_row->m_row_columns[s.first] = s.second;
        }
    }

    void add_row() {
        if (m_line.length() < 2) {
            return;
        }

        m_line = trim(m_line);
        char c = m_line[0];
        m_line = m_line.substr(1);
        m_line = trim(m_line);
        add_row(c);
    }

    void add_row(char c) {
        unsigned index= static_cast<unsigned>(m_rows.size() - m_cost_line_count);
        switch (c) {
        case 'E':
            m_rows[m_line] = new row(row_type::Equal, m_line, index);
            break;
        case 'L':
            m_rows[m_line] = new row(row_type::Less_or_equal, m_line, index);
            break;
        case 'G':
            m_rows[m_line] = new row(row_type::Greater_or_equal, m_line, index);
            break;
        case 'N':
            m_rows[m_line] = new row(row_type::Cost, m_line, index);
            m_cost_row_name = m_line;
            m_cost_line_count++;
            break;
        }
    }
    unsigned range_count()  {
        unsigned ret = 0;
        for (auto s : m_rows) {
            if (s.second->m_range != 0) {
                ret++;
            }
        }
        return ret;
    }

    /*
      If rhs is a constraint's right-hand-side value and range is the constraint's range value, then the range interval is defined according to the following table:
      sense   interval
      G   [rhs, rhs + |range|]
      L   [rhs - |range|, rhs]
      E   [rhs, rhs + |range|]     if range > 0,
          [rhs - |range|, rhs]     if range < 0
      where |range| is range's absolute value.
    */

    lp_relation get_relation_from_row(row_type rt) {
        switch (rt) {
        case mps_reader::Less_or_equal: return lp_relation::Less_or_equal;
        case mps_reader::Greater_or_equal: return lp_relation::Greater_or_equal;
        case mps_reader::Equal: return lp_relation::Equal;
        default:
            (*m_message_stream) << "Unexpected rt " << rt << std::endl;
            set_m_ok_to_false();
            throw;
        }
    }

    unsigned solver_row_count() {
        return m_rows.size() - m_cost_line_count + range_count();
    }

    void fill_solver_on_row(row * row, lp_solver<T, X> *solver)  {
        if (row->m_name != m_cost_row_name) {
            solver->add_constraint(get_relation_from_row(row->m_type), row->m_right_side, row->m_index);
            for (auto s : row->m_row_columns) {
                lean_assert(m_columns.find(s.first) != m_columns.end());
                solver->set_row_column_coefficient(row->m_index, m_columns[s.first]->m_index, s.second);
            }
        } else {
            set_solver_cost(row, solver);
        }
    }

    T abs(T & t) { return t < numeric_traits<T>::zero() ? -t: t; }

    void fill_solver_on_rows(lp_solver<T, X> * solver) {
        for (auto row_it : m_rows) {
            fill_solver_on_row(row_it.second, solver);
        }
    }


    void fill_solver_on_columns(lp_solver<T, X> * solver){
        for (auto s : m_columns) {
            mps_reader::column * col = s.second;
            unsigned index = col->m_index;
            set_boundary_for_column(index, col->m_bound, solver);
            // optional call
            solver->give_symbolic_name_to_column(col->m_name, col->m_index);
        }
    }

    void fill_solver(lp_solver<T, X> *solver) {
        fill_solver_on_rows(solver);
        fill_solver_on_columns(solver);
    }

    void set_solver_cost(row * row, lp_solver<T, X> *solver) {
        for (auto s : row->m_row_columns) {
            std::string name = s.first;
            lean_assert(m_columns.find(name) != m_columns.end());
            mps_reader::column * col = m_columns[name];
            solver->set_cost_for_column(col->m_index, s.second);
        }
    }

public:

    void set_message_stream(std::ostream * o) {
        lean_assert(o != nullptr);
        m_message_stream = o;
    }
    vector<std::string> column_names() {
        vector<std::string> v;
        for (auto s : m_columns) {
            v.push_back(s.first);
        }
        return v;
    }

    ~mps_reader() {
        for (auto s : m_rows) {
            delete s.second;
        }
        for (auto s : m_columns) {
            auto col = s.second;
            auto b = col->m_bound;
            if (b != nullptr) {
                delete b;
            }
            delete col;
        }
    }

    mps_reader(std::string file_name):
        m_is_OK(true),
        m_file_name(file_name), 
        m_file_stream(file_name),
        m_cost_line_count(0),
        m_line_number(0),
        m_message_stream(& std::cout) {}
    void read() {
        if (!m_file_stream.is_open()){
            set_m_ok_to_false();
            return;
        }

        read_name();
        read_rows();
        read_columns();
        read_rhs();
        if (m_line.find("BOUNDS") == 0) {
            read_bounds();
            read_ranges();
        } else  if (m_line.find("RANGES") == 0) {
            read_ranges();
            read_bounds();
        }
    }

    bool is_ok()  {
        return m_is_OK;
    }

    lp_solver<T, X> * create_solver(bool dual) {
        lp_solver<T, X> * solver = dual? (lp_solver<T, X>*)new lp_dual_simplex<T, X>() : new lp_primal_simplex<T, X>();
        fill_solver(solver);
        return solver;
    }

    lconstraint_kind get_lar_relation_from_row(row_type rt) {
        switch (rt) {
        case Less_or_equal: return LE;
        case Greater_or_equal: return GE;
        case Equal: return EQ;
        default:
            (*m_message_stream) << "Unexpected rt " << rt << std::endl;
            set_m_ok_to_false();
            throw;
        }
    }

    unsigned get_var_index(std::string s) {
        auto it = m_names_to_var_index.find(s);
        if (it != m_names_to_var_index.end())
            return it->second;
        unsigned ret = static_cast<unsigned>(m_names_to_var_index.size());
        m_names_to_var_index[s] = ret;
        return ret;
    }
    
    void fill_lar_solver_on_row(row * row, lar_solver *solver)  {
        if (row->m_name != m_cost_row_name) {
            auto kind = get_lar_relation_from_row(row->m_type);
            vector<std::pair<mpq, var_index>> ls;
            for (auto s : row->m_row_columns) {
                var_index i = solver->add_var(get_var_index(s.first));
                ls.push_back(std::make_pair(s.second, i));
            }
            solver->add_constraint(ls, kind, row->m_right_side);
        } else {
            // ignore the cost row
        }
    }


    void fill_lar_solver_on_rows(lar_solver * solver) {
        for (auto row_it : m_rows) {
            fill_lar_solver_on_row(row_it.second, solver);
        }
    }

    void create_low_constraint_for_var(column* col, bound * b, lar_solver *solver) {
        vector<std::pair<mpq, var_index>> ls;
        var_index i = solver->add_var(col->m_index);
        ls.push_back(std::make_pair(numeric_traits<T>::one(), i));
        solver->add_constraint(ls, GE, b->m_low);
    }

    void create_upper_constraint_for_var(column* col, bound * b, lar_solver *solver) {
        var_index i = solver->add_var(col->m_index);
        vector<std::pair<mpq, var_index>> ls;
        ls.push_back(std::make_pair(numeric_traits<T>::one(), i));
        solver->add_constraint(ls, LE, b->m_upper);
    }

    void create_equality_contraint_for_var(column* col, bound * b, lar_solver *solver) {
        var_index i = solver->add_var(col->m_index);
        vector<std::pair<mpq, var_index>> ls;
        ls.push_back(std::make_pair(numeric_traits<T>::one(), i));
        solver->add_constraint(ls, EQ, b->m_fixed_value);
    }

    void fill_lar_solver_on_columns(lar_solver * solver) {
        for (auto s : m_columns) {
            mps_reader::column * col = s.second;
            solver->add_var(col->m_index);
            auto b = col->m_bound;
            if (b == nullptr) return;

            if (b->m_free) continue;

            if (b->m_low_is_set) {
                create_low_constraint_for_var(col, b, solver);
            }
            if (b->m_upper_is_set) {
                create_upper_constraint_for_var(col, b, solver);
            }
            if (b->m_value_is_fixed) {
                create_equality_contraint_for_var(col, b, solver);
            }
        }
    }


    void fill_lar_solver(lar_solver * solver) {
        fill_lar_solver_on_columns(solver);
        fill_lar_solver_on_rows(solver);
    }

    lar_solver * create_lar_solver() {
        lar_solver * solver =  new lar_solver();
        fill_lar_solver(solver);
        return solver;
    }
};
}
