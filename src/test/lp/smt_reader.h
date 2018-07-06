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

// reads an MPS file reperesenting a Mixed Integer Program
#include <string>
#include <vector>
#include <unordered_map>
#include "util/lp/lp_primal_simplex.h"
#include "util/lp/lp_dual_simplex.h"
#include "util/lp/lar_solver.h"
#include <iostream>
#include <fstream>
#include <functional>
#include <algorithm>
#include "util/lp/mps_reader.h"
#include "util/lp/ul_pair.h"
#include "util/lp/lar_constraints.h"
#include <sstream>
#include <cstdlib>
namespace lp {

    template<typename T>
    T from_string(const std::string& str) {
        std::istringstream ss(str);
        T ret;
        ss >> ret;
        return ret;
    }

    class smt_reader {
    public:
        struct lisp_elem {
            std::string m_head;
            std::vector<lisp_elem> m_elems;
            void print() {
                if (m_elems.size()) {
                    std::cout << '(';
                    std::cout << m_head << ' ';
                    for (auto & el : m_elems)
                        el.print();

                    std::cout << ')';
                } else {
                    std::cout << " " << m_head;
                }
            }
            unsigned size() const { return static_cast<unsigned>(m_elems.size()); }
            bool is_simple() const { return size() == 0; }
        };
        struct formula_constraint {
            lconstraint_kind m_kind;
            std::vector<std::pair<mpq, std::string>> m_coeffs;
            mpq m_right_side;
            void add_pair(mpq c, std::string name) {
                m_coeffs.push_back(make_pair(c, name));
            }
            formula_constraint() : m_right_side(numeric_traits<mpq>::zero()) {}
        };

        lisp_elem m_formula_lisp_elem;

        std::unordered_map<std::string, unsigned> m_name_to_var_index;
        std::vector<formula_constraint>           m_constraints;
        bool                                      m_is_OK;
        unsigned                                  m_line_number;
        std::string                               m_file_name;
        std::ifstream                             m_file_stream;
        std::string                               m_line;
        smt_reader(std::string file_name):
            m_is_OK(true),
            m_line_number(0),
            m_file_name(file_name), 
            m_file_stream(file_name) {
        }

        void set_error() {
            std::cout << "setting error" << std::endl;
            m_is_OK = false;
        }

        bool is_ok() {
            return m_is_OK;
        }

        bool prefix(const char * pr) {
            return m_line.find(pr) == 0;
        }

        int first_separator() {
            unsigned blank_pos = static_cast<unsigned>(m_line.find(' '));
            unsigned br_pos = static_cast<unsigned>(m_line.find('('));
            unsigned reverse_br_pos = static_cast<unsigned>(m_line.find(')'));
            return std::min(blank_pos, std::min(br_pos, reverse_br_pos));
        }

        void fill_lisp_elem(lisp_elem & lm) {
            if (m_line[0] == '(')
                fill_nested_elem(lm);
            else
                fill_simple_elem(lm);
        }

        void fill_simple_elem(lisp_elem & lm) {
            int separator = first_separator();
            lp_assert(-1 != separator && separator != 0);
            lm.m_head = m_line.substr(0, separator);
            m_line = m_line.substr(separator);
        }

        void fill_nested_elem(lisp_elem & lm) {
            lp_assert(m_line[0] == '(');
            m_line = m_line.substr(1);
            int separator = first_separator();
            lm.m_head = m_line.substr(0, separator);
            m_line = m_line.substr(lm.m_head.size());
            eat_blanks();
            while (m_line.size()) {
                if (m_line[0] == '(') {
                    lisp_elem el;
                    fill_nested_elem(el);
                    lm.m_elems.push_back(el);
                } else {
                    if (m_line[0] == ')') {
                        m_line = m_line.substr(1);
                        break;
                    }
                    lisp_elem el;
                    fill_simple_elem(el);
                    lm.m_elems.push_back(el);
                }
                eat_blanks();
            }
        }

        void eat_blanks() {
            while (m_line.size()) {
                if (m_line[0] == ' ')
                    m_line = m_line.substr(1);
                else
                    break;
            }
        }

        void fill_formula_elem() {
            fill_lisp_elem(m_formula_lisp_elem);
        }

        void parse_line() {
            if (m_line.find(":formula") == 0) {
                int first_br = static_cast<int>(m_line.find('('));
                if (first_br == -1) {
                    std::cout << "empty formula" << std::endl;
                    return;
                }
                m_line = m_line.substr(first_br);
                fill_formula_elem();
            }
        }

        void set_constraint_kind(formula_constraint & c, lisp_elem & el) {
            if (el.m_head == "=") {
                c.m_kind = EQ;
            } else if (el.m_head == ">=") {
                c.m_kind = GE;
            } else if (el.m_head == "<=") {
                c.m_kind = LE;
            } else if (el.m_head == ">") {
                c.m_kind = GT;
            } else if (el.m_head == "<") {
                c.m_kind = LT;
            } else {
                std::cout << "kind " << el.m_head << " is not supported " << std::endl;
                set_error();
            }
        }

        void adjust_rigth_side(formula_constraint & /* c*/, lisp_elem & /*el*/) {
            // lp_assert(el.m_head == "0"); // do nothing for the time being
        }

        void set_constraint_coeffs(formula_constraint & c, lisp_elem & el) {
            lp_assert(el.m_elems.size() == 2);
            set_constraint_coeffs_on_coeff_element(c, el.m_elems[0]);
            adjust_rigth_side(c, el.m_elems[1]);
        }


        bool is_integer(std::string & s) {
            if (s.size() == 0) return false;
            return atoi(s.c_str()) != 0 || isdigit(s.c_str()[0]);
        }

        void add_complex_sum_elem(formula_constraint & c, lisp_elem & el) {
            if (el.m_head == "*") {
                add_mult_elem(c, el.m_elems);
            } else if (el.m_head == "~") {
                lisp_elem & minel = el.m_elems[0];
                lp_assert(minel.is_simple());
                c.m_right_side += mpq(str_to_int(minel.m_head));
            } else {
                std::cout << "unexpected input " << el.m_head << std::endl;
                set_error();
                return;
            }
        }

        std::string get_name(lisp_elem & name) {
            lp_assert(name.is_simple());
            lp_assert(!is_integer(name.m_head));
            return name.m_head;
        }


        void add_mult_elem(formula_constraint & c, std::vector<lisp_elem> & els) {
            lp_assert(els.size() == 2);
            mpq coeff = get_coeff(els[0]);
            std::string col_name = get_name(els[1]);
            c.add_pair(coeff, col_name);
        }

        mpq get_coeff(lisp_elem & le) {
            if (le.is_simple()) {
                return mpq(str_to_int(le.m_head));
            } else {
                lp_assert(le.m_head == "~");
                lp_assert(le.size() == 1);
                lisp_elem & el = le.m_elems[0];
                lp_assert(el.is_simple());
                return -mpq(str_to_int(el.m_head));
            }
        }

        int str_to_int(std::string & s) {
            lp_assert(is_integer(s));
            return atoi(s.c_str());
        }

        void add_sum_elem(formula_constraint & c, lisp_elem & el) {
            if (el.size()) {
                add_complex_sum_elem(c, el);
            } else {
                lp_assert(is_integer(el.m_head));
                int v = atoi(el.m_head.c_str());
                mpq vr(v);
                c.m_right_side -= vr;
            }
        }

        void add_sum(formula_constraint & c, std::vector<lisp_elem> & sum_els) {
            for (auto & el : sum_els)
                add_sum_elem(c, el);
        }

        void set_constraint_coeffs_on_coeff_element(formula_constraint & c, lisp_elem & el) {
            if (el.m_head == "*") {
                add_mult_elem(c, el.m_elems);
            } else if (el.m_head == "+") {
                add_sum(c, el.m_elems);
            } else {
                lp_assert(false); // unexpected input
            }
        }

        void create_constraint(lisp_elem & el) {
            formula_constraint c;
            set_constraint_kind(c, el);
            set_constraint_coeffs(c, el);
            m_constraints.push_back(c);
        }

        void fill_constraints() {
            if (m_formula_lisp_elem.m_head != "and") {
                std::cout << "unexpected top element " << m_formula_lisp_elem.m_head << std::endl;
                set_error();
                return;
            }
            for (auto & el : m_formula_lisp_elem.m_elems)
                create_constraint(el);
        }

        void read() {
            if (!m_file_stream.is_open()){
                std::cout << "cannot open file " << m_file_name << std::endl;
                set_error();
                return;
            }
            while (m_is_OK && getline(m_file_stream, m_line)) {
                parse_line();
                m_line_number++;
            }

            m_file_stream.close();
            fill_constraints();
        }

        /*
        void fill_lar_solver_on_row(row * row, lar_solver *solver)  {
            if (row->m_name != m_cost_row_name) {
                lar_constraint c(get_lar_relation_from_row(row->m_type), row->m_right_side);
                for (auto s : row->m_row_columns) {
                    var_index i = solver->add_var(s.first);
                    c.add_variable_to_constraint(i, s.second);
                }
                solver->add_constraint(&c);
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
            lar_constraint c(GE, b->m_low);
            var_index i = solver->add_var(col->m_name);
            c.add_variable_to_constraint(i, numeric_traits<T>::one());
            solver->add_constraint(&c);
        }

        void create_upper_constraint_for_var(column* col, bound * b, lar_solver *solver) {
            lar_constraint c(LE, b->m_upper);
            var_index i = solver->add_var(col->m_name);
            c.add_variable_to_constraint(i, numeric_traits<T>::one());
            solver->add_constraint(&c);
        }

        void create_equality_contraint_for_var(column* col, bound * b, lar_solver *solver) {
            lar_constraint c(EQ, b->m_fixed_value);
            var_index i = solver->add_var(col->m_name);
            c.add_variable_to_constraint(i, numeric_traits<T>::one());
            solver->add_constraint(&c);
        }

        void fill_lar_solver_on_columns(lar_solver * solver) {
            for (auto s : m_columns) {
                mps_reader::column * col = s.second;
                solver->add_var(col->m_name);
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
        */

        unsigned register_name(std::string s) {
            auto it = m_name_to_var_index.find(s);
            if (it!= m_name_to_var_index.end())
                return it->second;

            unsigned ret = static_cast<unsigned>(m_name_to_var_index.size());
            m_name_to_var_index[s] = ret;
            return ret;
        }
        
        void add_constraint_to_solver(lar_solver * solver, formula_constraint & fc) {
            vector<std::pair<mpq, var_index>> ls;
            for (auto & it : fc.m_coeffs) {
                ls.push_back(std::make_pair(it.first, solver->add_var(register_name(it.second), false)));
            }
            solver->add_constraint(ls, fc.m_kind, fc.m_right_side);
        }

        void fill_lar_solver(lar_solver * solver) {
            for (formula_constraint & fc : m_constraints)
                add_constraint_to_solver(solver, fc);
        }


        lar_solver * create_lar_solver() {
            lar_solver * ls = new lar_solver();
            fill_lar_solver(ls);
            return ls;
        }
    };
}
