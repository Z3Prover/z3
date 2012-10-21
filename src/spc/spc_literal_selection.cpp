/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    spc_literal_selection.cpp

Abstract:

    Superposition Calculus Literal Selection

Author:

    Leonardo de Moura (leonardo) 2008-02-05.

Revision History:

--*/
#include"spc_literal_selection.h"
#include"expr_stat.h"

namespace spc {

    void diff_literal_selection::operator()(clause * cls) { 
        bool found = false;
        unsigned target = UINT_MAX;
        unsigned best_count = 0;
        unsigned num = cls->get_num_literals();
        for (unsigned i = 0; i < num; i++) {
            literal & l = cls->get_literal(i);
            if (l.sign()) {
                unsigned count;
                if (m_manager.is_eq(l.atom())) {
                    unsigned c1 = get_symbol_count(to_app(l.atom())->get_arg(0));
                    unsigned c2 = get_symbol_count(to_app(l.atom())->get_arg(1));
                    count = c1 >= c2 ? c1 - c2 : c2 - c1;
                }
                else {
                    count = get_symbol_count(l.atom());
                }
                if (count > best_count) {
                    found      = true;
                    target     = i;
                    best_count = count;
                }
            }
        }
        if (found)
            cls->select_literal(target);
    }

    void complex_literal_selection::operator()(clause * cls) { 
        // look for x != y
        unsigned num = cls->get_num_literals();
        for (unsigned i = 0; i < num; i++) {
            literal & l = cls->get_literal(i);
            if (l.sign() && m_manager.is_eq(l.atom()) && is_var(to_app(l.atom())->get_arg(0)) && is_var(to_app(l.atom())->get_arg(1))) {
                cls->select_literal(i);
                return;
            }
        }

        // look for min ground neg literal
        bool found = false;
        unsigned target = UINT_MAX;
        unsigned  best_count = UINT_MAX;
        for (unsigned i = 0; i < num; i++) {
            literal & l = cls->get_literal(i);
            if (l.sign() && is_ground(l.atom())) {
                unsigned count = get_symbol_count(l.atom());
                if (count < best_count) {
                    found      = true;
                    target     = i;
                    best_count = count;
                }
            }
        }
        
        if (found) {
            cls->select_literal(target);
            return;
        }        
        
        diff_literal_selection::operator()(cls);
    }

    void max_no_selection::operator()(clause * cls) {
        unsigned num_lits = cls->get_num_literals();
        for (unsigned i = 0; i < num_lits; i++) {
            literal const & l1 = cls->get_literal(i);
            if (!l1.sign()) {
                unsigned j = 0;
                for (; j < num_lits; j++) {
                    if (i != j) {
                        literal const & l2 = cls->get_literal(j);
                        if (!greater(m_order, l1, l2))
                            break;
                    }
                }
                if (j == num_lits)
                    return; // clause has maximal positive literal.
            }
        }
        diff_literal_selection::operator()(cls);
    }

};
