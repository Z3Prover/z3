/*++
Copyright (c) 2010 Microsoft Corporation

Module Name:

    array_property_recognizer.cpp

Abstract:

    <abstract>

Author:

    Nikolaj Bjorner (nbjorner) 2010-16-12

Revision History:

--*/

#include"array_decl_plugin.h"
#include"array_property_recognizer.h"
#include"for_each_expr.h"


array_property_recognizer::array_property_recognizer(ast_manager& m):
    m_manager(m) {}

namespace is_array_property_ns {
    struct bad {};
    class proc {
        ast_manager& m_manager;
        family_id    m_fid;
        bool         m_has_quantifier;

        void check_array_sort(expr* n) {
            if (is_sort_of(m_manager.get_sort(n), m_fid, ARRAY_SORT)) {
                throw bad();
            }            
        }

    public:
        proc(ast_manager& m) : 
            m_manager(m), 
            m_fid(m.get_family_id("array")), 
            m_has_quantifier(false) {}

        bool has_quantifier() const { return m_has_quantifier; }

        void operator()(var* n) {
            check_array_sort(n);
        }

        void operator()(quantifier * ) { 
            m_has_quantifier = true; 
        }

        void operator()(app* n) {
            unsigned num_args = n->get_num_args();
            if (m_manager.is_eq(n) || m_manager.is_distinct(n)) {
                return;
            }
            family_id fid = n->get_family_id();
            if (fid == m_fid) {                
                switch(n->get_decl_kind()) {
                case OP_STORE:
                    for (unsigned i = 1; i + 1 < num_args; ++i) {
                        check_array_sort(n->get_arg(i));
                    }
                    return;
                case OP_SELECT:
                    for (unsigned i = 1; i < num_args; ++i) {
                        check_array_sort(n->get_arg(i));
                    }
                    return;
                case OP_CONST_ARRAY:
                case OP_ARRAY_MAP:
                    return;
                default:
                    throw bad();
                }                
            }
            // arrays cannot be arguments of other functions.
            for (unsigned i = 0; i < num_args; ++i) {
                check_array_sort(n->get_arg(i));
            }
        }
    };
};

bool array_property_recognizer::operator()(unsigned num_fmls, expr* const* fmls) {
    is_array_property_ns::proc p(m_manager);
    try {
        for (unsigned i = 0; i < num_fmls; ++i) {
            for_each_expr(p, fmls[i]);
        }
    }
    catch (is_array_property_ns::bad) {
        return false;
    }
    return p.has_quantifier();
}


