/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    smt_value_sort.cpp

Abstract:

    Determine if elements of a given sort can be values.

Author:

    Nikolaj Bjorner (nbjorner) 2012-11-25

Revision History:


--*/

#include "smt_value_sort.h"
#include "bv_decl_plugin.h"
#include "arith_decl_plugin.h"
#include "datatype_decl_plugin.h"

namespace smt {

        
    bool is_value_sort(ast_manager& m, sort* s) {
        arith_util arith(m);
        datatype_util data(m);
        bv_util bv(m);
        
        ptr_vector<sort> sorts;
        ast_mark mark;
        sorts.push_back(s);
        
        while (!sorts.empty()) {
            s = sorts.back();
            sorts.pop_back();
            if (mark.is_marked(s)) {
                continue;
            }
            mark.mark(s, true);
            if (arith.is_int_real(s)) {
                // simple
            }
            else if (m.is_bool(s)) {
                // simple
            }
            else if (bv.is_bv_sort(s)) {
                // simple
            }
            else if (data.is_datatype(s)) {
                ptr_vector<func_decl> const& cs = *data.get_datatype_constructors(s);
                for (unsigned i = 0; i < cs.size(); ++i) {
                    func_decl* f = cs[i];
                    for (unsigned j = 0; j < f->get_arity(); ++j) {
                        sorts.push_back(f->get_domain(j));
                    }
                }
            }
            else {
                return false;
            }
        }
        return true;        
    }

    bool is_value_sort(ast_manager& m, expr* e) {
        return is_value_sort(m, m.get_sort(e));
    }

}
