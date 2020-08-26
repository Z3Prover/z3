/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    euf_model.cpp

Abstract:

    Model building for EUF solver plugin.

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-25

--*/

#include "ast/ast_pp.h"
#include "sat/euf/euf_solver.h"
#include "model/value_factory.h"

namespace euf {

    model_converter* solver::get_model() {
        sat::th_dependencies deps;
#if 0
        collect_dependencies(deps);
        sort_dependencies(deps);
#endif
        expr_ref_vector values(m);
        dependencies2values(deps, values);
        return nullptr;
    }

    void solver::collect_dependencies(sat::th_dependencies& deps) {

    }

    void solver::sort_dependencies(sat::th_dependencies& deps) {

    }

    void solver::dependencies2values(sat::th_dependencies& deps, expr_ref_vector& values) {

        user_sort_factory user_sort(m);
        for (enode* n : deps) {
            unsigned id = n->get_root()->get_owner_id();
            if (values.get(id) != nullptr)
                continue;
            expr* e = n->get_owner();
            values.reserve(id + 1);
            if (m.is_bool(e)) {
                switch (s().value(m_expr2var.to_bool_var(e))) {
                case l_true:
                    values.set(id, m.mk_true());
                    break;
                default:
                    values.set(id, m.mk_false());
                    break;
                }
                continue;
            }
            auto* mb = get_model_builder(e);
            if (mb) 
                mb->add_value(n, values);
            else if (m.is_uninterp(m.get_sort(e))) {
                expr* v = user_sort.get_fresh_value(m.get_sort(e));
                values.set(id, v);
            }
            else {
                IF_VERBOSE(1, verbose_stream() << "no model values created for " << mk_pp(e, m) << "\n");
            }
                
        }
        NOT_IMPLEMENTED_YET();
    }
}
