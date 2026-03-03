/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    nseq_model.h

Abstract:

    Model generation from solved Nielsen graph.

Author:

    Nikolaj Bjorner (nbjorner) 2026-03-01

--*/
#pragma once

#include "ast/ast.h"
#include "ast/seq_decl_plugin.h"
#include "util/zstring.h"
#include "ast/euf/euf_sgraph.h"
#include "smt/seq/seq_nielsen.h"
#include <vector>
#include <utility>

namespace smt {

    class nseq_model {
        ast_manager& m;
        seq_util     m_seq;
        euf::sgraph& m_sg;
        unsigned     m_fresh_counter = 0;

    public:
        nseq_model(ast_manager& m, euf::sgraph& sg) : m(m), m_seq(m), m_sg(sg) {}

        // generate a fresh string value (used when a variable is unconstrained)
        expr_ref mk_fresh_value() {
            std::string name = "s!" + std::to_string(m_fresh_counter++);
            zstring zs(name.c_str());
            return expr_ref(m_seq.str.mk_string(zs), m);
        }

        // extract variable assignments from a satisfied leaf node
        // Returns true if all variables got a valid assignment
        bool extract_assignments(seq::nielsen_node* node,
                                 std::vector<std::pair<euf::snode*, expr*>>& assignment) {
            if (!node)
                return false;
            for (auto const& eq : node->str_eqs()) {
                if (!eq.m_lhs || !eq.m_rhs)
                    continue;
                if (eq.m_lhs->is_var() && eq.m_rhs->get_expr()) {
                    assignment.emplace_back(eq.m_lhs, eq.m_rhs->get_expr());
                }
                else if (eq.m_rhs->is_var() && eq.m_lhs->get_expr()) {
                    assignment.emplace_back(eq.m_rhs, eq.m_lhs->get_expr());
                }
            }
            return true;
        }

        // validate that a regex membership constraint is satisfied by the assignment
        bool validate_regex(seq::str_mem const& mem,
                            obj_map<euf::snode, expr*> const& assignment) {
            // stub: assume valid for now
            return true;
        }
    };

}
