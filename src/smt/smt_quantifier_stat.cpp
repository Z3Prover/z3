/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_quantifier_stat.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-20.

Revision History:

--*/
#include"smt_quantifier_stat.h"

namespace smt {

    quantifier_stat::quantifier_stat(unsigned generation):
        m_size(0),
        m_depth(0),
        m_generation(generation),
        m_case_split_factor(1),
        m_num_nested_quantifiers(0),
        m_num_instances(0),
        m_num_instances_curr_search(0),
        m_num_instances_curr_branch(0),
        m_max_generation(0),
        m_max_cost(0.0f) {
    }

    quantifier_stat_gen::quantifier_stat_gen(ast_manager & m, region & r):
        m_manager(m),
        m_region(r) {
    }

    void quantifier_stat_gen::reset() {
        m_already_found.reset();
        m_todo.reset();
        m_case_split_factor = 1;
    }

    quantifier_stat * quantifier_stat_gen::operator()(quantifier * q, unsigned generation) {
        reset();
        quantifier_stat * r = new (m_region) quantifier_stat(generation);
        m_todo.push_back(entry(q->get_expr()));
        while (!m_todo.empty()) {
            entry & e       = m_todo.back();
            expr * n        = e.m_expr;
            unsigned depth  = e.m_depth;
            bool depth_only = e.m_depth_only;
            m_todo.pop_back();
            unsigned old_depth;
            if (m_already_found.find(n, old_depth)) {
                if (old_depth >= depth)
                    continue;
                depth_only  = true;
            }
            m_already_found.insert(n, depth);
            if (depth >= r->m_depth) 
                r->m_depth = depth;
            if (!depth_only) {
                r->m_size++;
                if (is_quantifier(n))
                    r->m_num_nested_quantifiers ++;
                if (is_app(n) && to_app(n)->get_family_id() == m_manager.get_basic_family_id()) {
                    unsigned num_args = to_app(n)->get_num_args();
                    // Remark: I'm approximating the case_split factor.
                    // I'm also ignoring the case split factor due to theories.
                    switch (to_app(n)->get_decl_kind()) {
                    case OP_OR:
                        if (depth == 0)
                            m_case_split_factor *= num_args;
                        else
                            m_case_split_factor *= (num_args + 1);
                        break;
                    case OP_AND:
                        if (depth > 0)
                            m_case_split_factor *= (num_args + 1);
                        break;
                    case OP_IFF:
                        if (depth == 0)
                            m_case_split_factor *= 4;
                        else
                            m_case_split_factor *= 9;
                        break;
                    case OP_ITE:
                        if (depth == 0)
                            m_case_split_factor *= 4;
                        else
                            m_case_split_factor *= 9;
                        break;
                    default:
                        break;
                    }
                }
            }
            if (is_app(n)) {
                unsigned j = to_app(n)->get_num_args();
                while (j > 0) {
                    --j;
                    m_todo.push_back(entry(to_app(n)->get_arg(j), depth + 1, depth_only));
                }
            }
        }
        r->m_case_split_factor = m_case_split_factor.get_value();
        return r;
    }

};

