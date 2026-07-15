/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    bv1_blaster_tactic.cpp

Abstract:

    Probe for checking if a goal is in the QF_BV fragment that uses only =, extract, and concat.

Author:

    Leonardo (leonardo) 2011-10-25

Notes:

--*/
#include "tactic/bv/bv1_blaster_tactic.h"
#include "tactic/tactic.h"
#include "ast/bv_decl_plugin.h"
#include "ast/for_each_expr.h"

class is_qfbv_eq_probe : public probe {
    struct not_target : public std::exception {};

    struct visitor {
        family_id m_bv_fid;
        visitor(family_id bv_fid) : m_bv_fid(bv_fid) {}
        void operator()(var const* n) { throw not_target(); }
        void operator()(app const* n) {
            if (n->get_family_id() == m_bv_fid) {
                switch (n->get_decl_kind()) {
                case OP_BV_NUM:
                case OP_EXTRACT:
                case OP_CONCAT:
                    return;
                default:
                    throw not_target();
                }
            }
        }
        void operator()(quantifier const* n) { throw not_target(); }
    };

public:
    result operator()(goal const& g) override {
        bv_util util(g.m());
        expr_fast_mark1 visited;
        visitor proc(util.get_family_id());
        try {
            for (unsigned i = 0; i < g.size(); ++i)
                for_each_expr_core<visitor, expr_fast_mark1, false, true>(proc, visited, g.form(i));
        }
        catch (const not_target&) {
            return false;
        }
        return true;
    }
};

probe* mk_is_qfbv_eq_probe() {
    return alloc(is_qfbv_eq_probe);
}

