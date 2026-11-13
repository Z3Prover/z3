/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    qfslia_tactic.cpp

Abstract:

    Regular-preimage preprocessing and SMT solving for QF_SLIA.

--*/
#include "tactic/smtlogics/qfslia_tactic.h"
#include "ast/arith_decl_plugin.h"
#include "ast/for_each_expr.h"
#include "ast/seq_decl_plugin.h"
#include "ast/simplifiers/seq_regular_simplifier.h"
#include "params/smt_params_helper.hpp"
#include "tactic/core/elim_uncnstr_tactic.h"
#include "tactic/core/simplify_tactic.h"
#include "tactic/dependent_expr_state_tactic.h"
#include "tactic/goal_util.h"
#include "tactic/smtlogics/qflia_tactic.h"
#include "tactic/smtlogics/smt_tactic.h"
#include "tactic/tactical.h"

namespace {
class is_qfslia_probe : public probe {
    struct visitor {
        struct unsupported {};
        ast_manager& m;
        seq_util u;
        arith_util a;
        bool has_strings = false;

        visitor(ast_manager& m): m(m), u(m), a(m) {}

        void operator()(var*) { throw unsupported(); }
        void operator()(quantifier*) { throw unsupported(); }
        void operator()(app* n) {
            sort* s = n->get_sort(), *seq_sort = nullptr;
            has_strings |= u.is_string(s);
            if (!m.is_bool(n) && !a.is_int(n) && !u.is_string(s) && !u.is_char(s) &&
                !(u.is_re(s, seq_sort) && u.is_string(seq_sort)))
                throw unsupported();
            family_id fid = n->get_family_id();
            if (fid == m.get_basic_family_id() || fid == u.get_family_id() ||
                fid == u.get_char_family_id() || is_uninterp_const(n))
                return;
            if (fid != a.get_family_id())
                throw unsupported();
            switch (n->get_decl_kind()) {
            case OP_NUM:
            case OP_LE: case OP_GE: case OP_LT: case OP_GT:
            case OP_ADD: case OP_SUB: case OP_UMINUS:
                return;
            case OP_MUL: {
                unsigned non_numerals = 0;
                for (expr* arg : *n)
                    non_numerals += !a.is_numeral(arg);
                if (non_numerals <= 1)
                    return;
                break;
            }
            case OP_IDIV: case OP_MOD: case OP_REM:
                if (n->get_num_args() == 2 && a.is_numeral(n->get_arg(1)))
                    return;
                break;
            default:
                break;
            }
            throw unsupported();
        }
    };
public:
    result operator()(goal const& g) override {
        visitor v(g.m());
        try {
            for_each_expr_at(v, g);
            return v.has_strings;
        }
        catch (visitor::unsupported const&) {
            return false;
        }
    }
};

class automatic_seq_regular_tactic : public dependent_expr_state_tactic {
    params_ref m_params;
public:
    automatic_seq_regular_tactic(ast_manager& m, params_ref const& p):
        dependent_expr_state_tactic(m, p,
            [](ast_manager& m, params_ref const& p, dependent_expr_state& s) -> dependent_expr_simplifier* {
                return alloc(seq_regular_simplifier, m, p, s, true);
            }), m_params(p) {}

    void updt_params(params_ref const& p) override {
        m_params.append(p);
        dependent_expr_state_tactic::updt_params(p);
    }

    void collect_param_descrs(param_descrs& r) override {
        dependent_expr_state_tactic::collect_param_descrs(r);
        smt_params_helper::collect_param_descrs(r);
    }

    tactic* translate(ast_manager& m) override {
        return alloc(automatic_seq_regular_tactic, m, m_params);
    }

    void operator()(goal_ref const& in, goal_ref_buffer& result) override {
        smt_params_helper params(m_params);
        bool has_strings = false;
        bool eligible = params.seq_regular() && params.string_solver() == "nseq" && !in->proofs_enabled();
        for (unsigned i = 0; eligible && i < in->size(); ++i) {
            eligible = !::has_quantifiers(in->form(i));
            if (!has_strings)
                has_strings = seq_regular_simplifier::has_string_terms(in->m(), in->form(i));
        }
        if (eligible && has_strings)
            dependent_expr_state_tactic::operator()(in, result);
        else
            result.push_back(in.get());
    }
};
}

probe* mk_is_qfslia_probe() {
    return alloc(is_qfslia_probe);
}

tactic* mk_qfslia_tactic(ast_manager& m, params_ref const& p) {
    // Regular preimages need the original selectors, before eager rewriting.
    return using_params(and_then(alloc(automatic_seq_regular_tactic, m, p),
                                 mk_simplify_tactic(m, p),
                                 mk_elim_uncnstr_seq_concat_tactic(m, p),
                                 mk_preamble_tactic(m),
                                 mk_lazy_tactic(m, p, [](auto& m, auto const& p) { return mk_smt_tactic(m, p); })),
                        p);
}
