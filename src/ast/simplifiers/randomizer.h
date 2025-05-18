
/*++
Copyright (c) 2025 Microsoft Corporation

Module Name:

    randomizer.h

Abstract:

    Simplifier that randomizes formulas by renaming uninterpreted functions and permuting arguments of associative and commutative functions.

Author:

    GitHub Copilot (2025)

--*/

#pragma once

#include "ast/ast.h"
#include "ast/ast_pp.h"
#include "ast/ast_translation.h"
#include "ast/simplifiers/dependent_expr_state.h"
#include "util/obj_hashtable.h"
#include <random>
#include <unordered_map>
#include <algorithm>

class randomizer_simplifier : public dependent_expr_simplifier {
    ast_manager& m;
    std::unordered_map<func_decl*, func_decl*> m_uf_map;
    std::mt19937 m_rng;

    func_decl* get_random_func_decl(func_decl* f) {
        auto it = m_uf_map.find(f);
        if (it != m_uf_map.end())
            return it->second;
        // Create a new random name
        std::string rand_name = f->name().str() + "_rand_" + std::to_string(m_rng());
        symbol new_sym(rand_name.c_str());
        func_decl* new_f = m.mk_func_decl(new_sym, f->get_arity(), f->domain(), f->range());
        m_uf_map[f] = new_f;
        return new_f;
    }

    expr_ref randomize(expr* e) {
        if (is_app(e)) {
            app* a = to_app(e);
            func_decl* f = a->get_decl();
            unsigned arity = a->get_num_args();
            std::vector<expr_ref> args;
            for (unsigned i = 0; i < arity; ++i)
                args.push_back(expr_ref(randomize(a->get_arg(i)), m));

            // If uninterpreted function, rename
            if (f->get_family_id() == null_family_id) {
                f = get_random_func_decl(f);
            }

            // If associative and commutative, permute arguments
            if (f->is_associative() && f->is_commutative() && arity > 1) {
                std::shuffle(args.begin(), args.end(), m_rng);
            }
            return expr_ref(m.mk_app(f, args.size(), args.data()), m);
        } else if (is_quantifier(e)) {
            quantifier* q = to_quantifier(e);
            expr_ref body = randomize(q->get_expr());
            return expr_ref(m.update_quantifier(q, body), m);
        } else {
            return expr_ref(e, m);
        }
    }

public:
    randomizer_simplifier(ast_manager& m, dependent_expr_state& fmls)
        : dependent_expr_simplifier(m, fmls), m(m), m_rng(std::random_device{}()) {}

    char const* name() const override { return "randomizer"; }

    void reduce() override {
        for (unsigned idx : indices()) {
            auto d = m_fmls[idx];
            expr_ref new_fml = randomize(d.fml());
            m_fmls.update(idx, dependent_expr(m, new_fml, d.pr(), d.dep()));
        }
    }

    bool supports_proofs() const override { return true; }
};
