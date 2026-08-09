/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_membership_length_constraints.h

Abstract:

    Consistency checks for sequence membership constraints based on lengths.

--*/
#pragma once

#include "ast/ast.h"
#include "util/lbool.h"
#include "util/vector.h"
#include <tuple>

class seq_rewriter;

namespace seq {

class membership_length_constraints {
public:
    using constraint = std::tuple<expr_ref, expr_ref, void*>;
    using constraint_vector = vector<constraint>;

    struct atom {
        expr_ref var;
        expr_ref elem;

        atom(ast_manager& m, expr* var, expr* elem) :
            var(var, m), elem(elem, m) {}

        bool is_var() const { return var != nullptr; }
    };

    using atom_vector = vector<atom>;
    using atom_vectors = vector<atom_vector>;

    struct bucket {
        expr* var;
        expr* state;
        expr* target;
        void* dependency;
    };

    using bucket_vector = svector<bucket>;
    using bucket_vectors = vector<bucket_vector>;

private:
    seq_rewriter& m_rw;
    ptr_vector<void> m_core;

public:
    explicit membership_length_constraints(seq_rewriter& rw) : m_rw(rw) {}

    // Return l_false when the constraints are inconsistent and populate core().
    // Return l_true when no contradiction was found.
    lbool check(constraint_vector const& constraints, atom_vectors const& atoms,
                bucket_vectors const& buckets);

    ptr_vector<void> const& core() const { return m_core; }
};

}
