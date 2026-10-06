/*++
Copyright (c) 2026 Romain Soulat

Module Name:

    ff_solver.h

Abstract:

    Ground prime-field reasoning over AST terms, independent of SAT and SMT
    contexts. Frontends supply equality/disequality premises, justify foreign
    congruence, and arrange candidate values shared with other theories.

--*/
#pragma once
#include "ast/ff_decl_plugin.h"
#include "ast/rewriter/th_rewriter.h"
#include "math/ff/ff_polynomial.h"
#include <memory>

namespace ff {
    // Pure term encodings only; no assertions, assignments or conflict evidence.
    // A cache belongs to one manager/field. It pins its keys and may be shared
    // across sequential checks/scopes. Do not reset it while a solver borrows it.
    class ff_encoding_cache {
        struct imp;
        std::unique_ptr<imp> m_imp;
        friend class solver;
    public:
        ff_encoding_cache(ast_manager &m, sort *field);
        ~ff_encoding_cache();
        unsigned size() const;
        void reset();
    };

    // One field problem per check: add ground field constraints, call check once,
    // then consume either conflict indices or candidate values. Recreate the
    // problem for new assignments/scopes; only the pure encoding cache survives.
    // Foreign field terms are opaque leaves, NOT freely assignable UF models.
    // With solve_eqs enabled, rewriting and solve-eqs run on a private dependent-
    // expression state; its model trail restores eliminated constants. Tactic
    // pipelines disable this repeated preprocessing for their branch queries.
    // Dependencies
    // use private labels mapped to the exact signed input premises.
    // SAT here means a field candidate: the frontend must enforce congruence,
    // other-theory semantics and finite-field model arrangements before accepting.
    class solver {
        struct imp;
        std::unique_ptr<imp> m_imp;
    public:
        solver(ast_manager &m, sort *field, params_ref const &p,
                      ff_encoding_cache *cache = nullptr, basis_cache *basis = nullptr);
        ~solver();
        void add(expr *a, expr *b, bool equality, v_dependency *d);
        // May throw exhausted on resource limits, just like the algebra engine.
        // SAT candidates are rechecked against every supplied original constraint.
        lbool check();
        rational value(expr *term);
        // Exposes the manager that every dependency leaf passed to add() must
        // come from, and that conflict()'s pointer can be linearized with.
        // Callers may use their own opaque pointers (e.g. expr_dependency*) as
        // leaf values directly; this is also the manager threaded through the
        // solver's own polynomial/engine arithmetic, so no translation layer
        // sits between a caller's dependency and the conflict it may appear in.
        v_dependency_manager &dep_manager() const;
        // Exact input dependencies supporting UNSAT. This is an explanation, NOT
        // a checked proof object. A future evidence recorder must also certify
        // normalization, substitution and the frontend's premise justifications.
        v_dependency *conflict() const;
        void collect_statistics(statistics &st) const;
        // True only when encoding (not search) exceeded the polynomial limit.
        bool encoding_limit_hit() const;
        unsigned encoding_steps() const;
    };

}
