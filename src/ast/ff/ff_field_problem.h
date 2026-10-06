/*++
Copyright (c) 2026 Romain Soulat

Module Name:

    ff_field_problem.h

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
        friend class field_problem;
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
    // Generic rewriting and solve-eqs run on a private dependent-expression state;
    // its model reconstruction trail restores eliminated constants. Dependencies
    // use private labels mapped to the exact signed input premises.
    // SAT here means a field candidate: the frontend must enforce congruence,
    // other-theory semantics and finite-field model arrangements before accepting.
    class field_problem {
        struct imp;
        std::unique_ptr<imp> m_imp;
    public:
        field_problem(ast_manager &m, sort *field, params_ref const &p,
                      ff_encoding_cache *cache = nullptr, basis_cache *basis = nullptr);
        ~field_problem();
        void add(expr *a, expr *b, bool equality);
        // May throw exhausted on resource limits, just like the algebra engine.
        // SAT candidates are rechecked against every supplied original constraint.
        lbool check();
        rational value(expr *term);
        expr *premise(unsigned index) const;
        // Exact input indices supporting UNSAT. These are explanations, NOT
        // checked proof objects. A future evidence recorder must also certify
        // normalization, substitution and the frontend's premise justifications.
        std::set<unsigned> const &conflict() const;
        void collect_statistics(statistics &st) const;
        // True only when encoding (not search) exceeded the polynomial limit.
        bool encoding_limit_hit() const;
        unsigned encoding_steps() const;
    };

}
