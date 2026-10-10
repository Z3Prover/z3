// Copyright (c) 2026 Microsoft Corporation
// SPDX-License-Identifier: MIT
#pragma once
#include "clang-tidy/ClangTidyCheck.h"
#include "llvm/ADT/SmallVector.h"

namespace clang::tidy::z3 {
class AstTupleOrderCheck : public ClangTidyCheck {
public:
    using ClangTidyCheck::ClangTidyCheck;
    void registerMatchers(ast_matchers::MatchFinder* finder) override;
    void check(ast_matchers::MatchFinder::MatchResult const& result) override;
    void onEndOfTranslationUnit() override;
private:
    struct Candidate {
        QualType type;
        SourceLocation location;
    };
    ASTContext* m_ast = nullptr;
    llvm::SmallVector<Candidate, 16> m_candidates;
};
}
