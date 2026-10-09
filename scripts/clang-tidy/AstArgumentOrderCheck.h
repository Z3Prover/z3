// Copyright (c) 2026 Microsoft Corporation
// SPDX-License-Identifier: MIT
#pragma once

#include "clang-tidy/ClangTidyCheck.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallVector.h"

namespace clang::tidy::z3 {

class AstArgumentOrderCheck : public ClangTidyCheck {
public:
    using ClangTidyCheck::ClangTidyCheck;
    bool isLanguageVersionSupported(LangOptions const& opts) const override { return opts.CPlusPlus17; }
    void registerMatchers(ast_matchers::MatchFinder* finder) override;
    void check(ast_matchers::MatchFinder::MatchResult const& result) override;
    void onEndOfTranslationUnit() override;

private:
    struct Call {
        Expr const* expr;
        FunctionDecl const* function;
    };
    class Collector;
    ASTContext* m_ast = nullptr;
    llvm::SmallVector<FunctionDecl const*, 64> m_functions;
    llvm::SmallVector<Expr const*, 16> m_initializers;
    llvm::DenseMap<FunctionDecl const*, llvm::SmallVector<Call, 8>> m_calls;
    llvm::DenseMap<FunctionDecl const*, bool> m_allocates;

    llvm::SmallVector<Call, 8> const& calls(FunctionDecl const* function);
    bool allocates(FunctionDecl const* function);
    Call first_allocation(Expr const* expr);
    void check_arguments(Expr const* expr, llvm::ArrayRef<Expr const*> args);
};

}
