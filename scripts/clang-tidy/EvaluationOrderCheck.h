// Copyright (c) 2026 Microsoft Corporation
// SPDX-License-Identifier: MIT
#pragma once

#include "clang-tidy/ClangTidyCheck.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallVector.h"

namespace clang::tidy::z3 {

class EvaluationOrderCheck : public ClangTidyCheck {
public:
    using ClangTidyCheck::ClangTidyCheck;
    bool isLanguageVersionSupported(LangOptions const& opts) const override { return opts.CPlusPlus17; }
    void registerMatchers(ast_matchers::MatchFinder* finder) override;
    void check(ast_matchers::MatchFinder::MatchResult const& result) override;
    void onEndOfTranslationUnit() override;

protected:
    struct Call {
        Expr const* expr;
        FunctionDecl const* function;
    };
    virtual bool effect_root(FunctionDecl const* function) = 0;
    virtual void report(Expr const* expr, Call first, Call next) = 0;
    virtual bool check_operators() const { return false; }

private:
    class Collector;
    ASTContext* m_ast = nullptr;
    llvm::SmallVector<FunctionDecl const*, 64> m_functions;
    llvm::SmallVector<Expr const*, 16> m_initializers;
    llvm::DenseMap<FunctionDecl const*, llvm::SmallVector<Call, 8>> m_calls;
    llvm::DenseMap<FunctionDecl const*, bool> m_effects;

    llvm::SmallVector<Call, 8> const& calls(FunctionDecl const* function);
    bool has_effect(FunctionDecl const* function);
    Call first_effect(Expr const* expr);
    void check_arguments(Expr const* expr, llvm::ArrayRef<Expr const*> args);
};

}
