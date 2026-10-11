// Copyright (c) 2026 Microsoft Corporation
// SPDX-License-Identifier: MIT
#include "RandomOrderCheck.h"
#include "clang/AST/DeclTemplate.h"
#include "llvm/ADT/StringSwitch.h"

namespace clang::tidy::z3 {

bool RandomOrderCheck::effect_root(FunctionDecl const* function) {
    auto* method = dyn_cast<CXXMethodDecl>(function);
    if (!method)
        return llvm::StringSwitch<bool>(function->getQualifiedNameAsString())
            .Cases("rand", "std::rand", "rand_r", true)
            .Cases("random", "random_r", true)
            .Cases("drand48", "lrand48", "mrand48", true)
            .Cases("erand48", "nrand48", "jrand48", true)
            .Default(false);
    if (!method->isOverloadedOperator() || method->getOverloadedOperator() != OO_Call)
        return false;
    auto* record = method->getParent();
    if (auto* specialization = dyn_cast<ClassTemplateSpecializationDecl>(record))
        record = specialization->getSpecializedTemplate()->getTemplatedDecl();
    if (record->getQualifiedNameAsString() == "random_gen")
        return true;
    // Match declarations rather than library-specific implementations, including
    // std's inline ABI namespaces. Visible distribution/wrapper bodies are followed.
    return record->isInStdNamespace() &&
        llvm::StringSwitch<bool>(record->getName())
            .Cases("linear_congruential_engine", "mersenne_twister_engine", true)
            .Cases("subtract_with_carry_engine", "discard_block_engine", true)
            .Cases("independent_bits_engine", "shuffle_order_engine", "random_device", true)
            .Default(false);
}

void RandomOrderCheck::report(Expr const* expr, Call first, Call next) {
    diag(expr->getBeginLoc(), "random draws in separate arguments or operands have unspecified evaluation order; "
                             "draw the values in separate statements");
    diag(first.expr->getBeginLoc(), "call to %0 may consume random state", DiagnosticIDs::Note)
        << first.function;
    diag(next.expr->getBeginLoc(), "call to %0 may consume random state", DiagnosticIDs::Note)
        << next.function;
}
}
