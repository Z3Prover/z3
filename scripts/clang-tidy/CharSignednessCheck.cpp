// Copyright (c) 2026 Microsoft Corporation
// SPDX-License-Identifier: MIT
#include "CharSignednessCheck.h"
#include "clang/AST/Expr.h"
#include "llvm/ADT/StringSwitch.h"

namespace clang::tidy::z3 {
using namespace ast_matchers;

namespace {
bool plain_char(QualType type) {
    return type->isSpecificBuiltinType(BuiltinType::Char_S) ||
           type->isSpecificBuiltinType(BuiltinType::Char_U);
}

bool negative_constant(Expr const* expr, ASTContext const& ast) {
    expr = expr->IgnoreParenImpCasts();
    if (expr->isValueDependent())
        return false;
    Expr::EvalResult value;
    if (expr->EvaluateAsInt(value, ast))
        return value.Val.getInt().isNegative();
    if (auto* choice = dyn_cast<ConditionalOperator>(expr))
        return negative_constant(choice->getTrueExpr(), ast) ||
               negative_constant(choice->getFalseExpr(), ast);
    return false;
}

bool ctype_function(FunctionDecl const* function) {
    // Only the one-argument C functions, not std::locale overloads or user methods.
    auto name = function->getQualifiedNameAsString();
    llvm::StringRef unqualified(name);
    unqualified.consume_front("std::");
    return function->getNumParams() == 1 &&
           function->getParamDecl(0)->getType()->isSpecificBuiltinType(BuiltinType::Int) &&
           llvm::StringSwitch<bool>(unqualified)
               .Cases("isalnum", "isalpha", "isblank", "iscntrl", true)
               .Cases("isdigit", "isgraph", "islower", "isprint", true)
               .Cases("ispunct", "isspace", "isupper", "isxdigit", true)
               .Cases("tolower", "toupper", true)
               .Default(false);
}
}

void CharSignednessCheck::registerMatchers(MatchFinder* finder) {
    finder->addMatcher(implicitCastExpr(unless(hasParent(explicitCastExpr())),
                                       unless(isExpansionInSystemHeader())).bind("conversion"), this);
    finder->addMatcher(callExpr(callee(functionDecl()), unless(isExpansionInSystemHeader())).bind("call"), this);
}

void CharSignednessCheck::check(MatchFinder::MatchResult const& result) {
    if (auto* cast = result.Nodes.getNodeAs<ImplicitCastExpr>("conversion")) {
        if (cast->getCastKind() == CK_IntegralCast && plain_char(cast->getType()) &&
            negative_constant(cast->getSubExpr(), *result.Context))
            diag(result.SourceManager->getExpansionLoc(cast->getExprLoc()), "negative value converted to plain 'char'; its numeric value depends on the platform's char signedness; use an explicitly signed type");
        return;
    }
    auto* call = result.Nodes.getNodeAs<CallExpr>("call");
    auto* function = call->getDirectCallee();
    if (!ctype_function(function) || call->getNumArgs() != 1)
        return;
    auto* arg = call->getArg(0)->IgnoreParenImpCasts();
    // Casting to int does not make a negative byte a valid ctype argument.
    while (auto* cast = dyn_cast<ExplicitCastExpr>(arg)) {
        if (!cast->getType()->isSpecificBuiltinType(BuiltinType::Int))
            break;
        arg = cast->getSubExpr()->IgnoreParenImpCasts();
    }
    if (!plain_char(arg->getType()) && !arg->getType()->isSpecificBuiltinType(BuiltinType::SChar))
        return;
    Expr::EvalResult value;
    if (!arg->isValueDependent() && arg->EvaluateAsInt(value, *result.Context) &&
        value.Val.getInt() >= 0 && value.Val.getInt() <= 127)
        return; // ASCII character constants are safe with either char signedness.
    diag(call->getArg(0)->getExprLoc(), "possibly negative character passed to %0; convert the byte to 'unsigned char' before character classification or case conversion")
        << function->getNameAsString();
}

}
