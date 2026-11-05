// Copyright (c) 2026 Microsoft Corporation
// SPDX-License-Identifier: MIT
#include "EvaluationOrderCheck.h"
#include "clang/AST/EvaluatedExprVisitor.h"
#include "clang/AST/ExprCXX.h"
#include "llvm/ADT/SmallPtrSet.h"

namespace clang::tidy::z3 {
using namespace ast_matchers;

namespace {
bool unordered_operator(OverloadedOperatorKind op) {
    switch (op) {
    case OO_Plus: case OO_Minus: case OO_Star: case OO_Slash: case OO_Percent:
    case OO_Caret: case OO_Amp: case OO_Pipe:
    case OO_EqualEqual: case OO_ExclaimEqual: case OO_Less: case OO_Greater:
    case OO_LessEqual: case OO_GreaterEqual: case OO_Spaceship:
        return true;
    default:
        // C++17 sequences shifts, assignments, subscripts, &&, || and comma.
        return false;
    }
}
}

// Unlike walking all descendants, this excludes sizeof/noexcept operands and
// uncalled lambda bodies, but includes lambda capture initializers.
class EvaluationOrderCheck::Collector : public ConstEvaluatedExprVisitor<Collector> {
    using Base = ConstEvaluatedExprVisitor<Collector>;
public:
    llvm::SmallVector<Call, 8> found;
    explicit Collector(ASTContext const& ast) : Base(ast) {}
    bool shouldVisitDiscardedStmt() const { return false; }
    void Visit(Stmt const* stmt) {
        if (stmt)
            Base::Visit(stmt);
    }

    void VisitCallExpr(CallExpr const* expr) {
        if (expr->isUnevaluatedBuiltinCall(Context))
            return;
        found.push_back({expr, expr->getDirectCallee()});
        Base::VisitStmt(expr);
    }
    void VisitBinaryOperator(BinaryOperator const* expr) {
        found.push_back({expr, nullptr});
        Base::VisitStmt(expr);
    }
    void VisitCXXConstructExpr(CXXConstructExpr const* expr) {
        found.push_back({expr, expr->getConstructor()});
        Base::VisitStmt(expr);
    }
    void VisitCXXDefaultArgExpr(CXXDefaultArgExpr const* expr) { Visit(expr->getExpr()); }
    void VisitCXXDefaultInitExpr(CXXDefaultInitExpr const* expr) { Visit(expr->getExpr()); }
};

void EvaluationOrderCheck::registerMatchers(MatchFinder* finder) {
    finder->addMatcher(functionDecl(isDefinition(), unless(isExpansionInSystemHeader())).bind("function"), this);
    finder->addMatcher(varDecl(hasGlobalStorage(), hasInitializer(expr()),
                              unless(hasAncestor(functionDecl())),
                              unless(isExpansionInSystemHeader())).bind("global"), this);
}

void EvaluationOrderCheck::check(MatchFinder::MatchResult const& result) {
    m_ast = result.Context;
    if (auto* function = result.Nodes.getNodeAs<FunctionDecl>("function"))
        m_functions.push_back(function);
    if (auto* var = result.Nodes.getNodeAs<VarDecl>("global"))
        if (auto* init = var->getInit())
            m_initializers.push_back(init);
}

llvm::SmallVector<EvaluationOrderCheck::Call, 8> const&
EvaluationOrderCheck::calls(FunctionDecl const* function) {
    function = function->getCanonicalDecl();
    auto it = m_calls.find(function);
    if (it != m_calls.end())
        return it->second;
    Collector collector(*m_ast);
    if (auto* definition = function->getDefinition()) {
        if (auto* ctor = dyn_cast<CXXConstructorDecl>(definition))
            for (auto* init : ctor->inits())
                collector.Visit(init->getInit());
        if (auto* body = definition->getBody())
            collector.Visit(body);
    }
    return m_calls.try_emplace(function, std::move(collector.found)).first->second;
}

bool EvaluationOrderCheck::has_effect(FunctionDecl const* function) {
    if (!function)
        return false; // Indirect calls require information this check lacks.
    function = function->getCanonicalDecl();
    if (auto it = m_effects.find(function); it != m_effects.end())
        return it->second;

    // Reachability handles recursive wrappers without incorrectly caching an
    // in-progress node as pure. Only cache the result for the queried function.
    llvm::SmallVector<FunctionDecl const*, 16> pending{function};
    llvm::SmallPtrSet<FunctionDecl const*, 32> visited;
    while (!pending.empty()) {
        auto* current = pending.pop_back_val()->getCanonicalDecl();
        if (!visited.insert(current).second)
            continue;
        auto known = m_effects.find(current);
        if (known != m_effects.end()) {
            if (known->second)
                return m_effects[function] = true;
            continue;
        }
        if (effect_root(current))
            return m_effects[function] = true;
        for (auto const& call : calls(current))
            if (call.function)
                pending.push_back(call.function);
    }
    return m_effects[function] = false;
}

EvaluationOrderCheck::Call EvaluationOrderCheck::first_effect(Expr const* expr) {
    Collector collector(*m_ast);
    collector.Visit(expr);
    for (auto const& call : collector.found)
        if (has_effect(call.function))
            return call;
    return {nullptr, nullptr};
}

void EvaluationOrderCheck::check_arguments(Expr const* expr, llvm::ArrayRef<Expr const*> args) {
    Call first{nullptr, nullptr};
    for (auto* arg : args) {
        auto next = first_effect(arg);
        if (!next.expr)
            continue;
        if (!first.expr) {
            first = next;
            continue;
        }
        report(expr, first, next);
        return; // One warning per outer call; deliberately no FixItHints.
    }
}

void EvaluationOrderCheck::onEndOfTranslationUnit() {
    if (!m_ast)
        return;
    llvm::SmallVector<Call, 64> candidates;
    for (auto* function : m_functions)
        llvm::append_range(candidates, calls(function));
    for (auto* init : m_initializers) {
        Collector collector(*m_ast);
        collector.Visit(init);
        llvm::append_range(candidates, collector.found);
    }
    llvm::SmallPtrSet<Expr const*, 32> seen;
    for (auto const& candidate : candidates) {
        auto* expr = candidate.expr;
        if (!seen.insert(expr).second || m_ast->getSourceManager().isInSystemHeader(expr->getBeginLoc()))
            continue;
        llvm::SmallVector<Expr const*, 4> args;
        if (auto* call = dyn_cast<CallExpr>(expr)) {
            unsigned start = 0;
            if (auto* op = dyn_cast<CXXOperatorCallExpr>(call)) {
                // Operator notation has its own sequencing rules. operator()
                // follows ordinary call rules, with the object evaluated first.
                if (op->getOperator() == OO_Call)
                    start = 1;
                else if (!check_operators() || !unordered_operator(op->getOperator()))
                    continue;
            }
            for (unsigned i = start; i < call->getNumArgs(); ++i)
                args.push_back(call->getArg(i));
        }
        else if (auto* binary = dyn_cast<BinaryOperator>(expr)) {
            if (!check_operators() || !unordered_operator(BinaryOperator::getOverloadedOperator(binary->getOpcode())))
                continue;
            args.push_back(binary->getLHS());
            args.push_back(binary->getRHS());
        }
        else if (auto* ctor = dyn_cast<CXXConstructExpr>(expr)) {
            if (ctor->isListInitialization())
                continue; // Braced initializer clauses are sequenced.
            llvm::append_range(args, ctor->arguments());
        }
        if (args.size() > 1)
            check_arguments(expr, args);
    }
}

}
