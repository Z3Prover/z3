// Copyright (c) 2026 Microsoft Corporation
// SPDX-License-Identifier: MIT
#include "AstArgumentOrderCheck.h"
#include "clang/AST/EvaluatedExprVisitor.h"
#include "clang/AST/ExprCXX.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/StringSwitch.h"

namespace clang::tidy::z3 {
using namespace ast_matchers;

namespace {
bool ast_context_parameter(FunctionDecl const* function) {
    if (!function->getNumParams())
        return false;
    auto type = function->getParamDecl(0)->getType().getNonReferenceType();
    auto* record = type->getAsCXXRecordDecl();
    if (!record)
        return false;
    if (record->getQualifiedNameAsString() == "ast_manager")
        return true;
    auto* specialization = dyn_cast<ClassTemplateSpecializationDecl>(record);
    if (!specialization)
        return false;
    auto name = specialization->getSpecializedTemplate()->getQualifiedNameAsString();
    if (name != "obj_ref" && name != "ref_vector")
        return false;
    auto const& args = specialization->getTemplateArgs();
    if (args.size() != 2 || args[1].getKind() != TemplateArgument::Type)
        return false;
    auto* manager = args[1].getAsType()->getAsCXXRecordDecl();
    return manager && manager->getQualifiedNameAsString() == "ast_manager";
}

// These entry points can allocate even when their bodies are in another TU.
// Other functions are recognized by following their visible definitions, not
// by guessing from a mk_ prefix or from whether a method is const.
bool allocation_root(FunctionDecl const* function) {
    // Free AST utilities have overloads for tactic probes with the same names.
    // Only the overloads taking an AST manager or one of its ref types allocate ASTs.
    if (llvm::StringSwitch<bool>(function->getQualifiedNameAsString())
            .Cases("mk_and", "mk_or", "mk_not", true)
            .Cases("mk_distinct", "expand_distinct", "push_not", true)
            .Default(false))
        return ast_context_parameter(function);
    // Template method bodies may not be instantiated in a syntax-only run.
    // All specializations of this AST rewriter use the same allocating API.
    if (auto* method = dyn_cast<CXXMethodDecl>(function)) {
        auto* record = method->getParent();
        if (auto* specialization = dyn_cast<ClassTemplateSpecializationDecl>(record))
            record = specialization->getSpecializedTemplate()->getTemplatedDecl();
        if (record->getQualifiedNameAsString() == "poly_rewriter" &&
            llvm::StringSwitch<bool>(function->getNameAsString())
                .Cases("mk_add", "mk_mul", "mk_sub", "mk_uminus", true)
                .Default(false))
            return true;
    }
    return llvm::StringSwitch<bool>(function->getQualifiedNameAsString())
        .Cases("ast_manager::mk_app", "ast_manager::mk_app_core", true)
        .Cases("ast_manager::mk_sort", "ast_manager::mk_func_decl", true)
        .Cases("ast_manager::mk_var", "ast_manager::mk_quantifier", true)
        .Cases("ast_manager::mk_lambda", "ast_manager::mk_pattern", true)
        .Cases("ast_manager::mk_fresh_func_decl", "ast_manager::mk_fresh_sort", true)
        .Cases("ast_manager::mk_uninterpreted_sort", "ast_manager::mk_type_var", true)
        .Cases("ast_manager::mk_model_value", "ast_manager::mk_proof", true)
        .Case("ast_manager::register_node_core", true)
        // These factories reach the manager through out-of-line definitions.
        // In particular, numeral lookup can allocate on a cache miss.
        .Cases("bv_util::mk_numeral", "arith_decl_plugin::mk_numeral", true)
        .Case("fpa_decl_plugin::mk_numeral", true)
        .Cases("fpa_util::mk_nan", "fpa_util::mk_pinf", "fpa_util::mk_ninf", true)
        .Cases("fpa_util::mk_pzero", "fpa_util::mk_nzero", true)
        .Cases("seq::skolem::mk", "seq_util::mk_skolem", true)
        .Cases("seq_decl_plugin::mk_string", "seq_util::str::mk_string", true)
        .Cases("arith_rewriter::mk_lt_core", "arith_rewriter::mk_gt_core", true)
        .Cases("bool_rewriter::mk_eq_core", "bool_rewriter::mk_eq_plain", true)
        .Default(false);
}
}

// Unlike walking all descendants, this excludes sizeof/noexcept operands and
// uncalled lambda bodies, but includes lambda capture initializers.
class AstArgumentOrderCheck::Collector : public ConstEvaluatedExprVisitor<Collector> {
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
    void VisitCXXConstructExpr(CXXConstructExpr const* expr) {
        found.push_back({expr, expr->getConstructor()});
        Base::VisitStmt(expr);
    }
    void VisitCXXDefaultArgExpr(CXXDefaultArgExpr const* expr) { Visit(expr->getExpr()); }
    void VisitCXXDefaultInitExpr(CXXDefaultInitExpr const* expr) { Visit(expr->getExpr()); }
};

void AstArgumentOrderCheck::registerMatchers(MatchFinder* finder) {
    finder->addMatcher(functionDecl(isDefinition(), unless(isExpansionInSystemHeader())).bind("function"), this);
    finder->addMatcher(varDecl(hasGlobalStorage(), hasInitializer(expr()),
                              unless(hasAncestor(functionDecl())),
                              unless(isExpansionInSystemHeader())).bind("global"), this);
}

void AstArgumentOrderCheck::check(MatchFinder::MatchResult const& result) {
    m_ast = result.Context;
    if (auto* function = result.Nodes.getNodeAs<FunctionDecl>("function"))
        m_functions.push_back(function);
    if (auto* var = result.Nodes.getNodeAs<VarDecl>("global"))
        if (auto* init = var->getInit())
            m_initializers.push_back(init);
}

llvm::SmallVector<AstArgumentOrderCheck::Call, 8> const&
AstArgumentOrderCheck::calls(FunctionDecl const* function) {
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

bool AstArgumentOrderCheck::allocates(FunctionDecl const* function) {
    if (!function)
        return false; // Indirect calls require information this check lacks.
    function = function->getCanonicalDecl();
    if (auto it = m_allocates.find(function); it != m_allocates.end())
        return it->second;

    // Reachability handles recursive wrappers without incorrectly caching an
    // in-progress node as pure. Only cache the result for the queried function.
    llvm::SmallVector<FunctionDecl const*, 16> pending{function};
    llvm::SmallPtrSet<FunctionDecl const*, 32> visited;
    while (!pending.empty()) {
        auto* current = pending.pop_back_val()->getCanonicalDecl();
        if (!visited.insert(current).second)
            continue;
        auto known = m_allocates.find(current);
        if (known != m_allocates.end()) {
            if (known->second)
                return m_allocates[function] = true;
            continue;
        }
        if (allocation_root(current))
            return m_allocates[function] = true;
        for (auto const& call : calls(current))
            if (call.function)
                pending.push_back(call.function);
    }
    return m_allocates[function] = false;
}

AstArgumentOrderCheck::Call AstArgumentOrderCheck::first_allocation(Expr const* expr) {
    Collector collector(*m_ast);
    collector.Visit(expr);
    for (auto const& call : collector.found)
        if (allocates(call.function))
            return call;
    return {nullptr, nullptr};
}

void AstArgumentOrderCheck::check_arguments(Expr const* expr, llvm::ArrayRef<Expr const*> args) {
    Call first{nullptr, nullptr};
    for (auto* arg : args) {
        auto next = first_allocation(arg);
        if (!next.expr)
            continue;
        if (!first.expr) {
            first = next;
            continue;
        }
        diag(expr->getBeginLoc(), "AST allocation in separate arguments has unspecified evaluation order; "
                                 "construct the arguments in separate statements");
        diag(first.expr->getBeginLoc(), "call to %0 may allocate an AST node", DiagnosticIDs::Note)
            << first.function;
        diag(next.expr->getBeginLoc(), "call to %0 may allocate an AST node", DiagnosticIDs::Note)
            << next.function;
        return; // One warning per outer call; deliberately no FixItHints.
    }
}

void AstArgumentOrderCheck::onEndOfTranslationUnit() {
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
                if (op->getOperator() != OO_Call)
                    continue;
                start = 1;
            }
            for (unsigned i = start; i < call->getNumArgs(); ++i)
                args.push_back(call->getArg(i));
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
