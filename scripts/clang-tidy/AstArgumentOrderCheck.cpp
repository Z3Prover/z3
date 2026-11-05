// Copyright (c) 2026 Microsoft Corporation
// SPDX-License-Identifier: MIT
#include "AstArgumentOrderCheck.h"
#include "clang/AST/DeclTemplate.h"
#include "llvm/ADT/StringSwitch.h"

namespace clang::tidy::z3 {
static bool ast_context_parameter(FunctionDecl const* function) {
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
bool AstArgumentOrderCheck::effect_root(FunctionDecl const* function) {
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

void AstArgumentOrderCheck::report(Expr const* expr, Call first, Call next) {
    diag(expr->getBeginLoc(), "AST allocation in separate arguments has unspecified evaluation order; "
                             "construct the arguments in separate statements");
    diag(first.expr->getBeginLoc(), "call to %0 may allocate an AST node", DiagnosticIDs::Note)
        << first.function;
    diag(next.expr->getBeginLoc(), "call to %0 may allocate an AST node", DiagnosticIDs::Note)
        << next.function;
}
}
