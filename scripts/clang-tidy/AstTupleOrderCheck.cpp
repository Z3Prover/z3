// Copyright (c) 2026 Microsoft Corporation
// SPDX-License-Identifier: MIT
#include "AstTupleOrderCheck.h"
#include "clang/AST/DeclTemplate.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/StringSwitch.h"
#include <set>

namespace clang::tidy::z3 {
using namespace ast_matchers;
namespace {
struct TemplateInfo {
    TemplateDecl const* decl = nullptr;
    llvm::ArrayRef<TemplateArgument> args;
};

TemplateInfo template_info(QualType type) {
    if (auto* record = type->getAsCXXRecordDecl())
        if (auto* spec = dyn_cast<ClassTemplateSpecializationDecl>(record))
            return {spec->getSpecializedTemplate(), spec->getTemplateArgs().asArray()};
    // A spelled type alias need not instantiate the class definition.
    if (auto* spec = type->getAs<TemplateSpecializationType>())
        return {spec->getTemplateName().getAsTemplateDecl(), spec->template_arguments()};
    return {};
}

void type_arguments(llvm::ArrayRef<TemplateArgument> args, llvm::SmallVectorImpl<QualType>& out) {
    for (auto const& arg : args) {
        if (arg.getKind() == TemplateArgument::Type)
            out.push_back(arg.getAsType());
        else if (arg.getKind() == TemplateArgument::Pack)
            type_arguments(arg.pack_elements(), out);
    }
}

bool is_tuple(TemplateInfo const& info) {
    return info.decl && info.decl->isInStdNamespace() && info.decl->getName() == "tuple";
}

bool owns_ast(QualType type, ASTContext& ast) {
    llvm::SmallVector<QualType, 16> pending{type};
    llvm::SmallPtrSet<Type const*, 32> visited;
    while (!pending.empty()) {
        auto current = pending.pop_back_val();
        // In particular, std::tie and forward_as_tuple do not own their referents.
        if (current->isPointerType() || current->isReferenceType() ||
            !visited.insert(current.getCanonicalType().getTypePtr()).second)
            continue;
        if (auto* array = ast.getAsArrayType(current)) {
            pending.push_back(array->getElementType());
            continue;
        }
        auto info = template_info(current);
        if (info.decl) {
            auto name = info.decl->getQualifiedNameAsString();
            if ((name == "obj_ref" || name == "ref_vector" || name == "ref_buffer") &&
                info.args.size() >= 2 && info.args[1].getKind() == TemplateArgument::Type) {
                auto* manager = info.args[1].getAsType()->getAsCXXRecordDecl();
                if (manager && manager->getQualifiedNameAsString() == "ast_manager")
                    return true;
            }
            // Containers own their elements even when represented by raw pointers.
            if (name == "vector") {
                if (info.args.size() >= 2 && info.args[1].getKind() == TemplateArgument::Integral &&
                    info.args[1].getAsIntegral().isZero())
                    continue; // Z3's svector disables element destructors.
                if (!info.args.empty() && info.args[0].getKind() == TemplateArgument::Type)
                    pending.push_back(info.args[0].getAsType());
                continue;
            }
            if (info.decl->isInStdNamespace() &&
                llvm::StringSwitch<bool>(info.decl->getName())
                    .Cases("tuple", "pair", "array", "vector", true)
                    .Cases("deque", "list", "forward_list", true)
                    .Cases("optional", "variant", "unique_ptr", "shared_ptr", true)
                    .Cases("set", "multiset", "unordered_set", "unordered_multiset", true)
                    .Cases("map", "multimap", "unordered_map", "unordered_multimap", true)
                    .Default(false)) {
                type_arguments(info.args, pending);
                continue;
            }
        }
        // Follow by-value wrapper members and bases, but never raw pointers.
        if (auto* record = current->getAsCXXRecordDecl()) {
            if (record->getQualifiedNameAsString() == "z3::ast")
                return true;
            if (auto* definition = record->getDefinition()) {
                for (auto const* field : definition->fields())
                    pending.push_back(field->getType());
                for (auto const& base : definition->bases())
                    pending.push_back(base.getType());
            }
        }
    }
    return false;
}
}

void AstTupleOrderCheck::registerMatchers(MatchFinder* finder) {
    finder->addMatcher(templateSpecializationTypeLoc(unless(isExpansionInSystemHeader())).bind("type"), this);
    // Also catch deduced tuples and factories such as std::make_tuple.
    finder->addMatcher(expr(anyOf(cxxConstructExpr(), callExpr()),
                            unless(isInTemplateInstantiation()),
                            unless(isExpansionInSystemHeader())).bind("expr"), this);
}

void AstTupleOrderCheck::check(MatchFinder::MatchResult const& result) {
    m_ast = result.Context;
    if (auto const* loc = result.Nodes.getNodeAs<TemplateSpecializationTypeLoc>("type")) {
        if (is_tuple(template_info(loc->getType())))
            m_candidates.push_back({loc->getType(), loc->getBeginLoc()});
    }
    if (auto const* expr = result.Nodes.getNodeAs<Expr>("expr")) {
        if (expr->isPRValue() && is_tuple(template_info(expr->getType())))
            m_candidates.push_back({expr->getType(), expr->getBeginLoc()});
    }
}

void AstTupleOrderCheck::onEndOfTranslationUnit() {
    if (!m_ast)
        return;
    auto& sm = m_ast->getSourceManager();
    // Instantiations and a spelled type plus its constructor can describe the
    // same source use. Report it once per line, after wrapper definitions exist.
    std::set<std::pair<unsigned, unsigned>> reported;
    for (auto const& candidate : m_candidates) {
        llvm::SmallVector<QualType, 4> elements;
        type_arguments(template_info(candidate.type).args, elements);
        unsigned owners = 0;
        for (auto element : elements)
            owners += owns_ast(element, *m_ast);
        if (owners < 2)
            continue;
        auto loc = sm.getExpansionLoc(candidate.location);
        auto key = std::make_pair(sm.getFileID(loc).getHashValue(), sm.getSpellingLineNumber(loc));
        if (reported.insert(key).second)
            diag(loc, "std::tuple has multiple elements that own AST references; "
                      "unspecified element destruction order can change recycled AST IDs; "
                      "use a struct with a defined member order");
    }
}
}
