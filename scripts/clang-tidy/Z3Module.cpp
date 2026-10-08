// Copyright (c) 2026 Microsoft Corporation
// SPDX-License-Identifier: MIT
#include "AstArgumentOrderCheck.h"
#include "CharSignednessCheck.h"
#include "RandomOrderCheck.h"
#include "clang-tidy/ClangTidyModule.h"
#include "clang-tidy/ClangTidyModuleRegistry.h"

namespace clang::tidy::z3 {
class Z3Module : public ClangTidyModule {
public:
    void addCheckFactories(ClangTidyCheckFactories& factories) override {
        factories.registerCheck<AstArgumentOrderCheck>("z3-ast-argument-order");
        factories.registerCheck<CharSignednessCheck>("z3-char-signedness");
        factories.registerCheck<RandomOrderCheck>("z3-random-order");
    }
};
static ClangTidyModuleRegistry::Add<Z3Module> registration("z3-module", "Z3 determinism checks");
}
