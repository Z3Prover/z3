// Copyright (c) 2026 Microsoft Corporation
// SPDX-License-Identifier: MIT
#pragma once

#include "clang-tidy/ClangTidyCheck.h"

namespace clang::tidy::z3 {

class CharSignednessCheck : public ClangTidyCheck {
public:
    using ClangTidyCheck::ClangTidyCheck;
    void registerMatchers(ast_matchers::MatchFinder* finder) override;
    void check(ast_matchers::MatchFinder::MatchResult const& result) override;
};

}
