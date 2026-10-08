// Copyright (c) 2026 Microsoft Corporation
// SPDX-License-Identifier: MIT
#pragma once
#include "EvaluationOrderCheck.h"

namespace clang::tidy::z3 {
class RandomOrderCheck : public EvaluationOrderCheck {
public:
    using EvaluationOrderCheck::EvaluationOrderCheck;
private:
    bool effect_root(FunctionDecl const* function) override;
    void report(Expr const* expr, Call first, Call next) override;
    bool check_operators() const override { return true; }
};
}
