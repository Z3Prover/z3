/*++
Copyright (c) 2026 Microsoft Corporation
--*/
#pragma once

#include <map>
#include <memory>
#include <vector>
#include "math/lp/evidence.h"

namespace lp {
    class lar_solver;
}

namespace nla {
    class lemma;

    class lemma_certificate {
    public:
        using monomial = std::vector<unsigned>;
        using polynomial = std::map<monomial, lp::mpq>;
        struct fact {
            polynomial poly;
            lp::lconstraint_kind kind = lp::EQ;
            bool operator==(fact const &) const = default;
        };
        enum class rule { input, product, zero_product, square, linear };
        struct step {
            rule kind = rule::input;
            unsigned left = UINT_MAX, right = UINT_MAX;
            polynomial argument;
            std::vector<std::pair<unsigned, lp::mpq>> premises;
            lp::mpq offset;
        };
        lp::evidence_manager::proof_expression context;
        vector<lp::evidence_manager::fact> assumptions;
        unsigned premise_count = 0;
        std::vector<step> steps;
        unsigned root = UINT_MAX;

        bool check() const;
        void display(std::ostream &) const;
        static std::shared_ptr<lemma_certificate const> capture(lp::lar_solver &, lemma const &);
    };
}  // namespace nla
