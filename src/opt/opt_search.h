/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    opt_search.h

Abstract:

    Single-objective maximization results and certified bounds over search regions.
    Minimization is normalized to maximization by the caller. A region excludes
    only objective values at or below its supplied bound, not arbitrary Boolean
    branches. Certificates must cover the whole active region.

--*/
#pragma once

#include <algorithm>
#include <optional>
#include "opt/opt_value.h"
#include "util/lbool.h"

namespace opt {

    struct maximize_result {
        // The no-model path accepts the hint without validating it.
        bool bound_valid;
        inf_eps hint;
        // l_true: accepted; l_false: obj >= hint refuted; l_undef: undecided or unchecked.
        lbool hint_status;
        // Independent of hint attainability; justified over the current assertions.
        std::optional<rational> upper_bound;
    };

    class objective_search {
        inf_eps m_upper;
        inf_eps m_excluded_upper{rational(-1), inf_rational(0)};
        vector<inf_eps> m_regions;

    public:
        explicit objective_search(inf_eps const& upper): m_upper(upper) {}

        inf_eps const& upper() const { return m_upper; }

        void tighten_upper(inf_eps const& bound) {
            // Lift a region certificate to the original search space, including
            // the values discarded by every enclosing objective cut.
            m_upper = std::min(m_upper, std::max(bound, m_excluded_upper));
        }

        void update(maximize_result const& result) {
            if (result.upper_bound)
                tighten_upper(inf_eps(*result.upper_bound));
            if (!result.bound_valid && result.hint_status == l_false && result.hint.is_finite())
                tighten_upper(result.hint);
        }

        void exclude_below(inf_eps const& upper) {
            m_excluded_upper = std::max(m_excluded_upper, upper);
        }

        void enter_region(inf_eps const& excluded_upper) {
            m_regions.push_back(m_excluded_upper);
            exclude_below(excluded_upper);
        }

        void refute_region() {
            m_upper = std::min(m_upper, m_excluded_upper);
        }

        void leave_region(lbool status) {
            SASSERT(!m_regions.empty());
            if (status == l_false)
                refute_region();
            m_excluded_upper = m_regions.back();
            m_regions.pop_back();
        }

        void reset_regions() {
            if (!m_regions.empty())
                m_excluded_upper = m_regions[0];
            m_regions.reset();
        }
    };
}
