/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    project forbidden intervals to subslices

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

--*/
#pragma once

#include "util/rational.h"
#include "sat/smt/polysat/types.h"
#include "sat/smt/polysat/interval.h"

namespace polysat {

    class core;
    class constraints;

    class project_interval {
        core& c;
        constraints& cs();

        /* source variable and interval */
        pvar                m_var = null_var;
        r_interval          m_interval = r_interval::full();
        unsigned            m_width = 0;

        /* fixed subslices of source variable */
        fixed_bits_vector   m_fixed;
        unsigned_vector     m_fixed_levels;     // cache for level(dep_fixed(m_fixed[i]))
        unsigned_vector     m_target_levels;    // cache for max(level(dep_target_sub(m_fixed[i])), level(m_deps))
        void ensure_fixed_levels();
        void ensure_target_levels(unsigned ext_level);

        // target slices for which we will try projection.
        // - first entry is target with lowest level (more generic: possibly smaller interval, but less dependencies)
        // - second entry is target with highest level (more specific: possibly larger interval, but more dependencies)
        using target_t = std::pair<unsigned, unsigned>;  // indices into m_fixed
        svector<target_t>   m_targets;

        dependency_vector   m_deps;
        unsigned            m_deps_initial_size = 0;    // number of external deps
        void reset_deps();

        /* final result and explanation */
        lbool               m_result = l_undef;
        dependency_vector   m_explain;

        /**
         * subslice of m_var is fixed
         * m_var[f.end-1:f.offset] ~ f.value
         */
        dependency dep_fixed(fixed_slice const& fixed);

        /**
         * target pvar is fixed
         * w ~ value
         */
        dependency dep_target_fixed(pvar w, rational const& value);

        /**
         * target pvar is subslice of m_var
         * m_var[...] ~ w
         */
        dependency dep_target_sub(fixed_slice const& target);
        dependency dep_target_sub(pvar w, unsigned w_off);

        /**
         * Let x = concat(y, z) and x not in [lo;hi[.
         * Returns an interval I such that z not in I.
         */
        static r_interval chop_off_upper(r_interval const& i, unsigned Ny, unsigned Nz, rational const* y_fixed_value = nullptr);

        /**
         * Let x = concat(y, z) and x not in [lo;hi[.
         * Returns an interval I such that y not in I.
         */
        static r_interval chop_off_lower(r_interval const& i, unsigned Ny, unsigned Nz, rational const* z_fixed_value = nullptr);

        lbool try_project(pvar const w, unsigned const w_off, unsigned const w_sz, rational const& value, unsigned const max_level);
        r_interval chop_off_upper(r_interval ivl, unsigned max_level, unsigned x_sz, unsigned y_sz, unsigned z_sz);
        r_interval chop_off_lower(r_interval ivl, unsigned max_level, unsigned y_sz, unsigned z_sz);

        void select_targets();
        lbool try_generic();
        lbool try_specific();

    public:
        project_interval(core& c);

        /** Initialize for forbidden interval:
         *
         *      v[width-1:0] \not\in interval
         */
        void init(pvar v, r_interval interval, unsigned width, dependency_vector const& deps);

        /**
         * l_true: successfully projected interval onto subslice
         * l_false: also successfully projected interval onto subslice, resulted in full interval
         * l_undef: failed
         *
         * In case of l_true/l_false, use explain() to retrieve the conflict.
         */
        lbool operator()();

        void explain(dependency_vector& out);
    };

}
