/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    project forbidden intervals to subslices

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

Notes:


--*/


#include "util/debug.h"
#include "sat/smt/polysat/project_interval.h"
#include "sat/smt/polysat/core.h"
#include "sat/smt/polysat/number.h"
#include <algorithm>

namespace polysat {

    project_interval::project_interval(core& c) : c(c) {}

    constraints& project_interval::cs() {
        return c.cs();
    }

    void project_interval::init(pvar v, r_interval interval, unsigned width, dependency_vector const& deps) {
        m_var = v;
        m_interval = interval;
        m_width = width;

        m_fixed.reset();
        c.get_fixed_subslices(m_var, m_fixed);

        m_fixed_levels.reset();
        m_target_levels.reset();

        m_deps.reset();
        m_deps = deps;
        m_deps_initial_size = m_deps.size();

        m_result = l_undef;
        m_explain.reset();

        SASSERT(m_var != null_var);
        SASSERT(!m_interval.is_full());
        SASSERT(0 < m_width && m_width <= c.size(v));
    }

    void project_interval::reset_deps() {
        m_deps.shrink(m_deps_initial_size);
    }

    dependency project_interval::dep_fixed(fixed_slice const& fixed) {
        return fixed_claim(m_var, null_var, fixed.value, fixed.offset, fixed.length);
    }

    void project_interval::ensure_fixed_levels() {
        if (!m_fixed_levels.empty()) {
            SASSERT_EQ(m_fixed_levels.size(), m_fixed.size());
            return;
        }
        for (auto const& f : m_fixed) {
            unsigned level = c.level(dep_fixed(f));
            m_fixed_levels.push_back(level);
        }
    }

    dependency project_interval::dep_target(fixed_slice const& target) {
        SASSERT(target.child != null_var);
        SASSERT(target.length == c.size(target.child));
        return dep_target(target.child, target.value);
    }

    dependency project_interval::dep_target(pvar w, rational const& value) {
        SASSERT(w != null_var);
        return fixed_claim(w, null_var, value, 0, c.size(w));
    }

    void project_interval::ensure_target_levels() {
        if (!m_target_levels.empty()) {
            SASSERT_EQ(m_target_levels.size(), m_fixed.size());
            return;
        }

        auto compute_target_level = [&](fixed_slice const& f) -> unsigned {
            if (f.child == null_var)
                return UINT_MAX;
            return c.level(dep_target(f));
        };

        for (auto const& f : m_fixed) {
            unsigned level = compute_target_level(f);
            m_target_levels.push_back(level);
        }
    }

    lbool project_interval::operator()() {
        select_targets();
        if (lbool r = try_generic(); r != l_undef)
            return r;
        if (lbool r = try_specific(); r != l_undef)
            return r;
        return l_undef;
    }

    lbool project_interval::try_generic() {
        for (auto [i, _] : m_targets) {
            fixed_slice const& target = m_fixed[i];
            unsigned level = m_target_levels[i];
            lbool r = try_project(target.child, target.offset, target.length, target.value, level);
            if (r != l_undef)
                return r;
        }
        return l_undef;
    }

    lbool project_interval::try_specific() {
        for (auto [i, j] : m_targets) {
            fixed_slice const& target = m_fixed[j];
            unsigned level = m_target_levels[j];

            // did we try the same thing already in try_generic?
            unsigned prev_level = m_target_levels[i];
            if (prev_level == level)
                continue;

            lbool r = try_project(target.child, target.offset, target.length, target.value, level);
            if (r != l_undef)
                return r;
        }
        return l_undef;
    }

    void project_interval::select_targets() {
        ensure_target_levels();
        m_targets.reset();

        unsigned i = 0;
        unsigned j = 0;
        for (; i < m_fixed.size(); i = j) {
            j = i + 1;

            if (m_fixed[i].child == null_var)
                continue;

            unsigned generic_target = i;   // lowest level
            unsigned specific_target = i;  // highest level

            // Find other slices with the same offset
            // NOTE: core::get_fixed_subslices returns all slices with the same offset consecutively
            for (; j < m_fixed.size(); ++j) {
                if (m_fixed[i].offset != m_fixed[j].offset)
                    break;
                if (m_fixed[i].length != m_fixed[j].length)
                    break;
                SASSERT(m_fixed[i].value == m_fixed[j].value);
                if (m_target_levels[j] < m_target_levels[generic_target])
                    generic_target = j;
                if (m_target_levels[j] < m_target_levels[specific_target])
                    specific_target = j;
            }

            m_targets.push_back({generic_target, specific_target});
        }

        // try targets with lower level first, to try and get more general projections
        std::sort(m_targets.begin(), m_targets.end(), [&](target_t const& a, target_t const& b) -> bool {
            return m_target_levels[a.first] < m_target_levels[b.first];
        });
    }

    lbool project_interval::try_project(pvar const w, unsigned const w_off, unsigned const w_sz, rational const& value, unsigned const max_level) {
        SASSERT(w != null_var);
        SASSERT_EQ(c.size(w), w_sz);
        SASSERT(w != m_var);
        if (w == m_var)
            return l_undef;

        // verbose_stream() << "v" << m_var << " size " << c.size(m_var) << " -> v" << w << " size " << w_sz << " offset " << w_off << " level " << w_level << "\n";

        // Let:
        // v = m_var[m_width-1:0]
        // v = concat(x, y, z)
        // y = w[y_sz-1:0]

        //                      m_width
        // m_var = ???????vvvvvvvvvvvvvvvvvvvvvvv
        //                      wwwwwwww
        //                xxxxxxyyyyyyyyzzzzzzzzz
        //                        y_sz   w_offset
        //
        // or:
        // m_var = ???????vvvvvvvvvvvvvvvvvvvvvvv
        //             wwwwwwwwwwwwwwwww
        //                yyyyyyyyyyyyyyzzzzzzzzz
        //
        // or:
        // m_var = ?????????????????vvvvvvvvvvvvv
        //             wwwwwwwww
        unsigned const v_sz = m_width;
        if (w_off >= v_sz)
            return l_undef;

        unsigned const z_sz = w_off;
        unsigned const y_sz = std::min(w_sz, v_sz - z_sz);
        unsigned const x_sz = v_sz - y_sz - z_sz;
        rational const& w_shift = rational::power_of_two(w_sz - y_sz);
        // verbose_stream() << "v_sz " << v_sz << " w_sz " << w_sz << " / x_sz " << x_sz << " y_sz " << y_sz << " z_sz " << z_sz << "\n";
        SASSERT_EQ(v_sz, x_sz + y_sz + z_sz);

        IF_VERBOSE(3, {
            verbose_stream() << "propagate interval " << m_interval << " from v" << m_var << " to v" << w << "[" << y_sz << "]" << "\n";
        });

        reset_deps();
        ensure_fixed_levels();

        r_interval ivl = m_interval;
        ivl = chop_off_upper(ivl, max_level, x_sz, y_sz, z_sz);
        ivl = chop_off_lower(ivl, max_level, y_sz, z_sz);
        IF_VERBOSE(3, verbose_stream() << "=> " << ivl << "\n");

        if (ivl.is_empty())
            return l_undef;

        // m_deps contains at this point:
        // - external explanation for the interval on m_var
        // - explanation for the fixed parts that were used for projection

        // add explanation for m_var[...] = w
        m_deps.push_back(offset_claim{m_var, offset_slice{w, w_off}});

        SASSERT(m_result == l_undef);
        SASSERT(m_explain.empty());

        if (ivl.is_full()) {
            // m_deps is a conflict
            m_result = l_false;
            return l_false;
        }

        // proper interval
        SASSERT(ivl.is_proper() && !ivl.is_empty());

        // interval propagation worked but it doesn't conflict the currently assigned value
        if (!ivl.contains(value))
            return l_undef;

        // now: m_deps implies 2^w_shift * w is not in ivl
        signed_constraint sc = ~cs().ult(w_shift * (c.var(w) - ivl.lo()), w_shift * (ivl.hi() - ivl.lo()));
        dependency d = c.propagate(sc, m_deps, "propagate from containing slice");

        m_explain.push_back(d);
        m_explain.push_back(dep_target(w, value));

        IF_VERBOSE(3, {
            verbose_stream() << "=>  v" << w << "[" << y_sz << "] not in " << ivl << "\n";
        });
        // the conflict is projected interval + fixed value
        m_result = l_true;
        return l_true;
    }

    r_interval project_interval::chop_off_upper(r_interval ivl, unsigned const max_level, unsigned x_sz, unsigned const y_sz, unsigned const z_sz) {
        SASSERT(y_sz != 0);
        unsigned const x_off = y_sz + z_sz;
        while (x_sz > 0 && !ivl.is_empty() && !ivl.is_full()) {
            unsigned x_end = x_sz + x_off;
            // find next fixed slice (prefer lower level)
            fixed_slice const* best = nullptr;
            unsigned best_end = 0;
            unsigned best_level = UINT_MAX;
            for (unsigned i = 0; i < m_fixed.size(); ++i) {
                auto const& f = m_fixed[i];
                unsigned const f_level = m_fixed_levels[i];
                if (f_level > max_level)
                    continue;
                // ??????xxxxxxxyyyyyyzzzz
                //  1111            not useful at this point
                //    11111         OK
                //          1111    OK (has gap without fixed value)
                //            1111  NOT OK (overlaps y) ... although, why would that not be ok? it just restricts values of y too. maybe this can be used to improve interval for y further.
                //                111111  not useful at this point
                if (f.offset >= x_end)
                    continue;
                if (f.end() <= x_off)
                    continue;
                unsigned const f_end = std::min(x_end, f.end());  // for comparison, values beyond the current range don't matter
                if (f_end > best_end)
                    best = &f, best_end = f_end, best_level = f_level;
                else if (f_end == best_end && f_level < best_level)
                    best = &f, best_end = f_end, best_level = f_level;
            }

            if (best_end < x_end) {
                // there is a gap without a fixed value
                unsigned const b = std::max(best_end, x_off);
                unsigned const a = x_end - b;
                SASSERT(x_sz >= a);

                ivl = chop_off_upper(ivl, a, b);
                x_sz -= a, x_end -= a;

                IF_VERBOSE(4, {
                    verbose_stream() << "  chop " << a << " upper bits\n";
                    verbose_stream() << "  => " << ivl << "\n";
                });
            }

            if (best_end > x_off) {
                // chop off portion with fixed value
                SASSERT(best);
                SASSERT(x_end == best_end);
                SASSERT(x_end <= best->end());
                unsigned const b = std::max(x_off, best->offset);
                unsigned const a = x_end - b;
                SASSERT(x_sz >= a);

                rational value = best->value;
                if (b > best->offset)
                    value = machine_div2k(value, b - best->offset);
                value = mod2k(value, a);

                ivl = chop_off_upper(ivl, a, b, &value);
                m_deps.push_back(dep_fixed(*best));  // justification for the fixed value
                x_sz -= a, x_end -= a;

                IF_VERBOSE(4, {
                    verbose_stream() << "  chop " << a << " upper bits with value " << value << " from fixed slice " << best->value << "[" << best->length << "]@" << best->offset << "\n";
                    verbose_stream() << "  => " << ivl << "\n";
                });
            }
        }
        SASSERT(ivl.is_empty() || ivl.is_full() || x_sz == 0);
        return ivl;
    }

    r_interval project_interval::chop_off_lower(r_interval ivl, unsigned const max_level, unsigned const y_sz, unsigned z_sz) {
        SASSERT(y_sz != 0);
        unsigned const y_off = z_sz;
        unsigned z_off = 0;
        while (z_sz > 0 && !ivl.is_empty() && !ivl.is_full()) {
            // find next fixed slice (prefer lower level)
            fixed_slice const* best = nullptr;
            unsigned best_off = y_off;
            unsigned best_level = UINT_MAX;
            for (unsigned i = 0; i < m_fixed.size(); ++i) {
                auto const& f = m_fixed[i];
                unsigned const f_level = m_fixed_levels[i];
                if (f_level > max_level)
                    continue;
                // ?????????????yyyyyyzzzzz???
                //            1111              not useful at this point
                //                      1111    OK
                //                  1111        OK (has gap without fixed value)
                //                         111  not useful
                if (f.offset >= y_off)
                    continue;
                if (f.end() <= z_off)
                    continue;
                unsigned const f_off = std::max(z_off, f.offset);  // for comparison, values beyond the current range don't matter
                if (f_off < best_off)
                    best = &f, best_off = f_off, best_level = f_level;
                else if (f_off == best_off && f_level < best_level)
                    best = &f, best_off = f_off, best_level = f_level;
            }

            if (best_off > z_off) {
                // there is a gap without a fixed value
                unsigned const b = best_off - z_off;
                unsigned const a = y_sz + z_sz - b;
                SASSERT(z_sz >= b);

                ivl = chop_off_lower(ivl, a, b);
                z_sz -= b, z_off += b;

                IF_VERBOSE(4, {
                    verbose_stream() << "  chop " << b << " lower bits\n";
                    verbose_stream() << "  => " << ivl << "\n";
                });
            }

            if (best_off < y_off) {
                // chop off portion with fixed value
                SASSERT(best);
                SASSERT_EQ(best_off, z_off);
                unsigned const b = std::min(best->end(), y_off) - best_off;
                unsigned const a = y_sz + z_sz - b;
                SASSERT(z_sz >= b);

                rational value = best->value;
                if (best->offset < best_off)  // 'best' may protrude out to the right of the remaining z-part
                    value = machine_div2k(value, best_off - best->offset);
                value = mod2k(value, b);

                ivl = chop_off_lower(ivl, a, b, &value);
                m_deps.push_back(dep_fixed(*best));  // justification for the fixed value
                z_sz -= b, z_off += b;

                IF_VERBOSE(4, {
                    verbose_stream() << "  chop " << b << " lower bits with value " << value << " from fixed slice " << best->value << "[" << best->length << "]@" << best->offset << "\n";
                    verbose_stream() << "  => " << ivl << "\n";
                });
            }
        }
        SASSERT(ivl.is_empty() || ivl.is_full() || z_sz == 0);
        SASSERT(ivl.is_empty() || ivl.is_full() || z_off == y_off);
        return ivl;
    }

    void project_interval::explain(dependency_vector& out) {
        switch (m_result) {
        case l_false:
            SASSERT(m_explain.empty());
            out.append(m_deps);
            break;
        case l_true:
            out.append(m_explain);
            break;
        default:
            UNREACHABLE();
        }
    }

    r_interval project_interval::chop_off_upper(r_interval const& i, unsigned const Ny, unsigned const Nz, rational const* y_fixed_value) {
        if (i.is_full())
            return r_interval::full();
        if (i.is_empty())
            return r_interval::empty();
        if (Ny == 0)
            return i;
        unsigned const Nx = Ny + Nz;
        rational const& lo = i.lo();
        rational const& hi = i.hi();
        if (y_fixed_value) {
            rational const& n = *y_fixed_value;
            rational const lo_d = div2k_floor(lo, Nz);
            rational const hi_d = div2k_floor(hi, Nz);
            rational z_lo = (lo_d == n) ? mod2k(lo, Nz) : rational(0);
            rational z_hi = (hi_d == n) ? mod2k(hi, Nz) : rational(0);
            if (z_lo != z_hi)
                return r_interval::proper(std::move(z_lo), std::move(z_hi));
            else if (r_interval::contains(lo, hi, n * rational::power_of_two(Nz)))
                return r_interval::full();  // no value for z
            else
                return r_interval::empty();  // z unconstrained
        }
        else {
            rational const Mx = rational::power_of_two(Nx);
            rational const Mz = rational::power_of_two(Nz);
            rational const len = r_interval::len(lo, hi, Mx);
            if (len > Mx - Mz)
                return r_interval::proper(mod2k(lo, Nz), mod2k(hi, Nz));
            else
                return r_interval::empty();  // z unconstrained
        }
        UNREACHABLE();
    }

    r_interval project_interval::chop_off_lower(r_interval const& i, unsigned const Ny, unsigned const Nz, rational const* z_fixed_value) {
        if (i.is_full())
            return r_interval::full();
        if (i.is_empty())
            return r_interval::empty();
        if (Nz == 0)
            return i;
        unsigned const Nx = Ny + Nz;
        rational const& lo = i.lo();
        rational const& hi = i.hi();
        if (z_fixed_value) {
            rational const& n = *z_fixed_value;
            rational y_lo = mod2k(div2k_ceil(mod2k(lo - n, Nx), Nz), Ny);
            rational y_hi = mod2k(div2k_ceil(mod2k(hi - n, Nx), Nz), Ny);
            if (y_lo != y_hi)
                return r_interval::proper(std::move(y_lo), std::move(y_hi));
            else if (r_interval::contains(lo, hi, y_hi * rational::power_of_two(Nz) + n))
                return r_interval::full();  // no value for y
            else
                return r_interval::empty();  // y unconstrained
        }
        else {
            rational const Mx = rational::power_of_two(Nx);
            rational const Mz = rational::power_of_two(Nz);
            rational const len = r_interval::len(lo, hi, Mx);
            if (len >= Mz) {
                rational y_lo = mod2k(div2k_ceil(lo, Nz), Ny);
                rational y_hi = div2k_floor(hi, Nz);
                return r_interval::proper(std::move(y_lo), std::move(y_hi));
            }
            else
                return r_interval::empty();  // y unconstrained
        }
        UNREACHABLE();
    }

}
