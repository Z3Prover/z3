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
#include "util/log.h"
#include "sat/smt/polysat/project_interval.h"
#include "sat/smt/polysat/core.h"
#include "sat/smt/polysat/number.h"

namespace polysat {

    project_interval::project_interval(core& c) : c(c) {}

    constraints& project_interval::cs() {
        return c.cs();
    }

    void project_interval::init(pvar v, eval_interval interval, unsigned width, dependency_vector const& deps) {
        m_var = v;
        m_interval = interval;
        m_width = width;
        m_fixed.reset();
        c.get_fixed_subslices(m_var, m_fixed);

        m_deps.reset();
        m_deps = deps;
        m_deps_initial_size = m_deps.size();

        m_result = l_undef;
        m_explain.reset();

        m_fixed_levels.reset();
        m_target_levels.reset();

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
        return fixed_claim(target.child, null_var, target.value, 0, target.length);
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
        if (lbool r = try_generic(); r != l_undef)
            return r;
        if (lbool r = try_specific(); r != l_undef)
            return r;
        return l_undef;
    }

    /**
     * Try projection without taking fixed subslices into account.
     * The projected interval may be worse, but it may be propagated at an earlier level.
     * TODO: should take into account fixed slices from even earlier levels too? (e.g. zero_extend)
     */
    lbool project_interval::try_generic() {
        // TODO
        return l_undef;
    }
    /**
     * Try projection, taking as many fixed subslices into account as possible.
     */
    lbool project_interval::try_specific() {
        ensure_target_levels();
        for (unsigned i = 0; i < m_fixed.size(); ++i) {
            auto const& target = m_fixed[i];
            unsigned const target_level = m_target_levels[i];
            if (target.child == null_var)
                continue;
            lbool r = try_specific(target, target_level);
            if (r != l_undef)
                return r;
        }
        return l_undef;
    }


#if 0
    lbool project_interval::propagate_from_containing_slice(entry* e, dependency_vector const& e_deps) {
        // verbose_stream() << "\n\n\n\n\n\nNon-viable assignment for v" << m_var << " size " << c.size(m_var) << "\n";
        // display_one(verbose_stream() << "entry: ", e) << "\n";
        // verbose_stream() << "value " << value << "\n";
        // verbose_stream() << "m_overlaps " << m_overlaps << "\n";
        // m_fixed_bits.display(verbose_stream() << "fixed: ") << "\n";
        // TRACE("bv", c.display(tout));

        // TODO: each of subslices corresponds to one in fixed, but may occur with different pvars.
        //       for each offset/length with pvar we need to do the projection only once.
        //       although, the max admissible level of fixed slices depends on the child pvar under consideration, so we may not get the optimal interval anymore?
        //       (pvars on the same slice only differ by level. the fixed value is the same for all. so we can limit by the max level of pvars and then the projection will work for at least one.)

        bool has_pvar = any_of(fixed, [](fixed_slice const& f) { return f.child != null_var; });
        // this case occurs if e-graph merges e.g. nodes "x - 2" and "3";
        // polysat will see assignment "x = 5" but no fixed bits
        if (!has_pvar)
            return l_undef;


/*  skip the ordering for now
        unsigned_vector order;
        for (unsigned i = 0; i < fixed.size(); ++i) {
            fixed_slice const& f = fixed[i];
            if (f.child == null_var)
                continue;
            order.push_back(i);
        }

        // order by:
        // - level descending
        //     usually, a sub-slice at higher level is responsible for the assignment.
        //     not always: e.g., could assign slice at level 5 but merge makes it a sub-slice only at level 10.
        //     (seems to work by not only considering max-level sub-slices.)
        // - size ascending
        //     e.g., prefers 'c' if we have pvars for both 'c' and 'concat(c,...)'
        std::sort(order.begin(), order.end(), [&](auto const& i1, auto const& i2) -> bool {
            unsigned lvl1 = pvar_levels[i1];
            unsigned lvl2 = pvar_levels[i2];
            pvar v1 = fixed[i1].child;
            pvar v2 = fixed[i2].child;
            return lvl1 > lvl2
                || (lvl1 == lvl2 && c.size(v1) < c.size(v2));
        });

        for (auto const& i : order) {
            auto const& slice = fixed[i];
            unsigned const slice_level = pvar_levels[i];
            SASSERT(slice.child != null_var);
            lbool r = propagate_from_containing_slice(e, value, e_deps, fixed, fixed_levels, slice, slice_level);
            if (r != l_undef)
                return r;
        }
        */
        return l_undef;
    }
#endif


    lbool project_interval::try_specific(fixed_slice const& target, unsigned target_level) {
        pvar const w = target.child;
        unsigned const w_off = target.offset;
        unsigned const w_sz = target.length;
        unsigned const w_level = target_level;  // level where value of w was fixed
        SASSERT(w != null_var);
        SASSERT_EQ(c.size(w), w_sz);
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

        rational const& lo = m_interval.lo_val();
        rational const& hi = m_interval.hi_val();

        r_interval const v_ivl  = r_interval::proper(lo, hi);
        IF_VERBOSE(3, {
            verbose_stream() << "propagate interval " << v_ivl << " from v" << m_var << " to v" << w << "[" << y_sz << "]" << "\n";
        });

        reset_deps();
        ensure_fixed_levels();

        r_interval ivl = v_ivl;

        // chop off x-part, taking fixed values into account whenever possible.
        unsigned const x_off = y_sz + z_sz;
        unsigned remaining_x_sz = x_sz;
        while (remaining_x_sz > 0 && !ivl.is_empty() && !ivl.is_full()) {
            unsigned remaining_x_end = remaining_x_sz + x_off;
            // find next fixed slice (prefer lower level)
            fixed_slice best;
            unsigned best_end = 0;
            unsigned best_level = UINT_MAX;
            SASSERT(best_end < x_off);  // because y_sz != 0
            for (unsigned i = 0; i < m_fixed.size(); ++i) {
                auto const& f = m_fixed[i];
                unsigned const f_level = m_fixed_levels[i];
                if (f_level >= w_level)
                    continue;
                // ??????xxxxxxxyyyyyyzzzz
                //  1111            not useful at this point
                //    11111         OK
                //          1111    OK (has gap without fixed value)
                //            1111  NOT OK (overlaps y) ... although, why would that not be ok? it just restricts values of y too. maybe this can be used to improve interval for y further.
                //                111111  not useful at this point
                if (f.offset >= remaining_x_end)
                    continue;
                if (f.end() <= x_off)
                    continue;
                unsigned const f_end = std::min(remaining_x_end, f.end());  // for comparison, values beyond the current range don't matter
                if (f_end > best_end)
                    best = f, best_end = f_end, best_level = f_level;
                else if (f_end == best_end && f_level < best_level)
                    best = f, best_end = f_end, best_level = f_level;
            }

            if (best_end < remaining_x_end) {
                // there is a gap without a fixed value
                unsigned const b = std::max(best_end, x_off);
                unsigned const a = remaining_x_end - b;
                SASSERT(remaining_x_sz >= a);

                ivl = chop_off_upper(ivl, a, b);
                remaining_x_sz -= a;
                remaining_x_end -= a;

                IF_VERBOSE(4, {
                    verbose_stream() << "  chop " << a << " upper bits\n";
                    verbose_stream() << "  => " << ivl << "\n";
                });
            }

            if (best_end > x_off) {
                SASSERT(remaining_x_end == best_end);
                SASSERT(remaining_x_end <= best.end());
                // chop off portion with fixed value
                unsigned const b = std::max(x_off, best.offset);
                unsigned const a = remaining_x_end - b;
                rational value = best.value;
                if (b > best.offset)
                    value = machine_div2k(value, b - best.offset);
                value = mod2k(value, a);

                ivl = chop_off_upper(ivl, a, b, &value);
                m_deps.push_back(dep_fixed(best));  // justification for the fixed value
                remaining_x_sz -= a;
                remaining_x_end -= a;

                IF_VERBOSE(4, {
                    verbose_stream() << "  chop " << a << " upper bits with value " << value << " from fixed slice " << best.value << "[" << best.length << "]@" << best.offset << "\n";
                    verbose_stream() << "  => " << ivl << "\n";
                });
            }
        }

        if (ivl.is_empty())
            return l_undef;

        // chop off z-part
        unsigned remaining_z_sz = z_sz;
        while (remaining_z_sz > 0 && !ivl.is_empty() && !ivl.is_full()) {
            SASSERT(remaining_x_sz == 0);
            unsigned remaining_z_off = z_sz - remaining_z_sz;
            // find next fixed slice (prefer lower level)
            fixed_slice best;
            unsigned best_off = z_sz;
            unsigned best_level = UINT_MAX;
            for (unsigned i = 0; i < m_fixed.size(); ++i) {
                auto const& f = m_fixed[i];
                unsigned const f_level = m_fixed_levels[i];
                if (f_level >= w_level)
                    continue;
                // ?????????????yyyyyyzzzzz???
                //            1111              not useful at this point
                //                      1111    OK
                //                  1111        OK (has gap without fixed value)
                //                         111  not useful
                if (f.offset >= z_sz)
                    continue;
                if (f.end() <= remaining_z_off)
                    continue;
                unsigned const f_off = std::max(remaining_z_off, f.offset);  // for comparison, values beyond the current range don't matter
                if (f_off < best_off)
                    best = f, best_off = f_off, best_level = f_level;
                else if (f_off == best_off && f_level < best_level)
                    best = f, best_off = f_off, best_level = f_level;
            }

            if (best_off > remaining_z_off) {
                // there is a gap without a fixed value
                unsigned const b = best_off - remaining_z_off;
                unsigned const a = y_sz + z_sz - b;
                SASSERT(remaining_z_sz >= b);

                ivl = chop_off_lower(ivl, a, b);
                remaining_z_sz -= b;
                remaining_z_off += b;

                IF_VERBOSE(4, {
                    verbose_stream() << "  chop " << b << " lower bits\n";
                    verbose_stream() << "  => " << ivl << "\n";
                });
            }

            if (best_off < z_sz) {
                SASSERT_EQ(best_off, remaining_z_off);
                unsigned const b = std::min(best.end(), z_sz) - remaining_z_off;
                unsigned const a = y_sz + z_sz - b;
                rational value = best.value;
                if (best.offset < best_off)
                    value = machine_div2k(value, best_off - best.offset);
                value = mod2k(value, b);

                ivl = chop_off_lower(ivl, a, b, &value);
                m_deps.push_back(dep_fixed(best));  // justification for the fixed value
                remaining_z_sz -= b;
                remaining_z_off += b;

                IF_VERBOSE(4, {
                    verbose_stream() << "  chop " << b << " lower bits with value " << value << " from fixed slice " << best.value << "[" << best.length << "]@" << best.offset << "\n";
                    verbose_stream() << "  => " << ivl << "\n";
                });
            }
        }

        if (ivl.is_empty())
            return l_undef;

        IF_VERBOSE(3, {
            verbose_stream() << "=> " << ivl << "\n";
        });

        // m_deps currently contains:
        // - external explanation for the interval on m_var
        // - explanation for the fixed parts that were used for projection

        m_deps.push_back(offset_claim{m_var, offset_slice{w, w_off}});  // explains m_var[...] = w

        // TODO: try first the most general projection (without assuming fixed slices; purpose: get lemma with less dependencies)
        // TODO: for each fixed slice with multiple pvars, do the projection only once?

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
        if (!ivl.contains(target.value))
            return l_undef;

        // now: m_deps implies 2^w_shift * w is not in ivl
        signed_constraint sc = ~cs().ult(w_shift * (c.var(w) - ivl.lo()), w_shift * (ivl.hi() - ivl.lo()));
        dependency d = c.propagate(sc, m_deps, "propagate from containing slice");

        m_explain.push_back(d);
        m_explain.push_back(dep_target(target));

        IF_VERBOSE(3, {
            verbose_stream() << "=>  v" << w << "[" << y_sz << "] not in " << ivl << "\n";
        });
        // the conflict is projected interval + fixed value
        m_result = l_true;
        return l_true;
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
