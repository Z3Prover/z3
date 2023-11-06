/*++
Copyright (c) 2021 Microsoft Corporation

Module Name:

    helpers for refining intervals

Author:

    Nikolaj Bjorner (nbjorner) 2021-03-19
    Jakob Rath 2021-04-06

Notes:

--*/


#include "util/debug.h"
#include "math/polysat/refine.h"
#include "math/polysat/number.h"

namespace {
    rational div_floor(rational const& a, rational const& b) {
        return floor(a / b);
    }

    rational div_ceil(rational const& a, rational const& b) {
        return ceil(a / b);
    }
}

namespace polysat {

    rational refine_equal::compute_y_max(rational const& y0, rational const& a, rational const& lo0, rational const& hi, rational const& M) {
        // verbose_stream() << "y0=" << y0 << " a=" << a << " lo0=" << lo0 << " hi=" << hi << " M=" << M << std::endl;
        // SASSERT(0 <= y0 && y0 < M);  // not required
        SASSERT(1 <= a && a < M);
        SASSERT(0 <= lo0 && lo0 < M);
        SASSERT(0 <= hi && hi < M);

        if (lo0 <= hi) {
            SASSERT(lo0 <= mod(a*y0, M) && mod(a*y0, M) <= hi);
        }
        else {
            SASSERT(mod(a*y0, M) <= hi || mod(a*y0, M) >= lo0);
        }

        // wrapping intervals are handled by replacing the lower bound lo by lo - M
        rational const lo = lo0 > hi ? (lo0 - M) : lo0;

        // the length of the interval is now hi - lo + 1.
        // full intervals shouldn't go through this computation.
        SASSERT(hi - lo + 1 < M);

        auto contained = [&lo, &hi] (rational const& a_y) -> bool {
            return lo <= a_y && a_y <= hi;
        };

        auto delta_h = [&a, &lo, &hi] (rational const& a_y) -> rational {
            SASSERT(lo <= a_y && a_y <= hi);
            (void)lo;  // avoid warning in release mode
            return div_floor(hi - a_y, a);
        };

        // minimal k such that lo <= a*y0 + k*M
        rational const k = div_ceil(lo - a * y0, M);
        rational const kM = k*M;
        rational const a_y0 = a*y0 + kM;
        SASSERT(contained(a_y0));

        // maximal y for [lo;hi]-interval around a*y0
        // rational const y0h = y0 + div_floor(hi - a_y0, a);
        rational const delta0 = delta_h(a_y0);
        rational const y0h = y0 + delta0;
        rational const a_y0h = a_y0 + a*delta0;
        SASSERT(y0 <= y0h);
        SASSERT(contained(a_y0h));

        // Check the first [lo;hi]-interval after a*y0
        rational const y1l = y0h + 1;
        rational const a_y1l = a_y0h + a - M;
        if (!contained(a_y1l))
            return y0h;
        rational const delta1 = delta_h(a_y1l);
        rational const y1h = y1l + delta1;
        rational const a_y1h = a_y1l + a*delta1;
        SASSERT(y1l <= y1h);
        SASSERT(contained(a_y1h));

        // Check the second [lo;hi]-interval after a*y0
        rational const y2l = y1h + 1;
        rational const a_y2l = a_y1h + a - M;
        if (!contained(a_y2l))
            return y1h;
        SASSERT(contained(a_y2l));

        // At this point, [y1l;y1h] must be a full y-interval that can be extended to the right.
        // Extending the interval can only be possible if the part not covered by [lo;hi] is smaller than the coefficient a.
        // The size of the gap is (lo + M) - (hi + 1).
        SASSERT(lo + M - hi - 1 < a);

        // The points a*[y0l;y0h] + k*M fall into the interval [lo;hi].
        // After the first overflow, the points a*[y1l .. y1h] + (k - 1)*M fall into [lo;hi].
        // With each overflow, these points drift by some offset alpha.
        rational const step = y1h - y0h;
        rational const alpha = a * step - M;

        if (alpha == 0) {
            // the points do not drift after overflow
            // => y_max is infinite
            return y0 + M;
        }

        rational const i =
            alpha < 0
            // alpha < 0:
            // With each overflow to the right, the points drift to the left.
            // We can continue overflowing while a * yil >= lo, where yil = y1l + i * step.
            ? div_floor(lo - a_y1l, alpha)
            // alpha > 0:
            // With each overflow to the right, the points drift to the right.
            // We can continue overflowing while a * yih <= hi, where yih = y1h + i * step.
            : div_floor(hi - a_y1h, alpha);

        // i is the number of overflows to the right
        SASSERT(i >= 0);

        // a * [yil;yih] is the right-most y-interval that is completely in [lo;hi].
        rational const yih = y1h + i * step;
        rational const a_yih = a_y1h + i * alpha;
        SASSERT_EQ(a_yih, a*yih + (k - i - 1)*M);
        SASSERT(contained(a_yih));

        // The next interval to the right may contain a few more values if alpha > 0
        // (because only the upper end moved out of the interval)
        rational const y_next = yih + 1;
        rational const a_y_next = a_yih + a - M;
        if (contained(a_y_next))
            return y_next + delta_h(a_y_next);
        else
            return yih;
    }

    rational refine_equal::compute_y_min(rational const& y0, rational const& a, rational const& lo, rational const& hi, rational const& M) {
        // verbose_stream() << "y0=" << y0 << " a=" << a << " lo=" << lo << " hi=" << hi << " M=" << M << std::endl;
        // SASSERT(0 <= y0 && y0 < M);  // not required
        SASSERT(1 <= a && a < M);
        SASSERT(0 <= lo && lo < M);
        SASSERT(0 <= hi && hi < M);

        auto const negateM = [&M] (rational const& x) -> rational {
            if (x.is_zero())
                return x;
            else
                return M - x;
        };

        rational y_min = -compute_y_max(-y0, a, negateM(hi), negateM(lo), M);
        while (y_min > y0)
            y_min -= M;
        return y_min;
    }

    std::pair<rational, rational> refine_equal::compute_y_bounds(rational const& y0, rational const& a, rational const& lo, rational const& hi, rational const& M) {
        // verbose_stream() << "y0=" << y0 << " a=" << a << " lo=" << lo << " hi=" << hi << " M=" << M << std::endl;
        SASSERT(0 <= y0 && y0 < M);
        SASSERT(1 <= a && a < M);
        SASSERT(0 <= lo && lo < M);
        SASSERT(0 <= hi && hi < M);

        auto const is_valid = [&] (rational const& y) -> bool {
            rational const a_y = mod(a * y, M);
            if (lo <= hi)
                return lo <= a_y && a_y <= hi;
            else
                return a_y <= hi || lo <= a_y;
        };

        unsigned const max_refinements = 100;
        unsigned i = 0;
        rational const y_max_max = y0 + M - 1;
        rational y_max = compute_y_max(y0, a, lo, hi, M);
        while (y_max < y_max_max && is_valid(y_max + 1)) {
            y_max = compute_y_max(y_max + 1, a, lo, hi, M);
            if (++i == max_refinements) {
                // verbose_stream() << "y0=" << y0 << ", a=" << a << ", lo=" << lo << ", hi=" << hi << "\n";
                // verbose_stream() << "refined y_max: " << y_max << "\n";
                break;
            }
        }

        i = 0;
        rational const y_min_min = y_max - M + 1;
        rational y_min = y0;
        while (y_min > y_min_min && is_valid(y_min - 1)) {
            y_min = compute_y_min(y_min - 1, a, lo, hi, M);
            if (++i == max_refinements) {
                // verbose_stream() << "y0=" << y0 << ", a=" << a << ", lo=" << lo << ", hi=" << hi << "\n";
                // verbose_stream() << "refined y_min: " << y_min << "\n";
                break;
            }
        }

        SASSERT(y_min <= y0 && y0 <= y_max);
        rational const len = y_max - y_min + 1;
        if (len >= M)
            // full
            return { rational::zero(), M - 1 };
        else
            return { mod(y_min, M), mod(y_max, M) };
    }

}
