/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    index_sort_with_mutations.h

Abstract:

    Bounds-safe, mutation-aware stable merge sort of an index permutation.

    This exists to be shared between sites whose ordering comparator is NOT a
    fixed strict weak ordering over a single sort -- typically because the
    comparator MUTATES the objects it compares (e.g. algebraic numbers, whose
    comparison refines their isolating intervals) and may even throw when a
    resource limit is hit mid-sort. Against such a comparator std::sort
    (introsort) is undefined behavior: it relies on a comparator-derived
    sentinel and re-compares a pivot repeatedly, so a comparison that
    transiently strengthens from "uncertain" to "decided" invalidates the
    sentinel and its *unguarded* insertion pass walks off the array -> an
    out-of-bounds read -> SIGSEGV (a try/catch could not help).

    Merge sort is safe BECAUSE of how it meets a mutating comparator:
      1. It never re-compares a pair (each unordered pair is compared at exactly
         one merge level), so "the verdict for this pair changed" cannot occur
         within the sort.
      2. It uses no comparator-derived sentinel; every loop bound is arithmetic
         (i < mid, j < hi), so an inconsistent comparator can only yield a wrong
         order, never an out-of-bounds access or non-termination.
      3. If the comparator's refinement is monotone toward a true order, runs
         are ordered by decided verdicts that later refinement cannot un-decide,
         so each run stays sorted and deeper merges inherit cheaper comparisons.
    It runs in O(n log n) comparisons and O(n) scratch, is stable, and unwinds
    cleanly if the comparator throws on cancellation.

Author:

    Lev Nachmanson 2026

--*/
#pragma once

#include <algorithm>

/**
   \brief Stable merge sort of an index permutation.

   \c perm and \c scratch must each point to an array of \c n unsigned values;
   \c perm holds the permutation to sort (typically 0..n-1). \c less(a, b) takes
   two element indices and returns true iff element \c a must come strictly
   before element \c b. On return \c perm holds the sorted permutation and
   \c scratch has been used as working space. Equal/undecided pairs keep their
   relative order (stable).
*/
template<typename Less>
void stable_index_merge_sort(unsigned* perm, unsigned* scratch, unsigned n, Less less) {
    if (n < 2)
        return;
    unsigned* src = perm;
    unsigned* dst = scratch;
    for (unsigned width = 1; width < n; width <<= 1) {
        for (unsigned lo = 0; lo < n; lo += (width << 1)) {
            unsigned mid = std::min(lo + width, n);
            unsigned hi = std::min(lo + (width << 1), n);
            unsigned i = lo, j = mid, k = lo;
            // Take from the right run only on a strict decrease, so equal/
            // undecided pairs keep their relative order (stable).
            while (i < mid && j < hi)
                dst[k++] = less(src[j], src[i]) ? src[j++] : src[i++];
            while (i < mid)
                dst[k++] = src[i++];
            while (j < hi)
                dst[k++] = src[j++];
        }
        std::swap(src, dst);
    }
    if (src != perm)
        std::copy(src, src + n, perm);
}
