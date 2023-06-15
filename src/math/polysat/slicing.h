/*++
Copyright (c) 2023 Microsoft Corporation

Module Name:

    polysat slicing (relating variables of different bit-widths by extraction)

Author:

    Jakob Rath 2023-06-01

Notation:

    Let x be a bit-vector of width w.
    Let l, h indices such that 0 <= l <= h < w.
    Then x[h:l] extracts h - l + 1 bits of x.
    Shorthands:
    - x[h:] stands for x[h:0], and
    - x[:l] stands for x[w-1:l].

    Example:
        0001[0:] = 1
        0001[2:0] = 001

--*/
#pragma once
#include "math/polysat/types.h"

namespace polysat {

    class solver;

    class slicing final {

        // solver&     m_solver;

#if 0
        /// If y := x[h:l], then m_src[y] = x, m_hi[y] = h, m_lo[y] = l.
        /// Otherwise m_src[y] = null_var.
        ///
        /// Invariants:
        ///     m_src[y] != null_var ==> m_src[y] < y  (at least as long as we always introduce new variables for extract terms.)
        ///     m_lo[y] <= m_hi[y]
        unsigned_vector m_src;
        unsigned_vector m_hi;
        unsigned_vector m_lo;

        struct extract_key {
            pvar src;
            unsigned hi;
            unsigned lo;

            bool operator==(extract_key const& other) const {
                return src == other.src && hi == other.hi && lo == other.lo;
            }

            unsigned hash() const {
                return mk_mix(src, hi, lo);
            }
        };
        using extract_hash = obj_hash<extract_key>;
        using extract_eq = default_eq<extract_key>;
        using extract_map = map<extract_key, pvar, extract_hash, extract_eq>;

        extract_map m_extracted;  ///< src, hi, lo -> v
        // need src -> [v] and v -> [src] for propagation?
#endif

        using slice_idx = unsigned;
        using slice_idx_vector = unsigned_vector;
        static constexpr slice_idx null_slice_idx =  std::numeric_limits<slice_idx>::max();

        static constexpr unsigned null_cut = std::numeric_limits<unsigned>::max();

        // number of bits in the slice
        // TODO: slice width is useful for debugging but we can probably drop it in release mode?
        unsigned_vector     m_slice_width;
        // Cut point: if slice represents bit-vector x, then x has been sliced into x[|x|-1:cut+1] and x[cut:0].
        // The cut point is relative to the parent slice (rather than a root variable, which might not be unique)
        // (UINT_MAX for leaf slices)
        unsigned_vector     m_slice_cut;
        // The sub-slices are at indices sub and sub+1 (null_slice_idx if no subdivision)
        slice_idx_vector    m_slice_sub;
        slice_idx_vector    m_find;         // representative of equivalence class
        slice_idx_vector    m_size;         // number of elements in equivalence class
        slice_idx_vector    m_next;         // next element of the equivalence class

        slice_idx_vector    m_var2slice;    // pvar -> slice_idx

        slice_idx alloc_slice();

        // track slice range while traversing sub-slices
        // (reference point of hi/lo is user-defined, e.g., relative to entry point of traversal)
        struct slice {
            slice_idx idx = null_slice_idx;
            unsigned hi = UINT_MAX;
            unsigned lo = UINT_MAX;
        };
        using slice_vector = svector<slice>;
        slice var2slice(pvar v) const;
        bool has_sub(slice_idx i) const { return m_slice_sub[i] != null_slice_idx; }
        bool has_sub(slice const& s) const { return has_sub(s.idx); }
        slice sub_hi(slice const& s) const;
        slice sub_lo(slice const& s) const;
        // Split a slice into two; the cut is relative to |s|...0
        void split(slice_idx s, unsigned cut);
        // Split a slice into two; NOTE: the cut point here is relative to hi/lo in s
        void split(slice const& s, unsigned cut);
        // Retrieve base slices s_1,...,s_n such that src == s_1 ++ ... + s_n
        void find_base(slice src, slice_vector& out_base) const;
        // Retrieve (or create) base slices s_1,...,s_n such that src[hi:lo] == s_1 ++ ... ++ s_n
        void mk_slice(slice src, unsigned hi, unsigned lo, slice_vector& out_base);

        // find representative
        slice_idx find(slice_idx i) const;

        // merge equivalence classes of two base slices
        void merge(slice_idx s1, slice_idx s2);

        // Equality x_1 ++ ... ++ x_n == y_1 ++ ... ++ y_k
        //
        // Precondition:
        // - sequence of base slices without holes  (TODO: condition on holes probably not necessary? total widths have to match of course)
        // - ordered from msb to lsb
        // - slices have the same reference point
        void merge(slice_vector& xs, slice_vector& ys);

        void set_extract(pvar v, pvar src, unsigned hi_bit, unsigned lo_bit);


        enum class trail_item {
            add_var,
            alloc_slice,
            split_slice,
            merge_class,
        };
        svector<trail_item> m_trail;
        slice_idx_vector    m_split_trail;
        slice_idx_vector    m_merge_trail;
        unsigned_vector     m_scopes;

        void undo_add_var();
        void undo_alloc_slice();
        void undo_split_slice();
        void undo_merge_class();


        mutable slice_vector m_tmp1;


    public:
        // slicing(solver& s): m_solver(s) {}

        void push_scope();
        void pop_scope(unsigned num_scopes = 1);

        void add_var(unsigned bit_width);








        // bool is_extract(pvar v) const { return m_src[v] != null_var; }

        /** Get variable representing x[hi:lo] */
        pvar mk_extract_var(pvar x, unsigned hi, unsigned lo);

        // /** Create expression for x[hi:lo] */
        // pdd mk_extract(pvar x, unsigned hi, unsigned lo);

        // /** Create expression for p[hi:lo] */
        // pdd mk_extract(pdd const& p, unsigned hi, unsigned lo);

        // /** Create expression for p ++ q */
        // pdd mk_concat(pdd const& p, pdd const& q);

        // propagate:
        // - value assignments
        // - fixed bits
        // - intervals ?????  -- that will also need changes in the viable algorithm
        void propagate(pvar v);
    };

}
