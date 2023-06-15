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

        friend class test_slicing;

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

        using slice = unsigned;
        using slice_vector = unsigned_vector;
        static constexpr slice null_slice =  std::numeric_limits<slice>::max();

        static constexpr unsigned null_cut = std::numeric_limits<unsigned>::max();

        // number of bits in the slice
        unsigned_vector     m_slice_width;
        // Cut point: if slice represents bit-vector x, then x has been sliced into x[|x|-1:cut+1] and x[cut:0].
        // The cut point is relative to the parent slice (rather than a root variable, which might not be unique)
        // (UINT_MAX for leaf slices)
        unsigned_vector     m_slice_cut;
        // The sub-slices are at indices sub and sub+1 (null_slice if no subdivision)
        slice_vector    m_slice_sub;
        slice_vector    m_find;         // representative of equivalence class
        slice_vector    m_size;         // number of elements in equivalence class
        slice_vector    m_next;         // next element of the equivalence class

        slice_vector    m_var2slice;    // pvar -> slice

        slice alloc_slice();

        slice var2slice(pvar v) const { return find(m_var2slice[v]); }
        unsigned width(slice s) const { return m_slice_width[s]; }
        bool has_sub(slice s) const { return m_slice_sub[s] != null_slice; }

        /// Split slice s into s[|s|-1:cut+1] and s[cut:0]
        void split(slice s, unsigned cut);
        /// Retrieve base slices s_1,...,s_n such that src == s_1 ++ ... + s_n
        void find_base(slice src, slice_vector& out_base) const;
        // Retrieve (or create) base slices s_1,...,s_n such that src[hi:lo] == s_1 ++ ... ++ s_n
        // If output_full_src is true, returns the new base for src, i.e., src == s_1 ++ ... ++ s_n
        void mk_slice(slice src, unsigned hi, unsigned lo, slice_vector& out_base, bool output_full_src = false);

        /// Find representative
        slice find(slice s) const;
        /// Find representative of upper subslice
        slice find_sub_hi(slice s) const;
        /// Find representative of lower subslice
        slice find_sub_lo(slice s) const;

        // Merge equivalence classes of two base slices
        void merge(slice s1, slice s2);

        // Merge equality x_1 ++ ... ++ x_n == y_1 ++ ... ++ y_k
        //
        // Precondition:
        // - sequence of base slices (equal total width)
        // - ordered from msb to lsb
        void merge(slice_vector& xs, slice_vector& ys);
        void merge(slice_vector& xs, slice y);

        void set_extract(pvar v, pvar src, unsigned hi_bit, unsigned lo_bit);


        enum class trail_item {
            add_var,
            alloc_slice,
            split_slice,
            merge_class,
        };
        svector<trail_item> m_trail;
        slice_vector    m_split_trail;
        slice_vector    m_merge_trail;
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

        std::ostream& display(std::ostream& out) const;
        std::ostream& display(std::ostream& out, slice s) const;
    };

    inline std::ostream& operator<<(std::ostream& out, slicing const& s) { return s.display(out); }

}
