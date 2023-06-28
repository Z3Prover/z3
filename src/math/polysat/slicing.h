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
#include <optional>

namespace polysat {

    class solver;

    class slicing final {

        friend class test_slicing;

        solver&     m_solver;

#if 0
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

        using dep_t = sat::literal;
        using dep_vector = sat::literal_vector;
        static constexpr sat::literal null_dep = sat::null_literal;

        using slice = unsigned;
        using slice_vector = unsigned_vector;
        static constexpr slice null_slice =  std::numeric_limits<slice>::max();

        static constexpr unsigned null_cut = std::numeric_limits<unsigned>::max();

        // number of bits in the slice
        unsigned_vector m_slice_width;
        // Cut point: if slice represents bit-vector x, then x has been sliced into x[|x|-1:cut+1] and x[cut:0].
        // The cut point is relative to the parent slice (rather than a root variable, which might not be unique)
        // (UINT_MAX for leaf slices)
        unsigned_vector m_slice_cut;
        // The sub-slices are at indices sub and sub+1 (or null_slice if there is no subdivision)
        slice_vector    m_slice_sub;
        slice_vector    m_find;         // representative of equivalence class
        slice_vector    m_size;         // number of elements in equivalence class
        slice_vector    m_next;         // next element of the equivalence class

        slice_vector    m_proof_parent; // the proof forest
        dep_vector      m_proof_reason; // justification for merge of an element with its parent (in the proof forest)

        pvar_vector     m_slice2var;    // slice -> pvar, or null_var if slice is not equivalent to a variable
        slice_vector    m_var2slice;    // pvar -> slice

        unsigned_vector m_mark;
        unsigned        m_mark_timestamp = 0;
#if Z3DEBUG
        bool            m_mark_active = false;
#endif

        void begin_mark() {
            DEBUG_CODE({ SASSERT(!m_mark_active); m_mark_active = true; });
            m_mark_timestamp++;
            if (!m_mark_timestamp)
                m_mark_timestamp++;
        }
        void end_mark() { DEBUG_CODE({ SASSERT(!m_mark_active); m_mark_active = false; }); }
        bool is_marked(slice s) const { SASSERT(m_mark_active); return m_mark[s] == m_mark_timestamp; }
        void mark(slice s) { SASSERT(m_mark_active); m_mark[s] = m_mark_timestamp; }

        slice alloc_slice();

        slice var2slice(pvar v) const { return find(m_var2slice[v]); }
        pvar slice2var(slice s) const { return m_slice2var[find(s)]; }
        unsigned width(slice s) const { return m_slice_width[s]; }
        bool has_sub(slice s) const { return m_slice_sub[s] != null_slice; }

        // reverse all edges on the path from s to the root of its tree in the proof forest
        void make_proof_root(slice s);

        /// Split slice s into s[|s|-1:cut+1] and s[cut:0]
        void split(slice s, unsigned cut);
        /// Retrieve base slices s_1,...,s_n such that src == s_1 ++ ... ++ s_n
        void find_base(slice src, slice_vector& out_base) const;
        /// Retrieve (or create) base slices s_1,...,s_n such that src[hi:lo] == s_1 ++ ... ++ s_n.
        /// If output_full_src is true, return the new base for src, i.e., src == s_1 ++ ... ++ s_n.
        /// If output_base is false, return coarsest intermediate slices instead of only base slices.
        void mk_slice(slice src, unsigned hi, unsigned lo, slice_vector& out, bool output_full_src = false, bool output_base = true);

        /// Find representative
        slice find(slice s) const;
        /// Find representative of upper subslice
        slice find_sub_hi(slice s) const;
        /// Find representative of lower subslice
        slice find_sub_lo(slice s) const;

        // Merge equivalence classes of two base slices.
        // Returns true if merge succeeded without conflict.
        [[nodiscard]] bool merge_base(slice s1, slice s2, dep_t dep);

        // Extract reason for equality of base slices
        void explain_base(slice x, slice y, dep_vector& out_deps);

        // Merge equality x_1 ++ ... ++ x_n == y_1 ++ ... ++ y_k
        //
        // Precondition:
        // - sequence of slices with equal total width
        // - ordered from msb to lsb
        //
        // The argument vectors will be cleared.
        //
        // Returns true if merge succeeded without conflict.
        [[nodiscard]] bool merge(slice_vector& xs, slice_vector& ys, dep_t dep);
        [[nodiscard]] bool merge(slice_vector& xs, slice y, dep_t dep);
        [[nodiscard]] bool merge(slice x, slice y, dep_t dep);

        // Check whether two slices are known to be equal
        bool is_equal(slice x, slice y);

        enum class trail_item {
            add_var,
            alloc_slice,
            split_slice,
            merge_base,
        };
        svector<trail_item> m_trail;
        slice_vector        m_split_trail;
        svector<std::pair<slice, slice>>    m_merge_trail;  // pair of (representative, element)
        unsigned_vector     m_scopes;

        void undo_add_var();
        void undo_alloc_slice();
        void undo_split_slice();
        void undo_merge_base();


        mutable slice_vector m_tmp1;
        mutable slice_vector m_tmp2;
        mutable slice_vector m_tmp3;

        // get a slice that is equivalent to the given pdd (may introduce new variable)
        slice pdd2slice(pdd const& p);

        /** Get variable representing src[hi:lo] */
        pvar mk_slice_extract(slice src, unsigned hi, unsigned lo);

        bool invariant() const;

    public:
        slicing(solver& s): m_solver(s) {}

        void push_scope();
        void pop_scope(unsigned num_scopes = 1);

        void add_var(unsigned bit_width);

        /** Get variable representing x[hi:lo] */
        pvar mk_extract_var(pvar x, unsigned hi, unsigned lo);

        /** Create expression for x[hi:lo] */
        pdd mk_extract(pvar x, unsigned hi, unsigned lo);

        /** Create expression for p[hi:lo] */
        pdd mk_extract(pdd const& p, unsigned hi, unsigned lo);

        /** Create expression for p ++ q */
        pdd mk_concat(pdd const& p, pdd const& q);

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
