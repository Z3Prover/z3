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
#include "util/trail.h"
#include "util/union_find.h"

namespace polysat {

    class solver;

    class slicing final {

        solver&     s;

        /// If y := x[h:l], then m_src[y] = x, m_hi[y] = h, m_lo[y] = l.
        /// Otherwise m_src[y] = null_var.
        ///
        /// Invariants:
        ///     m_src[y] != null_var ==> m_src[y] < y  (at least as long as we always introduce new variables for extract terms.)
        ///     m_lo[y] <= m_hi[y]
        unsigned_vector m_src;
        unsigned_vector m_hi;
        unsigned_vector m_lo;

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




        trail_stack         m_stack;

        using slice_idx = unsigned;
        static constexpr slice_idx null_slice_idx = UINT_MAX;

        struct slice {
            // If sub != null_slice_idx, the bit-vector x has been sliced into x[|x|-1:cut+1] and x[cut:0]
            unsigned  cut = UINT_MAX;
            // If sub != null_slice_idx, the sub-slices are at indices sub and sub+1
            slice_idx sub = null_slice_idx;

            bool has_sub() const { return cut != 0; }
            slice_idx sub_hi() const { return sub; }
            slice_idx sub_lo() const { return sub + 1; }
        };
        svector<slice>      m_slices;       // slice_idx -> slice
        svector<slice_idx>  m_var_slices;   // pvar -> slice_idx

        // union_find over slices (union_find vars are indices into m_slices, i.e., slice_idx)
        union_find<slicing> m_slices_uf;

        slice_idx alloc_slice();

        friend class alloc_slice_trail;
        class alloc_slice_trail : public trail {
            slicing& m_owner;
        public:
            alloc_slice_trail(slicing& o): m_owner(o) {}
            void undo() override;
        };
        alloc_slice_trail m_alloc_slice_trail;

        void set_extract(pvar v, pvar src, unsigned hi_bit, unsigned lo_bit);

        struct slice_info {
            slice_idx idx;
            unsigned hi;
            unsigned lo;
        };
        slice_info var2slice(pvar v) const;
        bool has_sub(slice_info const& si) const { return m_slices[si.idx].has_sub(); }
        slice_info sub_hi(slice_info const& si) const;
        slice_info sub_lo(slice_info const& si) const;
        unsigned get_cut(slice_info const& si) const;
        void split(slice_info const& si, unsigned cut);
        void mk_slice(slice_info const& src, unsigned hi, unsigned lo, vector<slice_info>& out);

    public:
        slicing(solver& s):
            s(s),
            m_slices_uf(*this),
            m_alloc_slice_trail(*this)
        {}

        trail_stack& get_trail_stack() { return m_stack; }

        void push_var();
        void pop_var();

        bool is_extract(pvar v) const { return m_src[v] != null_var; }

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
    };

}
