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
#include "ast/euf/euf_egraph.h"
#include "math/polysat/types.h"
#include "math/polysat/constraint.h"
#include <optional>

namespace polysat {

    class solver;

    class slicing final {

        friend class test_slicing;

        solver&     m_solver;

        ast_manager m_ast;
        euf::egraph m_egraph;

        sort*                   m_slice_sort;
        ptr_vector<func_decl>   m_concat_decls;

        func_decl* get_concat_decl(unsigned arity);

        using dep_t = sat::literal;
        using dep_vector = sat::literal_vector;
        static constexpr sat::literal null_dep = sat::null_literal;
        void* encode_dep(dep_t d);
        dep_t decode_dep(void* d);

        using slice = unsigned;
        using slice_vector = unsigned_vector;
        static constexpr slice null_slice = std::numeric_limits<slice>::max();

        static constexpr unsigned null_cut = std::numeric_limits<unsigned>::max();

        struct slice_info {
            unsigned width = 0;
            unsigned cut = null_cut;
            euf::enode* sub_hi = nullptr;
            euf::enode* sub_lo = nullptr;
        };

        // using enode = euf::enode<slice_extra>;

        struct val2slice_key {
            rational value;
            unsigned bit_width;

            val2slice_key() {}
            val2slice_key(rational value, unsigned bit_width): value(std::move(value)), bit_width(bit_width) {}

            bool operator==(val2slice_key const& other) const {
                return bit_width == other.bit_width && value == other.value;
            }

            unsigned hash() const {
                return combine_hash(value.hash(), bit_width);
            }
        };
        using val2slice_hash = obj_hash<val2slice_key>;
        using val2slice_eq = default_eq<val2slice_key>;
        using val2slice_map = map<val2slice_key, slice, val2slice_hash, val2slice_eq>;

        unsigned_vector m_slice_width;  // number of bits in the slice
        // Cut point: if slice represents bit-vector x, then x has been sliced into x[|x|-1:cut+1] and x[cut:0].
        // The cut point is relative to the parent slice (rather than a root variable, which might not be unique)
        // (null_cut for leaf slices)
        unsigned_vector m_slice_cut;
        // The sub-slices are at indices sub and sub+1 (or null_slice if there is no subdivision)
        slice_vector    m_slice_sub;

        pvar_vector     m_slice2var;    // slice -> pvar, or null_var if slice is not equivalent to a variable
        slice_vector    m_var2slice;    // pvar -> slice

        // app_ref_vector  m_slice2app;    // slice -> app*
        // ptr_addr_map<app, slice> m_app2slice;

        ptr_vector<euf::enode>  m_slice2enode;
        ptr_addr_map<euf::enode, slice> m_enode2slice;
        expr_ref_vector m_expr_storage;
        unsigned_vector m_expr_scopes;

#if 0
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
        void end_mark() { DEBUG_CODE({ SASSERT(m_mark_active); m_mark_active = false; }); }
        bool is_marked(slice s) const { SASSERT(m_mark_active); return m_mark[s] == m_mark_timestamp; }
        void mark(slice s) { SASSERT(m_mark_active); m_mark[s] = m_mark_timestamp; }
#endif

        slice alloc_slice(unsigned width);

        slice var2slice(pvar v) const { return m_var2slice[v]; }
        pvar slice2var(slice s) const { return m_slice2var[s]; }
        // slice app2slice(app* a) const { return m_app2slice[a]; }
        // app* slice2app(slice s) const { return m_slice2app[s]; }
        slice enode2slice(euf::enode* n) const { return m_enode2slice[n]; }
        euf::enode* slice2enode(slice s) const { return m_slice2enode[s]; }

        unsigned width(slice s) const { return m_slice_width[s]; }

        bool has_sub(slice s) const { return m_slice_sub[s] != null_slice; }
        /// Upper subslice (direct child, not necessarily the representative)
        slice sub_hi(slice s) const;
        euf::enode* sub_hi(euf::enode* n) const;
        /// Lower subslice (direct child, not necessarily the representative)
        slice sub_lo(slice s) const;
        euf::enode* sub_lo(euf::enode* n) const;

        // slice val2slice(rational const& val, unsigned bit_width) const;

        // Retrieve (or create) a slice representing the given value.
        // slice mk_value_slice(rational const& val, unsigned bit_width);

        // bool has_value(slice s) const { SASSERT_EQ(s, find(s)); return m_slice2val[s].is_nonneg(); }
        // rational const& get_value(slice s) const { SASSERT(has_value(s)); return m_slice2val[s]; }

        // reverse all edges on the path from s to the root of its tree in the proof forest
        // void make_proof_root(slice s);

        /// Split slice s into s[|s|-1:cut+1] and s[cut:0]
        void split(slice s, unsigned cut);
        void split_core(slice s, unsigned cut);

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

        // Merge equality s == val and propagate the value downward into sub-slices.
        // Returns true if merge succeeded without conflict.
        [[nodiscard]] bool merge_value(slice s, rational val, dep_t dep);

        void push_reason(slice s, dep_vector& out_deps);

        // Extract reason why slices x and y are in the same equivalence class
        void explain_class(slice x, slice y, dep_vector& out_deps);

        // Extract reason why slices x and y are equal
        // (i.e., x and y have the same base, but are not necessarily in the same equivalence class)
        void explain_equal(slice x, slice y, dep_vector& out_deps);

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
            split_core,
            merge_base,
            mk_value_slice,
        };
        svector<trail_item> m_trail;
        slice_vector        m_split_trail;
        vector<val2slice_key>               m_val2slice_trail;
        unsigned_vector     m_scopes;

        void undo_add_var();
        void undo_alloc_slice();
        void undo_split_core();
        void undo_mk_value_slice();

        mutable slice_vector m_tmp1;
        mutable slice_vector m_tmp2;
        mutable slice_vector m_tmp3;

        // get a slice that is equivalent to the given pdd (may introduce new variable)
        slice pdd2slice(pdd const& p);

        /** Get variable representing src[hi:lo] */
        pvar mk_slice_extract(slice src, unsigned hi, unsigned lo);

        bool invariant() const;

        /** Get variable representing x[hi:lo] */
        pvar mk_extract_var(pvar x, unsigned hi, unsigned lo);

    public:
        slicing(solver& s);

        void push_scope();
        void pop_scope(unsigned num_scopes = 1);

        void add_var(unsigned bit_width);

        /** Create expression for x[hi:lo] */
        pdd mk_extract(pvar x, unsigned hi, unsigned lo);

        /** Create expression for p[hi:lo] */
        pdd mk_extract(pdd const& p, unsigned hi, unsigned lo);

        /** Create expression for p ++ q */
        pdd mk_concat(pdd const& p, pdd const& q);

        // Track value assignments to variables (and propagate to subslices)
        // (could generalize to fixed bits, then we need a way to merge interpreted enodes)
        void add_value(pvar v, rational const& value);
        void add_constraint(signed_constraint c);

        // TODO:
        // Query for a given variable v:
        // - set of variables that share at least one slice with v (need variable, offset/width relative to v)

        std::ostream& display(std::ostream& out) const;
        std::ostream& display(std::ostream& out, slice s) const;

        std::ostream& display_tree(std::ostream& out) const;
        std::ostream& display_tree(std::ostream& out, slice s, unsigned indent, unsigned hi, unsigned lo) const;
    };

    inline std::ostream& operator<<(std::ostream& out, slicing const& s) { return s.display(out); }

}
