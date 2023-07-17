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
#include "ast/bv_decl_plugin.h"
#include "math/polysat/types.h"
#include "math/polysat/constraint.h"
#include <optional>

namespace polysat {

    class solver;

    class slicing final {

        friend class test_slicing;

        using dep_t = sat::literal;
        using dep_vector = sat::literal_vector;
        static constexpr sat::literal null_dep = sat::null_literal;

        using enode = euf::enode;
        using enode_vector = euf::enode_vector;

        static constexpr unsigned null_cut = std::numeric_limits<unsigned>::max();

        // Kinds of slices:
        // - proper (from variables)
        // - values
        // - virtual concat(...) expressions
        struct slice_info {
            unsigned    width   = 0;            // number of bits in the slice
            // Cut point: if not null_cut, the slice s has been subdivided into s[|s|-1:cut+1] and s[cut:0].
            // The cut point is relative to the parent slice (rather than a root variable, which might not be unique)
            unsigned    cut     = null_cut;     // cut point, or null_cut if no subslices
            pvar        var     = null_var;     // slice is equivalent to this variable, if any (without dependencies)
            // enode*      parent  = nullptr;      // parent slice, only for proper slices (if not null: s == sub_hi(parent(s)) || s == sub_lo(parent(s)))
            enode*      slice   = nullptr;      // if enode corresponds to a concat(...) expression, this field links to the represented slice.
            enode*      sub_hi  = nullptr;      // upper subslice s[|s|-1:cut+1]
            enode*      sub_lo  = nullptr;      // lower subslice s[cut:0]

            void reset() { *this = slice_info(); }
            bool is_slice() const { return !slice; }
            bool has_sub() const { return !!sub_hi; }
            void set_cut(unsigned cut, enode* sub_hi, enode* sub_lo) { this->cut = cut; this->sub_hi = sub_hi; this->sub_lo = sub_lo; }
        };
        using slice_info_vector = svector<slice_info>;


        solver&                 m_solver;

        ast_manager             m_ast;
        scoped_ptr<bv_util>     m_bv;
        sort_ref                m_slice_sort;
        func_decl_ref_vector    m_embed_decls;
        func_decl_ref_vector    m_concat_decls;

        euf::egraph             m_egraph;
        slice_info_vector       m_info;         // indexed by enode::get_id()
        enode_vector            m_var2slice;    // pvar -> slice





        func_decl* get_embed_decl(unsigned bit_width);
        func_decl* get_concat_decl(unsigned arity);

        static void* encode_dep(dep_t d);
        static dep_t decode_dep(void* d);
        static void display_dep(std::ostream& out, void* d);

        slice_info& info(euf::enode* n);
        slice_info const& info(euf::enode* n) const;

        enode* alloc_enode(expr* e, unsigned width, pvar var);
        enode* find_or_alloc_enode(expr* e, unsigned width, pvar var);
        enode* alloc_slice(unsigned width, pvar var = null_var);

        enode* var2slice(pvar v) const { return m_var2slice[v]; }
        pvar slice2var(enode* s) const { return info(s).var; }

        unsigned width(enode* s) const { return info(s).width; }

        bool has_sub(enode* s) const { return info(s).has_sub(); }

        /// Upper subslice (direct child, not necessarily the representative)
        enode* sub_hi(enode* s) const { return info(s).sub_hi; }

        /// Lower subslice (direct child, not necessarily the representative)
        enode* sub_lo(enode* s) const { return info(s).sub_lo; }

        // Retrieve (or create) a slice representing the given value.
        enode* mk_value_slice(rational const& val, unsigned bit_width);

        bool has_value(enode* s) const { return s->interpreted(); }

        rational get_value(enode* s) const;
        bool try_get_value(enode* s, rational& val) const;

        /// Split slice s into s[|s|-1:cut+1] and s[cut:0]
        void split(enode* s, unsigned cut);
        void split_core(enode* s, unsigned cut);

        template <bool should_get_root>
        void get_base_core(enode* src, enode_vector& out_base) const;

        /// Retrieve base slices s_1,...,s_n such that src == s_1 ++ ... ++ s_n (actual descendant subslices)
        void get_base(enode* src, enode_vector& out_base) const;
        /// Retrieve base slices s_1,...,s_n such that src == s_1 ++ ... ++ s_n (representatives of subslices)
        void get_root_base(enode* src, enode_vector& out_base) const;

        /// Retrieve (or create) base slices s_1,...,s_n such that src[hi:lo] == s_1 ++ ... ++ s_n.
        /// If output_full_src is true, return the new base for src, i.e., src == s_1 ++ ... ++ s_n.
        /// If output_base is false, return coarsest intermediate slices instead of only base slices.
        void mk_slice(enode* src, unsigned hi, unsigned lo, enode_vector& out, bool output_full_src = false, bool output_base = true);

        void begin_explain();
        void end_explain();
        void push_dep(void* dp, dep_vector& out_deps);

        // Extract reason why slices x and y are in the same equivalence class
        void explain_class(enode* x, enode* y, dep_vector& out_deps);

        // Extract reason why slices x and y are equal
        // (i.e., x and y have the same base, but are not necessarily in the same equivalence class)
        void explain_equal(enode* x, enode* y, dep_vector& out_deps);

        // Merge equivalence classes of two base slices.
        // Returns true if merge succeeded without conflict.
        [[nodiscard]] bool merge_base(enode* s1, enode* s2, dep_t dep);

        // Merge equality x_1 ++ ... ++ x_n == y_1 ++ ... ++ y_k
        //
        // Precondition:
        // - sequence of slices with equal total width
        // - ordered from msb to lsb
        //
        // The argument vectors will be cleared.
        //
        // Returns true if merge succeeded without conflict.
        [[nodiscard]] bool merge(enode_vector& xs, enode_vector& ys, dep_t dep);
        [[nodiscard]] bool merge(enode_vector& xs, enode* y, dep_t dep);
        [[nodiscard]] bool merge(enode* x, enode* y, dep_t dep);

        // Check whether two slices are known to be equal
        bool is_equal(enode* x, enode* y);

        enum class trail_item {
            add_var,
            split_core,
        };
        svector<trail_item> m_trail;
        enode_vector        m_split_trail;
        unsigned_vector     m_scopes;

        void undo_add_var();
        void undo_split_core();

        mutable enode_vector m_tmp1;
        mutable enode_vector m_tmp2;
        mutable enode_vector m_tmp3;
        ptr_vector<void>     m_tmp_justifications;
        sat::literal_set     m_marked_deps;

        // get a slice that is equivalent to the given pdd (may introduce new variable)
        enode* pdd2slice(pdd const& p);

        /** Get variable representing src[hi:lo] */
        pvar mk_slice_extract(enode* src, unsigned hi, unsigned lo);

        bool invariant() const;

        /** Get variable representing x[hi:lo] */
        pvar mk_extract_var(pvar x, unsigned hi, unsigned lo);

        std::ostream& display(std::ostream& out, enode* s) const;
        std::ostream& display_tree(std::ostream& out, enode* s, unsigned indent, unsigned hi, unsigned lo) const;

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
        std::ostream& display_tree(std::ostream& out) const;
    };

    inline std::ostream& operator<<(std::ostream& out, slicing const& s) { return s.display(out); }

}
