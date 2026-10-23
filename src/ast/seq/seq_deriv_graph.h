/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_deriv_graph.h

Abstract:

    The explored part G of the derivative automaton used by the landing
    decomposition, the gates (regions) built over it, and concrete language
    tests over synchronized products of views.

    Transitions are the Brzozowski cofactors of a state read as character
    intervals, so every state is syntactically the one view_witness steps to.
    G only grows; it is not part of the trailed search state.

    Characters are partitioned by every constant character and range bound
    seen (add_chars); the lower bound of a class stands for all of it.

Author:

    Clemens Eisenhofer 2026

--*/
#pragma once

#include "ast/seq/seq_view.h"
#include "ast/rewriter/guard_set.h"
#include "ast/rewriter/seq_range_predicate.h"
#include "util/obj_pair_hashtable.h"
#include "util/scoped_ptr_vector.h"
#include <map>
#include <set>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace seq {

    class deriv_graph {
    public:
        struct comp {
            view m_view;
            bool m_neg = false;
            comp(view const& v, bool neg) : m_view(v), m_neg(neg) {}
        };

        // a concrete character, or a variable constrained by the conjunction of m_comps
        struct token {
            bool           m_is_char = false;
            unsigned       m_char = 0;
            vector<comp>   m_comps;
        };
        using side = vector<token>;

    private:
        struct tr { unsigned lo, hi; expr* target; };
        struct key_hash {
            size_t operator()(std::vector<unsigned> const& k) const {
                uint64_t h = 1469598103934665603ull;
                for (unsigned x : k)
                    h = (h ^ x) * 1099511628211ull;
                return static_cast<size_t>(h);
            }
        };
        using key_set = std::unordered_set<std::vector<unsigned>, key_hash>;

        ast_manager&     m;
        seq_rewriter&    m_rw;
        seq_util&        u;
        expr_ref_vector  m_pin;
        guard_set::cache m_rp_cache;
        obj_map<expr, svector<tr>*> m_trans;
        obj_map<expr, unsigned> m_idx;
        vector<ptr_vector<expr>> m_out;
        obj_pair_hashtable<expr, expr> m_edges;
        obj_hashtable<expr> m_expanded;
        obj_hashtable<expr> m_explored;
        scoped_ptr_vector<region> m_regions;
        std::map<std::vector<unsigned>, region*> m_region_ids;
        obj_map<expr, lbool> m_nullable;
        std::set<unsigned> m_cuts;
        unsigned_vector  m_reps;
        bool             m_reps_dirty = true;
        expr_mark        m_scanned;
        expr_mark        m_pinned;
        expr_ref         m_bot;
        std::unordered_map<std::vector<unsigned>, lbool, key_hash> m_nonempty_cache;
        std::vector<unsigned> m_key;      // reused across nonempty() calls

        void pin(expr* e) { if (!m_pinned.is_marked(e)) { m_pinned.mark(e); m_pin.push_back(e); } }
        svector<tr> const* trans(expr* r);
        ptr_vector<expr> const& out(expr* p);
        void add_cut(unsigned c);
        region const* mk_region(ptr_vector<expr> const& states);
        lbool accepts(comp const& c, expr* s);
        lbool nonempty_core(vector<side> const& sides, unsigned budget);

    public:
        deriv_graph(seq_rewriter& rw);
        ~deriv_graph();

        bool supported(expr* r) { return trans(r) != nullptr; }
        // Brzozowski successor; nullptr if the cofactors of r are not character intervals
        expr* step(expr* r, unsigned c);
        // the non-empty successors of r, one per target, with the characters leading there
        bool successors(expr* r, vector<std::pair<expr*, range_predicate>>& out);
        // does the run of a view end accepting at s
        lbool accepts(view const& v, expr* s) { return accepts(comp(v, false), s); }
        void record(expr* p, expr* q);
        void explore(expr* r, unsigned budget);
        bool on_cycle(expr* r);
        region const* reach_region(expr* r);
        region const* singleton(expr* r);
        void sweep(region const& q);

        void add_chars(expr* e);
        // the constant characters of e in pre-order, each once
        void chars_in_order(expr* e, unsigned_vector& out);
        unsigned_vector const& reps();

        // shortest run length d from the start to the target of a gated view, and the gcd of all run lengths - d
        bool length_info(view const& v, unsigned& d, unsigned& period);
        // is there a word matched by every side simultaneously
        lbool nonempty(vector<side> const& sides, unsigned budget = 20000);
    };

}
