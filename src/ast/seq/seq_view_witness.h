/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    seq_view_witness.h

Abstract:

    Incremental non-emptiness checking for products of sequence views.

--*/
#pragma once

#include "ast/rewriter/guard_set.h"
#include "ast/rewriter/seq_range_collapse.h"
#include "ast/seq/seq_regex_live.h"
#include "ast/seq/seq_view.h"
#include "util/trail.h"
#include <functional>
#include <map>
#include <unordered_map>
#include <vector>

namespace seq {

    enum class view_failure_reason {
        none,
        unsupported,
        budget,
        resource,
        state_expansion,
        nullability,
        guard
    };

    class view_witness {
        struct assertion {
            expr_ref m_var;
            view     m_view;
            void*    m_dependency;

            assertion(expr* var, view const& v, void* dependency, ast_manager& m) :
                m_var(var, m), m_view(v), m_dependency(dependency) {}
        };

        struct ivl_range {
            unsigned lo, hi, first, count;
        };

        struct ivl_list {
            svector<ivl_range> ranges;
            ptr_vector<expr>   targets;
            bool               ok = true;
        };

        using key = std::vector<unsigned>;

        struct key_hash {
            size_t operator()(key const& k) const {
                uint64_t h = 1469598103934665603ull;
                for (unsigned x : k)
                    h = (h ^ x) * 1099511628211ull;
                return static_cast<size_t>(h);
            }
        };

        using signature = std::vector<view::sig>;

        struct signature_hash {
            size_t operator()(signature const& s) const {
                uint64_t h = 1469598103934665603ull;
                for (auto const& p : s) {
                    h = (h ^ p.state) * 1099511628211ull;
                    h = (h ^ p.target) * 1099511628211ull;
                }
                return static_cast<size_t>(h);
            }
        };

        ast_manager&      m;
        seq_rewriter&     m_rw;
        trail_stack&      m_trail;
        live_states&      m_live;
        transition_mode   m_mode;
        vector<assertion> m_assertions;
        ptr_vector<void>  m_core;
        obj_map<expr, expr*> m_witnesses;
        expr_ref_vector   m_pin;
        expr_ref_vector   m_witness_pin;
        guard_set::cache  m_rp_cache;
        obj_map<expr, ivl_list*> m_ivl_cache;
        expr_ref_vector   m_ivl_pin;
        obj_map<expr, char> m_nullable_cache;
        std::unordered_map<signature, lbool, signature_hash> m_product_cache;
        std::function<view_failure_reason()> m_checkpoint;
        view_failure_reason m_failure = view_failure_reason::none;
        lbool            m_last_result = l_undef;
        bool             m_enable_witness = false;
        unsigned         m_cofactor_calls = 0;
        unsigned         m_states = 0;
        unsigned         m_max_state_expansion = 0;

        seq_util& u() const { return m_rw.u(); }
        seq_util::rex& re() const { return m_rw.u().re; }

        expr_ref_pair_vector const& derivative_cofactors(expr* r);
        ivl_list const* interval_cofactors(expr* r, expr* v0);
        void reset_ivl_cache();
        bool checkpoint();
        static void dedup_views(view_vector const& in, view_vector& out);
        static signature mk_signature(view_vector const& views);
        void minimize_core(expr* var, unsigned_vector const& indices);

    public:
        view_witness(trail_stack& t, seq_rewriter& rw, live_states& live,
                     transition_mode mode = transition_mode::light_antimirov_tm);
        ~view_witness();

        void add(expr* x, view const& v, void* dependency);
        lbool check();
        ptr_vector<void> core() const { return m_core; }
        expr_ref materialize_witness(expr* x);
        void set_enable_witness(bool f) { m_enable_witness = f; }
        void set_enable_witnes(bool f) { set_enable_witness(f); }
        view_failure_reason get_failure_reason() const { return m_failure; }

        lbool product_nonempty(expr* var, view_vector const& views, expr_ref* witness = nullptr);
        lbool nullable(expr* r);
        void set_checkpoint(std::function<view_failure_reason()> const& checkpoint) {
            m_checkpoint = checkpoint;
        }
        void reset_cache();

        unsigned cofactor_calls() const { return m_cofactor_calls; }
        unsigned states() const { return m_states; }
        unsigned max_state_expansion() const { return m_max_state_expansion; }
    };
}
