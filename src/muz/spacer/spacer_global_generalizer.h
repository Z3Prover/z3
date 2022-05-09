#pragma once
/*++
Copyright (c) 2020 Arie Gurfinkel

Module Name:

  spacer_global_generalizer.h

Abstract:

  Global Guidance for Spacer

Author:

  Hari Govind V K
  Arie Gurfinkel


--*/

#include "muz/spacer/spacer_context.h"
#include "muz/spacer/spacer_convex_closure.h"

namespace spacer {

/// Global guided generalization
///
/// See Hari Govind et al. Global Guidance for Local Generalization in Model
/// Checking. CAV 2020
class lemma_global_generalizer : public lemma_generalizer {
    /// Subsumption strategy
    class subsumer {
        struct stats {
            unsigned m_num_syn_cls;
            unsigned m_num_mbp_failed;
            unsigned m_num_no_ovr_approx;

            stopwatch watch;
            stats() { reset(); }
            void reset() {
                watch.reset();
                m_num_syn_cls = 0;
                m_num_mbp_failed = 0;
                m_num_no_ovr_approx = 0;
            }
        };
        stats m_st;

        ast_manager &m;
        arith_util m_arith;
        bv_util m_bv;

        // boolean variables used as local tags
        app_ref_vector m_tags;
        // number of tags currently used
        unsigned m_used_tags;

        // convex closure interface
        convex_closure m_cvx_cls;

        // save fresh constants for mbp
        app_ref_vector m_dim_frsh_cnsts;

        // save vars from cluster pattern
        var_ref_vector m_dim_vars;

        // create pob without free vars
        bool m_ground_pob;

        // Local solver to get model for computing mbp and to check whether
        // cvx_cls  ==> mbp
        ref<solver> m_solver;

        /// Return a fresh boolean variable
        app *mk_fresh_tag();

        /// Prepare internal state for computing subsumption
        void setup(const lemma_cluster &lc);

        /// Returns false if subsumption is not supported for given cluster
        bool is_handled(const lemma_cluster &lc);

        /// Find a representative for \p c
        expr *find_repr(const model_ref &mdl, const app *c);

        /// Skolemize m_dim_frsh_cnsts in \p f
        ///
        /// \p cnsts is appended with ground terms from \p mdl
        void skolemize(expr_ref &f, const model_ref &mdl,
                       app_ref_vector &cnsts);

        /// Create new vars to compute convex cls
        void add_dim_vars(const lemma_cluster &lc);

        /// Coerce LIA constants in \p m_dim_frsh_cnsts to LRA constants
        void to_real_cnsts();

        /// Populate \p m_cvx_cls
        ///
        /// 1. Collect all substitutions in the cluster \p lc
        /// 2. Convert all substitutions to integer numerals
        void populate_cvx_cls(const lemma_cluster &lc);

        /// Make \p fml ground using m_dim_frsh_cnsts. Store result in \p out
        void ground_free_vars(expr *fml, expr_ref &out);

        /// Weaken \p a such that (and a) overapproximates \p b
        bool over_approximate(expr_ref_vector &a, const expr_ref b);

        /// \p a is a hard constraint and \p b is a soft constraint that have to
        /// be satisfied by \p mdl
        bool maxsat_with_model(const expr_ref &hard, const expr_ref &soft,
                               model_ref &out_model);

        /// Eliminate m_dim_frsh_cnsts from \p cvx_cls
        ///
        /// Uses \p lc to get a model for mbp.
        /// \p mlir indicates whether \p cvx_cls contains both ints and reals.
        /// all vars that could not be eliminated are skolemized and added to \p
        /// bindings
        bool eliminate_vars(expr_ref &cvx_cls, const lemma_cluster &lc,
                            bool mlir, app_ref_vector &bindings);

        /// Add variables introduced by m_cvx_cls to the list of variables to be
        /// eliminated
        void add_cvx_cls_vars();

      public:
        subsumer(ast_manager &m, bool use_sage, bool ground_pob);

        void collect_statistics(statistics &st) const;

        /// Compute a cube \p res such that \neg p subsumes all the lemmas in \p
        /// lc
        ///
        /// \p cnsts is a set of constants that can be used to make \p res
        /// ground
        bool subsume(const lemma_cluster &lc, expr_ref_vector &res,
                     app_ref_vector &cnsts);
    };

    struct stats {
        unsigned m_num_cls_ofg;
        unsigned m_num_syn_cls;
        unsigned m_num_mbp_failed;
        unsigned m_num_non_lin;
        unsigned m_num_no_ovr_approx;
        unsigned m_num_cant_abs;

        stopwatch watch;
        stats() { reset(); }
        void reset() {
            watch.reset();
            m_num_cls_ofg = 0;
            m_num_non_lin = 0;
            m_num_syn_cls = 0;
            m_num_mbp_failed = 0;
            m_num_no_ovr_approx = 0;
            m_num_cant_abs = 0;
        }
    };
    stats m_st;
    ast_manager &m;
    subsumer m_subsumer;

    /// Decide global guidance based on lemma
    void generalize(lemma_ref &lemma);

    /// Attempt to set a conjecture on pob \p n.
    ///
    /// Done by dropping literal \p lit from
    /// post of \p n. \p lvl is level for conjecture pob. \p gas is the gas for
    /// the conjecture pob returns true if conjecture is set
    bool do_conjecture(pob_ref &n, const expr_ref &lit, unsigned lvl,
                       unsigned gas);

    /// Enable/disable subsume rule
    bool m_do_subsume;

  public:
    lemma_global_generalizer(context &ctx);
    ~lemma_global_generalizer() override {}

    void operator()(lemma_ref &lemma) override;

    void collect_statistics(statistics &st) const override;
    void reset_statistics() override { m_st.reset(); }

    // post-actions for pobs produced during generalization
    pob *mk_concretize_pob(pob &n, model_ref &model);
    pob *mk_subsume_pob(pob &n);
    pob *mk_conjecture_pob(pob &n);
};
} // namespace spacer
