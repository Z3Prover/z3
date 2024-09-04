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

        // save fresh constants for mbp
        app_ref_vector m_col_names;
        vector<rational> m_col_lcm;

        // create pob without free vars
        bool m_ground_pob;

        // Local solver to get model for computing mbp and to check whether
        // cvx_cls  ==> mbp
        ref<solver> m_solver;

        /// Return a fresh boolean variable
        app *mk_fresh_tag();

        void reset();

        /// Returns false if subsumption is not supported for given cluster
        bool is_handled(const lemma_cluster &lc);

        /// Find a representative for \p c
        expr *find_repr(const model_ref &mdl, const app *c);

        /// Skolemize m_dim_frsh_cnsts in \p f
        ///
        /// \p cnsts is appended with ground terms from \p mdl
        void skolemize_for_quic3(expr_ref &f, const model_ref &mdl,
                                 app_ref_vector &cnsts);

        /// Create new vars to compute convex cls
        void mk_col_names(const lemma_cluster &lc);

        void setup_cvx_closure(convex_closure &cc, const lemma_cluster &lc);

        /// Make \p fml ground using m_dim_frsh_cnsts. Store result in \p out
        void ground_free_vars(expr *fml, expr_ref &out);

        /// Weaken \p a such that (and a) overapproximates \p b
        bool over_approximate(expr_ref_vector &a, const expr_ref b);

        bool find_model(const expr_ref_vector &cc,
                        const expr_ref_vector &alphas, expr *bg,
                        model_ref &out_model);

        bool is_numeral(const expr *e, rational &n) {
            return m_arith.is_numeral(e, n) || m_bv.is_numeral(e, n);
        }

        expr *mk_rat_mul(rational n, expr *v) {
            if (n.is_one()) return v;
            return m_arith.mk_mul(m_arith.mk_numeral(n, m_arith.is_int(v)), v);
        }

      public:
        subsumer(ast_manager &m, bool ground_pob);

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
  bool do_conjecture(pob_ref &n, lemma_ref &lemma, const expr_ref &lit, unsigned lvl,
                       unsigned gas);

    /// Enable/disable subsume rule
    bool m_do_subsume;

  public:
    lemma_global_generalizer(context &ctx);

    void operator()(lemma_ref &lemma) override;

    void collect_statistics(statistics &st) const override;
    void reset_statistics() override { m_st.reset(); }

    // post-actions for pobs produced during generalization
    pob *mk_concretize_pob(pob &n, model_ref &model);
    pob *mk_subsume_pob(pob &n);
    pob *mk_conjecture_pob(pob &n);
};
} // namespace spacer
