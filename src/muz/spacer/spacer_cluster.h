#pragma once
/*++
Copyright (c) 2020 Arie Gurfinkel

Module Name:

  spacer_cluster.h

Abstract:

  Discover and mark lemma clusters

Author:

  Hari Govind V K
  Arie Gurfinkel


--*/

#include <ast/ast_util.h>
#include <ast/substitution/substitution.h>
#include <muz/spacer/spacer_sem_matcher.h>
#include <util/ref_vector.h>
#include <util/statistics.h>
#include <util/stopwatch.h>

#define GAS_POB_COEFF 5

namespace spacer {
class lemma;
using lemma_ref = ref<lemma>;

/// Representation of a cluster of lemmas
///
/// A cluster of lemmas is a collection of lemma instances. A cluster is
/// defined by a \p pattern that is a qff formula with free variables, and
/// contains lemmas that are instances of the pattern (i.e., obtained from the
/// pattern by substitution of constants for variables). That is, each lemma
/// in the cluster matches the pattern.
class lemma_cluster {
    /// Lemma in a cluster
    ///
    /// A lemma and a substitution witnessing that lemma is an instance of a
    /// pattern
    class lemma_info {
        // a lemma
        lemma_ref m_lemma;
        // a substitution such that for some pattern, \p m_lemma is an instance
        // substitution is stored in std_order for quantifiers (i.e., reverse of
        // expected)
        substitution m_sub;

      public:
        lemma_info(const lemma_ref &body, const substitution &sub)
            : m_lemma(body), m_sub(sub) {}

        const lemma_ref &get_lemma() const { return m_lemma; }
        const substitution &get_sub() const { return m_sub; }
    };

  public:
    using lemma_info_vector = vector<lemma_cluster::lemma_info, true>;

  private:
    ast_manager &m;
    arith_util m_arith;
    bv_util m_bv;

    // reference counter
    unsigned m_ref_count;
    // pattern defining the cluster
    expr_ref m_pattern;
    unsigned m_num_vars;

    // vector of lemmas in the cluster
    lemma_info_vector m_lemma_vec;

    // shared matcher object to match lemmas against the pattern
    sem_matcher m_matcher;

    // The number of times CSM has to be tried using this cluster
    unsigned m_gas;

    /// Remove subsumed lemmas in the cluster.
    ///
    /// Returns list of removed lemmas in \p removed_lemmas
    void rm_subsumed(lemma_info_vector &removed_lemmas);

    /// Checks whether \p e matches m_pattern.
    ///
    /// Returns true on success and sets \p sub to the corresponding
    /// substitution
    bool match(const expr_ref &e, substitution &sub);

    ast_manager &get_manager() const { return m; }

  public:
    lemma_cluster(const expr_ref &pattern);
    lemma_cluster(const lemma_cluster &other);

    const lemma_info_vector &get_lemmas() const { return m_lemma_vec; }

    void dec_gas() {
        if (m_gas > 0) m_gas--;
    }

    unsigned get_gas() const { return m_gas; }
    unsigned get_pob_gas() const { return GAS_POB_COEFF * m_lemma_vec.size(); }

    /// Get a conjunction of all the lemmas in cluster
    void get_conj_lemmas(expr_ref &e) const;

    /// Try to add \p lemma to cluster. Remove subsumed lemmas if \p subs_check
    /// is true
    ///
    /// Returns false if lemma does not match the pattern or if it is already in
    /// the cluster Repetition of lemmas is avoided by doing a linear scan over
    /// the lemmas in the cluster. Adding a lemma can reduce the size of the
    /// cluster due to subs_check
    bool add_lemma(const lemma_ref &lemma, bool subsume = false);

    bool contains(const lemma_ref &lemma);
    bool can_contain(const lemma_ref &lemma);

    /// Return the minimum level of lemmas in he cluster
    unsigned get_min_lvl();

    lemma_cluster::lemma_info *get_lemma_info(const lemma_ref &lemma);
    unsigned get_size() const { return m_lemma_vec.size(); }
    const expr_ref &get_pattern() const { return m_pattern; }

    void inc_ref() { ++m_ref_count; }
    void dec_ref() {
        --m_ref_count;
        if (m_ref_count == 0) { dealloc(this); }
    }
};

class lemma_cluster_finder {
    struct stats {
        unsigned max_group_size;
        stopwatch watch;
        stats() { reset(); }
        void reset() {
            max_group_size = 0;
            watch.reset();
        }
    };
    stats m_st;
    ast_manager &m;
    arith_util m_arith;
    bv_util m_bv;

    /// Check whether \p cube and \p lcube differ only in interpreted constants
    bool are_neighbours(const expr_ref &cube, const expr_ref &lcube);

    /// N-ary antiunify
    ///
    /// Returns whether there is a substitution with only interpreted consts
    bool anti_unify_n_intrp(const expr_ref &cube, expr_ref_vector &fmls,
                            expr_ref &res);

  public:
    lemma_cluster_finder(ast_manager &m);

    /// Add a new lemma \p lemma to a cluster
    ///
    /// Creates a new cluster for the lemma if necessary
    void cluster(lemma_ref &lemma);
    void collect_statistics(statistics &st) const;
    void reset_statistics() { m_st.reset(); }
};

using lemma_info_vector = lemma_cluster::lemma_info_vector;
} // namespace spacer
