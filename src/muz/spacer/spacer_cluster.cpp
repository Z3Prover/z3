/*++
Copyright (c) 2020 Arie Gurfinkel

Module Name:

  spacer_cluster.cpp

Abstract:

  Discover and mark lemma clusters

Author:

  Hari Govind V K
  Arie Gurfinkel


--*/
#include <algorithm>

#include "ast/arith_decl_plugin.h"
#include "ast/ast_util.h"
#include "ast/rewriter/var_subst.h"
#include "ast/substitution/substitution.h"
#include "muz/spacer/spacer_antiunify.h"
#include "muz/spacer/spacer_cluster.h"
#include "muz/spacer/spacer_context.h"
#include "muz/spacer/spacer_manager.h"
#include "muz/spacer/spacer_util.h"
#include "smt/tactic/unit_subsumption_tactic.h"
#include "util/mpq.h"
#include "util/vector.h"

#define MAX_CLUSTER_SIZE 5
#define MAX_CLUSTERS 5
#define GAS_INIT 10

namespace spacer {

using var_offset = std::pair<unsigned, unsigned>;

lemma_cluster::lemma_cluster(const expr_ref &pattern)
    : m(pattern.get_manager()), m_arith(m), m_bv(m), m_ref_count(0),
      m_pattern(pattern), m_matcher(m), m_gas(GAS_INIT) {
    m_num_vars = get_num_vars(m_pattern);
}

lemma_cluster::lemma_cluster(const lemma_cluster &other)
    : m(other.get_manager()), m_arith(m), m_bv(m), m_ref_count(0),
      m_pattern(other.get_pattern()), m_num_vars(other.m_num_vars),
      m_matcher(m), m_gas(other.get_gas()) {
    for (const auto &li : other.get_lemmas()) { m_lemma_vec.push_back(li); }
}

/// Get a conjunction of all the lemmas in cluster
void lemma_cluster::get_conj_lemmas(expr_ref &e) const {
    expr_ref_vector conj(m);
    for (const auto &lem : get_lemmas()) {
        conj.push_back(lem.get_lemma()->get_expr());
    }
    e = mk_and(conj);
}

bool lemma_cluster::contains(const lemma_ref &lemma) {
    for (const auto &li : get_lemmas()) {
        if (lemma->get_expr() == li.get_lemma()->get_expr()) return true;
    }
    return false;
}

unsigned lemma_cluster::get_min_lvl() {
    if (m_lemma_vec.empty()) return 0;
    unsigned lvl = m_lemma_vec[0].get_lemma()->level();
    for (auto l : m_lemma_vec) { lvl = std::min(lvl, l.get_lemma()->level()); }
    // if all lemmas are at infinity, use the level of the lowest pob
    if (is_infty_level(lvl)) {
        for (auto l : m_lemma_vec) {
          if (l.get_lemma()->has_pob())
            lvl = std::min(lvl, l.get_lemma()->get_pob()->level());
        }
    }
    return lvl;
}

/// Checks whether \p e matches the pattern of the cluster
/// Returns true on success and set \p sub to the corresponding substitution
bool lemma_cluster::match(const expr_ref &e, substitution &sub) {
    bool pos;
    var_offset var;
    expr_offset r;

    m_matcher.reset();
    bool is_match = m_matcher(m_pattern, e, sub, pos);
    if (!(is_match && pos)) return false;

    unsigned n_binds = sub.get_num_bindings();
    auto is_numeral = [&](expr *e) {
        return m_arith.is_numeral(e) || m_bv.is_numeral(e);
    };
    // All the matches should be numerals
    for (unsigned i = 0; i < n_binds; i++) {
        sub.get_binding(i, var, r);
        if (!is_numeral(r.get_expr())) return false;
    }
    return true;
}

bool lemma_cluster::can_contain(const lemma_ref &lemma) {
    substitution sub(m);
    expr_ref cube(m);

    sub.reserve(1, m_num_vars);
    cube = mk_and(lemma->get_cube());
    normalize_order(cube, cube);
    return match(cube, sub);
}

lemma_cluster::lemma_info *
lemma_cluster::get_lemma_info(const lemma_ref &lemma) {
    SASSERT(contains(lemma));
    for (auto &li : m_lemma_vec) {
        if (lemma == li.get_lemma()) { return &li; }
    }
    UNREACHABLE();
    return nullptr;
}

/// Removes subsumed lemmas in the cluster
///
/// Removed lemmas are placed into \p removed_lemmas
void lemma_cluster::rm_subsumed(lemma_info_vector &removed_lemmas) {
    removed_lemmas.reset();
    if (m_lemma_vec.size() <= 1) return;

    // set up and run the simplifier
    tactic_ref simplifier = mk_unit_subsumption_tactic(m);
    goal_ref g(alloc(goal, m, false, false, false));
    goal_ref_buffer result;
    for (auto l : m_lemma_vec) { g->assert_expr(l.get_lemma()->get_expr()); }
    (*simplifier)(g, result);

    SASSERT(result.size() == 1);
    goal *r = result[0];

    // nothing removed
    if (r->size() == m_lemma_vec.size()) return;

    // collect removed lemmas
    lemma_info_vector keep;
    for (auto lem : m_lemma_vec) {
        bool found = false;
        for (unsigned i = 0; i < r->size(); i++) {
            if (lem.get_lemma()->get_expr() == r->form(i)) {
                found = true;
                keep.push_back(lem);
                TRACE("cluster_stats_verb", tout << "Keeping lemma "
                                                 << lem.get_lemma()->get_cube()
                                                 << "\n";);
                break;
            }
        }
        if (!found) {
            TRACE("cluster_stats_verb", tout << "Removing subsumed lemma "
                                             << lem.get_lemma()->get_cube()
                                             << "\n";);
            removed_lemmas.push_back(lem);
        }
    }
    m_lemma_vec.reset();
    m_lemma_vec.append(keep);
}

/// A a lemma to a cluster
///
/// Removes subsumed lemmas if \p subs_check is true
///
/// Returns false if lemma does not match the pattern or if it is already in the
/// cluster. Repetition of lemmas is avoided by doing a linear scan over the
/// lemmas in the cluster. Adding a lemma can reduce the size of the cluster due
/// to subsumption reduction.
bool lemma_cluster::add_lemma(const lemma_ref &lemma, bool subsume) {
    substitution sub(m);
    expr_ref cube(m);

    sub.reserve(1, m_num_vars);
    cube = mk_and(lemma->get_cube());
    normalize_order(cube, cube);

    if (!match(cube, sub)) return false;

    // cluster already contains the lemma
    if (contains(lemma)) return false;

    TRACE("cluster_stats_verb",
          tout << "Trying to add lemma " << lemma->get_cube() << "\n";);

    lemma_cluster::lemma_info li(lemma, sub);
    m_lemma_vec.push_back(li);

    if (subsume) {
        lemma_info_vector removed_lemmas;
        rm_subsumed(removed_lemmas);
        for (auto rm : removed_lemmas) {
            // There is going to at most one removed lemma that matches l_i
            // if there is one, return false since the new lemma was not added
            if (rm.get_lemma() == li.get_lemma()) return false;
        }
    }
    TRACE("cluster_stats", tout << "Added lemma\n" << mk_and(lemma->get_cube()) << "\n"
                                << "to  existing cluster\n" << m_pattern << "\n";);
    return true;
}

lemma_cluster_finder::lemma_cluster_finder(ast_manager &_m)
    : m(_m), m_arith(m), m_bv(m) {}

/// Check whether \p cube and \p lcube differ only in interpreted constants
bool lemma_cluster_finder::are_neighbours(const expr_ref &cube1,
                                          const expr_ref &cube2) {
    SASSERT(is_ground(cube1));
    SASSERT(is_ground(cube2));

    anti_unifier antiunify(m);
    expr_ref pat(m);
    substitution sub1(m), sub2(m);

    antiunify(cube1, cube2, pat, sub1, sub2);
    SASSERT(sub1.get_num_bindings() == sub2.get_num_bindings());
    return is_numeric_sub(sub1) && is_numeric_sub(sub2);
}

/// Compute antiunification of \p cube with all formulas in \p fmls.
///
/// Should return
///         \exist res (\forall f \in fmls (\exist i_sub res[i_sub] == f))
/// However, the algorithm is incomplete: it returns such a res iff
///         res \in {antiU(cube,  e) | e \in fmls}
/// Returns true if res is found
/// TODO: do complete n-ary anti-unification. Not done now
/// because anti_unifier does not support free variables
bool lemma_cluster_finder::anti_unify_n_intrp(const expr_ref &cube,
                                              expr_ref_vector &fmls,
                                              expr_ref &res) {
    expr_ref_vector patterns(m);
    expr_ref pat(m);
    anti_unifier antiunify(m);
    substitution sub1(m), sub2(m);

    TRACE("cluster_stats_verb",
          tout << "Trying to generate a general pattern for " << cube
               << " neighbours are " << fmls << "\n";);

    // collect candidates for res
    for (expr *c : fmls) {
        antiunify.reset();
        sub1.reset();
        sub2.reset();

        SASSERT(are_neighbours(cube, {c, m}));
        antiunify(cube, expr_ref(c, m), pat, sub1, sub2);
        patterns.push_back(pat);
    }

    // go through all the patterns to see if there is a pattern which is general
    // enough to include all lemmas.
    bool is_general_pattern = false, pos = true, all_same = true;
    sem_matcher matcher(m);
    unsigned n_vars_pat = 0;
    for (expr *e : patterns) {
        TRACE("cluster_stats_verb",
              tout << "Checking pattern " << mk_pp(e, m) << "\n";);
        is_general_pattern = true;
        n_vars_pat = get_num_vars(e);
        all_same = all_same && n_vars_pat == 0;
        for (auto *lcube : fmls) {
            matcher.reset();
            sub1.reset();
            sub1.reserve(1, n_vars_pat);
            if (!(matcher(e, lcube, sub1, pos) && pos)) {
                // this pattern is no good
                is_general_pattern = false;
                break;
            }
        }
        if (is_general_pattern) {
            SASSERT(e != nullptr);
            TRACE("cluster_stats",
                  tout << "Found a general pattern\n" << mk_pp(e, m) << "\n";);
            // found a good pattern
            res = expr_ref(e, m);
            return true;
        }
    }

    CTRACE("cluster_stats", !all_same,
           tout << "Failed to find a general pattern for cluster. Cube is: "
                << cube << " Patterns are " << patterns << "\n";);
    return false;
}

/// Add a new lemma \p lemma to a cluster
///
/// Creates a new cluster for the lemma if necessary
void lemma_cluster_finder::cluster(lemma_ref &lemma) {
    scoped_watch _w_(m_st.watch);
    pred_transformer &pt = (lemma->get_pob())->pt();

    // check whether lemmas has already been added
    if (pt.clstr_contains(lemma)) return;

    /// Add the lemma to a cluster it is matched against
    lemma_cluster *clstr = pt.clstr_match(lemma);
    if (clstr && clstr->get_size() <= MAX_CLUSTER_SIZE) {
        TRACE("cluster_stats_verb", {
            tout << "Trying to add lemma\n" << lemma->get_cube()
                 << " to an existing cluster\n";
            for (auto lem : clstr->get_lemmas())
                tout << lem.get_lemma()->get_cube() << "\n";
        });
        clstr->add_lemma(lemma);
        return;
    }

    /// Dont create more than MAX_CLUSTERS number of clusters
    if (clstr && pt.clstr_count(clstr->get_pattern()) > MAX_CLUSTERS) {
        return;
    }

    // Try to create a new cluster with lemma even if it can belong to an
    // oversized cluster. The new cluster will not contain any lemma that is
    // already in another cluster.
    lemma_ref_vector all_lemmas;
    pt.get_all_lemmas(all_lemmas, false);

    expr_ref lcube(m), cube(m);
    lcube = mk_and(lemma->get_cube());
    normalize_order(lcube, lcube);

    expr_ref_vector lma_cubes(m);
    lemma_ref_vector neighbours;

    for (auto *l : all_lemmas) {
        cube.reset();
        cube = mk_and(l->get_cube());
        normalize_order(cube, cube);
        // make sure that l is not in any other clusters
        if (are_neighbours(lcube, cube) && cube != lcube &&
            !pt.clstr_contains(l)) {
            neighbours.push_back(l);
            lma_cubes.push_back(cube);
        }
    }

    if (neighbours.empty()) return;

    // compute the most general pattern to which lemmas fit
    expr_ref pattern(m);
    bool is_cluster = anti_unify_n_intrp(lcube, lma_cubes, pattern);

    // no general pattern
    if (!is_cluster || get_num_vars(pattern) == 0) return;

    // When creating a cluster, its size can be more than MAX_CLUSTER_SIZE. The
    // size limitation is only for adding new lemmas to the cluster. The size is
    // just an arbitrary number.
    // What matters is that we do not allow a cluster to grow indefinitely.
    // for example, given a cluster in which one lemma subsumes all other
    // lemmas. No matter how big the cluster is, GSpacer is going to produce the
    // exact same pob on this cluster. This can lead to divergence. The
    // subsumption check we do is based on unit propagation, it is not complete.
    lemma_cluster *cluster = pt.mk_cluster(pattern);

    TRACE("cluster_stats",
          tout << "created new cluster with pattern:\n" << pattern << "\n"
               << " and lemma cube:\n" << lcube << "\n";);

    IF_VERBOSE(2, verbose_stream() << "\ncreated new cluster with pattern: "
                                   << pattern << "\n"
                                   << " and lemma cube: " << lcube << "\n";);

    for (auto l : neighbours) {
        SASSERT(cluster->can_contain(l));
        bool added = cluster->add_lemma(l, false);
        (void)added;
        CTRACE("cluster_stats", added,
               tout << "Added neighbour lemma\n" << mk_and(l->get_cube()) << "\n";);
    }

    // finally add the lemma and do subsumption check
    cluster->add_lemma(lemma, true);
    SASSERT(cluster->get_size() >= 1);
}

void lemma_cluster_finder::collect_statistics(statistics &st) const {
    st.update("time.spacer.solve.reach.cluster", m_st.watch.get_seconds());
}

} // namespace spacer
