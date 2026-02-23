#include "nlsat/levelwise.h"
#include "nlsat/nlsat_types.h"
#include "nlsat/nlsat_assignment.h"
#include "math/polynomial/algebraic_numbers.h"
#include "math/polynomial/polynomial.h"
#include "nlsat_common.h"
#include "util/vector.h"
#include "util/trace.h"

#include <algorithm>
#include <cstdint>
#include <set>
#include <unordered_map>
#include <utility>
#include <vector>

static bool is_set(unsigned k) { return static_cast<int>(k) != -1; }

// Helper for sparse vector access with default value
template<typename T>
static T vec_get(std_vector<T> const& v, unsigned idx, T def) {
    return idx < v.size() ? v[idx] : def;
}

// Helper for sparse vector write with auto-resize
template<typename T>
static void vec_setx(std_vector<T>& v, unsigned idx, T val, T def) {
    if (idx >= v.size())
        v.resize(idx + 1, def);
    v[idx] = val;
}

namespace nlsat {

    // The three projection modes for a level:
    // 1. section_biggest_cell: Sample is on a root. All disc/lc added.
    // 2. sector_biggest_cell:  Sample between roots. noLdcf optimization only.
    // 3. sector_spanning_tree: Sample between roots with many both-side polys.
    //                          Both noLdcf and noDisc optimizations.
    enum class projection_mode {
        section_biggest_cell,
        sector_biggest_cell,
        sector_spanning_tree
    };


    struct levelwise::impl {
        solver&                      m_solver;
        polynomial_ref_vector const& m_P;
        unsigned                     m_n;        // maximal variable we project from
        pmanager&                    m_pm;
        anum_manager&                m_am;
        polynomial::cache&           m_cache;
        std_vector<root_function_interval> m_I; // intervals for variables 0..m_n-1

        unsigned               m_level = 0;      // current level being processed
        unsigned               m_spanning_tree_threshold = 3; // minimum both-side count for spanning tree
        unsigned               m_l_rf = UINT_MAX; // position of lower bound in m_rel.m_rfunc
        unsigned               m_u_rf = UINT_MAX; // position of upper bound in m_rel.m_rfunc, UINT_MAX in section case

        // Per-level state set by process_level/process_top_level
        todo_set                        m_todo;
        polynomial_ref_vector           m_level_ps;
        std_vector<polynomial_ref>     m_witnesses;
        std_vector<bool>                m_poly_has_roots;

        polynomial_ref_vector  m_psc_tmp;        // scratch for PSC chains

        // Vectors indexed by position in m_level_ps (more cache-friendly than maps)
        mutable std_vector<uint8_t> m_side_mask;       // bit0 = lower, bit1 = upper, 3 = both
        mutable std_vector<bool> m_omit_lc;
        mutable std_vector<bool> m_omit_disc;
        mutable std_vector<unsigned> m_deg_in_order_graph; // degree of polynomial in resultant graph
        mutable std_vector<unsigned> m_unique_neighbor;    // UINT_MAX = not set, UINT_MAX-1 = multiple

        assignment const& sample() const { return m_solver.sample(); }

        // Utility: call fn for each distinct irreducible factor of poly
        template <typename Func>
        void for_each_distinct_factor(polynomial_ref const& poly_in, Func&& fn) {
            if (!poly_in || is_zero(poly_in) || is_const(poly_in))
                return;
            polynomial_ref poly(poly_in);
            polynomial_ref_vector factors(m_pm);
            ::nlsat::factor(poly, m_cache, factors);
            for (unsigned i = 0; i < factors.size(); ++i) {
                polynomial_ref f(factors.get(i), m_pm);
                if (!f || is_zero(f) || is_const(f))
                    continue;
                fn(f);
            }
        }

        struct root_function {
            scoped_anum       val;
            indexed_root_expr ire;
            unsigned          ps_idx; // index in m_level_ps
            root_function(anum_manager& am, poly* p, unsigned idx, anum const& v, unsigned ps_idx)
                : val(am), ire{ p, idx }, ps_idx(ps_idx) { am.set(val, v); }
            root_function(root_function&& other) noexcept : val(other.val.m()), ire(other.ire), ps_idx(other.ps_idx) { val = other.val; }
            root_function(root_function const&) = delete;
            root_function& operator=(root_function const&) = delete;
            root_function& operator=(root_function&& other) noexcept {
                val = other.val;
                ire = other.ire;
                ps_idx = other.ps_idx;
                return *this;
            }
        };

        // Root functions (Theta) and the chosen relation (≼) on a given level.
        struct relation_E {
            std_vector<root_function>              m_rfunc; // Θ: root functions on current level
            std::set<std::pair<unsigned, unsigned>> m_pairs; // ≼ relation as unique m_level_ps index pairs
            bool empty() const { return m_rfunc.empty() && m_pairs.empty(); }
            void clear() {
                m_pairs.clear();
                m_rfunc.clear();
            }
            // Add pair by rfunc indices - canonicalizes and de-duplicates using ps_idx
            void add_pair(unsigned j, unsigned k) {
                unsigned a = m_rfunc[j].ps_idx;
                unsigned b = m_rfunc[k].ps_idx;
                if (a == b) return;
                if (a > b) std::swap(a, b);
                m_pairs.insert({a, b});
            }
        };

        relation_E m_rel;

        // Check that the relation forms a valid connected structure for order-invariance.
        // Every root function on each side must be connected to the boundary through edges.
        bool relation_invariant() const {
            auto const& rfs = m_rel.m_rfunc;
            auto n = rfs.size();
            if (n == 0) return true;

            // Build adjacency list from pairs (using ps_idx)
            // Use vectors indexed by ps_idx for efficiency
            unsigned max_ps_idx = 0;
            for (auto const& rf : rfs)
                if (rf.ps_idx > max_ps_idx) max_ps_idx = rf.ps_idx;
            for (auto const& pr : m_rel.m_pairs) {
                if (pr.first > max_ps_idx) max_ps_idx = pr.first;
                if (pr.second > max_ps_idx) max_ps_idx = pr.second;
            }

            std_vector<std_vector<unsigned>> adj(max_ps_idx + 1);
            for (auto const& pr : m_rel.m_pairs) {
                adj[pr.first].push_back(pr.second);
                adj[pr.second].push_back(pr.first);
            }

            // BFS to find all ps_idx reachable from a starting ps_idx
            auto reachable_from = [&](unsigned start_ps_idx) -> std_vector<bool> {
                std_vector<bool> visited(max_ps_idx + 1, false);
                std_vector<unsigned> queue;
                queue.push_back(start_ps_idx);
                visited[start_ps_idx] = true;
                while (!queue.empty()) {
                    unsigned curr = queue.back();
                    queue.pop_back();
                    for (unsigned neighbor : adj[curr]) {
                        if (!visited[neighbor]) {
                            visited[neighbor] = true;
                            queue.push_back(neighbor);
                        }
                    }
                }
                return visited;
            };

            // Check lower side: all rfuncs in [0, m_l_rf] must be connected to boundary
            if (is_set(m_l_rf) && m_l_rf < n) {
                unsigned boundary_ps_idx = rfs[m_l_rf].ps_idx;
                std_vector<bool> reachable = reachable_from(boundary_ps_idx);
                for (unsigned i = 0; i <= m_l_rf; ++i) {
                    unsigned ps_idx = rfs[i].ps_idx;
                    if (!reachable[ps_idx]) {
                        TRACE(lws, tout << "INVARIANT FAIL: lower side rfunc " << i
                              << " (ps_idx=" << ps_idx << ") not connected to boundary "
                              << m_l_rf << " (ps_idx=" << boundary_ps_idx << ")\n";);
                        return false;
                    }
                }
            }

            // Check upper side: all rfuncs in [m_u_rf, n-1] must be connected to boundary
            if (is_set(m_u_rf) && m_u_rf < n) {
                unsigned boundary_ps_idx = rfs[m_u_rf].ps_idx;
                std_vector<bool> reachable = reachable_from(boundary_ps_idx);
                for (unsigned i = m_u_rf; i < n; ++i) {
                    unsigned ps_idx = rfs[i].ps_idx;
                    if (!reachable[ps_idx]) {
                        TRACE(lws, tout << "INVARIANT FAIL: upper side rfunc " << i
                              << " (ps_idx=" << ps_idx << ") not connected to boundary "
                              << m_u_rf << " (ps_idx=" << boundary_ps_idx << ")\n";);
                        return false;
                    }
                }
            }

            return true;
        }

        // Weight function for estimating projection complexity.
        // w(p, level) estimates the "cost" of polynomial p at the given level.
        // w(disc(a)) ≈ 2*w(a), w(res(a,b)) ≈ w(a) + w(b)
        unsigned w(poly* p, unsigned level) const {
            if (!p) return 0;
            return m_pm.degree(p, level);
        }

        // Estimate resultant weight for m_rel.m_pairs (pairs of m_level_ps indices)
        unsigned estimate_resultant_weight() const {
            unsigned total = 0;
            for (auto const& pr : m_rel.m_pairs)
                total += w(m_level_ps.get(pr.first), m_level) + w(m_level_ps.get(pr.second), m_level);

            return total;
        }

        // Estimate leading coefficient weight for polynomials where omit_lc is false
        unsigned estimate_lc_weight() const {
            unsigned total = 0;
            for (unsigned i = 0; i < m_level_ps.size(); ++i) {
                if (vec_get(m_omit_lc, i, false))
                    continue;
                poly* p = m_level_ps.get(i);
                unsigned deg = m_pm.degree(p, m_level);
                if (deg > 0)
                    total += w(m_pm.coeff(p, m_level, deg), m_level - 1);
            }
            return total;
        }

        // Choose the best sector heuristic based on estimated weight.
        // Also fills m_rel.m_pairs with the winning heuristic's pairs.
        // Note: spanning_tree is handled at a higher level (process_level_sector)
        impl(
            solver& solver,
            polynomial_ref_vector const& ps,
            var max_x,
            assignment const&,
            pmanager& pm,
            anum_manager& am,
            polynomial::cache& cache)
            : m_solver(solver),
              m_P(ps),
              m_n(max_x),
              m_pm(pm),
              m_am(am),
              m_cache(cache),
              m_todo(m_cache, true),
              m_level_ps(m_pm),
              m_psc_tmp(m_pm) {
            m_I.reserve(m_n);
            for (unsigned i = 0; i < m_n; ++i)
                m_I.emplace_back(m_pm);

            m_spanning_tree_threshold = m_solver.lws_spt_threshold();
        }

        // Handle a polynomial whose every coefficient evaluates to zero at the sample.
        // Compute partial derivatives level by level. If all derivatives at a level vanish,
        // request_factorized each of them and continue to the next level.
        // When a non-vanishing derivative is found, request_factorized it and stop.
        void handle_nullified_poly(polynomial_ref const& p) {
            // Add all coefficients of p as a polynomial of x_{m_level} to m_todo.
            unsigned deg = m_pm.degree(p, m_level);
            for (unsigned j = 0; j <= deg; ++j) {
                polynomial_ref coeff(m_pm.coeff(p, m_level, j), m_pm);
                if (!coeff || is_zero(coeff) || is_const(coeff))
                    continue;
                request_factorized(coeff);
            }

            // Compute partial derivatives level by level. If all derivatives at a level vanish,
            // request_factorized each of them and continue to the next level.
            // When a non-vanishing derivative is found, request_factorized it and stop.
            // Parallel vectors: cur_polys owns the polynomials, cur_min_var tracks the
            // minimum variable index to differentiate by, ensuring each mixed partial
            // is computed in non-decreasing variable order, to try avoiding the duplication of the dxdy = dydx kind.
            polynomial_ref_vector cur_polys(m_pm);
            svector<unsigned> cur_min_var;
            cur_polys.push_back(p);
            cur_min_var.push_back(0);
            while (!cur_polys.empty()) {
                polynomial_ref_vector next_polys(m_pm);
                svector<unsigned> next_min_var;
                for (unsigned i = 0; i < cur_polys.size(); ++i) {
                    polynomial_ref q(cur_polys.get(i), m_pm);
                    unsigned mv = m_pm.max_var(q);
                    if (mv == null_var)
                        continue;
                    for (unsigned x = cur_min_var[i]; x <= mv; ++x) {
                        if (m_pm.degree(q, x) == 0)
                            continue;
                        polynomial_ref dq = derivative(q, x);
                        if (!dq || is_zero(dq) || is_const(dq))
                            continue;
                        if (sign(dq)) {
                            request_factorized(dq);
                            return;
                        }
                        next_polys.push_back(dq);
                        next_min_var.push_back(x);
                    }
                }
                for (unsigned i = 0; i < next_polys.size(); ++i) {
                    polynomial_ref dq(next_polys.get(i), m_pm);
                    request_factorized(dq);
                }
                cur_polys = std::move(next_polys);
                cur_min_var = std::move(next_min_var);
            }
            
        }

        static void reset_interval(root_function_interval& I) {
            I.section = false;
            I.l = nullptr;
            I.u = nullptr;
            I.l_index = 0;
            I.u_index = 0;
        }

        // PSC-based discriminant: returns the first non-zero, non-constant element from the PSC chain.
        polynomial_ref psc_discriminant(polynomial_ref const& p_in, unsigned x) {
            if (!p_in || is_zero(p_in) || is_const(p_in))
                return polynomial_ref(m_pm);
            if (m_pm.degree(p_in, x) < 2)
                return polynomial_ref(m_pm);
            polynomial_ref p(p_in);
            polynomial_ref d = derivative(p, x);
            polynomial_ref_vector& chain = m_psc_tmp;
            chain.reset();
            m_cache.psc_chain(p, d, x, chain);
            polynomial_ref disc(m_pm);
            for (unsigned i = 0; i < chain.size(); ++i) {
                disc = polynomial_ref(chain.get(i), m_pm);
                if (!disc || is_zero(disc))
                    continue;
                if (is_const(disc))
                    return polynomial_ref(m_pm);  // constant means discriminant is non-zero constant
                return disc;
            }
            return polynomial_ref(m_pm);
        }

        // PSC-based resultant: returns the first non-zero, non-constant element from the PSC chain.
        polynomial_ref psc_resultant(poly* a, poly* b, unsigned x) {
            if (!a || !b)
                return polynomial_ref(m_pm);
            polynomial_ref pa(a, m_pm);
            polynomial_ref pb(b, m_pm);
            polynomial_ref_vector& chain = m_psc_tmp;
            chain.reset();
            m_cache.psc_chain(pa, pb, x, chain);
            polynomial_ref r(m_pm);
            // Iterate forward: S[0] is the resultant (after reverse in psc_chain)
            for (unsigned i = 0; i < chain.size(); ++i) {
                r = polynomial_ref(chain.get(i), m_pm);
                if (!r || is_zero(r))
                    continue;
                if (is_const(r))
                    return polynomial_ref(m_pm);  // constant means polynomials are coprime
                return r;
            }
            return polynomial_ref(m_pm);
        }

        void request_factorized(polynomial_ref const& poly) {
            for_each_distinct_factor(poly, [&](polynomial_ref const& f) {
                TRACE(lws,
                      m_pm.display(tout << "      request_factorized: factor=", f) << " at level " << m_pm.max_var(f) << "\n";
                    );
                m_todo.insert(f.get());
            });
        }

        // Select a coefficient c of p (wrt x) such that c(s) != 0, or return null.
        // The coefficients are polynomials in lower variables; we prefer "simpler" ones
        // to reduce projection blow-up.
        polynomial_ref choose_nonzero_coeff(polynomial_ref const& p, unsigned x) {
            unsigned deg = m_pm.degree(p, x);
            polynomial_ref coeff(m_pm);
            
            // First pass: any non-zero constant coefficient is ideal (no need to project it).
            for (unsigned j = 0; j <= deg; ++j) {
                coeff = m_pm.coeff(p, x, j);
                if (!coeff || is_zero(coeff))
                    continue;
                if (is_const(coeff))
                    return coeff;
            }

            // Second pass: pick the non-constant coefficient with minimal (total_degree, size, max_var).
            polynomial_ref best(m_pm);
            unsigned best_td = 0;
            unsigned best_sz = 0;
            var best_mv = null_var;
            for (unsigned j = 0; j <= deg; ++j) {
                coeff = m_pm.coeff(p, x, j);
                if (!coeff || is_zero(coeff))
                    continue;
                if (sign(coeff) == 0)
                    continue;

                unsigned td = total_degree(coeff);
                unsigned sz = m_pm.size(coeff);
                var mv = m_pm.max_var(coeff);
                if (!best ||
                    td < best_td ||
                    (td == best_td && (sz < best_sz ||
                                       (sz == best_sz && (best_mv == null_var || mv < best_mv))))) {
                    best = coeff;
                    best_td = td;
                    best_sz = sz;
                    best_mv = mv;
                }
            }
            return best;
        }

        ::sign sign(polynomial_ref const & p) {
             return ::nlsat::sign(p, m_solver.sample(), m_am);
        }

        
        void add_projection_for_poly(polynomial_ref const& p, unsigned x, polynomial_ref const& nonzero_coeff, bool add_leading_coeff, bool add_discriminant) {
               TRACE(lws,
                  m_pm.display(tout << "  add_projection_for_poly: p=", p)
                      << " x=" << x << " add_lc=" << add_leading_coeff << " add_disc=" << add_discriminant << "\n";
                );

            bool add_nzero_coeff = nonzero_coeff && !is_const(nonzero_coeff);
            
            if (add_leading_coeff) {
                unsigned deg = m_pm.degree(p, x);
                polynomial_ref lc(m_pm);
                lc = m_pm.coeff(p, x, deg);
                TRACE(lws, m_pm.display(tout << "    adding lc: ", lc) << "\n";);
                request_factorized(lc);
                if (add_nzero_coeff && lc && sign(lc))
                    add_nzero_coeff = false;
            }

            if (add_discriminant) {
                polynomial_ref disc(m_pm);
                disc = psc_discriminant(p, x);
                if (disc) {
                    request_factorized(disc);
                    // If p is nullified at some point then at this point discriminant well be evaluated
                    // to zero, as can be seen from the Sylvester matrix which would
                    // have at least one zero row.
                    if (add_nzero_coeff && sign(disc)) // we can avoid adding a nonzero_coeff if sign(disc) != 0
                        add_nzero_coeff = false;
                }
            }

            if (add_nzero_coeff)
                request_factorized(nonzero_coeff);
        }

        // ============================================================================
        // noLdcf optimization - compute which leading coefficients can be omitted
        //
        // This optimization is justified by PROJECTIVE DELINEABILITY theory [1,2].
        //
        // Regular delineability (Theorem 2.1 in [2]) requires the leading coefficient
        // to be sign-invariant to ensure the polynomial's degree doesn't drop. However,
        // projective delineability (Theorem 3.1 in [2]) shows that order-invariance of
        // the discriminant alone (without LC sign-invariance) is sufficient to ensure
        // the polynomial's roots behave continuously - they may "go to infinity" when
        // the LC vanishes, but won't suddenly appear or disappear within the cell.
        //
        // For a polynomial p with roots on BOTH sides of the sample:
        // - Resultants with both boundary polynomials are computed anyway
        // - These resultants ensure p's roots don't cross the cell boundaries (Thm 3.2)
        // - Even if p's degree drops (LC becomes zero), existing roots remain ordered
        // - New roots can only appear "at infinity", outside the bounded cell
        //
        // Michel et al., "On Projective Delineability", arXiv:2411.13300, 2024
        // Nalbach et al., "Projective Delineability for Single Cell Construction", SC² 2025
        // ============================================================================

        // Compute side_mask: track which side(s) each polynomial appears on
        // bit0 = lower (<= sample), bit1 = upper (> sample), 3 = both sides
        void compute_side_mask() {
            if (!is_set(m_l_rf))
                return;
            m_side_mask.resize(m_level_ps.size(), 0);
            for (unsigned i = 0; i < m_rel.m_rfunc.size(); i ++) {
                unsigned ps_idx = m_rel.m_rfunc[i].ps_idx;
                if (i <= m_l_rf) 
                    m_side_mask[ps_idx] |= 1;
                else
                    m_side_mask[ps_idx] |= 2;
            }
        }

        // Check if lower and upper bounds come from the same polynomial
        bool same_boundary_poly() const {
            if (!is_set(m_l_rf) || !is_set(m_u_rf))
                return false;
            return m_rel.m_rfunc[m_l_rf].ps_idx == m_rel.m_rfunc[m_u_rf].ps_idx;
        }

        // Get lower bound polynomial index, or UINT_MAX if not set
        unsigned lower_bound_idx() const {
            return is_set(m_l_rf) ? m_rel.m_rfunc[m_l_rf].ps_idx : UINT_MAX;
        }

        // Get upper bound polynomial index, or UINT_MAX if not set
        unsigned upper_bound_idx() const {
            return is_set(m_u_rf) ? m_rel.m_rfunc[m_u_rf].ps_idx : UINT_MAX;
        }

        // Compute deg: count distinct resultant-neighbors for each polynomial
        // m_pairs contains index pairs into m_level_ps
        void compute_resultant_graph_degree() {
            m_deg_in_order_graph.clear();
            m_deg_in_order_graph.resize(m_level_ps.size(), 0);
            m_unique_neighbor.clear();
            m_unique_neighbor.resize(m_level_ps.size(), UINT_MAX);
            for (auto const& pr : m_rel.m_pairs) {
                unsigned idx1 = pr.first;
                unsigned idx2 = pr.second;
                m_deg_in_order_graph[idx1]++;
                m_deg_in_order_graph[idx2]++;
                // Track unique neighbor
                auto update_neighbor = [&](unsigned idx, unsigned other) {
                    if (m_unique_neighbor[idx] == UINT_MAX)
                        m_unique_neighbor[idx] = other;
                    else if (m_unique_neighbor[idx] != other)
                        m_unique_neighbor[idx] = UINT_MAX - 1;  // multiple neighbors
                };
                update_neighbor(idx1, idx2);
                update_neighbor(idx2, idx1);
            }
        }

        // TODO: Investigate noDisc optimization for spanning_tree mode when lb and ub are the same
        // polynomial. SMT-RAT does noDisc for leaves connected to the section-defining polynomial
        // in section case, which might extend to sectors where lb == ub. The previous implementation
        // here was unsound because it applied to general leaves connected to any boundary, but
        // discriminants are needed to ensure a polynomial's own roots don't merge/split.

        // ----------------------------------------------------------------------------
        // noLdcf heuristic helpers
        // ----------------------------------------------------------------------------

        // Compute noLdcf: which leading coefficients can be omitted using projective delineability.
        // 
        // A polynomial p with roots on BOTH sides of the sample has resultants with both bounds.
        // By projective delineability (Theorem 3.1 in [2]), we only need the discriminant to be
        // order-invariant - the LC can be omitted because roots "going to infinity" don't affect
        // sign-invariance within the bounded cell.
        //
        // - biggest_cell mode, require_leaf=false: all non-bound polys with both-side roots
        // - spanning_tree mode, require_leaf=true: only leaves with deg == 1 and both-side roots
        //
        // [2] Nalbach et al., "Projective Delineability for Single Cell Construction", SC² 2025
        void compute_omit_lc_both_sides(bool require_leaf) {
            m_omit_lc.clear();
            m_omit_lc.resize(m_level_ps.size(), false);
            if (m_rel.m_rfunc.empty() || m_rel.m_pairs.empty() || m_side_mask.empty())
                return;

            if (require_leaf)
                compute_resultant_graph_degree();

            unsigned l_bound_idx = lower_bound_idx();
            unsigned u_bound_idx = upper_bound_idx();

            for (unsigned i = 0; i < m_level_ps.size(); ++i) {
                if (m_side_mask[i] != 3)
                    continue;
                if (require_leaf && m_deg_in_order_graph[i] != 1)
                    continue;
                if (i == l_bound_idx || i == u_bound_idx)
                    continue;
                m_omit_lc[i] = true;
            }
        }

        // Relation construction heuristics (same intent as previous implementation).
        void fill_relation_sector_biggest_cell() {
            TRACE(lws,
                  tout << "  fill_biggest_cell: m_l_rf=" << m_l_rf << ", m_u_rf=" << m_u_rf << ", rfunc.size=" << m_rel.m_rfunc.size() << "\n";
                );
            if (is_set(m_l_rf))
                for (unsigned j = 0; j < m_l_rf; ++j) {
                    TRACE(lws, tout << "    add_pair(" << j << ", " << m_l_rf << ")\n";);
                    m_rel.add_pair(j, m_l_rf);
                }

            if (is_set(m_u_rf))
                for (unsigned j = m_u_rf + 1; j < m_rel.m_rfunc.size(); ++j) {
                    TRACE(lws, tout << "    add_pair(" << m_u_rf << ", " << j << ")\n";);
                    m_rel.add_pair(m_u_rf, j);
                }

            if (is_set(m_l_rf) && is_set(m_u_rf)) {
                SASSERT(m_l_rf + 1 == m_u_rf);
                TRACE(lws, tout << "    add_pair(" << m_l_rf << ", " << m_u_rf << ")\n";);
                m_rel.add_pair(m_l_rf, m_u_rf);
            }
            TRACE(lws,
                  tout << "  fill_biggest_cell done: pairs.size=" << m_rel.m_pairs.size() << "\n";
                );
        }

        void fill_relation_pairs_for_section_biggest_cell() {
            auto const& rfs = m_rel.m_rfunc;
            auto n = rfs.size();
            if (n == 0)
                return;
            SASSERT(is_set(m_l_rf));
            SASSERT(m_l_rf < n);
            for (unsigned j = 0; j < m_l_rf; ++j)
                m_rel.add_pair(j, m_l_rf);
            for (unsigned j = m_l_rf + 1; j < n; ++j)
                m_rel.add_pair(m_l_rf, j);
        }

        // ============================================================================
        // Spanning tree heuristic based on the Reaching Orders Lemma.
        // For polynomials appearing on both sides of the sample, we build a spanning
        // tree that ensures order-invariance on both sides with n-1 edges.
        // ============================================================================

        // Build spanning tree on both-side polynomials using the lemma construction.
        // Adds pairs directly to m_rel.m_pairs. Returns true if tree was built.
        // K = lower rfunc positions, f = upper rfunc positions
        void build_both_side_spanning_tree() {
            auto const& rfs = m_rel.m_rfunc;
            auto n = rfs.size();
            SASSERT(n > 0 && is_set(m_l_rf) && is_set(m_u_rf));
            SASSERT(!is_section());
            SASSERT(!same_boundary_poly());

            // Collect both-side polynomials with their rfunc indices on each side
            struct both_info {
                unsigned ps_idx;
                unsigned lower_rf;  // rfunc index on lower side
                unsigned upper_rf;  // rfunc index on upper side
            };
            std_vector<both_info> both;

            // For sector: lower side is [0, m_l_rf], upper side is [m_u_rf, n)

            // Build map from ps_idx to rfunc indices
            std_vector<unsigned> lower_rf(m_level_ps.size(), UINT_MAX);
            std_vector<unsigned> upper_rf(m_level_ps.size(), UINT_MAX);
            
            for (unsigned i = 0; i <= m_l_rf; ++i)
                lower_rf[rfs[i].ps_idx] = i;
            for (unsigned i = m_u_rf; i < n; ++i)
                upper_rf[rfs[i].ps_idx] = i;
            // Collect both-side polynomials
            for (unsigned i = 0; i < m_level_ps.size(); ++i) {
                if (m_side_mask[i] == 3) {
                    SASSERT(lower_rf[i] != UINT_MAX && upper_rf[i] != UINT_MAX);
                    both.push_back({i, lower_rf[i], upper_rf[i]});
                }
            }

            SASSERT(both.size() >= m_spanning_tree_threshold);

            // Sort by lower_rf (root position on lower side)
            std::sort(both.begin(), both.end(),
                      [](both_info const& a, both_info const& b) { return a.lower_rf < b.lower_rf; });

            // Build spanning tree using Reaching Orders Lemma (from the paper):
            // Process elements in order of increasing lower_rf.
            // For each new element a = min(remaining), connect to c where f(c) = min(f(K \ {a}))
            // i.e., c has minimum upper_rf among all elements except a.

            // Root of in-arborescence on lower side is max(K) = last element (max lower_rf)
            // Root of out-arborescence on upper side is min(f(K)) = element with min upper_rf
            unsigned upper_root_idx = 0;
            for (unsigned i = 1; i < both.size(); ++i)
                if (both[i].upper_rf < both[upper_root_idx].upper_rf)
                    upper_root_idx = i;
            (void)upper_root_idx;  // used in DEBUG_CODE below
            
            // Process in order of lower_rf 
            // First element (index 0) has min lower_rf
            for (unsigned a_idx = 0; a_idx < both.size() - 1; ++a_idx) {
                // Find c = element with min upper_rf among all elements except a_idx
                // Since we process in lower_rf order, elements [a_idx+1, n) are "K' = K \ {a}"
                // and we need min upper_rf among them
                unsigned c_idx = UINT_MAX;
                for (unsigned i = a_idx + 1; i < both.size(); ++i)
                    if (c_idx == UINT_MAX || both[i].upper_rf < both[c_idx].upper_rf)
                        c_idx = i;
                SASSERT(c_idx != UINT_MAX);
                
                // Add edge {a, c}
                unsigned ps_a = both[a_idx].ps_idx;
                unsigned ps_c = both[c_idx].ps_idx;
                m_rel.m_pairs.insert({std::min(ps_a, ps_c), std::max(ps_a, ps_c)});
            }

            
            // Check arborescence invariants (used in debug via SASSERT)
            DEBUG_CODE(
            auto lower_root_idx = both.size() - 1;
            auto arb_invariant = [&]() {
                // Reconstruct parent[] from the algorithm logic
                std_vector<unsigned> parent(both.size(), UINT_MAX);
                for (unsigned a_idx = 0; a_idx < both.size() - 1; ++a_idx) {
                    unsigned c_idx = UINT_MAX;
                    for (unsigned i = a_idx + 1; i < both.size(); ++i)
                        if (c_idx == UINT_MAX || both[i].upper_rf < both[c_idx].upper_rf)
                            c_idx = i;
                    parent[a_idx] = c_idx;
                }
                
                // Check it's a tree: exactly n-1 edges
                unsigned edge_count = 0;
                for (unsigned i = 0; i < both.size(); ++i)
                    if (parent[i] != UINT_MAX) edge_count++;
                SASSERT(edge_count == both.size() - 1);  // tree has n-1 edges
                
                // Check roots are at extremes
                // lower_root_idx should have max lower_rf
                for (unsigned i = 0; i < both.size(); ++i)
                    SASSERT(both[i].lower_rf <= both[lower_root_idx].lower_rf);
                // upper_root_idx should have min upper_rf
                for (unsigned i = 0; i < both.size(); ++i)
                    SASSERT(both[i].upper_rf >= both[upper_root_idx].upper_rf);
                
                // Root of in-arborescence (max lower_rf) has no parent
                SASSERT(parent[lower_root_idx] == UINT_MAX);
                for (unsigned i = 0; i < both.size(); ++i)
                    if (i != lower_root_idx)
                        SASSERT(parent[i] != UINT_MAX);  // non-root has exactly 1 parent
                
                // Check in-arborescence on left (lower) side:
                // Each node can reach lower_root by following parent pointers
                // and lower_rf increases (going right) at each step
                for (unsigned i = 0; i < both.size(); ++i) {
                    unsigned curr = i;
                    unsigned steps = 0;
                    while (curr != lower_root_idx) {
                        unsigned p = parent[curr];
                        SASSERT(p != UINT_MAX);
                        // Going to parent increases lower_rf (toward root which has max lower_rf)
                        SASSERT(both[curr].lower_rf < both[p].lower_rf);
                        curr = p;
                        steps++;
                        SASSERT(steps < both.size());  // prevent infinite loop
                    }
                }
                
                // Check out-arborescence on right (upper) side:
                // Re-orient edges based on upper_rf: edge goes from smaller to larger upper_rf
                // Build adjacency from the edges in parent[]
                std_vector<std_vector<unsigned>> out_children(both.size());
                for (unsigned i = 0; i < both.size(); ++i) {
                    if (parent[i] != UINT_MAX) {
                        unsigned p = parent[i];
                        // Edge {i, p} exists. Orient based on upper_rf.
                        if (both[i].upper_rf < both[p].upper_rf)
                            out_children[i].push_back(p);  // i has smaller upper_rf
                        else
                            out_children[p].push_back(i);  // p has smaller upper_rf
                    }
                }
                
                // Each node can be reached from upper_root by following out_children
                // and upper_rf increases (going away from root which has min upper_rf)
                std_vector<bool> reached(both.size(), false);
                std_vector<unsigned> stack;
                stack.push_back(upper_root_idx);
                reached[upper_root_idx] = true;
                while (!stack.empty()) {
                    unsigned curr = stack.back();
                    stack.pop_back();
                    for (unsigned child : out_children[curr]) {
                        // Going to child increases upper_rf (away from root which has min upper_rf)
                        SASSERT(both[child].upper_rf > both[curr].upper_rf);
                        SASSERT(!reached[child]);  // tree, no cycles
                        reached[child] = true;
                        stack.push_back(child);
                    }
                }
                // All nodes reachable from upper_root
                for (unsigned i = 0; i < both.size(); ++i)
                    SASSERT(reached[i]);
                
                return true;
            };
            SASSERT(arb_invariant()););
        }

        // Sector spanning tree heuristic:
        // 1. Build spanning tree on both-side polynomials
        // 2. Extend with lowest_degree for single-side polynomials
        // Helper: Connect non-tree (single-side) polynomials to their respective boundaries
        void connect_non_tree_to_bounds() {
            auto const& rfs = m_rel.m_rfunc;
            auto n = rfs.size();
            
            // Lower side: connect single-side polys to lower boundary
            for (unsigned j = 0; j < m_l_rf; ++j)
                if (m_side_mask[rfs[j].ps_idx] != 3)
                    m_rel.add_pair(j, m_l_rf);
            
            // Upper side: connect single-side polys to upper boundary
            for (unsigned j = m_u_rf + 1; j < n; ++j)
                if (m_side_mask[rfs[j].ps_idx] != 3)
                    m_rel.add_pair(m_u_rf, j);
        }

        // Helper: Connect spanning tree extremes to boundaries (when boundaries are different polys)
        void connect_tree_extremes_to_bounds() {
            auto const& rfs = m_rel.m_rfunc;
            auto n = rfs.size();
            
            // Find max lower both-side poly (closest to lower boundary from below)
            unsigned max_lower_both = UINT_MAX;
            for (unsigned j = 0; j < m_l_rf; ++j)
                if (m_side_mask[rfs[j].ps_idx] == 3)
                    max_lower_both = j;
            
            // Find min upper both-side poly (closest to upper boundary from above)
            unsigned min_upper_both = UINT_MAX;
            for (unsigned j = m_u_rf + 1; j < n; ++j) {
                if (m_side_mask[rfs[j].ps_idx] == 3) {
                    min_upper_both = j;
                    break;
                }
            }
            
            // Connect tree extremes to boundaries
            if (max_lower_both != UINT_MAX)
                m_rel.add_pair(max_lower_both, m_l_rf);
            if (min_upper_both != UINT_MAX)
                m_rel.add_pair(m_u_rf, min_upper_both);
        }

        void fill_relation_sector_spanning_tree() {
            build_both_side_spanning_tree();
            connect_non_tree_to_bounds();
            connect_tree_extremes_to_bounds(); // otherwise the trees on both sides are connected to bounds already

            // Connect lower and upper boundaries
            SASSERT(m_l_rf + 1 == m_u_rf);
            m_rel.add_pair(m_l_rf, m_u_rf);
        }

        // Extract roots of polynomial p around sample value v at the given level,
        // partitioning them into lhalf (roots <= v) and uhalf (roots > v).
        // ps_idx is the index of p in m_level_ps.
        // Returns whether the polynomial has any roots.
        bool isolate_roots_around_sample(poly* p, unsigned ps_idx,
                                         anum const& v, std_vector<root_function>& lhalf,
                                         std_vector<root_function>& uhalf) {
            scoped_anum_vector roots(m_am);
            
            
            // When the sample value is rational use a closest-root isolation
            // returning at most closest to the sample roots
            if (v.is_basic()) {
                scoped_mpq s(m_am.qm());
                m_am.to_rational(v, s);
                svector<unsigned> idx_vec;
                m_am.isolate_roots_closest(polynomial_ref(p, m_pm), undef_var_assignment(sample(), m_level), s, roots, idx_vec);
                SASSERT(roots.size() == idx_vec.size());
                SASSERT(roots.size() < 2 ||(roots.size() == 2 &&  m_am.compare(roots[0], v) < 0 && m_am.compare(roots[1], v) > 0));
                for (unsigned k = 0; k < roots.size(); ++k) {
                    if (m_am.compare(roots[k], v) <= 0)
                        lhalf.emplace_back(m_am, p, idx_vec[k], roots[k], ps_idx);
                    else 
                        uhalf.emplace_back(m_am, p, idx_vec[k], roots[k], ps_idx);
                }
                return roots.size();
            }

            m_am.isolate_roots(polynomial_ref(p, m_pm), undef_var_assignment(sample(), m_level), roots);

            // For single cell construction, we only need the closest roots to the sample point:
            // at most one root below v and one root above v, or a single root at v for sections.
            // Other roots are irrelevant for bounding the cell containing the sample.
            unsigned lower = UINT_MAX, upper = UINT_MAX;
            bool section = false;
            for (unsigned k = 0; k < roots.size(); ++k) {
                int cmp = m_am.compare(roots[k], v);
                if (cmp <= 0) {
                    lower = k;
                    if (cmp == 0) {
                        section = true;
                        break;
                    }
                }
                else {
                    upper = k;
                    break;
                }
            }
            if (lower != UINT_MAX) {
                lhalf.emplace_back(m_am, p, lower + 1, roots[lower], ps_idx);
                if (section)
                    return roots.size(); // only keep the section root for this polynomial
            }
            if (upper != UINT_MAX)
                uhalf.emplace_back(m_am, p, upper + 1, roots[upper], ps_idx);
            return roots.size();
        }

        void init_poly_has_roots() {
            m_poly_has_roots.clear();
            m_poly_has_roots.resize(m_level_ps.size(), false);
        }

        bool collect_partitioned_root_functions_around_sample(anum const& v,
                                                              std_vector<root_function>& lhalf, std_vector<root_function>& uhalf) {
            for (unsigned i = 0; i < m_level_ps.size(); ++i)
                m_poly_has_roots[i] = isolate_roots_around_sample(m_level_ps.get(i), i, v, lhalf, uhalf);
            return !lhalf.empty() || !uhalf.empty();
        }

        std_vector<root_function>::iterator set_relation_root_functions_from_partitions(
            std_vector<root_function>& lhalf,
            std_vector<root_function>& uhalf) {
            auto& rfs = m_rel.m_rfunc;
            size_t mid_pos = lhalf.size();
            rfs.clear();
            rfs.reserve(mid_pos + uhalf.size());
            for (auto& rf : lhalf)
                rfs.emplace_back(std::move(rf));
            for (auto& rf : uhalf)
                rfs.emplace_back(std::move(rf));
            return rfs.begin() + mid_pos;
        }

        bool root_function_lt(root_function const& a, root_function const& b, bool degree_desc) {
            if (a.ire.p == b.ire.p)
                return a.ire.i < b.ire.i;
            auto r = m_am.compare(a.val, b.val);
            if (r)
                return r == sign_neg;
            unsigned dega = m_pm.degree(a.ire.p, m_level);
            unsigned degb = m_pm.degree(b.ire.p, m_level);
            if (dega != degb)
                return degree_desc ? dega > degb : dega < degb;
            return m_pm.id(a.ire.p) < m_pm.id(b.ire.p);
        }

        void sort_root_function_partitions(std_vector<root_function>::iterator mid) {
            auto& rfs = m_rel.m_rfunc;
            std::sort(rfs.begin(), mid,
                      [&](root_function const& a, root_function const& b) { return root_function_lt(a, b, true); });
            std::sort(mid, rfs.end(),
                      [&](root_function const& a, root_function const& b) { return root_function_lt(a, b, false); });
        }

        // Populate Θ (root functions) around the sample, partitioned at `mid`, and sort each partition.
        // Returns whether any roots were found.
        bool build_sorted_root_functions_around_sample(anum const& v, std_vector<root_function>::iterator& mid) {
            init_poly_has_roots();

            std_vector<root_function> lhalf, uhalf;
            if (!collect_partitioned_root_functions_around_sample(v, lhalf, uhalf))
                return false;

            mid = set_relation_root_functions_from_partitions(lhalf, uhalf);

            // Sort each partition separately. For ties (equal root values), prefer low-degree defining
            // polynomials as interval boundaries:
            // - lower bound comes from the last element in the <= partition, so sort ties by degree descending
            // - upper bound comes from the first element in the > partition, so sort ties by degree ascending
            sort_root_function_partitions(mid);
            return true;
        }

        // Pick I_level around sample(m_level) from sorted Θ, split at `mid`.
        // Sets m_l_rf/m_u_rf (positions in m_rfunc) and m_I[m_level] (interval with root indices).
        void set_interval_from_root_partition(anum const& v, std_vector<root_function>::iterator mid) {
            auto& rfs = m_rel.m_rfunc;
            if (mid != rfs.begin()) {
                m_l_rf = static_cast<unsigned>((mid - rfs.begin()) - 1);
                auto& r = *(mid - 1);
                if (m_am.eq(r.val, v)) {
                    // Section case: only m_l_rf is defined
                    m_I[m_level].section = true;
                    m_I[m_level].l = r.ire.p;
                    m_I[m_level].l_index = r.ire.i;
                    m_u_rf = m_l_rf;
                }
                else {
                    m_I[m_level].l = r.ire.p;
                    m_I[m_level].l_index = r.ire.i;
                    if (mid != rfs.end()) {
                        m_u_rf = m_l_rf + 1;
                        m_I[m_level].u = mid->ire.p;
                        m_I[m_level].u_index = mid->ire.i;
                    }
                }
            }
            else {
                // sample is below all roots: I = (-oo, theta_1)
                m_l_rf = UINT_MAX;
                m_u_rf = 0;
                auto& r = *mid;
                m_I[m_level].u = r.ire.p;
                m_I[m_level].u_index = r.ire.i;
            }
        }

        // Build Θ (root functions) and pick I_level around sample(level).
        // Sets m_l_rf/m_u_rf and m_I[level].
        // Returns whether any roots were found (i.e., whether a relation can be built).
        bool build_interval() {
            m_rel.clear();
            reset_interval(m_I[m_level]);
            m_l_rf = UINT_MAX;
            m_u_rf = UINT_MAX;

            anum const& v = sample().value(m_level);
            std_vector<root_function>::iterator mid;
            if (!build_sorted_root_functions_around_sample(v, mid))
                return false;

            set_interval_from_root_partition(v, mid);
            compute_side_mask();
            return true;
        }


        void add_relation_resultants() {
            TRACE(lws, tout << "  add_relation_resultants: " << m_rel.m_pairs.size() << " pairs\n";);
            for (auto const& pr : m_rel.m_pairs) {
                poly* p1 = m_level_ps.get(pr.first);
                poly* p2 = m_level_ps.get(pr.second);
                TRACE(lws,
                      m_pm.display(m_pm.display(tout << "    resultant(" << pr.first << ", " << pr.second << "): ", p1) << " and ", p2) << "\n";
                    );
                polynomial_ref res = psc_resultant(p1, p2, m_level);
                TRACE(lws,
                      tout << "      resultant poly: ";
                      if (res)
                          m_pm.display(tout, res) << "\n      resultant sign at sample: " << sign(res);
                      else
                          tout << "(null)";
                      tout << "\n";
                    );
                request_factorized(res);
            }
        }

        // Top level (m_n): add resultants between adjacent roots of different polynomials.
        // Fills m_poly_has_roots as a side effect.
        void add_adjacent_root_resultants() {
            m_poly_has_roots.clear();
            m_poly_has_roots.resize(m_level_ps.size(), false);

            std_vector<std::pair<scoped_anum, poly*>> root_vals;
            for (unsigned i = 0; i < m_level_ps.size(); ++i) {
                poly* p = m_level_ps.get(i);
                scoped_anum_vector roots(m_am);
                m_am.isolate_roots(polynomial_ref(p, m_pm), undef_var_assignment(sample(), m_n), roots);
                m_poly_has_roots[i] = !roots.empty();
                TRACE(lws, 
                      tout << "  poly[" << i << "] has " << roots.size() << " roots: ";
                      for (unsigned k = 0; k < roots.size(); ++k) {
                          if (k > 0) tout << ", ";
                          m_am.display_decimal(tout, roots[k], 5);
                      }
                      tout << "\n";
                    );
                for (unsigned k = 0; k < roots.size(); ++k) {
                    scoped_anum root_v(m_am);
                    m_am.set(root_v, roots[k]);
                    root_vals.emplace_back(std::move(root_v), p);
                }
            }
            if (root_vals.size() < 2)
                return;

            std::sort(root_vals.begin(), root_vals.end(), [&](auto const& a, auto const& b) {
                return m_am.lt(a.first, b.first);
            });
            
            TRACE(lws,
                  tout << "  Sorted roots:\n";
                  for (unsigned j = 0; j < root_vals.size(); ++j)
                      m_pm.display(m_am.display_decimal(tout << "    [" << j << "] val=", root_vals[j].first, 5) << " poly=", root_vals[j].second) << "\n";
                );
            
            std::set<std::pair<poly*, poly*>> added_pairs;
            for (unsigned j = 0; j + 1 < root_vals.size(); ++j) {
                poly* p1 = root_vals[j].second;
                poly* p2 = root_vals[j + 1].second;
                if (!p1 || !p2 || p1 == p2)
                    continue;
                if (p1 > p2) std::swap(p1, p2);
                if (!added_pairs.insert({p1, p2}).second)
                    continue;
                TRACE(lws,
                      m_pm.display(m_pm.display(tout << "  Adjacent resultant pair: ", p1) << " and ", p2) << "\n";
                    );
                request_factorized(psc_resultant(p1, p2, m_n));
            }
        }

        bool is_section() { return m_I[m_level].is_section();}
        
        // Section case: the section-defining polynomial needs disc and lc projections.
        // For polynomials WITH roots: resultants with section polynomial ensure root ordering.
        // For polynomials WITHOUT roots: they need LC + disc to ensure they don't gain roots.
        //
        // Theory: For a section (sample on a root), sign-invariance of polynomials with roots
        // is ensured by resultants with the section-defining polynomial (Thm 2.2 in [1]).
        // But polynomials without roots need delineability (LC + disc) to stay root-free.
        //
        // [1] Nalbach et al., "Projective Delineability for Single Cell Construction", SC² 2025
        void add_section_projections() {
            poly* section_poly = m_I[m_level].l;
            SASSERT(section_poly);
            
            // Build set of polynomial indices that have roots at this level
            std::set<unsigned> has_roots;
            for (auto const& rf : m_rel.m_rfunc)
                has_roots.insert(rf.ps_idx);
            
            for (unsigned i = 0; i < m_level_ps.size(); ++i) {
                polynomial_ref p(m_level_ps.get(i), m_pm);
                polynomial_ref witness = m_witnesses[i];
                
                if (m_level_ps.get(i) == section_poly)
                    add_projection_for_poly(p, m_level, witness, true, true); // section poly: full projection
                else if (has_roots.find(i) == has_roots.end())
                    add_projection_for_poly(p, m_level, witness, true, true); // no roots: need LC+disc for delineability
                else 
                    add_projection_for_poly(p, m_level, witness, false, true);
            }
        }

        // Sector case: projection loop using m_omit_lc and m_omit_disc.
        void add_sector_projections() {
            for (unsigned i = 0; i < m_level_ps.size(); ++i) {
                polynomial_ref p(m_level_ps.get(i), m_pm);
                polynomial_ref lc(m_pm);
                unsigned deg = m_pm.degree(p, m_level);
                lc = m_pm.coeff(p, m_level, deg);

                bool add_lc = !vec_get(m_omit_lc, i, false);
                bool add_disc = !vec_get(m_omit_disc, i, false);

                TRACE(lws,
                      tout << "  poly[" << i << "]";
                      tout << " omit_lc=" << vec_get(m_omit_lc, i, false);
                      tout << " omit_disc=" << vec_get(m_omit_disc, i, false);
                      tout << "\n";
                    );

                // coeffNonNull optimization: if the leading coefficient is already non-zero at the
                // sample point AND we're projecting it, the LC itself serves as the non-null witness.
                // No need for an additional coefficient witness in this case.
                polynomial_ref witness = m_witnesses[i];
                if (add_lc && witness && !is_const(witness))
                    if (lc && !is_zero(lc) && sign(lc))
                        witness = polynomial_ref(m_pm);

                add_projection_for_poly(p, m_level, witness, add_lc, add_disc);
            }
        }

        // Check if spanning tree should be used based on both_count threshold.
        // Note: This is only called from process_level_sector which handles non-section cases.
        // Spanning tree requires distinct lower/upper bounds and enough both-side polys.
        bool should_use_spanning_tree() {
            SASSERT(!is_section());  // spanning_tree is for sector case only
            // Need at least 2 polynomials for a spanning tree to have edges
            if (m_spanning_tree_threshold < 2)
                return false;
            if (m_rel.m_rfunc.size() < 4) // 2 different bounds + at least 2 same out of bounds
                return false;
            if (m_side_mask.size() == 0)
                return false;

            if (!is_set(m_l_rf) || !is_set(m_u_rf))
                return false;

            if (same_boundary_poly())
                return false;  // spanning tree requires distinct lower/upper bounds
            
            unsigned both_count = 0;
            for (unsigned i = 0; i < m_level_ps.size(); ++i)
                if (m_side_mask[i] == 3)
                    if (++both_count >= m_spanning_tree_threshold)
                        return true;
            return false;
        }

        // Clear all per-level state that could be stale from previous levels.
        // This ensures no leftover heuristic decisions affect the current level.
        void clear_level_state() {
            m_omit_lc.clear();
            m_omit_disc.clear();
            m_rel.m_pairs.clear();
            m_side_mask.clear();
            m_deg_in_order_graph.clear();
            m_unique_neighbor.clear();
        }

        void process_level_with_mode(projection_mode mode, bool have_interval) {
            if (have_interval) {
                switch (mode) {
                case projection_mode::section_biggest_cell:
                    fill_relation_pairs_for_section_biggest_cell();
                    break;

                case projection_mode::sector_biggest_cell:
                    fill_relation_sector_biggest_cell();
                    compute_side_mask();
                    compute_omit_lc_both_sides(/*require_leaf=*/false);
                    // m_omit_disc stays empty - all discriminants added
                    break;

                case projection_mode::sector_spanning_tree:
                    fill_relation_sector_spanning_tree();
                    compute_side_mask();
                    compute_omit_lc_both_sides(/*require_leaf=*/true);
                    // m_omit_disc stays empty - all discriminants added
                    break;
                }
                SASSERT(relation_invariant());
            }

            if (mode == projection_mode::section_biggest_cell)
                add_section_projections();
            else
                add_sector_projections();
            
            add_relation_resultants();
        }

        void collect_non_null_witnesses() {
            // Line 10/11: detect nullification + pick a non-zero coefficient witness per p.
            m_witnesses.clear();
            m_witnesses.reserve(m_level_ps.size());
            // Fixpoint loop: handle_nullified_poly may add more polynomials back at m_level
            // via request_factorized. Drain them from m_todo into m_level_ps and
            // compute witnesses for the new entries until no more appear.
            for (unsigned i = 0; i < m_level_ps.size(); i++) {
                polynomial_ref p(m_level_ps.get(i), m_pm);
                polynomial_ref w = choose_nonzero_coeff(p, m_level);
                if (!w)
                    handle_nullified_poly(p);
                m_witnesses.push_back(w); // need to push anyway since m_witnesses is accessed by the index
                // Absorb any same-level polys that handle_nullified_poly added to m_todo
                if (i + 1 == m_level_ps.size())
                    m_todo.extract_polys_at_level(m_level, m_level_ps);
            }
        }

        void display_polys_at_level(std::ostream& out) {
            TRACE(lws, out << "Polynomials at level " << m_level << "\n";
                  for (unsigned i = 0; i < m_level_ps.size(); ++i) 
                      m_pm.display(out, m_level_ps.get(i)) << "\n";);            
        }
        
        void process_level() {
            TRACE(lws, display_polys_at_level(tout););
            clear_level_state();  // Clear stale state from previous level
            collect_non_null_witnesses();
            // Lines 3-8: Θ + I_level + relation ≼
            bool have_interval = build_interval();

            TRACE(lws,
                  display(tout << "Interval: ", m_solver, m_I[m_level])
                      << "\nSection? " << (m_I[m_level].section ? "yes" : "no")
                      << "\nhave_interval=" << have_interval << ", rfunc.size=" << m_rel.m_rfunc.size() << "\n";
                  for (unsigned i = 0; i < m_rel.m_rfunc.size(); ++i)
                      m_am.display(tout << "  rfunc[" << i << "]: ps_idx=" << m_rel.m_rfunc[i].ps_idx << ", val=", m_rel.m_rfunc[i].val) << "\n";
                );

            projection_mode mode;
            if (m_I[m_level].section)
                mode = projection_mode::section_biggest_cell;
            else if (should_use_spanning_tree())
                mode = projection_mode::sector_spanning_tree;
            else
                mode = projection_mode::sector_biggest_cell;

            process_level_with_mode(mode, have_interval);
        }

        bool poly_has_roots(unsigned i) { return vec_get(m_poly_has_roots, i, false); }
        
        void process_top_level() {
            TRACE(lws, display_polys_at_level(tout););
            collect_non_null_witnesses();
            add_adjacent_root_resultants();

            // Projections (coeff witness, disc, leading coeff).
            for (unsigned i = 0; i < m_level_ps.size(); ++i) {
                polynomial_ref p(m_level_ps.get(i), m_pm);
                polynomial_ref lc(m_pm);
                unsigned deg = m_pm.degree(p, m_n);
                lc = m_pm.coeff(p, m_n, deg);

                bool add_lc = true;  
                if (!poly_has_roots(i))
                    if (lc && !is_zero(lc) && sign(lc))
                        add_lc = false;

                // if the leading coefficient is already non-zero at the sample
                // AND we're adding lc, we do not need to project an additional non-null coefficient witness.
                polynomial_ref witness = m_witnesses[i];
                if (add_lc && witness && !is_const(witness))
                    if (lc && !is_zero(lc) && sign(lc))
                        witness = polynomial_ref(m_pm); // zero the witnsee as lc will be the witness
                add_projection_for_poly(p, m_n, witness, add_lc, true); //true to add the discriminant
            }
        }

        std_vector<root_function_interval> single_cell() {
            TRACE(lws,             
                  tout << "Input polynomials (" << m_P.size() << "):\n";
                  for (unsigned i = 0; i < m_P.size(); ++i)
                      m_pm.display(tout << "  p[" << i << "]: ", m_P.get(i)) << "\n";
                  tout << "Sample values:\n";
                  for (unsigned j = 0; j < m_n; ++j)
                      m_am.display(tout << "  x" << j << " = ", sample().value(j)) << "\n";
                );

            if (m_n == 0) return m_I;

            m_todo.reset();

            // Initialize m_todo with distinct irreducible factors of the input polynomials.
            for (unsigned i = 0; i < m_P.size(); ++i) {
                polynomial_ref pi(m_P.get(i), m_pm);
                request_factorized(pi);
            }

            if (m_todo.empty()) return m_I;

            // Process top level m_n :we project out from x_{m_n} and do not return an interval for it.
            if (m_todo.max_var() == m_n) {
                m_level = m_todo.extract_max_polys(m_level_ps);
                process_top_level();
            }

            // Now iteratively process remaining levels
            while (!m_todo.empty()) {
                m_level = m_todo.extract_max_polys(m_level_ps);                
                SASSERT(m_level < m_n);
                process_level();
                TRACE(lws,
                      tout << "After level " << m_level << ": m_todo.empty()=" << m_todo.empty();
                      if (!m_todo.empty()) tout << ", m_todo.max_var()=" << m_todo.max_var();
                      tout << "\n";
                    );
            }

            TRACE(lws,
                  for (unsigned i = 0; i < m_I.size(); ++i)
                      display(tout << "I[" << i << "]: ", m_solver, m_I[i]) << "\n";
                );

            return m_I;
        }

    };

    levelwise::levelwise(
        nlsat::solver& solver,
        polynomial_ref_vector const& ps,
        var n,
        assignment const& s,
        pmanager& pm,
        anum_manager& am,
        polynomial::cache& cache)
        : m_impl(new impl(solver, ps, n, s, pm, am, cache)) {}

    levelwise::~levelwise() { delete m_impl; }

    std_vector<levelwise::root_function_interval> levelwise::single_cell() {
        return m_impl->single_cell();
    }
} // namespace nlsat

// Free pretty-printer for symbolic_interval
std::ostream& nlsat::display(std::ostream& out, solver& s, levelwise::root_function_interval const& I) {
    if (I.section) {
        out << "Section: ";
        if (I.l == nullptr)
            out << "(undef)";
        else {
            ::nlsat::display(out, s, I.l);
            out << "[root_index:" << I.l_index << "]";
        }
    }
    else {
        out << "Sector: (";
        if (I.l_inf())
            out << "-oo";
        else {
            ::nlsat::display(out, s, I.l);
            out << "[root_index:" << I.l_index << "]";
        }
        out << ", ";
        if (I.u_inf())
            out << "+oo";
        else {
            ::nlsat::display(out, s, I.u);
            out << "[root_index:" << I.u_index << "]";
        }
        out << ")";
    }
    return out;
}
