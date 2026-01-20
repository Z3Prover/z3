#include "nlsat/levelwise.h"
#include "nlsat/nlsat_types.h"
#include "nlsat/nlsat_assignment.h"
#include "math/polynomial/algebraic_numbers.h"
#include "math/polynomial/polynomial.h"
#include "nlsat_common.h"
#include "util/z3_exception.h"
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

    enum relation_mode {
        // Sector (i.e., non-section) heuristics:
        biggest_cell,
        chain,
        lowest_degree,

        // Section-specific heuristics:
        section_biggest_cell,
        section_chain,
        section_lowest_degree
    };

// Tag indicating what kind of invariance we need to preserve for a polynomial on the cell:
// - SIGN: sign-invariance is sufficient
// - ORD:  order-invariance is required (a stronger requirement)
//
// This is inspired by SMT-RAT's InvarianceType and is used together with a
// de-dup/upgrade worklist discipline (appendOnCorrectLevel()).
    enum class inv_req : uint8_t { none = 0, sign = 1, ord = 2 };

    static inline inv_req max_req(inv_req a, inv_req b) {
        return static_cast<uint8_t>(a) < static_cast<uint8_t>(b) ? b : a;
    }

    struct nullified_poly_exception {};

    struct levelwise::impl {
        solver&                      m_solver;
        polynomial_ref_vector const& m_P;
        unsigned                     m_n;        // maximal variable we project from
        pmanager&                    m_pm;
        anum_manager&                m_am;
        polynomial::cache&           m_cache;
        std::vector<root_function_interval> m_I; // intervals for variables 0..m_n-1

        unsigned               m_level = 0;      // current level being processed
        relation_mode          m_sector_relation_mode = chain;
        relation_mode          m_section_relation_mode = section_chain;
        bool                   m_dynamic_heuristic = true; // dynamically select heuristic based on weight
        unsigned               m_l_rf = UINT_MAX; // position of lower bound in m_rel.m_rfunc
        unsigned               m_u_rf = UINT_MAX; // position of upper bound in m_rel.m_rfunc (UINT_MAX in section case)

        // Per-level state set by process_level/process_top_level
        using tagged_id = std::pair<unsigned, inv_req>; // <pm.id(poly), tag>
        todo_set                        m_todo;
        polynomial_ref_vector           m_level_ps;
        std::vector<tagged_id>          m_level_tags;
        std::vector<polynomial_ref>     m_witnesses;
        std_vector<bool>                m_poly_has_roots;

        polynomial_ref_vector  m_psc_tmp;        // scratch for PSC chains
        bool                   m_fail = false;
        // Current requirement tag for polynomials stored in the todo_set, keyed by pm.id(poly*).
        // Entries are upgraded SIGN -> ORD as needed and cleared when a polynomial is extracted.
        std_vector<uint8_t>    m_req;

        // Scratch set for tracking added polynomial pairs (reused to avoid allocations)
        mutable std::set<std::pair<unsigned, unsigned>> m_added_pairs;

        // Reusable maps keyed by polynomial ID (more efficient than vectors for sparse IDs)
        mutable std::unordered_map<unsigned, uint8_t> m_side_mask;
        mutable std::unordered_map<unsigned, unsigned> m_deg_in_order_graph;
        mutable std::unordered_map<unsigned, bool> m_omit_lc;
        mutable std::unordered_map<unsigned, bool> m_omit_disc;
        mutable std::unordered_map<unsigned, unsigned> m_unique_neighbor;

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
            scoped_anum      val;
            indexed_root_expr ire;
            root_function(anum_manager& am, poly* p, unsigned idx, anum const& v)
                : val(am), ire{ p, idx } { am.set(val, v); }
            root_function(root_function&& other) noexcept : val(other.val.m()), ire(other.ire) { val = other.val; }
            root_function(root_function const&) = delete;
            root_function& operator=(root_function const&) = delete;
            root_function& operator=(root_function&& other) noexcept {
                val = other.val;
                ire = other.ire;
                return *this;
            }
        };

        // Root functions (Theta) and the chosen relation (≼) on a given level.
        struct relation_E {
            std::vector<root_function>              m_rfunc; // Θ: root functions on current level
            std::vector<std::pair<unsigned, unsigned>> m_pairs; // ≼ relation on indices into m_rfunc
            bool empty() const { return m_rfunc.empty() && m_pairs.empty(); }
            void clear() {
                m_pairs.clear();
                m_rfunc.clear();
            }
            void add_pair(unsigned j, unsigned k) { m_pairs.emplace_back(j, k); }
        };

        relation_E m_rel;

        // Weight function for estimating projection complexity.
        // w(p, level) estimates the "cost" of polynomial p at the given level.
        // w(disc(a)) ≈ 2*w(a), w(res(a,b)) ≈ w(a) + w(b)
        unsigned w(poly* p, unsigned level) const {
            if (!p) return 0;
            return m_pm.degree(p, level);
        }

        // Estimate resultant weight for m_rel.m_pairs
        unsigned estimate_resultant_weight() const {
            auto const& rfs = m_rel.m_rfunc;
            unsigned total = 0;
            m_added_pairs.clear();
            for (auto const& pr : m_rel.m_pairs) {
                poly* a = rfs[pr.first].ire.p;
                poly* b = rfs[pr.second].ire.p;
                if (!a || !b) continue;
                unsigned id1 = m_pm.id(a);
                unsigned id2 = m_pm.id(b);
                if (id1 == id2) continue;
                auto key = id1 < id2 ? std::make_pair(id1, id2) : std::make_pair(id2, id1);
                if (!m_added_pairs.insert(key).second) continue;
                // w(res(a,b)) ≈ w(a) + w(b)
                total += w(a, m_level) + w(b, m_level);
            }
            return total;
        }

        // Choose the best sector heuristic based on estimated weight.
        // Also fills m_rel.m_pairs with the winning heuristic's pairs.
        relation_mode choose_best_sector_heuristic() {
            // With fewer than 2 root functions, no pairs can be generated
            // so all heuristics are equivalent - use default
            if (m_rel.m_rfunc.size() < 2) {
                TRACE(lws,
                    tout << "Level " << m_level << " SECTOR: rfunc.size=" << m_rel.m_rfunc.size()
                         << " < 2, using default heuristic\n";
                );
                return m_sector_relation_mode;
            }

            // Estimate weights by filling m_rel.m_pairs temporarily.
            // Fill lowest_degree last since it's the most common winner (tie-breaker).
            m_rel.m_pairs.clear();
            fill_relation_with_biggest_cell_heuristic();
            unsigned w_bc = estimate_resultant_weight();

            m_rel.m_pairs.clear();
            fill_relation_with_chain_heuristic();
            unsigned w_ch = estimate_resultant_weight();

            m_rel.m_pairs.clear();
            fill_relation_with_min_degree_resultant_sum();
            unsigned w_ld = estimate_resultant_weight();

            TRACE(lws,
                tout << "Level " << m_level << " SECTOR: rfunc.size=" << m_rel.m_rfunc.size()
                     << ", m_l_rf=" << (is_set(m_l_rf) ? std::to_string(m_l_rf) : "UNSET")
                     << ", m_u_rf=" << (is_set(m_u_rf) ? std::to_string(m_u_rf) : "UNSET")
                     << "\n  weight estimates: biggest_cell=" << w_bc
                     << ", chain=" << w_ch
                     << ", lowest_degree=" << w_ld << "\n";
            );

            unsigned w_min = std::min({w_bc, w_ch, w_ld});

            // If lowest_degree wins, pairs are already filled
            if (w_ld == w_min)
                return lowest_degree;

            // Otherwise, refill with the winning heuristic
            m_rel.m_pairs.clear();
            if (w_ch == w_min) {
                fill_relation_with_chain_heuristic();
                return chain;
            }
            TRACE(lws, tout << "bc wins\n");
            fill_relation_with_biggest_cell_heuristic();
            return biggest_cell;
        }

        // Choose the best section heuristic based on estimated weight.
        // Also fills m_rel.m_pairs with the winning heuristic's pairs.
        relation_mode choose_best_section_heuristic() {
            // With fewer than 2 root functions, no pairs can be generated
            // so all heuristics are equivalent - use default
            if (m_rel.m_rfunc.size() < 2) {
                TRACE(lws,
                    tout << "Level " << m_level << " SECTION: rfunc.size=" << m_rel.m_rfunc.size()
                         << " < 2, using default heuristic\n";
                );
                return m_section_relation_mode;
            }

            // Estimate weights by filling m_rel.m_pairs temporarily.
            // Fill lowest_degree last since it's the most common winner (tie-breaker).
            m_rel.m_pairs.clear();
            fill_relation_pairs_for_section_biggest_cell();
            unsigned w_bc = estimate_resultant_weight();

            m_rel.m_pairs.clear();
            fill_relation_pairs_for_section_chain();
            unsigned w_ch = estimate_resultant_weight();

            m_rel.m_pairs.clear();
            fill_relation_pairs_for_section_lowest_degree();
            unsigned w_ld = estimate_resultant_weight();

            TRACE(lws,
                tout << "Level " << m_level << " SECTION: rfunc.size=" << m_rel.m_rfunc.size()
                     << ", m_l_rf=" << (is_set(m_l_rf) ? std::to_string(m_l_rf) : "UNSET")
                     << "\n  weight estimates: biggest_cell=" << w_bc
                     << ", chain=" << w_ch
                     << ", lowest_degree=" << w_ld << "\n";
            );

            unsigned w_min = std::min({w_bc, w_ch, w_ld});

            // If lowest_degree wins, pairs are already filled
            if (w_ld == w_min)
                return section_lowest_degree;

            // Otherwise, refill with the winning heuristic
            m_rel.m_pairs.clear();
            if (w_ch == w_min) {
                fill_relation_pairs_for_section_chain();
                return section_chain;
            }
            fill_relation_pairs_for_section_biggest_cell();
            return section_biggest_cell;
        }

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

            switch (m_solver.lws_sector_relation_mode()) {
            case 0:
                m_sector_relation_mode = biggest_cell;
                break;
            case 1:
                m_sector_relation_mode = chain;
                break;
            case 2:
                m_sector_relation_mode = lowest_degree;
                break;
            default:
                m_sector_relation_mode = chain;
                break;
            }

            switch (m_solver.lws_section_relation_mode()) {
            case 0:
                m_section_relation_mode = section_biggest_cell;
                break;
            case 1:
                m_section_relation_mode = section_chain;
                break;
            case 2:
                m_section_relation_mode = section_lowest_degree;
                break;
            default:
                m_section_relation_mode = section_chain;
                break;
            }

            m_dynamic_heuristic = m_solver.lws_dynamic_heuristic();
        }

        void fail() { throw nullified_poly_exception(); }

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

        poly* request(todo_set& P, poly* p, inv_req req) {
            if (!p || req == inv_req::none)
                return p;
            p = P.insert(p);
            unsigned id = m_pm.id(p);
            auto cur = static_cast<inv_req>(vec_get(m_req, id, static_cast<uint8_t>(inv_req::none)));
            inv_req nxt = max_req(cur, req);
            if (nxt != cur)
                vec_setx(m_req, id, static_cast<uint8_t>(nxt), static_cast<uint8_t>(inv_req::none));
            return p;
        }

        void request_factorized(todo_set& P, polynomial_ref const& poly, inv_req req) {
            for_each_distinct_factor(poly, [&](polynomial_ref const& f) {
                request(P, f.get(), req); // inherit tag across factorization (SMT-RAT appendOnCorrectLevel)
            });
        }

        // Extract polynomials at max level from m_todo into m_level_ps and m_level_tags.
        // Sets m_level to the extracted level.
        void extract_max_tagged() {
            m_level = m_todo.extract_max_polys(m_level_ps);
            m_level_tags.clear();
            m_level_tags.reserve(m_level_ps.size());
            for (unsigned i = 0; i < m_level_ps.size(); ++i) {
                poly* p = m_level_ps.get(i);
                unsigned id = m_pm.id(p);
                inv_req req = static_cast<inv_req>(vec_get(m_req, id, static_cast<uint8_t>(inv_req::sign)));
                if (req == inv_req::none)
                    req = inv_req::sign;
                m_level_tags.emplace_back(id, req);
                // Clear: extracted polynomials are no longer part of the worklist.
                vec_setx(m_req, id, static_cast<uint8_t>(inv_req::none), static_cast<uint8_t>(inv_req::none));
            }
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
                if (m_am.eval_sign_at(coeff, sample()) == 0)
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

        void add_projections_for(todo_set& P, polynomial_ref const& p, unsigned x, polynomial_ref const& nonzero_coeff, bool add_leading_coeff, bool add_discriminant) {
            // Line 11 (non-null witness coefficient)
            if (nonzero_coeff && !is_const(nonzero_coeff))
                request_factorized(P, nonzero_coeff, inv_req::sign);

            // Line 12 (disc + leading coefficient)
            if (add_discriminant)
                request_factorized(P, psc_discriminant(p, x), inv_req::ord);
            if (add_leading_coeff) {
                unsigned deg = m_pm.degree(p, x);
                polynomial_ref lc(m_pm);
                lc = m_pm.coeff(p, x, deg);
                request_factorized(P, lc, inv_req::sign);
            }
        }

        // ============================================================================
        // noLdcf helpers - compute which leading coefficients can be omitted
        // Inspired by SMT-RAT's "noLdcf" optimization in OneCellCAD.h.
        // ============================================================================

        // Compute side_mask: track which side(s) each polynomial appears on
        // bit0 = lower (<= sample), bit1 = upper (> sample), 3 = both sides
        void compute_side_mask() {
            m_side_mask.clear();
            anum const& v = sample().value(m_level);
            for (auto const& rf : m_rel.m_rfunc) {
                poly* p = rf.ire.p;
                if (!p)
                    continue;
                unsigned id = m_pm.id(p);
                uint8_t& mask = m_side_mask[id];
                if (m_am.compare(rf.val, v) <= 0)
                    mask |= 1;
                else
                    mask |= 2;
            }
        }

        // Compute deg: count distinct resultant-neighbors for each polynomial
        void compute_resultant_degree() {
            m_deg_in_order_graph.clear();
            m_added_pairs.clear();
            for (auto const& pr : m_rel.m_pairs) {
                poly* a = m_rel.m_rfunc[pr.first].ire.p;
                poly* b = m_rel.m_rfunc[pr.second].ire.p;
                if (!a || !b)
                    continue;
                unsigned id1 = m_pm.id(a);
                unsigned id2 = m_pm.id(b);
                if (id1 == id2)
                    continue;
                std::pair<unsigned, unsigned> key = id1 < id2 ? std::make_pair(id1, id2) : std::make_pair(id2, id1);
                if (!m_added_pairs.insert(key).second)
                    continue;
                m_deg_in_order_graph[id1]++;
                m_deg_in_order_graph[id2]++;
            }
        }

        // ----------------------------------------------------------------------------
        // noLdcf heuristic helpers
        // ----------------------------------------------------------------------------

        // Helper for biggest_cell and lowest_degree heuristics:
        // Omit lc for polynomials appearing on both sides of the sample.
        // If require_leaf is true, additionally require deg == 1 (leaf in resultant graph).
        void compute_omit_lc_both_sides(bool require_leaf) {
            m_omit_lc.clear();
            if (m_rel.m_rfunc.empty() || m_rel.m_pairs.empty())
                return;

            compute_side_mask();
            if (require_leaf)
                compute_resultant_degree();

            for (unsigned i = 0; i < m_level_ps.size(); ++i) {
                poly* p = m_level_ps.get(i);
                if (!p)
                    continue;
                unsigned id = m_pm.id(p);
                auto sm_it = m_side_mask.find(id);
                if (sm_it == m_side_mask.end() || sm_it->second != 3)
                    continue;
                if (require_leaf) {
                    auto deg_it = m_deg_in_order_graph.find(id);
                    if (deg_it == m_deg_in_order_graph.end() || deg_it->second != 1)
                        continue;
                }
                m_omit_lc[id] = true;
            }
        }

        // Helper for chain heuristics:
        // Omit lc for extremes of chain that appear on the other side.
        // - Extreme of lower chain (index 0): omit if it also appears on upper side
        // - Extreme of upper chain (index n-1): omit if it also appears on lower side
        void compute_omit_lc_chain_extremes(bool has_lower, bool has_upper) {
            m_omit_lc.clear();
            if (m_rel.m_rfunc.empty())
                return;

            compute_side_mask();
            unsigned n = m_rel.m_rfunc.size();

            if (has_lower) {
                poly* p = m_rel.m_rfunc[0].ire.p;
                unsigned id = m_pm.id(p);
                auto it = m_side_mask.find(id);
                if (it != m_side_mask.end() && (it->second & 2))
                    m_omit_lc[id] = true;
            }

            if (has_upper) {
                poly* p = m_rel.m_rfunc[n - 1].ire.p;
                unsigned id = m_pm.id(p);
                auto it = m_side_mask.find(id);
                if (it != m_side_mask.end() && (it->second & 1))
                    m_omit_lc[id] = true;
            }
        }

        // Dispatch to appropriate sector heuristic
        void compute_omit_lc_sector() {
            switch (m_sector_relation_mode) {
            case biggest_cell:
                compute_omit_lc_both_sides(false);
                break;
            case chain:
                compute_omit_lc_chain_extremes(is_set(m_l_rf), is_set(m_u_rf));
                break;
            case lowest_degree:
                compute_omit_lc_both_sides(true);
                break;
            default:
                m_omit_lc.clear();
                break;
            }
        }

        // Dispatch to appropriate section heuristic
        void compute_omit_lc_section() {
            switch (m_section_relation_mode) {
            case section_biggest_cell:
                m_omit_lc.clear();  // no omit_lc - handled via ORD_INV tag
                break;
            case section_chain: {
                unsigned partition_idx = m_l_rf + 1;
                compute_omit_lc_chain_extremes(partition_idx > 0, partition_idx < m_rel.m_rfunc.size());
                break;
            }
            case section_lowest_degree:
                compute_omit_lc_both_sides(true);
                break;
            default:
                m_omit_lc.clear();
                break;
            }
        }

        // Decide which discriminants can be omitted in the SECTION case based on the chosen
        // resultant relation. Inspired by SMT-RAT's "noDisc" optimization in OneCellCAD.h:
        // if a polynomial is only connected to the section-defining polynomial via resultants,
        // we do not need its discriminant for transitive root-order reasoning.
        void compute_omit_disc_from_section_relation() {
            auto const& I = m_I[m_level];
            m_omit_disc.clear();
            if (!I.section)
                return;
            poly* section_p = I.l.get();
            if (!section_p)
                return;
            if (m_rel.m_rfunc.empty() || m_rel.m_pairs.empty())
                return;

            unsigned section_id = m_pm.id(section_p);

            // Track the unique (if any) resultant-neighbor for each polynomial and its degree in the
            // de-duplicated resultant graph. If deg(p) == 1 and neighbor(p) == section_id, then p is
            // a leaf connected only to the section polynomial.
            m_unique_neighbor.clear();
            m_deg_in_order_graph.clear();

            m_added_pairs.clear();
            for (auto const& pr : m_rel.m_pairs) {
                poly* a = m_rel.m_rfunc[pr.first].ire.p;
                poly* b = m_rel.m_rfunc[pr.second].ire.p;
                if (!a || !b)
                    continue;
                unsigned id1 = m_pm.id(a);
                unsigned id2 = m_pm.id(b);
                if (id1 == id2)
                    continue;
                std::pair<unsigned, unsigned> key = id1 < id2 ? std::make_pair(id1, id2) : std::make_pair(id2, id1);
                if (!m_added_pairs.insert(key).second)
                    continue;

                auto add_neighbor = [&](unsigned id, unsigned other) {
                    m_deg_in_order_graph[id]++;
                    auto it = m_unique_neighbor.find(id);
                    if (it == m_unique_neighbor.end())
                        m_unique_neighbor[id] = other;
                    else if (it->second != other)
                        it->second = UINT_MAX - 1; // multiple neighbors
                };
                add_neighbor(id1, id2);
                add_neighbor(id2, id1);
            }

            for (unsigned i = 0; i < m_level_ps.size(); ++i) {
                poly* p = m_level_ps.get(i);
                if (!p)
                    continue;
                unsigned id = m_pm.id(p);
                if (id == section_id)
                    continue;
                auto deg_it = m_deg_in_order_graph.find(id);
                if (deg_it == m_deg_in_order_graph.end() || deg_it->second != 1)
                    continue;
                auto un_it = m_unique_neighbor.find(id);
                if (un_it == m_unique_neighbor.end() || un_it->second != section_id)
                    continue;
                // If p vanishes at the sample on the section, we may need p's delineability to
                // reason about coinciding root functions; be conservative and keep disc(p).
                if (m_am.eval_sign_at(polynomial_ref(p, m_pm), sample()) == 0)
                    continue;
                m_omit_disc[id] = true;
            }
        }

        // Relation construction heuristics (same intent as previous implementation).
        void fill_relation_with_biggest_cell_heuristic() {
            if (is_set(m_l_rf))
                for (unsigned j = 0; j < m_l_rf; ++j)
                    m_rel.add_pair(j, m_l_rf);

            if (is_set(m_u_rf))
                for (unsigned j = m_u_rf + 1; j < m_rel.m_rfunc.size(); ++j)
                    m_rel.add_pair(m_u_rf, j);

            if (is_set(m_l_rf) && is_set(m_u_rf)) {
                SASSERT(m_l_rf + 1 == m_u_rf);
                m_rel.add_pair(m_l_rf, m_u_rf);
            }
        }

        void fill_relation_with_chain_heuristic() {
            if (is_set(m_l_rf))
                for (unsigned j = 0; j < m_l_rf; ++j)
                    m_rel.add_pair(j, j + 1);

            if (is_set(m_u_rf))
                for (unsigned j = m_u_rf + 1; j < m_rel.m_rfunc.size(); ++j)
                    m_rel.add_pair(j - 1, j);

            if (is_set(m_l_rf) && is_set(m_u_rf)) {
                SASSERT(m_l_rf + 1 == m_u_rf);
                m_rel.add_pair(m_l_rf, m_u_rf);
            }
        }

        void fill_relation_with_min_degree_resultant_sum() {
            auto const& rfs = m_rel.m_rfunc;
            unsigned n = rfs.size();
            if (n == 0)
                return;

            std::vector<unsigned> degs;
            degs.reserve(n);
            for (unsigned i = 0; i < n; ++i)
                degs.push_back(m_pm.degree(rfs[i].ire.p, m_level));

            if (is_set(m_l_rf)) {
                unsigned min_idx = m_l_rf;
                unsigned min_deg = degs[m_l_rf];
                for (int j = static_cast<int>(m_l_rf) - 1; j >= 0; --j) {
                    unsigned jj = static_cast<unsigned>(j);
                    m_rel.add_pair(jj, min_idx);
                    if (degs[jj] < min_deg) {
                        min_deg = degs[jj];
                        min_idx = jj;
                    }
                }
            }

            if (is_set(m_u_rf)) {
                unsigned min_idx = m_u_rf;
                unsigned min_deg = degs[m_u_rf];
                for (unsigned j = m_u_rf + 1; j < n; ++j) {
                    m_rel.add_pair(min_idx, j);
                    if (degs[j] < min_deg) {
                        min_deg = degs[j];
                        min_idx = j;
                    }
                }
            }

            if (is_set(m_l_rf) && is_set(m_u_rf)) {
                SASSERT(m_l_rf + 1 == m_u_rf);
                m_rel.add_pair(m_l_rf, m_u_rf);
            }
        }

        void fill_relation_pairs_for_section_biggest_cell() {
            auto const& rfs = m_rel.m_rfunc;
            unsigned n = rfs.size();
            if (n == 0)
                return;
            SASSERT(is_set(m_l_rf));
            SASSERT(m_l_rf < n);
            for (unsigned j = 0; j < m_l_rf; ++j)
                m_rel.add_pair(j, m_l_rf);
            for (unsigned j = m_l_rf + 1; j < n; ++j)
                m_rel.add_pair(m_l_rf, j);
        }

        void fill_relation_pairs_for_section_chain() {
            auto const& rfs = m_rel.m_rfunc;
            unsigned n = rfs.size();
            if (n == 0)
                return;
            SASSERT(is_set(m_l_rf));
            SASSERT(m_l_rf < n);
            for (unsigned j = 0; j < m_l_rf; ++j)
                m_rel.add_pair(j, j + 1);
            for (unsigned j = m_l_rf + 1; j < n; ++j)
                m_rel.add_pair(j - 1, j);
        }

        void fill_relation_pairs_for_section_lowest_degree() {
            auto const& rfs = m_rel.m_rfunc;
            unsigned n = rfs.size();
            if (n == 0)
                return;
            SASSERT(is_set(m_l_rf));
            SASSERT(m_l_rf < n);

            std::vector<unsigned> degs;
            degs.reserve(n);
            for (unsigned i = 0; i < n; ++i)
                degs.push_back(m_pm.degree(rfs[i].ire.p, m_level));

            // For roots below m_l_rf: connect each to the minimum-degree root seen so far
            unsigned min_idx_below = m_l_rf;
            unsigned min_deg_below = degs[m_l_rf];
            for (int j = static_cast<int>(m_l_rf) - 1; j >= 0; --j) {
                unsigned jj = static_cast<unsigned>(j);
                m_rel.add_pair(jj, min_idx_below);
                if (degs[jj] < min_deg_below) {
                    min_deg_below = degs[jj];
                    min_idx_below = jj;
                }
            }

            // For roots above m_l_rf: connect minimum-degree root to each subsequent root
            unsigned min_idx_above = m_l_rf;
            unsigned min_deg_above = degs[m_l_rf];
            for (unsigned j = m_l_rf + 1; j < n; ++j) {
                m_rel.add_pair(min_idx_above, j);
                if (degs[j] < min_deg_above) {
                    min_deg_above = degs[j];
                    min_idx_above = j;
                }
            }
        }

        void fill_relation_pairs_for_section() {
            SASSERT(m_I[m_level].section);
            switch (m_section_relation_mode) {
            case biggest_cell:
            case section_biggest_cell:
                fill_relation_pairs_for_section_biggest_cell();
                break;
            case chain:
            case section_chain:
                fill_relation_pairs_for_section_chain();
                break;
            case lowest_degree:
            case section_lowest_degree:
                fill_relation_pairs_for_section_lowest_degree();
                break;
            default:
                NOT_IMPLEMENTED_YET();
            }
        }

        void fill_relation_pairs_for_sector() {
            SASSERT(!m_I[m_level].section);
            switch (m_sector_relation_mode) {
            case biggest_cell:
                fill_relation_with_biggest_cell_heuristic();
                break;
            case chain:
                fill_relation_with_chain_heuristic();
                break;
            case lowest_degree:
                fill_relation_with_min_degree_resultant_sum();
                break;
            default:
                NOT_IMPLEMENTED_YET();
            }
        }

        // Extract roots of polynomial p around sample value v at the given level,
        // partitioning them into lhalf (roots <= v) and uhalf (roots > v).
        // Returns whether the polynomial has any roots.
        bool isolate_roots_around_sample(unsigned level, poly* p, unsigned idx,
                                          anum const& v, std::vector<root_function>& lhalf,
                                          std::vector<root_function>& uhalf) {
            scoped_anum_vector roots(m_am);

            // When the sample value is rational use a closest-root isolation 
            // returning at most two roots
            if (v.is_basic()) {
                scoped_mpq s(m_am.qm());
                m_am.to_rational(v, s);
                svector<unsigned> idx_vec;
                m_am.isolate_roots_closest(polynomial_ref(p, m_pm), undef_var_assignment(sample(), level), s, roots, idx_vec);
                SASSERT(roots.size() == idx_vec.size());
                for (unsigned k = 0; k < roots.size(); ++k) {
                    if (m_am.compare(roots[k], v) <= 0)
                        lhalf.emplace_back(m_am, p, idx_vec[k], roots[k]);
                    else
                        uhalf.emplace_back(m_am, p, idx_vec[k], roots[k]);
                }
                return roots.size();
            }

            m_am.isolate_roots(polynomial_ref(p, m_pm), undef_var_assignment(sample(), level), roots);
            
            // SMT-RAT style reduction: keep only the closest to v roots: one below and one above v,
            // or a single root at v
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
                lhalf.emplace_back(m_am, p, lower + 1, roots[lower]);
                if (section)
                    return roots.size(); // only keep the section root for this polynomial
            }
            if (upper != UINT_MAX)
                uhalf.emplace_back(m_am, p, upper + 1, roots[upper]);
            return roots.size();
        }

        void init_poly_has_roots() {
            m_poly_has_roots.clear();
            m_poly_has_roots.resize(m_level_ps.size(), false);
        }

        bool collect_partitioned_root_functions_around_sample(anum const& v,
                            std::vector<root_function>& lhalf, std::vector<root_function>& uhalf) {
            for (unsigned i = 0; i < m_level_ps.size(); ++i)
                m_poly_has_roots[i] = isolate_roots_around_sample(m_level, m_level_ps.get(i), i, v, lhalf, uhalf);
            return !lhalf.empty() || !uhalf.empty();
        }

        std::vector<root_function>::iterator set_relation_root_functions_from_partitions(std::vector<root_function>& lhalf,
                            std::vector<root_function>& uhalf) {
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

        void sort_root_function_partitions(std::vector<root_function>::iterator mid) {
            auto& rfs = m_rel.m_rfunc;
            std::sort(rfs.begin(), mid,
                [&](root_function const& a, root_function const& b) { return root_function_lt(a, b, true); });
            std::sort(mid, rfs.end(),
                [&](root_function const& a, root_function const& b) { return root_function_lt(a, b, false); });
        }

        // Populate Θ (root functions) around the sample, partitioned at `mid`, and sort each partition.
        // Returns whether any roots were found.
        bool build_sorted_root_functions_around_sample(anum const& v, std::vector<root_function>::iterator& mid) {
            init_poly_has_roots();

            std::vector<root_function> lhalf, uhalf;
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
        void set_interval_from_root_partition(anum const& v, std::vector<root_function>::iterator mid) {
            auto& rfs = m_rel.m_rfunc;
            if (mid != rfs.begin()) {
                m_l_rf = static_cast<unsigned>((mid - rfs.begin()) - 1);
                auto& r = *(mid - 1);
                if (m_am.eq(r.val, v)) {
                    // Section case: only m_l_rf is defined
                    m_I[m_level].section = true;
                    m_I[m_level].l = r.ire.p;
                    m_I[m_level].l_index = r.ire.i;
                    m_u_rf = UINT_MAX;
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
            std::vector<root_function>::iterator mid;
            if (!build_sorted_root_functions_around_sample(v, mid))
                return false;

            set_interval_from_root_partition(v, mid);
            return true;
        }


        void add_relation_resultants() {
            m_added_pairs.clear();
            for (auto const& pr : m_rel.m_pairs) {
                poly* a = m_rel.m_rfunc[pr.first].ire.p;
                poly* b = m_rel.m_rfunc[pr.second].ire.p;
                if (!a || !b)
                    continue;
                unsigned id1 = m_pm.id(a);
                unsigned id2 = m_pm.id(b);
                if (id1 == id2)
                    continue;
                std::pair<unsigned, unsigned> key = id1 < id2 ? std::make_pair(id1, id2) : std::make_pair(id2, id1);
                if (!m_added_pairs.insert(key).second)
                    continue;
                request_factorized(m_todo, psc_resultant(a, b, m_level), inv_req::ord);
            }
        }

        // Top level (m_n): add resultants between adjacent roots of different polynomials.
        // Fills m_poly_has_roots as a side effect.
        void add_adjacent_root_resultants() {
            m_poly_has_roots.clear();
            m_poly_has_roots.resize(m_level_ps.size(), false);

            std::vector<std::pair<scoped_anum, poly*>> root_vals;
            for (unsigned i = 0; i < m_level_ps.size(); ++i) {
                poly* p = m_level_ps.get(i);
                scoped_anum_vector roots(m_am);
                m_am.isolate_roots(polynomial_ref(p, m_pm), undef_var_assignment(sample(), m_n), roots);
                m_poly_has_roots[i] = !roots.empty();
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
            m_added_pairs.clear();
            for (unsigned j = 0; j + 1 < root_vals.size(); ++j) {
                poly* p1 = root_vals[j].second;
                poly* p2 = root_vals[j + 1].second;
                if (!p1 || !p2)
                    continue;
                unsigned id1 = m_pm.id(p1);
                unsigned id2 = m_pm.id(p2);
                if (id1 == id2)
                    continue;
                std::pair<unsigned, unsigned> key = id1 < id2 ? std::make_pair(id1, id2) : std::make_pair(id2, id1);
                if (!m_added_pairs.insert(key).second)
                    continue;
                request_factorized(m_todo, psc_resultant(p1, p2, m_n), inv_req::ord);
            }
        }

        void upgrade_bounds_to_ord() {
            poly* lb = m_I[m_level].l;
            poly* ub = m_I[m_level].u;
            for (unsigned i = 0; i < m_level_ps.size(); ++i) {
                poly* p = m_level_ps.get(i);
                if (p == lb || p == ub)
                    m_level_tags[i].second = inv_req::ord;
            }
        }

        void add_level_projections_sector() {
            // Lines 11-12 (Algorithm 1): add projections for each p
            // Note: Algorithm 1 adds disc + ldcf for ALL polynomials (classical delineability)
            // We additionally omit leading coefficients for rootless polynomials when possible
            // (cf. projective delineability, Lemma 3.2).
            compute_omit_lc_sector();
            for (unsigned i = 0; i < m_level_ps.size(); ++i) {
                polynomial_ref p(m_level_ps.get(i), m_pm);
                polynomial_ref lc(m_pm);
                unsigned deg = m_pm.degree(p, m_level);
                lc = m_pm.coeff(p, m_level, deg);

                unsigned pid = m_pm.id(p.get());
                auto it = m_omit_lc.find(pid);
                bool add_lc = (it == m_omit_lc.end() || !it->second);

                if (add_lc && i < usize(m_poly_has_roots) && !m_poly_has_roots[i])
                    if (lc && !is_zero(lc) && m_am.eval_sign_at(lc, sample()) != 0)
                        add_lc = false;

                // SMT-RAT-style coeffNonNull: if the leading coefficient is already non-zero at the sample
                // AND we're adding lc, we do not need to project an additional non-null coefficient witness.
                polynomial_ref witness = m_witnesses[i];
                if (add_lc && witness && !is_const(witness))
                    if (lc && !is_zero(lc) && m_am.eval_sign_at(lc, sample()) != 0)
                        witness = polynomial_ref(m_pm);
                add_projections_for(m_todo, p, m_level, witness, add_lc, true); //true for adding the discriminant: always add it in sector, required by Lemma 3.2.
            }
        }

        void add_level_projections_section() {
            SASSERT(m_I[m_level].section);
            poly* section_p = m_I[m_level].l.get();

            // Compute omission information derived from the chosen relation (still used for heuristics 2/3).
            compute_omit_lc_section();
            // SMT-RAT only applies noDisc optimization for section_lowest_degree (heuristic 3)
            if (m_section_relation_mode == section_lowest_degree)
                compute_omit_disc_from_section_relation();
            else
                m_omit_disc.clear();

            for (unsigned i = 0; i < m_level_ps.size(); ++i) {
                polynomial_ref p(m_level_ps.get(i), m_pm);
                unsigned pid = m_pm.id(p.get());
                bool is_section_poly = section_p && p.get() == section_p;
                bool has_roots = i < usize(m_poly_has_roots) && m_poly_has_roots[i];

                polynomial_ref lc(m_pm);
                unsigned deg = m_pm.degree(p, m_level);
                lc = m_pm.coeff(p, m_level, deg);

                bool add_lc = true;
                if (is_section_poly) {
                    // add_lc stays true
                }
                else if (m_section_relation_mode == section_biggest_cell) {
                    // SMT-RAT section heuristic 1 projects leading coefficients primarily for the
                    // defining section polynomial; keep LCs only for upstream ORD polynomials.
                    if (m_level_tags[i].second != inv_req::ord)
                        add_lc = false;
                }
                else {
                    auto it = m_omit_lc.find(pid);
                    if (add_lc && it != m_omit_lc.end() && it->second)
                        add_lc = false;

                    if (add_lc && !has_roots)
                        if (lc && !is_zero(lc) && m_am.eval_sign_at(lc, sample()) != 0)
                            add_lc = false;
                }

                bool add_disc = true;
                if (is_section_poly)
                    add_disc = true;
                else if (m_section_relation_mode == section_biggest_cell) {
                    // SMT-RAT section heuristic 1 projects discriminants primarily for the defining
                    // polynomial; keep discriminants only for upstream ORD polynomials.
                    if (m_level_tags[i].second != inv_req::ord)
                        add_disc = false;
                }
                // DISABLED: chain disc skipping is unsound
                // else if (m_section_relation_mode == section_chain) {
                //     // In SMT-RAT's chain-style section heuristic, discriminants are projected for
                //     // polynomials that actually have roots around the sample.
                //     if (m_level_tags[i].second != inv_req::ord && !has_roots)
                //         add_disc = false;
                // }

                // Only omit discriminants for polynomials that were not required to be order-invariant
                // by upstream projection steps.
                if (add_disc && m_level_tags[i].second != inv_req::ord) {
                    auto it = m_omit_disc.find(pid);
                    if (it != m_omit_disc.end() && it->second)
                        add_disc = false;
                }

                // SMT-RAT-style coeffNonNull: if the leading coefficient is already non-zero at the sample
                // AND we're adding lc, we do not need to project an additional non-null coefficient witness.
                polynomial_ref witness = m_witnesses[i];
                if (add_lc && witness && !is_const(witness))
                    if (lc && !is_zero(lc) && m_am.eval_sign_at(lc, sample()) != 0)
                        witness = polynomial_ref(m_pm);

                add_projections_for(m_todo, p, m_level, witness, add_lc, add_disc);
            }
        }

        void process_level_section(bool have_interval) {
            SASSERT(m_I[m_level].section);
            if (have_interval) {
                if (m_dynamic_heuristic)
                    m_section_relation_mode = choose_best_section_heuristic(); // also fills pairs
                else
                    fill_relation_pairs_for_section();
            }
            upgrade_bounds_to_ord();
            add_level_projections_section();
            add_relation_resultants();
        }

        void process_level_sector(bool have_interval) {
            SASSERT(!m_I[m_level].section);
            if (have_interval) {
                if (m_dynamic_heuristic)
                    m_sector_relation_mode = choose_best_sector_heuristic(); // also fills pairs
                else
                    fill_relation_pairs_for_sector();
            }
            upgrade_bounds_to_ord();
            add_level_projections_sector();
            add_relation_resultants();
        }

        void process_level() {
            SASSERT(m_level_ps.size() == m_level_tags.size());

            // Line 10/11: detect nullification + pick a non-zero coefficient witness per p.
            m_witnesses.clear();
            m_witnesses.reserve(m_level_ps.size());
            for (unsigned i = 0; i < m_level_ps.size(); ++i) {
                polynomial_ref p(m_level_ps.get(i), m_pm);
                SASSERT(m_level_tags[i].first == m_pm.id(p.get()));

                polynomial_ref w = choose_nonzero_coeff(p, m_level);
                if (!w)
                    fail();
                m_witnesses.push_back(w);
            }

            // Lines 3-8: Θ + I_level + relation ≼
            bool have_interval = build_interval();
            if (m_I[m_level].section)
                process_level_section(have_interval);
            else
                process_level_sector(have_interval);
        }

        void process_top_level() {
            SASSERT(m_level_ps.size() == m_level_tags.size());
            m_witnesses.clear();
            m_witnesses.reserve(m_level_ps.size());
            for (unsigned i = 0; i < m_level_ps.size(); ++i) {
                polynomial_ref p(m_level_ps.get(i), m_pm);
                SASSERT(m_level_tags[i].first == m_pm.id(p.get()));
                polynomial_ref w = choose_nonzero_coeff(p, m_n);
                if (!w)
                    fail();
                m_witnesses.push_back(w);
            }

            // Resultants between adjacent root functions (a lightweight ordering for the top level).
            add_adjacent_root_resultants();

            // Projections (coeff witness, disc, leading coeff).
            // Note: SMT-RAT's levelwise implementation additionally has dedicated heuristics for
            // selecting resultants and selectively adding leading coefficients (see OneCellCAD.h,
            // sectionHeuristic/sectorHeuristic). Z3's levelwise currently uses the relation_mode
            // ordering heuristics instead of these specialized cases.
            for (unsigned i = 0; i < m_level_ps.size(); ++i) {
                polynomial_ref p(m_level_ps.get(i), m_pm);
                polynomial_ref lc(m_pm);
                unsigned deg = m_pm.degree(p, m_n);
                lc = m_pm.coeff(p, m_n, deg);

                bool add_lc = true;  // Let todo_set handle duplicates if witness == lc
                if (i < usize(m_poly_has_roots) && !m_poly_has_roots[i]) {
                    if (lc && !is_zero(lc) && m_am.eval_sign_at(lc, sample()) != 0)
                        add_lc = false;
                }
                // SMT-RAT-style coeffNonNull: if the leading coefficient is already non-zero at the sample
                // AND we're adding lc, we do not need to project an additional non-null coefficient witness.
                polynomial_ref witness = m_witnesses[i];
                if (add_lc && witness && !is_const(witness) && add_lc)
                    if (lc && !is_zero(lc) && m_am.eval_sign_at(lc, sample()) != 0)
                        witness = polynomial_ref(m_pm);
                add_projections_for(m_todo, p, m_n, witness, add_lc, true);
            }
        }

        std::vector<root_function_interval> single_cell_work() {
            if (m_n == 0)
                return m_I;

            m_todo.reset();

            // Initialize m_todo with distinct irreducible factors of the input polynomials.
            for (unsigned i = 0; i < m_P.size(); ++i) {
                polynomial_ref pi(m_P.get(i), m_pm);
                for_each_distinct_factor(pi, [&](polynomial_ref const& f) {
                    request(m_todo, f.get(), inv_req::sign);
                });
            }

            if (m_todo.empty())
                return m_I;

            // Process top level m_n (we project from x_{m_n} and do not return an interval for it).
            if (m_todo.max_var() == m_n) {
                extract_max_tagged();
                process_top_level();
            }

            // Now iteratively process remaining levels (descending).
            while (!m_todo.empty()) {
                extract_max_tagged();
                SASSERT(m_level < m_n);
                process_level();
            }

            return m_I;
        }

        std::vector<root_function_interval> single_cell() {
            try {
                return single_cell_work();
            }
            catch (nullified_poly_exception&) {
                m_fail = true;
                return m_I;
            }
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

    std::vector<levelwise::root_function_interval> levelwise::single_cell() {
        return m_impl->single_cell();
    }

    bool levelwise::failed() const { return m_impl->m_fail; }

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
