#include "nlsat/levelwise.h"
#include "nlsat/nlsat_types.h"
#include "nlsat/nlsat_assignment.h"
#include <vector>
#include <unordered_map>
#include <map>
#include <algorithm>
#include <memory>
#include "math/polynomial/algebraic_numbers.h"
#include "nlsat_common.h"
namespace nlsat {

// Local enums reused from previous scaffolding
    enum class property_mapping_case : unsigned { case1 = 0, case2 = 1, case3 = 2 };    
    
    enum class prop_enum : unsigned {
        ir_ord,
        an_del,
        non_null,
        ord_inv_reducible,
        ord_inv_irreducible,
        sgn_inv_reducible,
        sgn_inv_irreducible,
        connected,
        an_sub,
        sample,
        repr,
        holds,
        _count 
    };

    unsigned prop_count() { return static_cast<unsigned>(prop_enum::_count);}
    // no score-based ordering; precedence is defined by m_p_relation only
    
    struct levelwise::impl {
        struct property {
            prop_enum prop;
            poly*            p = nullptr;
            unsigned         s_idx = 0; // index into current sample roots on level, if applicable
            unsigned         level = 0;
        };
        solver& m_solver;
        polynomial_ref_vector const& m_P;
        var                          m_n;
        pmanager&                    m_pm;
        anum_manager&                m_am;
        std::vector<property>        m_Q; // the set of properties to prove as in single_cell
        bool                         m_fail = false;
        // Property precedence relation stored as pairs (lesser, greater)
        std::vector<std::pair<prop_enum, prop_enum>> m_p_relation;
        // Transitive closure matrix: dom[a][b] == true iff a ▹ b (a strictly dominates b).
        // Since m_p_relation holds (lesser -> greater), we invert edges when populating dom: greater ▹ lesser.
        std::vector<std::vector<bool>> m_prop_dom;

        assignment const&            sample() const { return m_solver.sample();}
        assignment & sample() { return m_solver.sample(); }

// max_x plays the role of n in algorith 1 of the levelwise paper.
        impl(solver& solver, polynomial_ref_vector const& ps, var max_x, assignment const& s, pmanager& pm, anum_manager& am)
            : m_solver(solver), m_P(ps), m_n(max_x),  m_pm(pm), m_am(am) {
            TRACE(levelwise, tout  << "m_n:" << m_n << "\n";);    
            init_relation();
        }

#ifdef Z3DEBUG
        bool check_prop_init() {
            for (unsigned k = 0; k < prop_count(); ++k)
                if (m_prop_dom[k][k])
                    return false;
            return !dominates(prop_enum::ord_inv_irreducible, prop_enum::non_null);
        }
#endif
        
        void init_relation() {
            m_p_relation.clear();
            auto add = [&](prop_enum lesser, prop_enum greater) { m_p_relation.emplace_back(lesser, greater); };
            // m_p_relation stores edges (lesser -> greater). 
            // The edges below follow Figure 8. Examples include: an_del -> ir_ord, sample -> ir_ord.
            add(prop_enum::holds,   prop_enum::repr);
            add(prop_enum::repr,    prop_enum::sample);
            add(prop_enum::sample,  prop_enum::an_sub);
            add(prop_enum::an_sub,  prop_enum::connected);
            // connected < sgn_inv_*
            add(prop_enum::connected, prop_enum::sgn_inv_reducible);
            add(prop_enum::connected, prop_enum::sgn_inv_irreducible);
            // sgn_inv_* < ord_inv_* (same reducibility)
            add(prop_enum::sgn_inv_reducible,   prop_enum::ord_inv_reducible);
            add(prop_enum::sgn_inv_irreducible, prop_enum::ord_inv_irreducible);
            // ord_inv_* < non_null

            add(prop_enum::ord_inv_reducible,   prop_enum::non_null);
            add(prop_enum::ord_inv_irreducible, prop_enum::non_null);
            // non_null < an_del
            add(prop_enum::non_null, prop_enum::an_del);
            // an_del < ir_ord
            add(prop_enum::an_del,    prop_enum::ir_ord);
            // Additional explicit edge from Fig 8
            add(prop_enum::sample,    prop_enum::ir_ord);

            // Build transitive closure matrix for quick comparisons
            unsigned N = prop_count();
            m_prop_dom.assign(N, std::vector<bool>(N, false));
            for (auto const& pr : m_p_relation) {
                unsigned lesser  = static_cast<unsigned>(pr.first);
                unsigned greater = static_cast<unsigned>(pr.second);
                // Build dominance relation as: greater ▹ lesser
                m_prop_dom[greater][lesser] = true;
            }
            // Floyd-Warshall style closure on a tiny fixed-size set
            for (unsigned k = 0; k < N; ++k)
                for (unsigned i = 0; i < N; ++i)
                    if (m_prop_dom[i][k])
                        for (unsigned j = 0; j < N; ++j)
                            if (m_prop_dom[k][j])
                                m_prop_dom[i][j] = true;

#ifdef Z3DEBUG
            SASSERT(check_prop_init());
#endif            
        }

        unsigned  max_var(poly* p) {
            return m_pm.max_var(p);
        }

        std::vector<property> seed_properties() {
            std::vector<property> Q;

            // Algorithm 1: initial goals are sgn_inv(p, s) for p in ps at current level of max_x
            for (unsigned i = 0; i < m_P.size(); ++i) {
                poly* p = m_P.get(i);
                TRACE(levelwise, display(tout << "p:", m_solver, polynomial_ref(p, m_pm)) << std::endl;
                      tout << "max_var:" << m_pm.max_var(p) << std::endl;
                      m_solver.display_assignment(tout << "sample()") << std::endl;);
                Q.push_back(property{ prop_enum::sgn_inv_irreducible, p, /*s_idx*/0, /* level */ max_var(p)});
            }
            return Q;
        }
        struct result_struct {
            symbolic_interval I;
            // Set E of indexed root expressions at level i for P_non_null: the root functions from E pass throug s[i]
            std::vector<indexed_root_expr> E;
            // Initial ordering buckets for omega: each bucket groups equal-valued roots
            std::vector<std::vector<indexed_root_expr>> omega_buckets;
            std::vector<property> Q;
            bool fail;
        };

        // Bucket of equal-valued roots used for initial omega ordering
        struct bucket_t {
            scoped_anum val;
            std::vector<indexed_root_expr> members;
            bucket_t(anum_manager& am): val(am) {}
            bucket_t(bucket_t&& other) noexcept : val(other.val.m()), members(std::move(other.members)) { val = other.val; }
            bucket_t(bucket_t const&) = delete;
            bucket_t& operator=(bucket_t const&) = delete;
        };

        bool dominates(const property& a, const property& b) const {
            return a.p == b.p && dominates(a.prop, b.prop);
        }
        bool dominates(prop_enum a, prop_enum b) const {
            return m_prop_dom[static_cast<unsigned>(a)][static_cast<unsigned>(b)];
        }
        
        std::vector<property> greatest_to_refine(unsigned level) {
            // Collect candidates on current level, excluding sgn_inv_irreducible
            std::vector<property> cand;
            cand.reserve(m_Q.size());
            for (const auto& q : m_Q)
                if (q.level == level && q.prop != prop_enum::sgn_inv_irreducible)
                    cand.push_back(q);
            if (cand.empty()) return {};

            // Determine maxima w.r.t. ▹ using the transitive closure matrix
            // Dominance requires the same polynomial in both compared properties
            std::vector<bool> dominated(cand.size(), false);
            for (size_t i = 0; i < cand.size(); ++i) {
                for (size_t j = 0; j < cand.size(); ++j) {
                    if (i != j && dominates(cand[j], cand[i])) {
                        dominated[i] = true;
                        break;
                    }
                }
            }

            // Extract non-dominated (greatest) candidates; keep deterministic order by (poly id, prop enum)
            struct Key { unsigned pid; unsigned pprop; size_t idx; };
            std::vector<Key> keys;
            keys.reserve(cand.size());
            for (size_t i = 0; i < cand.size(); ++i) {
                if (!dominated[i]) {
                    keys.push_back(Key{ polynomial::manager::id(cand[i].p), static_cast<unsigned>(cand[i].prop), i });
                }
            }
            std::sort(keys.begin(), keys.end(), [](Key const& a, Key const& b){
                if (a.pid != b.pid) return a.pid < b.pid;
                return a.pprop < b.pprop;
            });
            std::vector<property> ret;
            ret.reserve(keys.size());
            for (auto const& k : keys) ret.push_back(cand[k.idx]);
            return ret;
        }
        // check that at least one coeeficient of p \in Q[x0,..., x_{i-1}](x) does not evaluate to zere at the sample. 
        bool poly_is_not_nullified_at_sample_at_level(poly* p, unsigned i) {
            // iterate coefficients of p with respect to the current level variable m_i
            unsigned deg = m_pm.degree(p, i);
            polynomial_ref c(m_pm);
            for (unsigned j = 0; j <= deg; ++j) {
                c = m_pm.coeff(p, i, j);
                if (sign(c, sample(), m_am) != 0)
                    return true;
            }
            return false;
        }

        // Step 1: collect E and build equality buckets of roots for initial omega ordering
        void collect_E_and_buckets(std::vector<const poly*> const& P_non_null,
                                   unsigned i,
                                   std::vector<indexed_root_expr>& E,
                                   std::vector<std::unique_ptr<bucket_t>>& buckets) {
            var y = i;
            for (auto const* p0 : P_non_null) {
                auto* p = const_cast<poly*>(p0);
                if (m_pm.max_var(p) != y)
                    continue;
                scoped_anum_vector roots(m_am);
                m_am.isolate_roots(polynomial_ref(p, m_pm), undef_var_assignment(sample(), y), roots);
                unsigned num_roots = roots.size();
                for (unsigned k = 0; k < num_roots; ++k) {
                    E.push_back(indexed_root_expr{ p, k + 1 });
                    bool placed = false;
                    for (auto& b : buckets) {
                        if (m_am.compare(roots[k], b->val) == 0) {
                            b->members.push_back(indexed_root_expr{ p, k + 1 });
                            placed = true;
                            break;
                        }
                    }
                    if (!placed) {
                        auto nb = std::make_unique<bucket_t>(m_am);
                        nb->members.push_back(indexed_root_expr{ p, k + 1 });
                        m_am.set(nb->val, roots[k]);
                        buckets.push_back(std::move(nb));
                    }
                }
            }
        }

        // Step 2: finalize representation (I and omega buckets) from collected buckets
        void finalize_representation_from_buckets(unsigned i,
                                                  std::vector<std::unique_ptr<bucket_t>>& buckets,
                                                  symbolic_interval& I,
                                                  std::vector<std::vector<indexed_root_expr>>& omega_buckets) {
            var y = i;
            // default: whole line sector (-inf, +inf)
            I.section = false;
            I.l = nullptr; I.u = nullptr; I.l_index = 0; I.u_index = 0;

            // Sort buckets by numeric value and form omega_buckets
            std::sort(buckets.begin(), buckets.end(), [&](std::unique_ptr<bucket_t> const& a, std::unique_ptr<bucket_t> const& b){
                return m_am.lt(a->val, b->val);
            });
            omega_buckets.clear();
            omega_buckets.reserve(buckets.size());
            for (auto& b : buckets)
                omega_buckets.push_back(b->members);

            if (!sample().is_assigned(y))
                return;

            anum const& y_val = sample().value(y);
            // Check for section first
            for (auto const& b : buckets) {
                if (m_am.compare(y_val, b->val) == 0) {
                    I.section = true;
                    // pick a representative indexed root expression from the bucket
                    auto const& ire = b->members.front();
                    I.l = ire.p;
                    I.l_index = ire.i;
                    I.u = nullptr; I.u_index = 0;
                    return;
                }
            }
            // Otherwise compute nearest lower/upper buckets
            bucket_t* lower_b = nullptr;
            bucket_t* upper_b = nullptr;
            for (auto& b : buckets) {
                int cmp = m_am.compare(y_val, b->val);
                if (cmp > 0) {
                    lower_b = b.get();
                }
                else if (cmp < 0) {
                    upper_b = b.get();
                    break;
                }
            }
            if (lower_b) {
                auto const& ire = lower_b->members.front();
                I.l = ire.p;
                I.l_index = ire.i;
            }
            if (upper_b) {
                auto const& ire = upper_b->members.front();
                I.u = ire.p;
                I.u_index = ire.i;
            }
        }
            
        result_struct construct_interval(unsigned i) {
            result_struct ret;

            std::vector<property> to_refine = greatest_to_refine(i);
            for (const auto& p: to_refine) {
                apply_pre(p);
            }
            if (m_fail) {
                ret.fail = true;
                return ret;
            }

            /*
              P_{nonnull} := {p | sgn_inv(p) ∈ Q |i s.t. p(s[i−1], xi ) ̸= 0}
              6 E:= irExpr(P_{nonnull} , s[i−1])
              7 choose representation (I, E, ≼) of with respect to s
              8 if i > 1 then
              9 foreach q ∈ Q |i where q is the greatest element with respect to ▹ (from Definition 4.5) and q ̸= holds(I) do
              10 Q := apply_pre(i, Q ,q,(s, I, ≼)) 
              11 if Q == FAIL return FAIL
            */
     
            
            std::vector<const poly*> p_non_null;
            for (const auto & pr: m_Q) {
                if (pr.prop == prop_enum::sgn_inv_irreducible && m_pm.max_var(pr.p) == i && poly_is_not_nullified_at_sample_at_level(pr.p, i))
                    p_non_null.push_back(pr.p);
            }
            // Line 7: choose representation (I, E, ≼) with respect to s.
            std::vector<std::unique_ptr<bucket_t>> buckets;
            collect_E_and_buckets(p_non_null, i, ret.E, buckets);
            finalize_representation_from_buckets(i, buckets, ret.I, ret.omega_buckets);
            return ret;
        }
        // overload exists in explain; keep local poly*-based API only for now
        void apply_pre(const property& p) {
            NOT_IMPLEMENTED_YET();
        }
        // return an empty vector on failure
        std::vector<symbolic_interval> single_cell() {
            std::vector<symbolic_interval> ret;

            m_Q = seed_properties(); // Q is the set of properties on level m_n
            for (unsigned i = m_n; i > 0; --i) {
                auto result = construct_interval(i);
                if (result.fail)
                    return std::vector<symbolic_interval>(); // return empty
                ret.push_back(result.I);
                m_Q = result.Q;
            }

            return ret; // the order is reversed!
        }
    };
// constructor
    levelwise::levelwise(nlsat::solver& solver, polynomial_ref_vector const& ps, var n, assignment const& s, pmanager& pm, anum_manager& am)
        : m_impl(new impl(solver, ps, n, s, pm, am)) {}

    levelwise::~levelwise() { delete m_impl; }

    std::vector<levelwise::symbolic_interval> levelwise::single_cell() {
        return m_impl->single_cell();
    }

} // namespace nlsat
