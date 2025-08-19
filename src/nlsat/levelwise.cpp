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
            unsigned         s_idx = 0; // index of the root function, if applicable
            unsigned         level = 0;
        };
        solver& m_solver;
        polynomial_ref_vector const& m_P;
        var                          m_n;
        pmanager&                    m_pm;
        anum_manager&                m_am;
        std::vector<property>        m_Q; // the set of properties to prove
        bool                         m_fail = false; 
        // Property precedence relation stored as pairs (lesser, greater)
        std::vector<std::pair<prop_enum, prop_enum>> m_p_relation;
        // Transitive closure matrix: dom[a][b] == true iff a ▹ b (a strictly dominates b).
        // Invert edges when populating dom: greater ▹ lesser.
        std::vector<std::vector<bool>> m_prop_dom;

        assignment const & sample() const { return m_solver.sample();}
        assignment & sample() { return m_solver.sample(); }

       // max_x plays the role of n in algorith 1 of the levelwise paper.
        impl(solver& solver, polynomial_ref_vector const& ps, var max_x, assignment const& s, pmanager& pm, anum_manager& am)
            : m_solver(solver), m_P(ps), m_n(max_x),  m_pm(pm), m_am(am) {
            TRACE(levelwise, tout  << "m_n:" << m_n << "\n";);    
            init_property_relation();
        }

#ifdef Z3DEBUG
        bool check_prop_init() {
            for (unsigned k = 0; k < prop_count(); ++k)
                if (m_prop_dom[k][k])
                    return false;
            return !dominates(prop_enum::ord_inv_irreducible, prop_enum::non_null);
        }
#endif
        
        void init_property_relation() {
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

        unsigned  max_var(poly* p) { return m_pm.max_var(p); }

        std::vector<property> seed_properties() {
            std::vector<property> Q;

            // Algorithm 1: initial goals are sgn_inv(p, s) for p in ps at current level of max_x
            for (unsigned i = 0; i < m_P.size(); ++i) {
                poly* p = m_P.get(i);                
                Q.push_back(property{ prop_enum::sgn_inv_irreducible, p, /*s_idx*/0, /* level */ m_n - 1});
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
            bool fail = false;
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

        // Internal carrier to keep root value paired with indexed root expr
        struct root_item_t {
            scoped_anum val;
            indexed_root_expr ire;
            root_item_t(anum_manager& am, poly* p, unsigned idx, anum const& v)
                : val(am), ire{ p, idx } { am.set(val, v); }
            root_item_t(root_item_t&& other) noexcept : val(other.val.m()), ire(other.ire) { val = other.val; }
            root_item_t(root_item_t const&) = delete;
            root_item_t& operator=(root_item_t const&) = delete;
        };

        bool dominates(const property& a, const property& b) const {
            return a.p == b.p && dominates(a.prop, b.prop);
        }
        bool dominates(prop_enum a, prop_enum b) const {
            return m_prop_dom[static_cast<unsigned>(a)][static_cast<unsigned>(b)];
        }
        
        // Pretty-print helpers
        static const char* prop_name(prop_enum p) {
            switch (p) {
            case prop_enum::ir_ord:               return "ir_ord";
            case prop_enum::an_del:               return "an_del";
            case prop_enum::non_null:             return "non_null";
            case prop_enum::ord_inv_reducible:    return "ord_inv_reducible";
            case prop_enum::ord_inv_irreducible:  return "ord_inv_irreducible";
            case prop_enum::sgn_inv_reducible:    return "sgn_inv_reducible";
            case prop_enum::sgn_inv_irreducible:  return "sgn_inv_irreducible";
            case prop_enum::connected:            return "connected";
            case prop_enum::an_sub:               return "an_sub";
            case prop_enum::sample:               return "sample";
            case prop_enum::repr:                 return "repr";
            case prop_enum::holds:                return "holds";
            case prop_enum::_count:               return "_count";
            }
            return "?";
        }

        std::ostream& display(std::ostream& out, const property & pr) {
            out << "{prop:" << prop_name(pr.prop)
                << ", level:" << pr.level
                << ", s_idx:" << pr.s_idx;
            if (pr.p) {
                out << ", p:";
                ::nlsat::display(out, m_solver, polynomial_ref(pr.p, m_pm));
            }
            else {
                out << ", p:null";
            }
            out << "}";
            return out;
        }
        
        std::vector<property> greatest_to_refine(unsigned level, prop_enum prop_to_avoid) {
            // Collect candidates on current level, excluding sgn_inv_irreducible
            std::vector<property> cand;
            cand.reserve(m_Q.size());
            for (const auto& q : m_Q)
                if (q.level == level && q.prop != prop_to_avoid)
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

        // Step 1a: collect E and root values
        void collect_E_and_roots(std::vector<const poly*> const& P_non_null,
                                 unsigned i,
                                 std::vector<indexed_root_expr>& E,
                                 std::vector<root_item_t>& roots_out) {
            var y = i;
            for (auto const* p0 : P_non_null) {
                auto* p = const_cast<poly*>(p0);
                if (m_pm.max_var(p) != y)
                    continue;
                scoped_anum_vector roots(m_am);
                m_am.isolate_roots(polynomial_ref(p, m_pm), undef_var_assignment(sample(), y), roots);

                unsigned num_roots = roots.size();
                TRACE(levelwise,
                      tout << "roots (" << num_roots << "):";
                      for (unsigned kk = 0; kk < num_roots; ++kk) {
                          tout << " "; m_am.display(tout, roots[kk]);
                      }
                      tout << std::endl;
                );
                for (unsigned k = 0; k < num_roots; ++k) {
                    E.push_back(indexed_root_expr{ p, k + 1 });
                    roots_out.emplace_back(m_am, p, k + 1, roots[k]);
                }
            }
        }

        // Find an existing bucket that has the same algebraic value; returns nullptr if none found
        bucket_t* find_bucket_by_value(anum const& v,
                                       std::vector<std::unique_ptr<bucket_t>>& buckets) {
            for (auto& b : buckets)
                if (m_am.compare(v, b->val) == 0)
                    return b.get();
            return nullptr;
        }

        // Append a root to a given bucket (does not change the bucket's value)
        void add_root_to_bucket(bucket_t& bucket, root_item_t const& r) {
            bucket.members.push_back(r.ire);
        }

        // Step 1b: bucketize roots by equality of values
        void add_root_to_buckets(root_item_t const& r,
                                 std::vector<std::unique_ptr<bucket_t>>& buckets) {
            if (auto* b = find_bucket_by_value(r.val, buckets)) {
                add_root_to_bucket(*b, r);
                return;
            }
            auto nb = std::make_unique<bucket_t>(m_am);
            m_am.set(nb->val, r.val);
            add_root_to_bucket(*nb, r);
            buckets.push_back(std::move(nb));
        }

        void bucketize_roots(std::vector<root_item_t> const& roots,
                             std::vector<std::unique_ptr<bucket_t>>& buckets) {
            for (auto const& r : roots)
                add_root_to_buckets(r, buckets);
        }

        // Step 2a: sort buckets and form omega_buckets
        void build_omega_buckets(std::vector<std::unique_ptr<bucket_t>>& buckets,
                                 std::vector<std::vector<indexed_root_expr>>& omega_buckets) {
            std::sort(buckets.begin(), buckets.end(), [&](std::unique_ptr<bucket_t> const& a, std::unique_ptr<bucket_t> const& b){
                return m_am.lt(a->val, b->val);
            });
            omega_buckets.clear();
            omega_buckets.reserve(buckets.size());
            for (auto& b : buckets)
                omega_buckets.push_back(b->members);
        }

        // Helper: set I as a section if sample matches a bucket value; returns true if set
        bool initialize_section_from_bucket(unsigned i,
                                      std::vector<std::unique_ptr<bucket_t>>& buckets,
                                      symbolic_interval& I) {
            var y = i;
            if (!sample().is_assigned(y))
                return false;
            anum const& y_val = sample().value(y);
            for (auto const& b : buckets) {
                if (m_am.compare(y_val, b->val) == 0) {
                    I.section = true;
                    auto const& ire = b->members.front();
                    I.l = ire.p;
                    I.l_index = ire.i;
                    I.u = nullptr; I.u_index = 0;
                    return true;
                }
            }
            return false;
        }

        // Helper: set sector bounds from neighboring buckets; assumes buckets sorted; no-op if sample unassigned
        void set_sector_bounds_from_buckets(unsigned i,
                                            std::vector<std::unique_ptr<bucket_t>>& buckets,
                                            symbolic_interval& I) {
            var y = i;
            if (!sample().is_assigned(y))
                return;
            anum const& y_val = sample().value(y);
            bucket_t* lower_b = nullptr;
            bucket_t* upper_b = nullptr;
            for (auto& b : buckets) {
                int cmp = m_am.compare(y_val, b->val);
                if (cmp > 0) lower_b = b.get();
                else if (cmp < 0) { upper_b = b.get(); break; }
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

        // Step 2b: compute interval I from (sorted) buckets and current sample
        void compute_interval_from_buckets(unsigned i,
                                           std::vector<std::unique_ptr<bucket_t>>& buckets,
                                           symbolic_interval& I) {
            // default: whole line sector (-inf, +inf)
            I.section = false;
            I.l = nullptr; I.u = nullptr; I.l_index = 0; I.u_index = 0;

            if (initialize_section_from_bucket(i, buckets, I))
                return;
            set_sector_bounds_from_buckets(i, buckets, I);
        }
            
        // Part A of construct_interval: apply pre-conditions (line 8-11 scaffolding)
        bool apply_property_rules(unsigned i, prop_enum prop_to_avoid) {
            std::vector<property> to_refine = greatest_to_refine(i, prop_to_avoid);
            for (const auto& p: to_refine)
                apply_pre(p);
            return !m_fail;
        }

        // Part B of construct_interval: build (I, E, ≼) representation for level i
        void build_representation(unsigned i, result_struct& ret) {
            std::vector<const poly*> p_non_null;
            for (const auto & pr: m_Q) {
                if (pr.prop == prop_enum::sgn_inv_irreducible && m_pm.max_var(pr.p) == i && poly_is_not_nullified_at_sample_at_level(pr.p, i))
                    p_non_null.push_back(pr.p);
            }
            std::vector<std::unique_ptr<bucket_t>> buckets;
            std::vector<root_item_t> roots;
            collect_E_and_roots(p_non_null, i, ret.E, roots);
            bucketize_roots(roots, buckets);
            build_omega_buckets(buckets, ret.omega_buckets);
            compute_interval_from_buckets(i, buckets, ret.I);
        }

        void remove_level_i_from_Q(std::vector<property> & Q, unsigned i) {
            Q.erase(std::remove_if(Q.begin(), Q.end(),
                                   [i](const property &p) { return p.level == i; }),
            Q.end());
        }

        result_struct construct_interval(unsigned i) {
            result_struct ret;
            if (!apply_property_rules(i, prop_enum::sgn_inv_irreducible)) {
                ret.fail = true;
                return ret;
            }

            build_representation(i, ret);
            apply_property_rules(i, prop_enum(prop_enum::holds));
            ret.Q = m_Q;
            ret.fail = m_fail;
            remove_level_i_from_Q(ret.Q, i);
            return ret;
        }

        void apply_pre(const property& p) {
            TRACE(levelwise, display(tout << "p:", p) << std::endl;);
            NOT_IMPLEMENTED_YET();
        }
        // return an empty vector on failure, otherwis returns the cell representations with intervals
        std::vector<symbolic_interval> single_cell() {
            TRACE(levelwise,
                  m_solver.display_assignment(tout << "sample()") << std::endl;
                  tout << "m_P:\n";
                  for (const auto & p: m_P) {
                      ::nlsat::display(tout, m_solver, polynomial_ref(p, m_pm)) << std::endl;
                      tout << "max0_var:" << m_pm.max_var(p) << std::endl;
                  }
                );
            std::vector<symbolic_interval> ret;
            m_Q = seed_properties(); // Q is the set of properties on level m_n
            for (unsigned i = m_n; --i > 0; ) {
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
