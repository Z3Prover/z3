#include "nlsat/levelwise.h"
#include "nlsat/nlsat_types.h"
#include <vector>
#include <unordered_map>
#include <map>
#include <algorithm>
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
    
    struct property {
        prop_enum prop;
        poly*            p = nullptr;
        unsigned         s_idx = 0; // index into current sample roots on level, if applicable
        unsigned         level = 0;
    };
    struct levelwise::impl {
        polynomial_ref_vector const& m_P;
        var                          m_n;
        assignment const&            m_s;
        std::vector<property>        m_Q; // the set of properties to prove as in single_cell
        bool                         m_fail = false;
        unsigned                     m_i; // current level
        // Property precedence relation stored as pairs (lesser, greater)
        std::vector<std::pair<prop_enum, prop_enum>> m_p_relation;
        // Transitive closure matrix: dom[a][b] == true iff a ▹ b (a strictly dominates b).
        // Since m_p_relation holds (lesser -> greater), we invert edges when populating dom: greater ▹ lesser.
        std::vector<std::vector<bool>> m_prop_dom;
        // max_x plays the role of n in algorith 1 of the levelwise paper.
        impl(polynomial_ref_vector const& ps, var max_x, assignment const& s)
            : m_P(ps), m_n(max_x), m_s(s) {
            init_relation();
        }

        #ifdef Z3DEBUG
        
        bool check_prop_init() {
            std::cout << "checked\n";
            for (unsigned k = 0; k < prop_count(); ++k)
                if (m_prop_dom[k][k])
                    return false;
            return !dominates(prop_enum::ord_inv_irreducible, prop_enum::non_null);
        }
        #endif
        
        void init_relation() {
            m_p_relation.clear();
            auto add = [&](prop_enum lesser, prop_enum greater) { m_p_relation.emplace_back(lesser, greater); };
            // m_p_relation stores edges (lesser -> greater). We later invert these to build dom (greater ▹ lesser).
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


            SASSERT(check_prop_init());            
        }
        std::vector<property> seed_properties() {
            std::vector<property> Q;
            // Algorithm 1: initial goals are sgn_inv(p, s) for p in ps at current level of max_x
            for (unsigned i = 0; i < m_P.size(); ++i) {
                poly* p = m_P.get(i);
                Q.push_back(property{ prop_enum::sgn_inv_irreducible, p, /*s_idx*/0, /* level */ m_n});
            }
            return Q;
        }
        struct result_struct {
            symbolic_interval I;
            std::vector<property> Q;
            bool status;
        };
        
        bool dominates(prop_enum a, prop_enum b) {
            return m_prop_dom[static_cast<unsigned>(a)][static_cast<unsigned>(b)];
        }

        
        std::vector<property> greatest_to_refine() {
            // Collect candidates on current level, excluding sgn_inv_irreducible
            std::vector<property> cand;
            cand.reserve(m_Q.size());
            for (const auto& q : m_Q)
                if (q.level == m_i && q.prop != prop_enum::sgn_inv_irreducible)
                    cand.push_back(q);
            if (cand.empty()) return {};

            // Determine maxima w.r.t. ▹ using the transitive closure matrix

            std::vector<bool> dominated(cand.size(), false);
            for (size_t i = 0; i < cand.size(); ++i) {
                for (size_t j = 0; j < cand.size(); ++j) {
                    if (i != j && dominates(cand[j].prop, cand[i].prop)) {
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

        result_struct construct_interval() {
            result_struct ret;
/*foreach q ∈ Q |i where q is the greatest element with respect to ▹ (from Definition 4.5) and q ̸= sgn_inv(p) for an irreducible p
  do
  2 Q := apply_pre(i, Q ,q,(s)) // Algorithm 3
  3 if Q= FAIL then
  4 return FAIL
*/        
            std::vector<property> to_refine = greatest_to_refine();
            // refine using to_refine (TBD)
            return ret;
        }
        // return an empty vector on failure
        std::vector<symbolic_interval> single_cell() {
            std::vector<symbolic_interval> ret;
            m_Q = seed_properties(); // Q is the set of properties on level m_n
            for (unsigned i = m_n; i >= 1; i--) {
                auto result = construct_interval();
                if (result.status == false)
                    return std::vector<symbolic_interval>(); // return empty
                ret.push_back(result.I);
                m_Q = result.Q;
            }
     
            return ret; // the order is reversed!
        }
    };
// constructor
    levelwise::levelwise(polynomial_ref_vector const& ps, var n, assignment const& s)
        : m_impl(new impl(ps, n, s)) {}

    levelwise::~levelwise() { delete m_impl; }

    std::vector<levelwise::symbolic_interval> levelwise::single_cell() {
        return m_impl->single_cell();
    }

} // namespace nlsat
