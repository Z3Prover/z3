#include "nlsat/levelwise.h"
#include "nlsat/nlsat_types.h"
#include <vector>
#include <unordered_map>
#include <map>
namespace nlsat {

// Local enums reused from previous scaffolding
    enum class property_mapping_case : unsigned { case1 = 0, case2 = 1, case3 = 2 };    
    
    enum class prop_enum : unsigned {
        ir_ord,
        an_del,
        non_null,
        sgn_inv_reducible,
        sgn_inv_irreducible,
        connected,
        an_sub,
        sample,
        repr,
        holds,
        _count 
    };

    static unsigned score(prop_enum pe) {
        return static_cast<unsigned>(prop_enum::_count) - static_cast<unsigned>(pe);
    }
    
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
        // max_x plays the role of n in algorith 1 of the levelwise paper.
        impl(polynomial_ref_vector const& ps, var max_x, assignment const& s)
            : m_P(ps), m_n(max_x), m_s(s) {
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
        

        
        std::vector<property> greatest_to_refine() {
            // Deterministic order: use ascending polynomial id as key
            std::map<unsigned, property> best_by_poly;
            for (const auto& q : m_Q) {
                if (q.level != m_i)
                    continue;
                if (q.prop == prop_enum::sgn_inv_irreducible)
                    continue;
                unsigned pid = polynomial::manager::id(q.p);
                auto it = best_by_poly.find(pid);
                if (it == best_by_poly.end() || score(q.prop) > score(it->second.prop))
                    best_by_poly[pid] = q;
            }
            std::vector<property> ret;
            ret.reserve(best_by_poly.size());
            for (auto const& kv : best_by_poly)
                ret.push_back(kv.second);
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
           for (const auto & q : this->m_Q) {
               if (false)
                   ;
           }
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
