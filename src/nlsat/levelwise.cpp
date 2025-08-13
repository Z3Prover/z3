#include "nlsat/levelwise.h"
#include "nlsat/nlsat_types.h"
#include <vector>
#include <unordered_map>
namespace nlsat {

// Local enums reused from previous scaffolding
    enum class property_mapping_case : unsigned { case1 = 0, case2 = 1, case3 = 2 };

    enum class prop : unsigned {
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
    struct property_goal {
        prop prop;
        poly*            p = nullptr;
        unsigned         s_idx = 0; // index into current sample roots on level, if applicable
        unsigned         level = 0;
    };
    struct levelwise::impl {
        polynomial_ref_vector const& m_P;
        var                          m_max_x;
        assignment const&            m_s;
        std::vector<property_goal>   m_Q; // the set of properties to prove as in single_cell

        // max_x plays the role of n in algorith 1 of the levelwise paper.
        impl(polynomial_ref_vector const& ps, var max_x, assignment const& s)
            : m_P(ps), m_max_x(max_x), m_s(s) {
            seed_initial_goals();
        }
        void seed_initial_goals() {
            // Algorithm 1: initial goals are sgn_inv(p, s) for p in ps at current level of max_x
            for (unsigned i = 0; i < m_P.size(); ++i) {
                poly* p = m_P.get(i);
                m_Q.push_back(property_goal{ prop::sgn_inv_irreducible, p, /*s_idx*/0, /* level */ m_max_x});
            }
        }
    };

    levelwise::levelwise(polynomial_ref_vector const& ps, var n, assignment const& s)
        : m_impl(new impl(ps, n, s)) {}

    levelwise::~levelwise() { delete m_impl; }
    levelwise::levelwise(levelwise&& o) noexcept : m_impl(o.m_impl) { o.m_impl = nullptr; }

    levelwise& levelwise::operator=(levelwise&& o) noexcept { if (this != &o) { delete m_impl; m_impl = o.m_impl; o.m_impl = nullptr; } return *this; }

// Free-function driver: create a local implementation and seed initial goals.
    polynomial_ref_vector levelwise_project(polynomial_ref_vector & ps, var max_x, assignment const& s) {
        struct impl {
            polynomial_ref_vector const& m_P;
            var                          m_max_x;
            assignment const&            m_sample;
            std::vector<property_goal>   m_goals;
            // simple fact DB
            struct key {
                prop      pr;
                poly*     p;
                unsigned  s_idx;
                unsigned  level;
                bool operator==(key const& o) const noexcept {
                    return pr == o.pr && p == o.p && s_idx == o.s_idx && level == o.level;
                }
            };
            struct key_hash {
                size_t operator()(key const& k) const noexcept {
                    size_t h = static_cast<size_t>(k.pr);
                    h ^= (reinterpret_cast<size_t>(k.p) >> 3) + 0x9e3779b97f4a7c15ULL + (h<<6) + (h>>2);
                    h ^= static_cast<size_t>(k.s_idx) + 0x9e3779b9 + (h<<6) + (h>>2);
                    h ^= static_cast<size_t>(k.level) + 0x9e3779b9 + (h<<6) + (h>>2);
                    return h;
                }
            };
            std::unordered_map<key, unsigned, key_hash>  m_index; // key -> fact id
            std::vector<property_goal>                   m_facts; // id -> fact
            std::vector<unsigned>                        m_worklist;
            impl(polynomial_ref_vector const& ps_, var mx, assignment const& sa)
                : m_P(ps_), m_max_x(mx), m_sample(sa) {
                seed_initial_goals();
            }
            void seed_initial_goals() {
                for (unsigned i = 0; i < m_P.size(); ++i) {
                    poly* p = m_P.get(i);
                    m_goals.push_back(property_goal{ prop::sgn_inv_irreducible, p, /*s_idx*/0, /*level*/0 });
                }
            }
            unsigned intern(property_goal const& g) {
                key k{ g.prop, g.p, g.s_idx, g.level };
                auto it = m_index.find(k);
                if (it != m_index.end())
                    return it->second;
                unsigned id = static_cast<unsigned>(m_facts.size());
                m_index.emplace(k, id);
                m_facts.push_back(g);
                m_worklist.push_back(id);
                return id;
            }
            bool pop(unsigned& id) {
                if (m_worklist.empty())
                    return false;
                id = m_worklist.back();
                m_worklist.pop_back();
                return true;
            }
            void derive_from(property_goal const& f) {
                // Minimal rule: sgn_inv_irreducible(p) => non_null(p) and ir_ord(p)
                if (f.prop == prop::sgn_inv_irreducible) {
                    intern(property_goal{ prop::non_null, f.p, f.s_idx, f.level });
                    intern(property_goal{ prop::ir_ord,   f.p, f.s_idx, f.level });
                }
            }
            // Construct an interval at level n = m_max_x around the current sample s per the levelwise paper.
            void construct_interval() {
                // TODO: Implement per Algorithm "construct_interval" in the paper:
                // 1) Collect polynomials of level n (max_x) from m_P.
                // 2) Compute relevant roots under current sample m_sample.
                // 3) Build an interval I delimited by adjacent roots around s.
                // 4) Select a representative sample within I.
                // 5) Record properties (repr(I,s), sample(s), etc.) as needed.
                // This is a placeholder skeleton; no-op for now.
                (void)m_P; (void)m_max_x; (void)m_sample;
            }
            void single_cell() {
                construct_interval();
            }
        }; // end of impl structure

        impl m_impl(ps, max_x, s);
        m_impl.single_cell();
        return ps;
    }

} // namespace nlsat
