#include "nlsat/levelwise.h"
#include "nlsat/nlsat_types.h"
#include <vector>
namespace nlsat {

// Local enums reused from previous scaffolding
enum class property_mapping_case : unsigned { case1 = 0, case2 = 1, case3 = 2 };

enum class polynom_property : unsigned {
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
  polynom_property prop;
  poly*            p = nullptr;
  unsigned         s_idx = 0; // index into current sample roots on level, if applicable
  unsigned         level = 0;
};
struct levelwise::impl {
  polynomial_ref_vector const& m_ps;
  var                          m_max_x;
  assignment const&            m_sample;
  std::vector<property_goal>   m_goals;

  impl(polynomial_ref_vector const& ps, var max_x, assignment const& s)
    : m_ps(ps), m_max_x(max_x), m_sample(s) {
    seed_initial_goals();
  }
  void seed_initial_goals() {
    // Algorithm 1: initial goals are sgn_inv(p, s) for p in ps at current level of max_x
    for (unsigned i = 0; i < m_ps.size(); ++i) {
      poly* p = m_ps.get(i);
      m_goals.push_back(property_goal{ polynom_property::sgn_inv_irreducible /*or reducible later*/, p, /*s_idx*/0, /*level*/0});
    }
  }
};

levelwise::levelwise(polynomial_ref_vector const& ps, var max_x, assignment const& s)
  : m_impl(new impl(ps, max_x, s)) {}

levelwise::~levelwise() { delete m_impl; }
levelwise::levelwise(levelwise&& o) noexcept : m_impl(o.m_impl) { o.m_impl = nullptr; }

levelwise& levelwise::operator=(levelwise&& o) noexcept { if (this != &o) { delete m_impl; m_impl = o.m_impl; o.m_impl = nullptr; } return *this; }

// Free-function driver: create a local implementation and seed initial goals.
void levelwise_project(polynomial_ref_vector const& ps, var max_x, assignment const& s) {
  struct impl {
    polynomial_ref_vector const& m_ps;
    var                          m_max_x;
    assignment const&            m_sample;
    std::vector<property_goal>   m_goals;
    impl(polynomial_ref_vector const& ps_, var mx, assignment const& sa)
      : m_ps(ps_), m_max_x(mx), m_sample(sa) {
      seed_initial_goals();
    }
    void seed_initial_goals() {
      for (unsigned i = 0; i < m_ps.size(); ++i) {
        poly* p = m_ps.get(i);
        m_goals.push_back(property_goal{ polynom_property::sgn_inv_irreducible, p, /*s_idx*/0, /*level*/0 });
      }
    }
    void run() {
      // TODO: apply Levelwise rules to discharge goals and build a proof.
    }
  } I(ps, max_x, s);
  I.run();
}

} // namespace nlsat
