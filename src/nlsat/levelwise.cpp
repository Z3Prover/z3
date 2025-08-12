#include "levelwise.h"
#include <vector>
#include <string>
#include <sstream>

namespace nlsat {

  // Context for property propagation (e.g., which case of rule 4.2 applies)
  enum class property_mapping_case : unsigned {
    case1 = 0,
    case2 = 1,
    case3 = 2,
  };

  /**
   * Properties for indexed roots, in the order specified by the levelwise paper.
   * The order is important for the algorithm and must match the paper exactly.
   */
  enum class polynom_property : unsigned {
    ir_ord,              // ir_ord(≼, s) for all ≼ for roots of level i and s ∈ Ri−1
    an_del,              // an_del(p) for all p of level i
    non_null,            // non_null(p) for all p of level i
    ord_inv_reducible,   // ord_inv(p) for all reducible p of level i
    ord_inv_irreducible, // ord_inv(p) for all irreducible p of level i
    sgn_inv_reducible,   // sgn_inv(p) for all reducible p of level i
    sgn_inv_irreducible, // sgn_inv(p) for all irreducible p of level i
    connected,           // connected(i)
    an_sub,              // an_sub(i)
    sample,              // sample(s) for all s ∈ Ri of level i
    repr,                // repr(I, s) for all I of level i and s ∈ ...
    holds,               // marker for "goal holds" (terminal)
    _count               // always last: number of properties
  };

  // Utility: property to string (for debugging, logging, etc.)
  inline const char* to_string(polynom_property prop) {
    switch (prop) {
    case polynom_property::ir_ord:              return "ir_ord";
    case polynom_property::an_del:              return "an_del";
    case polynom_property::non_null:            return "non_null";
    case polynom_property::ord_inv_reducible:   return "ord_inv_reducible";
    case polynom_property::ord_inv_irreducible: return "ord_inv_irreducible";
    case polynom_property::sgn_inv_reducible:   return "sgn_inv_reducible";
    case polynom_property::sgn_inv_irreducible: return "sgn_inv_irreducible";
    case polynom_property::connected:           return "connected";
    case polynom_property::an_sub:              return "an_sub";
    case polynom_property::sample:              return "sample";
    case polynom_property::repr:                return "repr";
    case polynom_property::holds:               return "holds";
    default:                                    return "?";
    }
  }

  // A single property instance ("fact") subject.
  // Note: Not all fields are used by every property; unused fields are left at defaults.
  struct property_inst {
    polynom_property prop;
    // Optional subject parameters
    poly*            p      = nullptr;  // for properties about a polynomial p
    var              y      = -1;       // variable (e.g., indexed root variable)
    unsigned         i      = 0;        // level/index (paper's i)
    unsigned         s_idx  = 0;        // index for "s ∈ R_i" (sample/root index), if applicable
    unsigned         I_idx  = 0;        // index for interval I (for repr), if applicable
    unsigned         ord_id = 0;        // identifier for an indexed root ordering ≼, if applicable

    // Convenience builders
    static property_inst of(poly* p, polynom_property prop, unsigned level) {
      property_inst r{prop}; r.p = p; r.i = level; return r;
    }
    static property_inst at_level(polynom_property prop, unsigned level) {
      property_inst r{prop}; r.i = level; return r;
    }
    static property_inst sample_at(unsigned s_idx, unsigned level) {
      property_inst r{polynom_property::sample}; r.s_idx = s_idx; r.i = level; return r;
    }
    static property_inst repr_of(unsigned I_idx, unsigned s_idx, unsigned level) {
      property_inst r{polynom_property::repr}; r.I_idx = I_idx; r.s_idx = s_idx; r.i = level; return r;
    }

    // Display
    std::string str() const {
      std::ostringstream out;
      out << to_string(prop) << "(";
      bool first = true;
      auto add = [&](std::string const& k, uint64_t v) {
        if (!first) out << ", ";
        first = false;
        out << k << "=" << v;
      };
      if (p) add("p", reinterpret_cast<uint64_t>(p));
      if (y != -1) add("y", static_cast<uint64_t>(y));
      add("i", i);
      if (s_idx) add("s", s_idx);
      if (I_idx) add("I", I_idx);
      if (ord_id) add("ord", ord_id);
      out << ")";
      return out.str();
    }

    // Equality (coarse; pointer identity for p is intentional)
    bool operator==(property_inst const& o) const {
      return prop == o.prop &&
             p == o.p &&
             y == o.y &&
             i == o.i &&
             s_idx == o.s_idx &&
             I_idx == o.I_idx &&
             ord_id == o.ord_id;
    }
  };

  // Proof rule identifiers (align roughly with paper sections; can be refined later).
  enum class proof_rule : unsigned {
    // Skeleton rules; refine/extend as we implement specific inferences
    axiom,          // introduce a known/assumed property
    derive,         // generic derivation step (placeholder)
    r_ir_ord,       // rules for ir_ord propagation
    r_an_del,
    r_non_null,
    r_ord_inv_red,
    r_ord_inv_irred,
    r_sgn_inv_red,
    r_sgn_inv_irred,
    r_connected,
    r_an_sub,
    r_sample,
    r_repr,
    r_close_holds   // closes to 'holds'
  };

  inline const char* to_string(proof_rule r) {
    switch (r) {
    case proof_rule::axiom:         return "axiom";
    case proof_rule::derive:        return "derive";
    case proof_rule::r_ir_ord:      return "r_ir_ord";
    case proof_rule::r_an_del:      return "r_an_del";
    case proof_rule::r_non_null:    return "r_non_null";
    case proof_rule::r_ord_inv_red: return "r_ord_inv_red";
    case proof_rule::r_ord_inv_irred:return "r_ord_inv_irred";
    case proof_rule::r_sgn_inv_red: return "r_sgn_inv_red";
    case proof_rule::r_sgn_inv_irred:return "r_sgn_inv_irred";
    case proof_rule::r_connected:   return "r_connected";
    case proof_rule::r_an_sub:      return "r_an_sub";
    case proof_rule::r_sample:      return "r_sample";
    case proof_rule::r_repr:        return "r_repr";
    case proof_rule::r_close_holds: return "r_close_holds";
    default:                        return "?";
    }
  }

  // A single proof step: premises -> conclusion, with metadata.
  struct proof_step {
    proof_rule                    rule;
    property_mapping_case         ctx = property_mapping_case::case1; // for multi-case rules (e.g., 4.2)
    std::vector<unsigned>         premises;   // indices into facts_
    unsigned                      conclusion; // index into facts_

    std::string str(std::vector<property_inst> const& facts) const {
      std::ostringstream out;
      out << to_string(rule) << "[case=" << static_cast<unsigned>(ctx) << "]: ";
      out << "{";
      for (unsigned k = 0; k < premises.size(); ++k) {
        if (k) out << ", ";
        out << facts[premises[k]].str();
      }
      out << "} => " << facts[conclusion].str();
      return out.str();
    }
  };

  // A lightweight proof object to manage facts and steps.
  class levelwise_proof {
    std::vector<property_inst> m_facts;
    std::vector<proof_step>    m_steps;

    // Linear lookup to avoid hashing complexity here.
    int find_fact(property_inst const& f) const {
      for (unsigned i = 0; i < m_facts.size(); ++i)
        if (m_facts[i] == f) return static_cast<int>(i);
      return -1;
    }

  public:
    unsigned intern_fact(property_inst const& f) {
      int idx = find_fact(f);
      if (idx >= 0) return static_cast<unsigned>(idx);
      m_facts.push_back(f);
      return static_cast<unsigned>(m_facts.size() - 1);
    }

    unsigned add_axiom(property_inst const& concl) {
      unsigned c = intern_fact(concl);
      m_steps.push_back(proof_step{proof_rule::axiom, property_mapping_case::case1, {}, c});
      return c;
    }

    unsigned add_step(proof_rule rule,
                      property_mapping_case ctx,
                      std::vector<unsigned> const& premises,
                      property_inst const& conclusion) {
      unsigned c = intern_fact(conclusion);
      m_steps.push_back(proof_step{rule, ctx, premises, c});
      return c;
    }

    std::string dump() const {
      std::ostringstream out;
      for (auto const& st : m_steps)
        out << st.str(m_facts) << "\n";
      return out.str();
    }

    std::vector<property_inst> const& facts() const { return m_facts; }
    std::vector<proof_step>    const& steps() const { return m_steps; }
  };

  // Property propagation mapping: for each property, the set of properties it implies (see levelwise paper, e.g., rule 4.2)
  // Overload: property_dependencies with context (for rules like 4.2 with multiple cases).
  // Note: This is a scaffold. Fill per paper’s precise rules (TODO).
  inline std::vector<polynom_property>
  get_property_dependencies(polynom_property prop, property_mapping_case /*p_case*/, polynomial_ref& /*p*/, unsigned /*i*/) {
    std::vector<polynom_property> ret;
    switch (prop) {
    case polynom_property::ir_ord:
      // TODO: fill using Property 4.3 / Rule 4.2 cases; currently no direct property implications recorded here.
      break;

    case polynom_property::an_del:
      // Example: an_del(p) might imply non_null(p) or be used in combination with others; leave empty until specified.
      break;

    case polynom_property::non_null:
      // Usually terminal for p; no generic implications without context.
      break;

    case polynom_property::ord_inv_reducible:
      // Often accompanies sign invariance for reducible polynomials; no generic implication recorded here.
      break;

    case polynom_property::ord_inv_irreducible:
      // Likewise for irreducible.
      break;

    case polynom_property::sgn_inv_reducible:
      // In many presentations, sign invariance implies order invariance on reducible components.
      // If the paper states so, uncomment:
      // ret.push_back(polynom_property::ord_inv_reducible);
      break;

    case polynom_property::sgn_inv_irreducible:
      // If sign invariance implies order invariance for irreducible p, uncomment:
      // ret.push_back(polynom_property::ord_inv_irreducible);
      break;

    case polynom_property::connected:
      // connected(i) might enable sample or representation derivations; leave empty here.
      break;

    case polynom_property::an_sub:
      // an_sub(i) may enable additional sampling; leave empty here.
      break;

    case polynom_property::sample:
      // sample(s) is often a leaf for evaluating properties at s.
      break;

    case polynom_property::repr:
      // repr(I, s) together with others may lead to holds; no generic implication alone.
      break;

    case polynom_property::holds:
      // Terminal goal, no further implications.
      break;

    default:
      break;
    }
    return ret;
  }

  // Example driver/stub that will eventually orchestrate Levelwise projection with proof logging.
  void lewelwise_project(polynomial_ref_vector & /*ps*/, var /*max_x*/) {
    //std::cout << "call\n";
    //exit(0);
    // Scaffold example (no-ops for now):
    // levelwise_proof pr;
    // for (auto* p : ps) { pr.add_axiom(property_inst::of(p, polynom_property::an_del, /*level*/0)); }
    // std::cout << pr.dump();
  }
}