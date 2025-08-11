  // Context for property propagation (e.g., which case of rule 4.2 applies)
  enum class property_mapping_case : unsigned {
    case1 = 0, 
    case2 = 1,  
    case3 = 3,
  };

/*++
  Copyright (c) 2025

  Module Name:
    levelwise.h

  Abstract:
    Levelwise algorithm property and mapping definitions (see levelwise paper).

  --*/
#pragma once

#include <vector>
#include "nlsat_types.h"

namespace nlsat {

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
    default: return "unknown";
    }
  }


  // Property propagation mapping: for each property, the set of properties it implies (see levelwise paper, e.g., rule 4.2)
  // Example: property_dependencies[root_property::sgn_inv] = {root_property::ord_inv, ...}
  // Overload: property_dependencies with context (for rules like 4.2 with multiple cases)
  inline const std::vector<polynom_property>& property_dependencies(polynom_property prop, property_mapping_case p_case) {
    // Each property has a table of vectors, one per context case
    static const std::vector<polynom_property> table[][2] = {
      /* sgn_inv  */ { { /* case1: ... */ }, { /* case2: ... */ } },
      /* ord_inv  */ { { /* case1: ... */ }, { /* case2: ... */ } },
      /* non_null */ { { /* case1: ... */ }, { /* case2: ... */ } }
      // Extend as needed for more properties
    };
    return table[(unsigned)prop][(unsigned)p_case];
  }

  // For static (context-free) queries, default to case1
  inline const std::vector<polynom_property>& property_dependencies(polynom_property prop) {
    return property_dependencies(prop, property_mapping_case::case1);
  }

} // namespace nlsat
