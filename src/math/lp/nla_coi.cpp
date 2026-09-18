/*++
  Copyright (c) 2025 Microsoft Corporation

  Author:
    Lev Nachmanson (levnach)
    Nikolaj Bjorner (nbjorner)
  --*/

#include "math/lp/nla_core.h"
#include "math/lp/nla_coi.h"

namespace nla {

  void coi::init() {
      indexed_uint_set visited;
      unsigned_vector todo;
      vector<occurs> var2occurs;
      m_term_set.reset();
      m_mon_set.reset();
      m_constraint_set.reset();
      m_var_set.reset();
      auto& lra = c.lra_solver();

      for (auto ci : lra.constraints().indices()) {
          auto const& c = lra.constraints()[ci];
          if (c.is_auxiliary())
              continue;
          for (auto const& [coeff, v] : c.coeffs()) {
              var2occurs.reserve(v + 1);
              var2occurs[v].constraints.push_back(ci);
          }
      }

      for (auto const& m : c.emons()) {
          for (auto v : m.vars()) {
              var2occurs.reserve(v + 1);
              var2occurs[v].monics.push_back(m.var());
          }
      }

      // Transcendental applications (sin(x), cos(x), ...) are not monomials
      // or lar_solver terms, so without this they would never be reachable
      // by the occurs-graph traversal below: seed both the argument and the
      // output variable of every registered application directly, so any
      // linear constraint that mentions either one (e.g. an assertion on
      // sin(x), or the Taylor-sandwich axiom nra_solver adds relating val to
      // arg) gets pulled into the COI, and nra_solver's setup_solver_poly
      // creates nlsat variables/definitions for them.
      for (auto const& a : c.get_transcendentals().apps()) {
          todo.push_back(a.arg);
          todo.push_back(a.val);
      }

      for (const auto *t :  lra.terms() ) {
          for (auto const iv : *t) {
              auto v = iv.j();
              var2occurs.reserve(v + 1);
              var2occurs[v].terms.push_back(t->j());
          }
      }

      for (auto const& m : c.to_refine())
          todo.push_back(m);

      for (unsigned i = 0; i < todo.size(); ++i) {
          auto v = todo[i];
          if (visited.contains(v))
              continue;
          visited.insert(v);
          m_var_set.insert(v);
          var2occurs.reserve(v + 1);
          for (auto ci : var2occurs[v].constraints) {
              m_constraint_set.insert(ci);
              auto const& c = lra.constraints()[ci];
              for (auto const& [coeff, w] : c.coeffs())
                  todo.push_back(w);
          }
          for (auto w : var2occurs[v].monics)
              todo.push_back(w);

          for (auto ti : var2occurs[v].terms) {
              for (auto iv : lra.get_term(ti))
                  todo.push_back(iv.j());
              todo.push_back(ti);
          }

          if (lra.column_has_term(v)) {
              m_term_set.insert(v);
              for (auto kv : lra.get_term(v))
                  todo.push_back(kv.j());
          }            

          if (c.is_monic_var(v)) {
              m_mon_set.insert(v);
              for (auto w : c.emons()[v])
                  todo.push_back(w);
          }
      }
  }
}
