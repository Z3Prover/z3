/*++
  Copyright (c) 2017 Microsoft Corporation


  Abstract:

    simplification routines for pdd polys

  Author:
    Nikolaj Bjorner (nbjorner)
    Lev Nachmanson (levnach)

  --*/
#pragma once

#include "util/uint_set.h"
#include "math/grobner/pdd_solver.h"

namespace dd {

class simplifier {

    typedef solver::equation equation;
    typedef ptr_vector<equation> equation_vector;

    solver& s;
public:

    simplifier(solver& s): s(s) {}

    void operator()();

private:

    struct compare_top_var;
    bool simplify_linear_step(bool binary);
    bool simplify_linear_step(equation_vector& linear);
    typedef vector<equation_vector> use_list_t;
    use_list_t get_use_list();
    void add_to_use(equation* e, use_list_t& use_list);
    void remove_from_use(equation* e, use_list_t& use_list);
    void remove_from_use(equation* e, use_list_t& use_list, unsigned except_v);

    bool simplify_cc_step();
    bool simplify_elim_pure_step();
    bool simplify_elim_dual_step();
    bool simplify_leaf_step();
    bool simplify_exlin();
    void init_orbits(vector<pdd> const& eqs, vector<uint_set>& orbits);
    void exlin_augment(vector<uint_set> const& orbits, vector<pdd>& eqs);
    void simplify_exlin(vector<uint_set> const& orbits, vector<pdd> const& eqs, vector<pdd>& simp_eqs);


};

}
