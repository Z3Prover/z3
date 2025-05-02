/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    <name>

Abstract:

    <abstract>

Author:
    Nikolaj Bjorner (nbjorner)
    Lev Nachmanson (levnach)

Revision History:


--*/
#pragma once
#include "math/lp/lp_settings.h"
#include "math/lp/static_matrix.h"
#include "util/uint_set.h"
#include "math/lp/lar_term.h"
#include "math/lp/lar_constraints.h"
#include "math/lp/hnf_cutter.h"
#include "math/lp/int_gcd_test.h"
#include "math/lp/lia_move.h"
#include "math/lp/explanation.h"

namespace lp {
class lar_solver;
class lar_core_solver;
class int_solver {

    friend struct create_cut;
    friend class gomory;
    friend class int_cube;
    friend class int_branch;
    friend class int_gcd_test;
    friend class hnf_cutter;
    friend class imp;
    friend class dioph_eq;
    class imp;
    lar_solver&         lra;
    lar_core_solver&    lrac;
    imp*                m_imp; 
    vector<equality>       m_equalities;
    bool get_freedom_interval_for_column(unsigned j, bool & inf_l, impq & l, bool & inf_u, impq & u, mpq & m);
    bool is_boxed(unsigned j) const;
    bool is_free(unsigned j) const;
    bool value_is_int(unsigned j) const;
    bool is_feasible() const;
    bool column_is_int_inf(unsigned j) const;
    std::ostream& display_inf_rows(std::ostream&) const;
   
    lp_settings& settings();
    const lp_settings& settings() const;
public:
    bool at_bound(unsigned j) const;
    bool has_lower(unsigned j) const;
    bool has_upper(unsigned j) const;
    unsigned row_of_basic_column(unsigned j) const;
public:
    int_solver(lar_solver& lp);
    ~int_solver();
    // the function that doing the main job
    lia_move check(explanation *);
    lar_term const& get_term() const;
    lar_term & get_term();
    mpq const& offset() const;
    mpq & offset();
    bool is_upper() const;
    bool& is_upper();
    bool is_base(unsigned j) const;
    bool is_real(unsigned j) const;
    const impq & lower_bound(unsigned j) const;
    const impq & upper_bound(unsigned j) const;
    bool column_is_int(lpvar j) const;
    const impq & get_value(unsigned j) const;
    bool at_lower(unsigned j) const;
    bool at_upper(unsigned j) const;
    void simplify(std::function<bool(unsigned)>& is_root);
    vector<equality> const& equalities() const { return m_equalities; }
    bool is_fixed(unsigned j) const;
    std::ostream& display_column(std::ostream & out, unsigned j) const;
    u_dependency* column_upper_bound_constraint(unsigned j) const;
    u_dependency* column_lower_bound_constraint(unsigned j) const;
    bool current_solution_is_inf_on_cut() const;

    bool shift_var(unsigned j, unsigned range);
    std::ostream&  display_row_info(std::ostream & out, unsigned row_index) const;
    std::ostream & display_row(std::ostream & out, std_vector<row_cell<rational>> const & row) const;
    bool is_term(unsigned j) const;
    unsigned column_count() const;
    int select_int_infeasible_var();
    void set_expl(lp::explanation * ex);
    explanation * expl();
    #if Z3DEBUG
    lia_move dio_test(); 
    #endif
};
}
