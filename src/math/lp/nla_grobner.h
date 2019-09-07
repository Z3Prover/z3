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

#include "math/lp/nla_common.h"
#include "math/lp/nex.h"
namespace nla {
class core;

enum class var_weight {
        FIXED = 0,
            QUOTED_FIXED =  1,
            BOUNDED    =    2,
            QUOTED_BOUNDED = 3,
            NOT_FREE      =  4,
            QUOTED_NOT_FREE = 5,
            FREE          =   6,
            QUOTED_FREE    = 7,
            MAX_DEFAULT_WEIGHT = 7
            };

class nla_grobner : common {
    lp::int_set         m_rows;
    lp::int_set         m_active_vars;
    svector<var_weight> m_active_vars_weights;
    unsigned            m_num_new_equations;
public:
    nla_grobner(core *core);
    void grobner_lemmas();
private:
    void find_nl_cluster();
    void prepare_rows_and_active_vars();
    void add_var_and_its_factors_to_q_and_collect_new_rows(lpvar j,  std::queue<lpvar>& q);
    void display(std::ostream&);
    void set_active_vars_weights();
    void init();
    var_weight get_var_weight(lpvar) const;
    void compute_basis();
    void update_statistics();
    bool find_conflict();
    bool push_calculation_forward();
    void compute_basis_init();        
    bool compute_basis_loop();
    void set_gb_exhausted();
}; // end of grobner
}
