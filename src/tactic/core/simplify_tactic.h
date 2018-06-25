/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    simplify_tactic.h

Abstract:

    Apply simplification and rewriting rules.

Author:

    Leonardo (leonardo) 2011-11-20

Notes:

--*/
#ifndef SIMPLIFY_TACTIC_H_
#define SIMPLIFY_TACTIC_H_

#include "tactic/tactic.h"
#include "tactic/tactical.h"

class simplify_tactic : public tactic {
    struct     imp;
    imp *      m_imp;
    params_ref m_params;
public:
    simplify_tactic(ast_manager & m, params_ref const & ref = params_ref());
    ~simplify_tactic() override;

    void updt_params(params_ref const & p) override;

    static void get_param_descrs(param_descrs & r);
    
    void collect_param_descrs(param_descrs & r) override { get_param_descrs(r); }
    
    void operator()(goal_ref const & in, goal_ref_buffer & result) override;
    
    void cleanup() override;

    unsigned get_num_steps() const;

    tactic * translate(ast_manager & m) override { return alloc(simplify_tactic, m, m_params); }

};

tactic * mk_simplify_tactic(ast_manager & m, params_ref const & p = params_ref());
tactic * mk_elim_and_tactic(ast_manager & m, params_ref const & p = params_ref());

/*
  ADD_TACTIC("simplify", "apply simplification rules.", "mk_simplify_tactic(m, p)")
  ADD_TACTIC("elim-and", "convert (and a b) into (not (or (not a) (not b))).", "mk_elim_and_tactic(m, p)")
*/

#endif
