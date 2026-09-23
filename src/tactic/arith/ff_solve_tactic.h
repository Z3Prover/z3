#pragma once
#include "util/params.h"
class ast_manager;
class tactic;
tactic *mk_ff_solve_tactic(ast_manager &m, params_ref const &p = params_ref());
tactic *mk_ff_sat_tactic(ast_manager &m, params_ref const &p = params_ref());
tactic *mk_ff_simplify_tactic(ast_manager &m, params_ref const &p = params_ref());
#include "tactic/tactic.h"
Z3_ADD_TACTIC(ff_sat, "ff-sat", "combine Boolean SAT search with modular field algebra.", mk_ff_sat_tactic(m, p));
Z3_ADD_TACTIC(ff_solve, "ff-solve", "solve prime-field conjunctions using modular elimination and Groebner bases.",
              mk_ff_solve_tactic(m, p));
Z3_ADD_TACTIC(ff_simplify, "ff-simplify", "simplify field expressions and propagate constants (no certificates).",
              mk_ff_simplify_tactic(m, p));
