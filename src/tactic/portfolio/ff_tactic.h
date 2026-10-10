#pragma once
#include "util/params.h"
class ast_manager;
class tactic;
tactic *mk_ff_smt_tactic(ast_manager &m, params_ref const &p);

class expr;
bool has_ff_terms(ast_manager &m, expr *e);
