// things which you probably want to do off-thread
// from https://github.com/Z3Prover/z3/issues/5746#issuecomment-1006289146
export const asyncFuncs = [
  'Z3_eval_smtlib2_string',
  'Z3_simplify',
  'Z3_simplify_ex',
  'Z3_solver_check',
  'Z3_solver_check_assumptions',
  'Z3_solver_cube',
  'Z3_solver_get_consequences',
  'Z3_tactic_apply',
  'Z3_tactic_apply_ex',
  'Z3_optimize_check',
  'Z3_algebraic_roots',
  'Z3_algebraic_eval',
  'Z3_fixedpoint_query',
  'Z3_fixedpoint_query_relations',
  'Z3_fixedpoint_query_from_lvl',
  'Z3_polynomial_subresultants',
];
