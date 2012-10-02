# Automatically generated file, generator: mk_z3tactics.py
import z3core
import z3

def simplify_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'simplify'), ctx)

def split_clause_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'split-clause'), ctx)

def normalize_bounds_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'normalize-bounds'), ctx)

def elim_uncnstr_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'elim-uncnstr'), ctx)

def elim_and_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'elim-and'), ctx)

def add_bounds_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'add-bounds'), ctx)

def aig_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'aig'), ctx)

def skip_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'skip'), ctx)

def fail_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'fail'), ctx)

def smt_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'smt'), ctx)

def bit_blast_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'bit-blast'), ctx)

def bv1_blast_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'bv1-blast'), ctx)

def sat_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'sat'), ctx)

def sat_preprocess_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'sat-preprocess'), ctx)

def ctx_simplify_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'ctx-simplify'), ctx)

def ctx_solver_simplify_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'ctx-solver-simplify'), ctx)

def der_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'der'), ctx)

def unit_subsume_simplify_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'unit-subsume-simplify'), ctx)

def occf_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'occf'), ctx)

def qe_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'qe'), ctx)

def qe_sat_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'qe-sat'), ctx)

def propagate_values_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'propagate-values'), ctx)

def snf_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'snf'), ctx)

def nnf_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'nnf'), ctx)

def solve_eqs_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'solve-eqs'), ctx)

def max_bv_sharing_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'max-bv-sharing'), ctx)

def elim_term_ite_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'elim-term-ite'), ctx)

def fix_dl_var_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'fix-dl-var'), ctx)

def tseitin_cnf_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'tseitin-cnf'), ctx)

def tseitin_cnf_core_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'tseitin-cnf-core'), ctx)

def degree_shift_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'degree-shift'), ctx)

def purify_arith_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'purify-arith'), ctx)

def nlsat_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'nlsat'), ctx)

def factor_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'factor'), ctx)

def fm_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'fm'), ctx)

def fail_if_undecided_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'fail-if-undecided'), ctx)

def diff_neq_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'diff-neq'), ctx)

def lia2pb_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'lia2pb'), ctx)

def fpa2bv_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'fpa2bv'), ctx)

def qffpa_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'qffpa'), ctx)

def pb2bv_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'pb2bv'), ctx)

def recover_01_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'recover-01'), ctx)

def symmetry_reduce_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'symmetry-reduce'), ctx)

def distribute_forall_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'distribute-forall'), ctx)

def reduce_args_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'reduce-args'), ctx)

def reduce_bv_size_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'reduce-bv-size'), ctx)

def propagate_ineqs_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'propagate-ineqs'), ctx)

def cofactor_term_ite_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'cofactor-term-ite'), ctx)

def mip_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'mip'), ctx)

def nla2bv_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'nla2bv'), ctx)

def vsubst_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'vsubst'), ctx)

def qfbv_sls_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'qfbv-sls'), ctx)

def qflia_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'qflia'), ctx)

def qflra_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'qflra'), ctx)

def qfnia_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'qfnia'), ctx)

def qfnra_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'qfnra'), ctx)

def qfbv_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'qfbv'), ctx)

def subpaving_tactic(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Tactic(z3core.Z3_mk_tactic(ctx.ref(), 'subpaving'), ctx)

def memory_probe(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Probe(z3core.Z3_mk_probe(ctx.ref(), 'memory'), ctx)

def depth_probe(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Probe(z3core.Z3_mk_probe(ctx.ref(), 'depth'), ctx)

def size_probe(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Probe(z3core.Z3_mk_probe(ctx.ref(), 'size'), ctx)

def num_exprs_probe(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Probe(z3core.Z3_mk_probe(ctx.ref(), 'num-exprs'), ctx)

def num_consts_probe(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Probe(z3core.Z3_mk_probe(ctx.ref(), 'num-consts'), ctx)

def num_bool_consts_probe(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Probe(z3core.Z3_mk_probe(ctx.ref(), 'num-bool-consts'), ctx)

def num_arith_consts_probe(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Probe(z3core.Z3_mk_probe(ctx.ref(), 'num-arith-consts'), ctx)

def num_bv_consts_probe(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Probe(z3core.Z3_mk_probe(ctx.ref(), 'num-bv-consts'), ctx)

def produce_proofs_probe(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Probe(z3core.Z3_mk_probe(ctx.ref(), 'produce-proofs'), ctx)

def produce_model_probe(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Probe(z3core.Z3_mk_probe(ctx.ref(), 'produce-model'), ctx)

def produce_unsat_cores_probe(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Probe(z3core.Z3_mk_probe(ctx.ref(), 'produce-unsat-cores'), ctx)

def has_patterns_probe(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Probe(z3core.Z3_mk_probe(ctx.ref(), 'has-patterns'), ctx)

def is_propositional_probe(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Probe(z3core.Z3_mk_probe(ctx.ref(), 'is-propositional'), ctx)

def is_qfbv_probe(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Probe(z3core.Z3_mk_probe(ctx.ref(), 'is-qfbv'), ctx)

def is_qfbv_eq_probe(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Probe(z3core.Z3_mk_probe(ctx.ref(), 'is-qfbv-eq'), ctx)

def is_qflia_probe(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Probe(z3core.Z3_mk_probe(ctx.ref(), 'is-qflia'), ctx)

def is_qflra_probe(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Probe(z3core.Z3_mk_probe(ctx.ref(), 'is-qflra'), ctx)

def is_qflira_probe(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Probe(z3core.Z3_mk_probe(ctx.ref(), 'is-qflira'), ctx)

def is_ilp_probe(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Probe(z3core.Z3_mk_probe(ctx.ref(), 'is-ilp'), ctx)

def is_mip_probe(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Probe(z3core.Z3_mk_probe(ctx.ref(), 'is-mip'), ctx)

def is_unbounded_probe(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Probe(z3core.Z3_mk_probe(ctx.ref(), 'is-unbounded'), ctx)

def is_pb_probe(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Probe(z3core.Z3_mk_probe(ctx.ref(), 'is-pb'), ctx)

def arith_max_deg_probe(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Probe(z3core.Z3_mk_probe(ctx.ref(), 'arith-max-deg'), ctx)

def arith_avg_deg_probe(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Probe(z3core.Z3_mk_probe(ctx.ref(), 'arith-avg-deg'), ctx)

def arith_max_bw_probe(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Probe(z3core.Z3_mk_probe(ctx.ref(), 'arith-max-bw'), ctx)

def arith_avg_bw_probe(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Probe(z3core.Z3_mk_probe(ctx.ref(), 'arith-avg-bw'), ctx)

def is_qfnia_probe(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Probe(z3core.Z3_mk_probe(ctx.ref(), 'is-qfnia'), ctx)

def is_qfnra_probe(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Probe(z3core.Z3_mk_probe(ctx.ref(), 'is-qfnra'), ctx)

def is_nia_probe(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Probe(z3core.Z3_mk_probe(ctx.ref(), 'is-nia'), ctx)

def is_nra_probe(ctx=None):
  ctx = z3._get_ctx(ctx)
  return z3.Probe(z3core.Z3_mk_probe(ctx.ref(), 'is-nra'), ctx)

