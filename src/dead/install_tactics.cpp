/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    install_tactics.cpp

Abstract:
    Install tactics in the SMT 2.0 frontend.

Author:

    Leonardo (leonardo) 2012-02-19

Notes:

--*/
#include"tactic_cmds.h"
#include"cmd_context.h"
#include"simplify_tactic.h"
#include"split_clause_tactic.h"
#include"normalize_bounds_tactic.h"
#include"elim_uncnstr_tactic.h"
#include"add_bounds_tactic.h"
#include"ctx_simplify_tactic.h"
#include"ctx_solver_simplify_tactic.h"

#include"bit_blaster_tactic.h"
#include"bv1_blaster_tactic.h"
#include"der_tactic.h"
#include"aig_tactic.h"
#include"smt_tactic.h"
#include"sat_tactic.h"
#include"occf_tactic.h"
#include"qe_tactic.h"
#include"qe_sat_tactic.h"
#include"propagate_values_tactic.h"
#include"nnf_tactic.h"
#include"solve_eqs_tactic.h"
#include"max_bv_sharing_tactic.h"
#include"elim_term_ite_tactic.h"
#include"fix_dl_var_tactic.h"
#include"tseitin_cnf_tactic.h"
#include"degree_shift_tactic.h"
#include"purify_arith_tactic.h"
#include"nla2bv_tactic.h"
#include"nlsat_tactic.h"
#include"factor_tactic.h"
#include"fm_tactic.h"
#include"diff_neq_tactic.h"
#include"lia2pb_tactic.h"
#include"fpa2bv_tactic.h"
#include"qffpa_tactic.h"
#include"pb2bv_tactic.h"
#include"recover_01_tactic.h"
#include"symmetry_reduce_tactic.h"
#include"distribute_forall_tactic.h"
#include"reduce_args_tactic.h"
#include"bv_size_reduction_tactic.h"
#include"propagate_ineqs_tactic.h"
#include"cofactor_term_ite_tactic.h"
// include"mip_tactic.h"
#include"vsubst_tactic.h"
#include"sls_tactic.h"
#include"probe_arith.h"
#include"qflia_tactic.h"
#include"qflra_tactic.h"
#include"qfnia_tactic.h"
#include"qfnra_tactic.h"
#include"qfbv_tactic.h"
#include"subpaving_tactic.h"
#include"unit_subsumption_tactic.h"
#include"qfnra_nlsat_tactic.h"
#include"ufbv_tactic.h"

MK_SIMPLE_TACTIC_FACTORY(simplifier_fct,         mk_simplify_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(split_clause_fct,       mk_split_clause_tactic(p));
MK_SIMPLE_TACTIC_FACTORY(normalize_bounds_fct,   mk_normalize_bounds_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(elim_uncnstr_fct,       mk_elim_uncnstr_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(add_bounds_fct,         mk_add_bounds_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(bitblaster_fct,         mk_bit_blaster_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(bv1blaster_fct,         mk_bv1_blaster_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(aig_fct,                mk_aig_tactic(p));
MK_SIMPLE_TACTIC_FACTORY(skip_fct,               mk_skip_tactic());
MK_SIMPLE_TACTIC_FACTORY(fail_fct,               mk_fail_tactic());
MK_SIMPLE_TACTIC_FACTORY(smt_fct,                mk_smt_tactic(p));
MK_SIMPLE_TACTIC_FACTORY(sat_fct,                mk_sat_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(sat_preprocess_fct,     mk_sat_preprocessor_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(ctx_simplify_fct,       mk_ctx_simplify_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(ctx_solver_simplify_fct,       mk_ctx_solver_simplify_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(unit_subsume_fct,       mk_unit_subsumption_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(der_fct,                mk_der_tactic(m));
MK_SIMPLE_TACTIC_FACTORY(occf_fct,               mk_occf_tactic(m));
MK_SIMPLE_TACTIC_FACTORY(qe_fct,                 mk_qe_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(qe_sat_fct,             qe::mk_sat_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(propagate_values_fct,   mk_propagate_values_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(snf_fct,                mk_snf_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(nnf_fct,                mk_nnf_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(solve_eqs_fct,          mk_solve_eqs_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(max_bv_sharing_fct,     mk_max_bv_sharing_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(elim_term_ite_fct,      mk_elim_term_ite_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(fix_dl_var_fct,         mk_fix_dl_var_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(tseitin_cnf_fct,        mk_tseitin_cnf_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(tseitin_cnf_core_fct,   mk_tseitin_cnf_core_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(degree_shift_fct,       mk_degree_shift_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(purify_arith_fct,       mk_purify_arith_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(nlsat_fct,              mk_nlsat_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(factor_fct,             mk_factor_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(fm_fct,                 mk_fm_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(fail_if_undecided_fct,  mk_fail_if_undecided_tactic());
MK_SIMPLE_TACTIC_FACTORY(diff_neq_fct,           mk_diff_neq_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(lia2pb_fct,             mk_lia2pb_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(fpa2bv_fct,             mk_fpa2bv_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(qffpa_fct,              mk_qffpa_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(pb2bv_fct,              mk_pb2bv_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(recover_01_fct,         mk_recover_01_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(elim_and_fct,           mk_elim_and_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(symmetry_reduce_fct,    mk_symmetry_reduce_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(distribute_forall_fct,  mk_distribute_forall_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(reduce_args_fct,        mk_reduce_args_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(bv_size_reduction_fct,  mk_bv_size_reduction_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(propagate_ineqs_fct,    mk_propagate_ineqs_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(cofactor_term_ite_fct,  mk_cofactor_term_ite_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(nla2bv_fct,             mk_nla2bv_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(vsubst_fct,             mk_vsubst_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(qfbv_sls_fct,           mk_qfbv_sls_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(subpaving_fct,          mk_subpaving_tactic(m, p));

MK_SIMPLE_TACTIC_FACTORY(qflia_fct,              mk_qflia_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(qflra_fct,              mk_qflra_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(qfbv_fct,               mk_qfbv_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(qfnia_fct,              mk_qfnia_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(qfnra_fct,              mk_qfnra_tactic(m, p));
MK_SIMPLE_TACTIC_FACTORY(ufbv_fct,               mk_ufbv_tactic(m, p));

#define ADD_TACTIC_CMD(NAME, DESCR, FACTORY) ctx.insert(alloc(tactic_cmd, symbol(NAME), DESCR, alloc(FACTORY)))
#define ADD_PROBE(NAME, DESCR, PROBE) ctx.insert(alloc(probe_info, symbol(NAME), DESCR, PROBE))

void install_tactics(tactic_manager & ctx) {


    ADD_TACTIC_CMD("ctx-solver-simplify", "apply solver-based contextual simplification rules.", ctx_solver_simplify_fct);
    ADD_TACTIC_CMD("unit-subsume-simplify", "unit subsumption simplification.", unit_subsume_fct);


    ADD_PROBE("memory", "ammount of used memory in megabytes.", mk_memory_probe());
    ADD_PROBE("depth", "depth of the input goal.", mk_depth_probe());
    ADD_PROBE("size", "number of assertions in the given goal.", mk_size_probe());
    ADD_PROBE("num-exprs", "number of expressions/terms in the given goal.", mk_num_exprs_probe());
    ADD_PROBE("num-consts", "number of non Boolean constants in the given goal.", mk_num_consts_probe());
    ADD_PROBE("num-bool-consts", "number of Boolean constants in the given goal.", mk_num_bool_consts_probe());
    ADD_PROBE("num-arith-consts", "number of arithmetic constants in the given goal.", mk_num_arith_consts_probe());
    ADD_PROBE("num-bv-consts", "number of bit-vector constants in the given goal.", mk_num_bv_consts_probe());
    ADD_PROBE("produce-proofs", "true if proof generation is enabled for the given goal.", mk_produce_proofs_probe());
    ADD_PROBE("produce-model", "true if model generation is enabled for the given goal.", mk_produce_models_probe());
    ADD_PROBE("produce-unsat-cores", "true if unsat-core generation is enabled for the given goal.", mk_produce_unsat_cores_probe());
    ADD_PROBE("has-patterns", "true if the goal contains quantifiers with patterns.", mk_has_pattern_probe());
    ADD_PROBE("is-propositional", "true if the goal is in propositional logic.", mk_is_propositional_probe());
    ADD_PROBE("is-qfbv", "true if the goal is in QF_BV.", mk_is_qfbv_probe());
    ADD_PROBE("is-qfbv-eq", "true if the goal is in a fragment of QF_BV which uses only =, extract, concat.", mk_is_qfbv_eq_probe());
    ADD_PROBE("is-qflia", "true if the goal is in QF_LIA.", mk_is_qflia_probe());
    ADD_PROBE("is-qflra", "true if the goal is in QF_LRA.", mk_is_qflra_probe());
    ADD_PROBE("is-qflira", "true if the goal is in QF_LIRA.", mk_is_qflira_probe());
    ADD_PROBE("is-ilp", "true if the goal is ILP.", mk_is_ilp_probe());
    ADD_PROBE("is-unbounded", "true if the goal contains integer/real constants that do not have lower/upper bounds.", mk_is_unbounded_probe());
    ADD_PROBE("is-pb", "true if the goal is a pseudo-boolean problem.", mk_is_pb_probe());
    ADD_PROBE("arith-max-deg", "max polynomial total degree of an arithmetic atom.", mk_arith_max_degree_probe());
    ADD_PROBE("arith-avg-deg", "avg polynomial total degree of an arithmetic atom.", mk_arith_avg_degree_probe());
    ADD_PROBE("arith-max-bw", "max coefficient bit width.", mk_arith_max_bw_probe());
    ADD_PROBE("arith-avg-bw", "avg coefficient bit width.", mk_arith_avg_bw_probe());

    ADD_PROBE("is-qfnia", "true if the goal is in QF_NIA (quantifier-free nonlinear integer arithmetic).", mk_is_qfnia_probe());
    ADD_PROBE("is-qfnra", "true if the goal is in QF_NRA (quantifier-free nonlinear real arithmetic).", mk_is_qfnra_probe());
    ADD_PROBE("is-nia", "true if the goal is in NIA (nonlinear integer arithmetic, formula may have quantifiers).", mk_is_nia_probe());
    ADD_PROBE("is-nra", "true if the goal is in NRA (nonlinear real arithmetic, formula may have quantifiers).", mk_is_nra_probe());
}


