/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    probe_arith.h

Abstract:

    Some probes for arithmetic problems.

Author:

    Leonardo de Moura (leonardo) 2012-03-01.

Revision History:

--*/
#pragma once
#include "tactic/probe.h"

class probe;
probe * mk_arith_avg_bw_probe();
probe * mk_arith_max_bw_probe();
probe * mk_arith_avg_degree_probe();
probe * mk_arith_max_degree_probe();

Z3_ADD_PROBE(arith_max_deg, "arith-max-deg", "max polynomial total degree of an arithmetic atom.", mk_arith_max_degree_probe());
Z3_ADD_PROBE(arith_avg_deg, "arith-avg-deg", "avg polynomial total degree of an arithmetic atom.", mk_arith_avg_degree_probe());
Z3_ADD_PROBE(arith_max_bw, "arith-max-bw", "max coefficient bit width.", mk_arith_max_bw_probe());
Z3_ADD_PROBE(arith_avg_bw, "arith-avg-bw", "avg coefficient bit width.", mk_arith_avg_bw_probe());

probe * mk_is_qflia_probe();
probe * mk_is_qfauflia_probe();
probe * mk_is_qflra_probe();
probe * mk_is_qflira_probe();
probe * mk_is_ilp_probe();
probe * mk_is_mip_probe();

Z3_ADD_PROBE(is_qflia, "is-qflia", "true if the goal is in QF_LIA.", mk_is_qflia_probe());
Z3_ADD_PROBE(is_qfauflia, "is-qfauflia", "true if the goal is in QF_AUFLIA.", mk_is_qfauflia_probe());
Z3_ADD_PROBE(is_qflra, "is-qflra", "true if the goal is in QF_LRA.", mk_is_qflra_probe());
Z3_ADD_PROBE(is_qflira, "is-qflira", "true if the goal is in QF_LIRA.", mk_is_qflira_probe());
Z3_ADD_PROBE(is_ilp, "is-ilp", "true if the goal is ILP.", mk_is_ilp_probe());

probe * mk_is_qfnia_probe();
probe * mk_is_qfnra_probe();
probe * mk_is_nia_probe();
probe * mk_is_nra_probe();
probe * mk_is_nira_probe();
probe * mk_is_lia_probe();
probe * mk_is_lra_probe();
probe * mk_is_lira_probe();
probe * mk_is_qfufnra_probe();

Z3_ADD_PROBE(is_qfnia, "is-qfnia", "true if the goal is in QF_NIA (quantifier-free nonlinear integer arithmetic).", mk_is_qfnia_probe());
Z3_ADD_PROBE(is_qfnra, "is-qfnra", "true if the goal is in QF_NRA (quantifier-free nonlinear real arithmetic).", mk_is_qfnra_probe());
Z3_ADD_PROBE(is_nia, "is-nia", "true if the goal is in NIA (nonlinear integer arithmetic, formula may have quantifiers).", mk_is_nia_probe());
Z3_ADD_PROBE(is_nra, "is-nra", "true if the goal is in NRA (nonlinear real arithmetic, formula may have quantifiers).", mk_is_nra_probe());
Z3_ADD_PROBE(is_nira, "is-nira", "true if the goal is in NIRA (nonlinear integer and real arithmetic, formula may have quantifiers).", mk_is_nira_probe());
Z3_ADD_PROBE(is_lia, "is-lia", "true if the goal is in LIA (linear integer arithmetic, formula may have quantifiers).", mk_is_lia_probe());
Z3_ADD_PROBE(is_lra, "is-lra", "true if the goal is in LRA (linear real arithmetic, formula may have quantifiers).", mk_is_lra_probe());
Z3_ADD_PROBE(is_lira, "is-lira", "true if the goal is in LIRA (linear integer and real arithmetic, formula may have quantifiers).", mk_is_lira_probe());
Z3_ADD_PROBE(is_qfufnra, "is-qfufnra", "true if the goal is QF_UFNRA (quantifier-free nonlinear real arithmetic with other theories).", mk_is_qfufnra_probe());
