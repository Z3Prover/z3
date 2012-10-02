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
#ifndef _PROBE_ARITH_H_
#define _PROBE_ARITH_H_

class probe;
probe * mk_arith_avg_bw_probe();
probe * mk_arith_max_bw_probe();
probe * mk_arith_avg_degree_probe();
probe * mk_arith_max_degree_probe();

probe * mk_is_qflia_probe();
probe * mk_is_qflra_probe();
probe * mk_is_qflira_probe();
probe * mk_is_ilp_probe();
probe * mk_is_mip_probe();

probe * mk_is_qfnia_probe();
probe * mk_is_qfnra_probe();
probe * mk_is_nia_probe();
probe * mk_is_nra_probe();

#endif
