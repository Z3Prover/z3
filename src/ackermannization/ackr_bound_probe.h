 /*++
 Copyright (c) 2016 Microsoft Corporation

 Module Name:

  ackr_bound_probe.h

 Abstract:

 A probe to give an upper bound of Ackermann congruence lemmas that a formula might generate.

 Author:

 Mikolas Janota

 Revision History:
 --*/
#ifndef ACKR_BOUND_PROBE_H_
#define ACKR_BOUND_PROBE_H_

#include "tactic/probe.h"

probe * mk_ackr_bound_probe();

/*
  ADD_PROBE("ackr-bound-probe", "A probe to give an upper bound of Ackermann congruence lemmas that a formula might generate.", "mk_ackr_bound_probe()")
*/

#endif /* ACKR_BOUND_PROBE_H_ */
