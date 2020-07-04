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
#pragma once

#include "tactic/probe.h"

probe * mk_ackr_bound_probe();

/*
  ADD_PROBE("ackr-bound-probe", "A probe to give an upper bound of Ackermann congruence lemmas that a formula might generate.", "mk_ackr_bound_probe()")
*/

