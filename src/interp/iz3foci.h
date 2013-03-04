/* Copyright 2011 Microsoft Research. */

#ifndef IZ3FOCI_H
#define IZ3FOCI_H

#include "iz3secondary.h"

/** Secondary prover based on Cadence FOCI. */

class iz3foci {
 public:
  static iz3secondary *create(iz3mgr *mgr, int num, int *parents);
};

#endif
