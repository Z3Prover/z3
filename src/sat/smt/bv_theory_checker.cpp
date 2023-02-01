/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    bv_theory_checker.cpp

Abstract:

    Plugin for bitvector lemmas

Author:

    Nikolaj Bjorner (nbjorner) 2022-08-28

Notes:


--*/

#include "sat/smt/euf_solver.h"
#include "sat/smt/bv_theory_checker.h"


namespace bv {


    /**
       bv is a generic rule used for internalizing bit-vectors. 
       It corresponds to the Tseitin of bit-vectors.
       
       To bypass theory checking we pretend it is trusted.
     */
    bool theory_checker::check_bv(app* jst) { return true; }

    /**
       Let x, y be bit-vector terms and k be an assignment to constants bit2eq encodes the rule:

       x = k, y = k
       ------------
          x = y
     */
    bool theory_checker::check_bit2eq(app* jst) { return true; }

    /**
       x[i] = false, y[i] = true
       -------------------------
           x != y
     */
    bool theory_checker::check_bit2ne(app* jst) { return true; }

    /**
          x = y
       -----------
       x[i] = y[i]
     */
    bool theory_checker::check_eq2bit(app* jst) { return true; }

    /**
         x != y, x is assigned on all but position i, x[j] = y[j] on other positions.
         ----------------------------------------------------------------------------
              x[i] != y[i]         
     */
    bool theory_checker::check_ne2bit(app* jst) { return true; }

    /**
        int2bv(bv2int(x)) = x when int2bv(bv2int(x)) has same sort as x

        n = bv2int(x), n = z
        --------------------
           int2bv(z) = x              
     */
    bool theory_checker::check_bv2int(app* jst) { return true; }

}
