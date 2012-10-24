/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    atom2bool_var.h

Abstract:

    The mapping between SAT boolean variables and atoms

Author:

    Leonardo (leonardo) 2011-10-25

Notes:

--*/
#ifndef _ATOM2BOOL_VAR_H_
#define _ATOM2BOOL_VAR_H_

#include"expr2var.h"
#include"sat_types.h"

/**
   \brief Mapping from atoms into SAT boolean variables.
*/
class atom2bool_var : public expr2var {
public:
    atom2bool_var(ast_manager & m):expr2var(m) {}
    void insert(expr * n, sat::bool_var v) { expr2var::insert(n, v); }
    sat::bool_var to_bool_var(expr * n) const;
    void mk_inv(expr_ref_vector & lit2expr) const;
    // return true if the mapping contains uninterpreted atoms.
    bool interpreted_atoms() const { return expr2var::interpreted_vars(); }
};

class goal;

void collect_boolean_interface(goal const & g, obj_hashtable<expr> & r);
void collect_boolean_interface(ast_manager & m, unsigned num, expr * const * fs, obj_hashtable<expr> & r);

#endif
