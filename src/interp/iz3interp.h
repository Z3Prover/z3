/*++
  Copyright (c) 2011 Microsoft Corporation

  Module Name:

  iz3interp.h

  Abstract:

  Interpolation based on proof translation.

  Author:

  Ken McMillan (kenmcmil)

  Revision History:

  --*/

#ifndef IZ3_INTERP_H
#define IZ3_INTERP_H

#include "iz3hash.h"
#include "iz3exception.h"
#include "solver.h"

class iz3base;

struct interpolation_options_struct {
    stl_ext::hash_map<std::string,std::string> map;
public:
    void set(const std::string &name, const std::string &value){
        map[name] = value;
    }
    void apply(iz3base &b);
};

/** This object is thrown if a tree interpolation problem is mal-formed */
struct iz3_bad_tree: public iz3_exception {
    iz3_bad_tree(): iz3_exception("iz3_bad_tree") {}
};

/** This object is thrown when iz3 fails due to an incompleteness in
    the secondary solver. */
struct iz3_incompleteness: public iz3_exception {
    iz3_incompleteness(): iz3_exception("iz3_incompleteness") {}
};

// This is thrown if there is some bug in the
// interpolation procedure
class interpolation_failure : public default_exception {
 public:
 interpolation_failure(const char *msg)
     : default_exception(msg)
    {
    }
};

// This is thrown if we cannot derive an interpolant from a proof
// because it contains unsupported theories or if the proof contains
// errors
class interpolation_error : public default_exception {
 public:
 interpolation_error()
     : default_exception("theory not supported by interpolation or bad proof" )
        {
        }
};

typedef interpolation_options_struct *interpolation_options;

/* Compute an interpolant from a proof. This version uses the parents vector
   representation, for compatibility with the old API. */

void iz3interpolate(ast_manager &_m_manager,
		    ast *proof,
		    const ptr_vector<ast> &cnsts,
		    const ::vector<int> &parents,
		    ptr_vector<ast> &interps,
		    const ptr_vector<ast> &theory,
		    interpolation_options_struct * options = 0);

/* Same as above, but each constraint is a vector of formulas. */

void iz3interpolate(ast_manager &_m_manager,
		    ast *proof,
		    const vector<ptr_vector<ast> > &cnsts,
		    const ::vector<int> &parents,
		    ptr_vector<ast> &interps,
		    const ptr_vector<ast> &theory,
		    interpolation_options_struct * options = 0);

/* Compute an interpolant from a proof. This version uses the ast
   representation, for compatibility with the new API. Here, cnsts is
   a vector of all the assertions in the proof. This can be
   over-approximated by the set of all assertions in the
   solver. However, if it is empty it will be reconstructed from the
   proof, so it can be considered a hint.  */

void iz3interpolate(ast_manager &_m_manager,
		    ast *proof,
		    const ptr_vector<ast> &cnsts,
		    ast *tree,
		    ptr_vector<ast> &interps,
		    interpolation_options_struct * options);


/* Compute an interpolant from an ast representing an interpolation
   problem, if unsat, else return a model (if enabled). Uses the
   given solver to produce the proof/model. Also returns a vector
   of the constraints in the problem, helpful for checking correctness.
*/

lbool iz3interpolate(ast_manager &_m_manager,
		     solver &s,
		     ast *tree,
		     ptr_vector<ast> &cnsts,
		     ptr_vector<ast> &interps,
		     model_ref &m,
		     interpolation_options_struct * options);


#endif
