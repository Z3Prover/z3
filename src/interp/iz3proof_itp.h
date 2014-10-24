/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    iz3proof.h

Abstract:

   This class defines a simple interpolating proof system.

Author:

    Ken McMillan (kenmcmil)

Revision History:

--*/

#ifndef IZ3PROOF_ITP_H
#define IZ3PROOF_ITP_H

#include <set>

#include "iz3base.h"
#include "iz3secondary.h"

// #define CHECK_PROOFS

/** This class defines a simple proof system.

    As opposed to iz3proof, this class directly computes interpolants,
    so the proof representation is just the interpolant itself.
    
 */

class iz3proof_itp : public iz3mgr {
 public:

  /** Enumeration of proof rules. */
  enum rule {Resolution,Assumption,Hypothesis,Theory,Axiom,Contra,Lemma,Reflexivity,Symmetry,Transitivity,Congruence,EqContra};

  /** Interface to prover. */
  typedef iz3base prover;

  /** Ast type. */
  typedef prover::ast ast;

  /** The type of proof nodes (just interpolants). */
  typedef ast node;

  /** Object thrown in case of a proof error. */
  struct proof_error {};


  /** Make a resolution node with given pivot literal and premises.
      The conclusion of premise1 should contain the negation of the
      pivot literal, while the conclusion of premise2 should containe the
      pivot literal.
   */
  virtual node make_resolution(ast pivot, const std::vector<ast> &conc, node premise1, node premise2) = 0;

  /** Make an assumption node. The given clause is assumed in the given frame. */
  virtual node make_assumption(int frame, const std::vector<ast> &assumption) = 0;

  /** Make a hypothesis node. If phi is the hypothesis, this is
      effectively phi |- phi. */
  virtual node make_hypothesis(const ast &hypothesis) = 0;

  /** Make an axiom node. The conclusion must be an instance of an axiom. */
  virtual node make_axiom(const std::vector<ast> &conclusion) = 0;

  /** Make an axiom node. The conclusion must be an instance of an axiom. Localize axiom instance to range*/
  virtual node make_axiom(const std::vector<ast> &conclusion, prover::range) = 0;

  /** Make a Contra node. This rule takes a derivation of the form
     Gamma |- False and produces |- \/~Gamma. */

  virtual node make_contra(node prem, const std::vector<ast> &conclusion) = 0;

  /** Make a Reflexivity node. This rule produces |- x = x */
  
  virtual node make_reflexivity(ast con) = 0;
  
  /** Make a Symmetry node. This takes a derivation of |- x = y and
      produces | y = x */

  virtual node make_symmetry(ast con, const ast &premcon, node prem) = 0;

  /** Make a transitivity node. This takes derivations of |- x = y
      and |- y = z produces | x = z */

  virtual node make_transitivity(const ast &x, const ast &y, const ast &z, node prem1, node prem2) = 0;
  
  /** Make a congruence node. This takes a derivation of |- x_i = y_i
      and produces |- f(...x_i,...) = f(...,y_i,...) */
  
  virtual node make_congruence(const ast &xi_eq_yi, const ast &con, const ast &prem1) = 0;

  /** Make a congruence node. This takes derivations of |- x_i1 = y_i1, |- x_i2 = y_i2,...
      and produces |- f(...x_i1...x_i2...) = f(...y_i1...y_i2...) */

  virtual node make_congruence(const std::vector<ast> &xi_eq_yi, const ast &con, const std::vector<ast> &prems) = 0;

  /** Make a modus-ponens node. This takes derivations of |- x
      and |- x = y and produces |- y */
  
  virtual node make_mp(const ast &x_eq_y, const ast &prem1, const ast &prem2) = 0;

  /** Make a farkas proof node. */

  virtual node make_farkas(ast con, const std::vector<node> &prems, const std::vector<ast> &prem_cons, const std::vector<ast> &coeffs) = 0;

  /* Make an axiom instance of the form |- x<=y, y<= x -> x =y */
  virtual node make_leq2eq(ast x, ast y, const ast &xleqy, const ast &yleqx) = 0;

  /* Make an axiom instance of the form |- x = y -> x <= y */
  virtual node make_eq2leq(ast x, ast y, const ast &xeqy) = 0;

  /* Make an inference of the form t <= c |- t/d <= floor(c/d) where t
     is an affine term divisble by d and c is an integer constant */
  virtual node make_cut_rule(const ast &tleqc, const ast &d, const ast &con, const ast &prem) = 0;

  /* Return an interpolant from a proof of false */
  virtual ast interpolate(const node &pf) = 0;

  /** Create proof object to construct an interpolant. */
  static iz3proof_itp *create(prover *p, const prover::range &r, bool _weak);

 protected:
  iz3proof_itp(iz3mgr &m)
    : iz3mgr(m)
  {
  }

 public:
  virtual ~iz3proof_itp(){
  }
};

#endif
