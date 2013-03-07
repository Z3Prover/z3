/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    iz3base.h

Abstract:

   Base class for interpolators. Includes an AST manager and a scoping
   object as bases.

Author:

    Ken McMillan (kenmcmil)

Revision History:

--*/

#ifndef IZ3BASE_H
#define IZ3BASE_H

#include "iz3mgr.h"
#include "iz3scopes.h"

/* Base class for interpolators. Includes an AST manager and a scoping
   object as bases. */
 
class iz3base : public iz3mgr, public scopes {

 public:

  /** Get the range in which an expression occurs. This is the
      smallest subtree containing all occurrences of the
      expression. */
  range &ast_range(ast);

  /** Get the scope of an expression. This is the set of tree nodes in
      which all of the expression's symbols are in scope. */
  range &ast_scope(ast);

  /** Get the range of a symbol. This is the smallest subtree containing
      all occurrences of the symbol. */ 
  range &sym_range(symb);

  /** Is an expression local (in scope in some frame)? */

  bool is_local(ast node){
    return !range_is_empty(ast_scope(node));
  }

  /** Simplify an expression */

  ast simplify(ast);

  /** Constructor */

  iz3base(ast_manager &_m_manager,
	 const std::vector<ast> &_cnsts,
	 const std::vector<int> &_parents,
	 const std::vector<ast> &_theory)
    : iz3mgr(_m_manager), scopes(_parents)  {
    initialize(_cnsts,_parents,_theory);
    weak = false;
  }

 iz3base(const iz3mgr& other,
	 const std::vector<ast> &_cnsts,
	 const std::vector<int> &_parents,
	 const std::vector<ast> &_theory)
   : iz3mgr(other), scopes(_parents)  {
    initialize(_cnsts,_parents,_theory);
    weak = false;
  }

  /* Set our options */
  void set_option(const std::string &name, const std::string &value){
    if(name == "weak" && value == "1") weak = true;
  }
  
  /* Are we doing weak interpolants? */
  bool weak_mode(){return weak;}

  /** Print interpolation problem to an SMTLIB format file */
  void print(const std::string &filename);

  /** Check correctness of a solutino to this problem. */
  void check_interp(const std::vector<ast> &itps, std::vector<ast> &theory);

  /** For convenience -- is this formula SAT? */
  bool is_sat(ast);

  /** Interpolator for clauses, to be implemented */
  virtual void interpolate_clause(std::vector<ast> &lits, std::vector<ast> &itps){
    throw "no interpolator";
  }

  ast get_proof_check_assump(range &rng){
    std::vector<ast> cs(theory);
    cs.push_back(cnsts[rng.hi]);
    return make(And,cs);
  }
  
 private:

  struct ranges {
    range rng;
    range scp;
    bool scope_computed;
    ranges(){scope_computed = false;}
  };

  stl_ext::hash_map<symb,range> sym_range_hash;
  stl_ext::hash_map<ast,ranges> ast_ranges_hash;
  stl_ext::hash_map<ast,ast> simplify_memo;


  void add_frame_range(int frame, ast t);

  void initialize(const std::vector<ast> &_parts, const std::vector<int> &_parents, const std::vector<ast> &_theory);

  std::vector<ast> cnsts;
  std::vector<ast> theory;

  bool is_literal(ast n);
  void gather_conjuncts_rec(ast n, std::vector<ast> &conjuncts, stl_ext::hash_set<ast> &memo);
  void gather_conjuncts(ast n, std::vector<ast> &conjuncts);
  ast simplify_and(std::vector<ast> &conjuncts);
  ast simplify_with_lit_rec(ast n, ast lit, stl_ext::hash_map<ast,ast> &memo, int depth);
  ast simplify_with_lit(ast n, ast lit);  

  bool weak;

};





#endif
