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

namespace hash_space {
  template <>
    class hash<func_decl *> {
  public:
    size_t operator()(func_decl * const &s) const {
      return (size_t) s;
    }
  };
}

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

  iz3base(const iz3mgr& other,
	  const std::vector<std::vector<ast> > &_cnsts,
	 const std::vector<int> &_parents,
	 const std::vector<ast> &_theory)
   : iz3mgr(other), scopes(_parents)  {
    initialize(_cnsts,_parents,_theory);
    weak = false;
  }

  iz3base(const iz3mgr& other)
   : iz3mgr(other), scopes()  {
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
  bool is_sat(const std::vector<ast> &consts, ast &_proof, std::vector<ast> &vars);

  /** Interpolator for clauses, to be implemented */
  virtual void interpolate_clause(std::vector<ast> &lits, std::vector<ast> &itps){
    throw "no interpolator";
  }

  ast get_proof_check_assump(range &rng){
    std::vector<ast> cs(theory);
    cs.push_back(cnsts[rng.hi]);
    return make(And,cs);
  }
  
  int frame_of_assertion(const ast &ass){
    stl_ext::hash_map<ast,int>::iterator it = frame_map.find(ass);
    if(it == frame_map.end())
      throw "unknown assertion";
    return it->second;
  }
  

  void to_parents_vec_representation(const std::vector<ast> &_cnsts,
				     const ast &tree,
				     std::vector<ast> &cnsts,
				     std::vector<int> &parents,
				     std::vector<ast> &theory,
				     std::vector<int> &pos_map,
				     bool merge = false
				   );

 protected:
  std::vector<ast> cnsts;
  std::vector<ast> theory;

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
  stl_ext::hash_map<ast,int> frame_map;                      // map assertions to frames

  // int frames;                               // number of frames

 protected:
  void add_frame_range(int frame, ast t);

 private:
  void initialize(const std::vector<ast> &_parts, const std::vector<int> &_parents, const std::vector<ast> &_theory);

  void initialize(const std::vector<std::vector<ast> > &_parts, const std::vector<int> &_parents, const std::vector<ast> &_theory);

  bool is_literal(ast n);
  void gather_conjuncts_rec(ast n, std::vector<ast> &conjuncts, stl_ext::hash_set<ast> &memo);
  void gather_conjuncts(ast n, std::vector<ast> &conjuncts);
  ast simplify_and(std::vector<ast> &conjuncts);
  ast simplify_with_lit_rec(ast n, ast lit, stl_ext::hash_map<ast,ast> &memo, int depth);
  ast simplify_with_lit(ast n, ast lit);  
  void find_children(const stl_ext::hash_set<ast> &cnsts_set,
		     const ast &tree,
		     std::vector<ast> &cnsts,
		     std::vector<int> &parents,
		     std::vector<ast> &conjuncts,
		     std::vector<int> &children,
		     std::vector<int> &pos_map,
		     bool merge
		     );
  bool weak;

};



#endif
