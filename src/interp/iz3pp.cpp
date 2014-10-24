/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

   iz3pp.cpp

Abstract:

   Pretty-print interpolation problems

Author:

    Ken McMillan (kenmcmil)

Revision History:

--*/

/* Copyright 2011 Microsoft Research. */
#include <assert.h>
#include <algorithm>
#include <stdio.h>
#include <fstream>
#include <sstream>
#include <set>
#include <iostream>

#include "iz3mgr.h"
#include "iz3pp.h"
#include "func_decl_dependencies.h"
#include"for_each_expr.h"
#include"ast_smt_pp.h"
#include"ast_smt2_pp.h"
#include"expr_functors.h"
#include"expr_abstract.h"


using namespace stl_ext;

// We promise not to use this for hash_map with range destructor
namespace stl_ext {
  template <>
    class hash<expr *> {
  public:
    size_t operator()(const expr *p) const {
      return (size_t) p;
    }
  };
}


// TBD: algebraic data-types declarations will not be printed.
class free_func_visitor {
  ast_manager& m;
  func_decl_set m_funcs;
  obj_hashtable<class sort> m_sorts;
public:        
  free_func_visitor(ast_manager& m): m(m) {}
  void operator()(var * n)        { }
  void operator()(app * n)        { 
    m_funcs.insert(n->get_decl()); 
    class sort* s = m.get_sort(n);
    if (s->get_family_id() == null_family_id) {
      m_sorts.insert(s);
    }
  }
  void operator()(quantifier * n) { }
  func_decl_set& funcs() { return m_funcs; }
  obj_hashtable<class sort>& sorts() { return m_sorts; }
};

class iz3pp_helper : public iz3mgr {
public:
  
  void print_tree(const ast &tree, hash_map<expr*,symbol> &cnames, std::ostream &out){
    hash_map<expr*,symbol>::iterator foo = cnames.find(to_expr(tree.raw()));
    if(foo != cnames.end()){
      symbol nm = foo->second;
      if (is_smt2_quoted_symbol(nm)) {
	out << mk_smt2_quoted_symbol(nm);
      }
      else {
	out << nm;
      }
    }
    else if(op(tree) == And){
      out << "(and";
      int nargs = num_args(tree);
      for(int i = 0; i < nargs; i++){
	out << " ";
	print_tree(arg(tree,i), cnames, out);
      }
      out << ")";
    }
    else if(op(tree) == Interp){
      out << "(interp ";
      print_tree(arg(tree,0), cnames, out);
      out << ")";
    }
    else throw iz3pp_bad_tree();
  }


  iz3pp_helper(ast_manager &_m_manager)
    : iz3mgr(_m_manager) {}
};

void iz3pp(ast_manager &m,
	   const ptr_vector<expr> &cnsts_vec,
	   expr *tree,
	   std::ostream& out) {

  unsigned sz = cnsts_vec.size();
  expr* const* cnsts = &cnsts_vec[0];

  out << "(set-option :produce-interpolants true)\n";

  free_func_visitor visitor(m);
  expr_mark visited;
  bool print_low_level = true; // m_params.print_low_level_smt2();
  
#define PP(_e_) if (print_low_level) out << mk_smt_pp(_e_, m); else ast_smt2_pp(out, _e_, env);
  
  smt2_pp_environment_dbg env(m);

  for (unsigned i = 0; i < sz; ++i) {
    expr* e = cnsts[i];
    for_each_expr(visitor, visited, e);
  }
  
  // name all the constraints
  hash_map<expr *, symbol> cnames;
  int ctr = 1;
  for(unsigned i = 0; i < sz; i++){
    symbol nm;
    std::ostringstream s;
    s << "f!" << (ctr++);
    cnames[cnsts[i]] = symbol(s.str().c_str());
  }
  
  func_decl_set &funcs = visitor.funcs();
  func_decl_set::iterator it  = funcs.begin(), end = funcs.end();
  
  obj_hashtable<class sort>& sorts = visitor.sorts();
  obj_hashtable<class sort>::iterator sit = sorts.begin(), send = sorts.end();
  

  
  for (; sit != send; ++sit) {
    PP(*sit);
  }
  
  for (; it != end; ++it) {
    func_decl* f = *it;
    if(f->get_family_id() == null_family_id){
      PP(f);
      out << "\n";
    }
  }
  
  for (unsigned i = 0; i < sz; ++i) {            
    out << "(assert ";
    expr* r = cnsts[i];
    symbol nm = cnames[r];
    out << "(! ";
    PP(r);
    out << " :named ";
    if (is_smt2_quoted_symbol(nm)) {
      out << mk_smt2_quoted_symbol(nm);
    }
    else {
      out << nm;
    }
    out << ")";
    out << ")\n";
  }
  out << "(check-sat)\n";
  out << "(get-interpolant ";
  iz3pp_helper pp(m);
  pp.print_tree(pp.cook(tree),cnames,out);
  out << ")\n";
}


