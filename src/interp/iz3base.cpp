/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    iz3base.cpp

Abstract:

   Base class for interpolators. Includes an AST manager and a scoping
   object as bases.

Author:

    Ken McMillan (kenmcmil)

Revision History:

--*/

#ifdef _WINDOWS
#pragma warning(disable:4996)
#pragma warning(disable:4800)
#pragma warning(disable:4267)
#pragma warning(disable:4101)
#endif

#include "iz3base.h"
#include <stdio.h>
#include <fstream>
#include <iostream>
#include <ostream>
#include "solver.h"
#include "../smt/smt_solver.h"


using namespace stl_ext;


iz3base::range &iz3base::ast_range(ast t){
  return ast_ranges_hash[t].rng;
}

iz3base::range &iz3base::sym_range(symb d){
  return sym_range_hash[d];
}

void iz3base::add_frame_range(int frame, ast t){
  range &rng = ast_range(t);
  if(!in_range(frame,rng)){
    range_add(frame,rng);
    for(int i = 0, n = num_args(t); i < n; ++i)
      add_frame_range(frame,arg(t,i));
    if(op(t) == Uninterpreted)
      range_add(frame,sym_range(sym(t)));
  }
}

#if 1
iz3base::range &iz3base::ast_scope(ast t){
  ranges &rngs = ast_ranges_hash[t];
  range &rng = rngs.scp;
  if(!rngs.scope_computed){ // not computed yet
    rng = range_full();
    for(int i = 0, n = num_args(t); i < n; ++i)
      rng = range_glb(rng,ast_scope(arg(t,i)));
    if(op(t) == Uninterpreted)
      if(parents.empty() || num_args(t) == 0) // in tree mode, all function syms are global
	rng = range_glb(rng,sym_range(sym(t)));
    rngs.scope_computed = true;
  }
  return rng;
}
#else
iz3base::range &iz3base::ast_scope(ast t){
  ranges &rngs = ast_ranges_hash[t];
  if(rngs.scope_computed) return rngs.scp;
  range rng = range_full();
  for(int i = 0, n = num_args(t); i < n; ++i)
    rng = range_glb(rng,ast_scope(arg(t,i)));
  if(op(t) == Uninterpreted)
    if(parents.empty() || num_args(t) == 0) // in tree mode, all function syms are global
      rng = range_glb(rng,sym_range(sym(t)));
  rngs = ast_ranges_hash[t];
  rngs.scope_computed = true;
  rngs.scp = rng;
  return rngs.scp;
}
#endif

void iz3base::print(const std::string &filename){
  ast t = make(And,cnsts);
  std::ofstream f(filename.c_str());
  print_sat_problem(f,t);
  f.close();
}


void iz3base::gather_conjuncts_rec(ast n, std::vector<ast> &conjuncts, stl_ext::hash_set<ast> &memo){
  if(memo.find(n) == memo.end()){
    memo.insert(n);
    if(op(n) == And){
      int nargs = num_args(n);
      for(int i = 0; i < nargs; i++)
	gather_conjuncts_rec(arg(n,i),conjuncts,memo);
    }
    else
      conjuncts.push_back(n);
  }
}

void iz3base::gather_conjuncts(ast n, std::vector<ast> &conjuncts){
  hash_set<ast> memo;
  gather_conjuncts_rec(n,conjuncts,memo);
}

bool iz3base::is_literal(ast n){
  if(is_not(n))n = arg(n,0);
  if(is_true(n) || is_false(n)) return false;
  if(op(n) == And) return false;
  return true;
}

iz3base::ast iz3base::simplify_and(std::vector<ast> &conjuncts){
  hash_set<ast> memo;
  for(unsigned i = 0; i < conjuncts.size(); i++){
    if(is_false(conjuncts[i]))
      return conjuncts[i];
    if(is_true(conjuncts[i]) || memo.find(conjuncts[i]) != memo.end()){
      std::swap(conjuncts[i],conjuncts.back());
      conjuncts.pop_back();
    }
    else if(memo.find(mk_not(conjuncts[i])) != memo.end())
      return mk_false(); // contradiction!
    else
      memo.insert(conjuncts[i]);
  }
  if(conjuncts.empty())return mk_true();
  return make(And,conjuncts);
}

iz3base::ast iz3base::simplify_with_lit_rec(ast n, ast lit, stl_ext::hash_map<ast,ast> &memo, int depth){
  if(is_not(n))return mk_not(simplify_with_lit_rec(mk_not(n),lit,memo,depth));
  if(n == lit) return mk_true();
  ast not_lit = mk_not(lit);
  if(n == not_lit) return mk_false();
  if(op(n) != And || depth <= 0) return n;
  std::pair<ast,ast> foo(n,ast());
  std::pair<hash_map<ast,ast>::iterator,bool> bar = memo.insert(foo);
  ast &res = bar.first->second;
  if(!bar.second) return res;
  int nargs = num_args(n);
  std::vector<ast> args(nargs);
  for(int i = 0; i < nargs; i++)
    args[i] = simplify_with_lit_rec(arg(n,i),lit,memo,depth-1);
  res = simplify_and(args);
  return res;
}

iz3base::ast iz3base::simplify_with_lit(ast n, ast lit){
  hash_map<ast,ast> memo;
  return simplify_with_lit_rec(n,lit,memo,1);
}

iz3base::ast iz3base::simplify(ast n){
  if(is_not(n)) return mk_not(simplify(mk_not(n)));
  std::pair<ast,ast> memo_obj(n,ast());
  std::pair<hash_map<ast,ast>::iterator,bool> memo = simplify_memo.insert(memo_obj);
  ast &res = memo.first->second;
  if(!memo.second) return res;
  switch(op(n)){
  case And: {
    std::vector<ast> conjuncts;
    gather_conjuncts(n,conjuncts);
    for(unsigned i = 0; i < conjuncts.size(); i++)
      conjuncts[i] = simplify(conjuncts[i]);
#if 0
    for(unsigned i = 0; i < conjuncts.size(); i++)
      if(is_literal(conjuncts[i]))
	for(unsigned j = 0; j < conjuncts.size(); j++)
	  if(j != i)
	    conjuncts[j] = simplify_with_lit(conjuncts[j],conjuncts[i]);
#endif
    res = simplify_and(conjuncts);
  }
    break;
  case Equal: {
    ast x = arg(n,0);
    ast y = arg(n,1);
    if(ast_id(x) > ast_id(y))
      std::swap(x,y);
    res = make(Equal,x,y);
    break;
  }
  default:
    res = n;
  }
  return res;
}

void iz3base::initialize(const std::vector<ast> &_parts, const std::vector<int> &_parents, const std::vector<ast> &_theory){
  cnsts = _parts;
  theory = _theory;
  for(unsigned i = 0; i < cnsts.size(); i++)
    add_frame_range(i, cnsts[i]);
  for(unsigned i = 0; i < _theory.size(); i++){
    add_frame_range(SHRT_MIN, _theory[i]);
    add_frame_range(SHRT_MAX, _theory[i]);
  }
  for(unsigned i = 0; i < cnsts.size(); i++)
    frame_map[cnsts[i]] = i;
  for(unsigned i = 0; i < theory.size(); i++)
    frame_map[theory[i]] = INT_MAX;
}

void iz3base::initialize(const std::vector<std::vector<ast> > &_parts, const std::vector<int> &_parents, const std::vector<ast> &_theory){
  cnsts.resize(_parts.size());
  theory = _theory;
  for(unsigned i = 0; i < _parts.size(); i++)
    for(unsigned j = 0; j < _parts[i].size(); j++){
      cnsts[i] = make(And,_parts[i]);
      add_frame_range(i, _parts[i][j]);
      frame_map[_parts[i][j]] = i;
    }  
  for(unsigned i = 0; i < _theory.size(); i++){
    add_frame_range(SHRT_MIN, _theory[i]);
    add_frame_range(SHRT_MAX, _theory[i]);
    frame_map[theory[i]] = INT_MAX;
  }
}

void iz3base::check_interp(const std::vector<ast> &itps, std::vector<ast> &theory){
#if 0
  Z3_config config = Z3_mk_config();
  Z3_context vctx = Z3_mk_context(config);
  int frames = cnsts.size();
  std::vector<Z3_ast> foocnsts(cnsts);
  for(unsigned i = 0; i < frames; i++)
    foocnsts[i] = Z3_mk_implies(ctx,Z3_mk_true(ctx),cnsts[i]);
  Z3_write_interpolation_problem(ctx,frames,&foocnsts[0],0, "temp_lemma.smt", theory.size(), &theory[0]);
  int vframes,*vparents;
  Z3_ast *vcnsts;
  const char *verror;
  bool ok = Z3_read_interpolation_problem(vctx,&vframes,&vcnsts,0,"temp_lemma.smt",&verror);
  assert(ok);
  std::vector<Z3_ast> vvcnsts(vframes);
  std::copy(vcnsts,vcnsts+vframes,vvcnsts.begin());
  std::vector<Z3_ast> vitps(itps.size());
  for(unsigned i = 0; i < itps.size(); i++)
    vitps[i] = Z3_mk_implies(ctx,Z3_mk_true(ctx),itps[i]);
  Z3_write_interpolation_problem(ctx,itps.size(),&vitps[0],0,"temp_interp.smt");
  int iframes,*iparents;
  Z3_ast *icnsts;
  const char *ierror;
  ok = Z3_read_interpolation_problem(vctx,&iframes,&icnsts,0,"temp_interp.smt",&ierror);
  assert(ok);
  const char *error = 0;
  bool iok = Z3_check_interpolant(vctx, frames, &vvcnsts[0], parents.size() ? &parents[0] : 0, icnsts, &error);
  assert(iok);
#endif
}

bool iz3base::is_sat(const std::vector<ast> &q, ast &_proof, std::vector<ast> &vars){

  params_ref p;
  p.set_bool("proof", true); // this is currently useless
  p.set_bool("model", true); 
  p.set_bool("unsat_core", true); 
  scoped_ptr<solver_factory> sf = mk_smt_solver_factory();
  ::solver *m_solver = (*sf)(m(), p, true, true, true, ::symbol::null);
  ::solver &s = *m_solver;

  for(unsigned i = 0; i < q.size(); i++)
    s.assert_expr(to_expr(q[i].raw()));
  lbool res = s.check_sat(0,0);
  if(res == l_false){
    ::ast *proof = s.get_proof();
    _proof = cook(proof);
  }
  else if(vars.size()) {
    model_ref(_m);
    s.get_model(_m);
    for(unsigned i = 0; i < vars.size(); i++){
      expr_ref r(m());
      _m.get()->eval(to_expr(vars[i].raw()),r,true);
      vars[i] = cook(r.get());
    }
  }
  dealloc(m_solver);
  return res != l_false;
}


void iz3base::find_children(const stl_ext::hash_set<ast> &cnsts_set,
			    const ast &tree,
			    std::vector<ast> &cnsts,
			    std::vector<int> &parents,
			    std::vector<ast> &conjuncts,
			    std::vector<int> &children,
			    std::vector<int> &pos_map,
			    bool merge
			    ){
  std::vector<int> my_children;
  std::vector<ast> my_conjuncts;
  if(op(tree) == Interp){ // if we've hit an interpolation position...
    find_children(cnsts_set,arg(tree,0),cnsts,parents,my_conjuncts,my_children,pos_map,merge);
    if(my_conjuncts.empty()) 
      my_conjuncts.push_back(mk_true()); // need at least one conjunct
    int root = cnsts.size() + my_conjuncts.size() - 1;
    for(unsigned i = 0; i < my_conjuncts.size(); i++){
      parents.push_back(root);
      cnsts.push_back(my_conjuncts[i]);
    }
    for(unsigned i = 0; i < my_children.size(); i++)
      parents[my_children[i]] = root;
    children.push_back(root);
    pos_map.push_back(root);
  }
  else {
    if(op(tree) == And){
      int nargs = num_args(tree);
      for(int i = 0; i < nargs; i++)
	find_children(cnsts_set,arg(tree,i),cnsts,parents,my_conjuncts,my_children,pos_map,merge);
    }
    if(cnsts_set.find(tree) != cnsts_set.end()){
      if(merge && !my_conjuncts.empty())
	my_conjuncts.back() = mk_and(my_conjuncts.back(),tree);
      else
	my_conjuncts.push_back(tree);
    }
    for(unsigned i = 0; i < my_children.size(); i++)
      children.push_back(my_children[i]);
    for(unsigned i = 0; i < my_conjuncts.size(); i++)
      conjuncts.push_back(my_conjuncts[i]);
  }
}
    
void iz3base::to_parents_vec_representation(const std::vector<ast> &_cnsts,
					    const ast &tree,
					    std::vector<ast> &cnsts,
					    std::vector<int> &parents,
					    std::vector<ast> &theory,
					    std::vector<int> &pos_map,
					    bool merge
					    ){
  std::vector<int> my_children;
  std::vector<ast> my_conjuncts;
  hash_set<ast> cnsts_set;
  for(unsigned i = 0; i < _cnsts.size(); i++)
    cnsts_set.insert(_cnsts[i]);
  ast _tree = (op(tree) != Interp) ? make(Interp,tree) : tree;
  find_children(cnsts_set,_tree,cnsts,parents,my_conjuncts,my_children,pos_map,merge);
  if(op(tree) != Interp) pos_map.pop_back();
  parents[parents.size()-1] = SHRT_MAX;
    
  // rest of the constraints are the background theory
    
  hash_set<ast> used_set;
  for(unsigned i = 0; i < cnsts.size(); i++)
    used_set.insert(cnsts[i]);
  for(unsigned i = 0; i < _cnsts.size(); i++)
    if(used_set.find(_cnsts[i]) == used_set.end())
      theory.push_back(_cnsts[i]);
}

