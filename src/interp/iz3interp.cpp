/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

   iz3interp.cpp

Abstract:

   Interpolation based on proof translation.

Author:

    Ken McMillan (kenmcmil)

Revision History:

--*/

/* Copyright 2011 Microsoft Research. */

#ifdef _WINDOWS
#pragma warning(disable:4996)
#pragma warning(disable:4800)
#pragma warning(disable:4267)
#pragma warning(disable:4101)
#endif

#include <assert.h>
#include <algorithm>
#include <stdio.h>
#include <fstream>
#include <sstream>
#include <set>
#include <iostream>

#include "iz3profiling.h"
#include "iz3translate.h"
#include "iz3foci.h"
#include "iz3proof.h"
#include "iz3hash.h"
#include "iz3interp.h"

#include"scoped_proof.h"


using namespace stl_ext;



#if 1

struct frame_reducer : public iz3mgr {
  
  int frames;
  hash_map<ast,int> frame_map;
  std::vector<int> assertions_map;
  std::vector<int> orig_parents_copy;
  std::vector<bool> used_frames;


  frame_reducer(const iz3mgr &other)
    : iz3mgr(other) {}

  void get_proof_assumptions_rec(z3pf proof, hash_set<ast> &memo, std::vector<bool> &used_frames){
    if(memo.find(proof) != memo.end())return;
    memo.insert(proof);
    pfrule dk = pr(proof);
    if(dk == PR_ASSERTED){
      ast con = conc(proof);
      if(frame_map.find(con) != frame_map.end()){  // false for theory facts
        int frame = frame_map[con];
        used_frames[frame] = true;
      }
    }
    else {
      unsigned nprems = num_prems(proof);
      for(unsigned i = 0; i < nprems; i++){
	z3pf arg = prem(proof,i);
	get_proof_assumptions_rec(arg,memo,used_frames);
      }
    }
  }
  
  void get_frames(const std::vector<std::vector<ast> >&z3_preds, 
		  const std::vector<int> &orig_parents,
		  std::vector<std::vector<ast> >&assertions,
		  std::vector<int> &parents,
		  z3pf proof){
    frames = z3_preds.size();
    orig_parents_copy = orig_parents;
    for(unsigned i = 0; i < z3_preds.size(); i++)
      for(unsigned j = 0; j < z3_preds[i].size(); j++)
	frame_map[z3_preds[i][j]] = i;
    used_frames.resize(frames);
    hash_set<ast> memo;
    get_proof_assumptions_rec(proof,memo,used_frames);
    std::vector<int> assertions_back_map(frames);

    // if multiple children of a tree node are used, we can't delete it
    std::vector<int> used_children; 
    for(int i = 0; i < frames; i++)
      used_children.push_back(0);
    for(int i = 0; i < frames; i++)
      if(orig_parents[i] != SHRT_MAX)
	if(used_frames[i] || used_children[i]){
	  if(used_children[i] > 1)
	    used_frames[i] = true;
	  used_children[orig_parents[i]]++;
	}

    for(unsigned i = 0; i < z3_preds.size(); i++)
      if(used_frames[i] || i == z3_preds.size() - 1){
	assertions.push_back(z3_preds[i]);
	assertions_map.push_back(i);
        assertions_back_map[i] = assertions.size() - 1;
      }
    
    if(orig_parents.size()){
      parents.resize(assertions.size());
      for(unsigned i = 0; i < assertions.size(); i++){
	int p = orig_parents[assertions_map[i]];
	while(p != SHRT_MAX && !used_frames[p])
	  p = orig_parents[p];
	parents[i] = p == SHRT_MAX ? p : assertions_back_map[p];
      }
    }

    // std::cout << "used frames = " << frames << "\n";
  }

  void fix_interpolants(std::vector<ast> &interpolants){
    std::vector<ast> unfixed = interpolants;
    interpolants.resize(frames - 1);
    for(int i = 0; i < frames - 1; i++)
      interpolants[i] = mk_true();
    for(unsigned i = 0; i < unfixed.size(); i++)
      interpolants[assertions_map[i]] = unfixed[i];
    for(int i = 0; i < frames-2; i++){
      int p = orig_parents_copy.size() == 0 ? i+1 : orig_parents_copy[i];
      if(p < frames - 1 && !used_frames[p])
        interpolants[p] = mk_and(interpolants[i],interpolants[p]);
    }
  }
};

#else
struct frame_reducer {
  


  frame_reducer(context _ctx){
  }

  void get_frames(const std::vector<ast> &z3_preds, 
		  const std::vector<int> &orig_parents,
		  std::vector<ast> &assertions,
		  std::vector<int> &parents,
		  ast proof){
    assertions = z3_preds;
    parents = orig_parents;
  }

  void fix_interpolants(std::vector<ast> &interpolants){
  }
};

#endif  


#if 0
static lbool test_secondary(context ctx,
			 int num, 
			 ast *cnsts,
			 ast *interps,
			 int *parents = 0
			 ){
      iz3secondary *sp = iz3foci::create(ctx,num,parents);
      std::vector<ast> frames(num), interpolants(num-1);
      std::copy(cnsts,cnsts+num,frames.begin());
      int res = sp->interpolate(frames,interpolants);
      if(res == 0)
        std::copy(interpolants.begin(),interpolants.end(),interps);
      return res ? L_TRUE : L_FALSE;
}                         
#endif
    
template<class T>
struct killme {
  T *p;
  killme(){p = 0;}
  void set(T *_p) {p = _p;} 
  ~killme(){
    if(p)
      delete p;
  }
};


class iz3interp : public iz3base {
public:

  killme<iz3secondary> sp_killer;
  killme<iz3translation> tr_killer;

  bool is_linear(std::vector<int> &parents){
    for(int i = 0; i < ((int)parents.size())-1; i++)
      if(parents[i] != i+1)
	return false;
    return true;
  }

  void test_secondary(const std::vector<ast> &cnsts,
			     const std::vector<int> &parents,
			     std::vector<ast> &interps
			     ){
    int num = cnsts.size();
    iz3secondary *sp = iz3foci::create(this,num,(int *)(parents.empty()?0:&parents[0]));
    int res = sp->interpolate(cnsts, interps);
    if(res != 0)
      throw "secondary failed";
  }                         

  void proof_to_interpolant(z3pf proof,
			    const std::vector<std::vector<ast> > &cnsts,
			    const std::vector<int> &parents,
			    std::vector<ast> &interps,
			    const std::vector<ast> &theory,
			    interpolation_options_struct *options = 0
			    ){
#if 0
    test_secondary(cnsts,parents,interps);
    return;
#endif

    profiling::timer_start("Interpolation prep");

    // get rid of frames not used in proof

    std::vector<std::vector<ast> > cnsts_vec;
    std::vector<int> parents_vec;
    frame_reducer fr(*this);
    fr.get_frames(cnsts,parents,cnsts_vec,parents_vec,proof);

    int num = cnsts_vec.size();
    std::vector<ast> interps_vec(num-1);
    
    // if this is really a sequence problem, we can make it easier
    if(is_linear(parents_vec))
      parents_vec.clear();

    // create a secondary prover
    iz3secondary *sp = iz3foci::create(this,num,parents_vec.empty()?0:&parents_vec[0]);
    sp_killer.set(sp); // kill this on exit
	  
#define BINARY_INTERPOLATION
#ifndef BINARY_INTERPOLATION    
    // create a translator
    iz3translation *tr = iz3translation::create(*this,sp,cnsts_vec,parents_vec,theory);
    tr_killer.set(tr);
    
    // set the translation options, if needed
    if(options)
      for(hash_map<std::string,std::string>::iterator it = options->map.begin(), en = options->map.end(); it != en; ++it)
	tr->set_option(it->first, it->second);
    
    // create a proof object to hold the translation
    iz3proof pf(tr);
    
    profiling::timer_stop("Interpolation prep");

    // translate into an interpolatable proof
    profiling::timer_start("Proof translation");
    tr->translate(proof,pf);
    profiling::timer_stop("Proof translation");
    
    // translate the proof into interpolants
    profiling::timer_start("Proof interpolation");
    for(int i = 0; i < num-1; i++){
      interps_vec[i] = pf.interpolate(tr->range_downward(i),tr->weak_mode());
      interps_vec[i] = tr->quantify(interps_vec[i],tr->range_downward(i)); 
    }
    profiling::timer_stop("Proof interpolation");
#else
    iz3base the_base(*this,cnsts_vec,parents_vec,theory);

    profiling::timer_stop("Interpolation prep");
    
    for(int i = 0; i < num-1; i++){
      range rng = the_base.range_downward(i);
      std::vector<std::vector<ast> > cnsts_vec_vec(2);
      for(unsigned j = 0; j < cnsts_vec.size(); j++){
	bool is_A = the_base.in_range(j,rng);
	for(unsigned k = 0; k < cnsts_vec[j].size(); k++)
	  cnsts_vec_vec[is_A ? 0 : 1].push_back(cnsts_vec[j][k]);
      }

      killme<iz3translation> tr_killer_i;
      iz3translation *tr = iz3translation::create(*this,sp,cnsts_vec_vec,std::vector<int>(),theory);
      tr_killer_i.set(tr);
    
      // set the translation options, if needed
      if(options)
	for(hash_map<std::string,std::string>::iterator it = options->map.begin(), en = options->map.end(); it != en; ++it)
	  tr->set_option(it->first, it->second);
      
      // create a proof object to hold the translation
      iz3proof pf(tr);
      
      // translate into an interpolatable proof
      profiling::timer_start("Proof translation");
      tr->translate(proof,pf);
      profiling::timer_stop("Proof translation");
      
      // translate the proof into interpolants
      profiling::timer_start("Proof interpolation");
      interps_vec[i] = pf.interpolate(tr->range_downward(0),tr->weak_mode());
      interps_vec[i] = tr->quantify(interps_vec[i],tr->range_downward(0)); 
      profiling::timer_stop("Proof interpolation");
    }
#endif       
    // put back in the removed frames
    fr.fix_interpolants(interps_vec);

    interps = interps_vec;

  }


  void proof_to_interpolant(z3pf proof,
			    std::vector<ast> &cnsts,
			    const std::vector<int> &parents,
			    std::vector<ast> &interps,
			    const std::vector<ast> &theory,
			    interpolation_options_struct *options = 0
			    ){
    std::vector<std::vector<ast> > cnsts_vec(cnsts.size());
    for(unsigned i = 0; i < cnsts.size(); i++)
      cnsts_vec[i].push_back(cnsts[i]);
    proof_to_interpolant(proof,cnsts_vec,parents,interps,theory,options);
  }    

  // same as above, but represents the tree using an ast

  void proof_to_interpolant(const z3pf &proof,
			    const std::vector<ast> &_cnsts,
			    const ast &tree,
			    std::vector<ast> &interps,
			    interpolation_options_struct *options = 0
			    ){
    std::vector<int> pos_map;
    
    // convert to the parents vector representation
    
    to_parents_vec_representation(_cnsts, tree, cnsts, parents, theory, pos_map);

    //use the parents vector representation to compute interpolant
    proof_to_interpolant(proof,cnsts,parents,interps,theory,options);
    
    // get the interps for the tree positions
    std::vector<ast> _interps = interps;
    interps.resize(pos_map.size());
    for(unsigned i = 0; i < pos_map.size(); i++){
      unsigned j = pos_map[i];
      interps[i] = j < _interps.size() ? _interps[j] : mk_false();
    }
  }

  bool has_interp(hash_map<ast,bool> &memo, const ast &t){
    if(memo.find(t) != memo.end())
      return memo[t];
    bool res = false;
    if(op(t) == Interp)
      res = true;
    else if(op(t) == And){
      int nargs = num_args(t);
      for(int i = 0; i < nargs; i++)
	res |= has_interp(memo, arg(t,i));
    }
    memo[t] = res;
    return res;
  }

  void collect_conjuncts(std::vector<ast> &cnsts, hash_map<ast,bool> &memo, const ast &t){
    if(!has_interp(memo,t))
      cnsts.push_back(t);
    else {
      int nargs = num_args(t);
      for(int i = 0; i < nargs; i++)
	collect_conjuncts(cnsts, memo, arg(t,i));
    }
  }
  
  void assert_conjuncts(solver &s, std::vector<ast> &cnsts, const ast &t){
    hash_map<ast,bool> memo;    
    collect_conjuncts(cnsts,memo,t);
    for(unsigned i = 0; i < cnsts.size(); i++)
      s.assert_expr(to_expr(cnsts[i].raw()));
  }

  iz3interp(ast_manager &_m_manager)
    : iz3base(_m_manager) {}
};

void iz3interpolate(ast_manager &_m_manager,
		    ast *proof,
		    const ptr_vector<ast> &cnsts,
		    const ::vector<int> &parents,
		    ptr_vector<ast> &interps,
		    const ptr_vector<ast> &theory,
		    interpolation_options_struct * options)
{
  iz3interp itp(_m_manager);
  if(options)
    options->apply(itp);
  std::vector<iz3mgr::ast> _cnsts(cnsts.size());
  std::vector<int> _parents(parents.size());
  std::vector<iz3mgr::ast> _interps;
  std::vector<iz3mgr::ast> _theory(theory.size());
  for(unsigned i = 0; i < cnsts.size(); i++)
    _cnsts[i] = itp.cook(cnsts[i]);
  for(unsigned i = 0; i < parents.size(); i++)
    _parents[i] = parents[i];
  for(unsigned i = 0; i < theory.size(); i++)
    _theory[i] = itp.cook(theory[i]);
  iz3mgr::ast _proof = itp.cook(proof);
  itp.proof_to_interpolant(_proof,_cnsts,_parents,_interps,_theory,options);
  interps.resize(_interps.size());
  for(unsigned i = 0; i < interps.size(); i++)
    interps[i] = itp.uncook(_interps[i]);
}

void iz3interpolate(ast_manager &_m_manager,
		    ast *proof,
		    const ::vector<ptr_vector<ast> > &cnsts,
		    const ::vector<int> &parents,
		    ptr_vector<ast> &interps,
		    const ptr_vector<ast> &theory,
		    interpolation_options_struct * options)
{
  iz3interp itp(_m_manager);
  if(options)
    options->apply(itp);
  std::vector<std::vector<iz3mgr::ast> > _cnsts(cnsts.size());
  std::vector<int> _parents(parents.size());
  std::vector<iz3mgr::ast> _interps;
  std::vector<iz3mgr::ast> _theory(theory.size());
  for(unsigned i = 0; i < cnsts.size(); i++)
    for(unsigned j = 0; j < cnsts[i].size(); j++)
      _cnsts[i].push_back(itp.cook(cnsts[i][j]));
  for(unsigned i = 0; i < parents.size(); i++)
    _parents[i] = parents[i];
  for(unsigned i = 0; i < theory.size(); i++)
    _theory[i] = itp.cook(theory[i]);
  iz3mgr::ast _proof = itp.cook(proof);
  itp.proof_to_interpolant(_proof,_cnsts,_parents,_interps,_theory,options);
  interps.resize(_interps.size());
  for(unsigned i = 0; i < interps.size(); i++)
    interps[i] = itp.uncook(_interps[i]);
}

void iz3interpolate(ast_manager &_m_manager,
		    ast *proof,
		    const ptr_vector<ast> &cnsts,
		    ast *tree,
		    ptr_vector<ast> &interps,
		    interpolation_options_struct * options)
{
  iz3interp itp(_m_manager);
  if(options)
    options->apply(itp);
  std::vector<iz3mgr::ast> _cnsts(cnsts.size());
  std::vector<iz3mgr::ast> _interps;
  for(unsigned i = 0; i < cnsts.size(); i++)
    _cnsts[i] = itp.cook(cnsts[i]);
  iz3mgr::ast _proof = itp.cook(proof);
  iz3mgr::ast _tree = itp.cook(tree);
  itp.proof_to_interpolant(_proof,_cnsts,_tree,_interps,options);
  interps.resize(_interps.size());
  for(unsigned i = 0; i < interps.size(); i++)
    interps[i] = itp.uncook(_interps[i]);
}

lbool iz3interpolate(ast_manager &_m_manager,
		     solver &s,
		     ast *tree,
		     ptr_vector<ast> &cnsts,
		     ptr_vector<ast> &interps,
		     model_ref &m,
		     interpolation_options_struct * options)
{
  iz3interp itp(_m_manager);
  if(options)
    options->apply(itp);
  iz3mgr::ast _tree = itp.cook(tree);
  std::vector<iz3mgr::ast> _cnsts;
  itp.assert_conjuncts(s,_cnsts,_tree);
  profiling::timer_start("solving");
  lbool res = s.check_sat(0,0);
  profiling::timer_stop("solving");
  if(res == l_false){
    ast *proof = s.get_proof();
    iz3mgr::ast _proof = itp.cook(proof);
    std::vector<iz3mgr::ast> _interps;
    itp.proof_to_interpolant(_proof,_cnsts,_tree,_interps,options);
    interps.resize(_interps.size());
    for(unsigned i = 0; i < interps.size(); i++)
      interps[i] = itp.uncook(_interps[i]);
  }
  else if(m){
    s.get_model(m);
  }
  cnsts.resize(_cnsts.size());
  for(unsigned i = 0; i < cnsts.size(); i++)
    cnsts[i] = itp.uncook(_cnsts[i]);
  return res;
}



void interpolation_options_struct::apply(iz3base &b){
  for(stl_ext::hash_map<std::string,std::string>::iterator it = map.begin(), en = map.end();
      it != en;
      ++it)
    b.set_option((*it).first,(*it).second);
}

// On linux and mac, unlimit stack space so we get recursion

#if defined(_WINDOWS) || defined(_CYGWIN)

#else

#include <sys/time.h>
#include <sys/resource.h>

class iz3stack_unlimiter {
public:
  iz3stack_unlimiter() {
    struct rlimit rl = {RLIM_INFINITY, RLIM_INFINITY};
    setrlimit(RLIMIT_STACK, &rl);
    // nothing to be done if above fails
  }
};

// initializing this will unlimit stack

iz3stack_unlimiter the_iz3stack_unlimiter;

#endif
