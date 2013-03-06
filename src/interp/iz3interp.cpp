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


#ifndef WIN32
using namespace stl_ext;
#endif



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
    if(memo.count(proof))return;
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
  
  void get_frames(const std::vector<ast> &z3_preds, 
		  const std::vector<int> &orig_parents,
		  std::vector<ast> &assertions,
		  std::vector<int> &parents,
		  z3pf proof){
    frames = z3_preds.size();
    orig_parents_copy = orig_parents;
    for(unsigned i = 0; i < z3_preds.size(); i++)
      frame_map[z3_preds[i]] = i;
    used_frames.resize(frames);
    hash_set<ast> memo;
    get_proof_assumptions_rec(proof,memo,used_frames);
    std::vector<int> assertions_back_map(frames);

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
        interpolants[p] = interpolants[i];
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
    

class iz3interp : public iz3mgr {
public:
  void proof_to_interpolant(z3pf proof,
			    const std::vector<ast> &cnsts,
			    const std::vector<int> &parents,
			    std::vector<ast> &interps,
			    const std::vector<ast> &theory,
			    interpolation_options_struct *options = 0
			    ){
    
    profiling::timer_start("Interpolation prep");

    // get rid of frames not used in proof

    std::vector<ast> cnsts_vec;
    std::vector<int> parents_vec;
    frame_reducer fr(*this);
    fr.get_frames(cnsts,parents,cnsts_vec,parents_vec,proof);

    int num = cnsts_vec.size();
    std::vector<ast> interps_vec(num-1);
    
    // create a secondary prover
    iz3secondary *sp = iz3foci::create(this,num,parents_vec.empty()?0:&parents_vec[0]);
	  
    // create a translator
    iz3translation *tr = iz3translation::create(*this,sp,cnsts_vec,parents_vec,theory);
    
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
       
    // put back in the removed frames
    fr.fix_interpolants(interps_vec);

    interps = interps_vec;
    delete tr;
    delete sp;
  }

  iz3interp(scoped_ptr<ast_manager> &_m_manager)
    : iz3mgr(_m_manager) {}
};

void iz3interpolate(scoped_ptr<ast_manager> &_m_manager,
		    ast *proof,
		    const ptr_vector<ast> &cnsts,
		    const ::vector<int> &parents,
		    ptr_vector<ast> &interps,
		    const ptr_vector<ast> &theory,
		    interpolation_options_struct * options)
{
  std::vector<ast_r> _cnsts(cnsts.size());
  std::vector<int> _parents(parents.size());
  std::vector<ast_r> _interps;
  std::vector<ast_r> _theory(theory.size());
  for(unsigned i = 0; i < cnsts.size(); i++)
    _cnsts[i] = cnsts[i];
  for(unsigned i = 0; i < parents.size(); i++)
    _parents[i] = parents[i];
  for(unsigned i = 0; i < theory.size(); i++)
    _theory[i] = theory[i];
  ast_r _proof(proof);
  iz3interp itp(_m_manager);
  itp.proof_to_interpolant(_proof,_cnsts,_parents,_interps,_theory,options);
  interps.resize(_interps.size());
  for(unsigned i = 0; i < interps.size(); i++)
    _interps[i] = interps[i];
}

