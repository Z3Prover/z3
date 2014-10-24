/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

   iz3translate_direct.cpp

Abstract:

   Translate a Z3 proof into the interpolating proof calculus.
   Translation is direct, without transformations on the target proof
   representaiton.

Author:

    Ken McMillan (kenmcmil)

Revision History:

--*/


#ifdef _WINDOWS
#pragma warning(disable:4996)
#pragma warning(disable:4800)
#pragma warning(disable:4267)
#pragma warning(disable:4101)
#pragma warning(disable:4390)
#endif

#include "iz3translate.h"
#include "iz3proof.h"
#include "iz3profiling.h"
#include "iz3interp.h"

#include <assert.h>
#include <algorithm>
#include <stdio.h>
#include <fstream>
#include <sstream>
#include <iostream>
#include <set>

//using std::vector;
using namespace stl_ext;

/* This can introduce an address dependency if the range type of hash_map has
   a destructor. Since the code in this file is not used and only here for
   historical comparisons, we allow this non-determinism.
 */
namespace stl_ext {
  template <class T>
    class hash<T *> {
  public:
    size_t operator()(const T *p) const {
      return (size_t) p;
    }
  };
}

static int lemma_count = 0;
#if 0
static int nll_lemma_count = 0;
#endif
#define SHOW_LEMMA_COUNT -1

// One half of a resolution. We need this to distinguish
// between resolving as a clause and as a unit clause.
// if pivot == conclusion(proof) it is unit.

struct Z3_resolvent {
  iz3base::ast proof;
  bool is_unit;
  iz3base::ast pivot;
  Z3_resolvent(const iz3base::ast &_proof,  bool _is_unit, const iz3base::ast &_pivot){
    proof = _proof;
    is_unit = _is_unit;
    pivot = _pivot;
  }
};

namespace hash_space {
  template <>
  class hash<Z3_resolvent > {
  public:
    size_t operator()(const Z3_resolvent &p) const {
      return (p.proof.hash() + p.pivot.hash());
    }
  };
}


bool operator==(const Z3_resolvent &x, const Z3_resolvent &y) {
  return x.proof == y.proof && x.pivot == y.pivot;
}



typedef std::vector<Z3_resolvent *> ResolventAppSet;

struct non_local_lits {
  ResolventAppSet proofs; // the proof nodes being raised
  non_local_lits(ResolventAppSet &_proofs){
    proofs.swap(_proofs);
  }
};

namespace hash_space {
  template <>
  class hash<non_local_lits > {
  public:
    size_t operator()(const non_local_lits &p) const {
      size_t h = 0;
      for(ResolventAppSet::const_iterator it = p.proofs.begin(), en = p.proofs.end(); it != en; ++it)
	h += (size_t)*it;
      return h;
    }
  };
}


bool operator==(const non_local_lits &x, const non_local_lits &y) {
     ResolventAppSet::const_iterator itx = x.proofs.begin();
     ResolventAppSet::const_iterator ity = y.proofs.begin();
     while(true){
       if(ity == y.proofs.end()) return itx == x.proofs.end();
       if(itx == x.proofs.end()) return ity == y.proofs.end();
       if(*itx != *ity) return false;
       ++itx; ++ity;
     }
}


/* This translator goes directly from Z3 proofs to interpolatable
   proofs without an intermediate representation as an iz3proof. */

class iz3translation_direct : public iz3translation {
public:

  typedef ast Zproof;   // type of non-interpolating proofs
  typedef iz3proof Iproof; // type of interpolating proofs
  
  /* Here we have lots of hash tables for memoizing various methods and
     other such global data structures.
   */

  typedef hash_map<ast,int> AstToInt;
  AstToInt locality;                        // memoizes locality of Z3 proof terms

  typedef std::pair<ast,ast> EquivEntry;
  typedef hash_map<ast,EquivEntry> EquivTab;
  EquivTab equivs;                          // maps non-local terms to equivalent local terms, with proof

  typedef hash_set<ast> AstHashSet;
  AstHashSet equivs_visited;                // proofs already checked for equivalences


  typedef std::pair<hash_map<ast,Iproof::node>, hash_map<ast,Iproof::node> > AstToIpf;
  AstToIpf translation;                     // Zproof nodes to Iproof nodes
  
  AstHashSet antes_added;                   // Z3 proof terms whose antecedents have been added to the list
  std::vector<std::pair<ast,int> > antes;   // list of antecedent/frame pairs
  std::vector<ast> local_antes;                       // list of local antecedents

  Iproof *iproof;                            // the interpolating proof we are constructing

  int frames;                               // number of frames

  typedef std::set<ast> AstSet;
  typedef hash_map<ast,AstSet> AstToAstSet;
  AstToAstSet hyp_map;                      // map proof terms to hypothesis set

  struct LocVar {                           // localization vars
    ast var;                                // a fresh variable
    ast term;                               // term it represents
    int frame;                              // frame in which it's defined
    LocVar(ast v, ast t, int f){var=v;term=t;frame=f;}
  };

  std::vector<LocVar> localization_vars;         // localization vars in order of creation
  typedef hash_map<ast,ast> AstToAst;
  AstToAst localization_map;                // maps terms to their localization vars

  typedef hash_map<ast,bool> AstToBool;



  iz3secondary *secondary;                // the secondary prover

  // Unique table for sets of non-local resolutions
  hash_map<non_local_lits, non_local_lits *> non_local_lits_unique;

  // Unique table for resolvents
  hash_map<Z3_resolvent, Z3_resolvent *> Z3_resolvent_unique;

  // Translation memo for case of non-local resolutions
  hash_map<non_local_lits *, AstToIpf> non_local_translation;

 public:

 
#define from_ast(x) (x)

  // determine locality of a proof term
  // return frame of derivation if local, or -1 if not
  // result INT_MAX means the proof term is a tautology
  // memoized in hash_map "locality"

  int get_locality_rec(ast proof){
    std::pair<ast,int> foo(proof,INT_MAX);
    std::pair<AstToInt::iterator, bool> bar = locality.insert(foo);
    int &res = bar.first->second;
    if(!bar.second) return res;
    if(pr(proof) == PR_ASSERTED){
      ast ass = conc(proof);
      res = frame_of_assertion(ass);
    }
    else {
      unsigned nprems = num_prems(proof);
      for(unsigned i = 0; i < nprems; i++){
	ast arg = prem(proof,i);
	int bar = get_locality_rec(arg);
	if(res == INT_MAX || res == bar) res = bar;
	else if(bar != INT_MAX) res = -1;
      }
    }
    return res;
  }


  int get_locality(ast proof){
    // if(lia_z3_axioms_only) return -1;
    int res = get_locality_rec(proof);
    if(res != -1){
      ast con = conc(proof);
      range rng = ast_scope(con);

      // hack: if a clause contains "true", it reduces to "true",
      // which means we won't compute the range correctly. we handle
      // this case by computing the ranges of the literals separately

      if(is_true(con)){
	std::vector<ast> lits;
	get_Z3_lits(conc(proof),lits);
	for(unsigned i = 0; i < lits.size(); i++)
	  rng = range_glb(rng,ast_scope(lits[i]));
      }
      
      if(!range_is_empty(rng)){
	AstSet &hyps = get_hyps(proof);
	for(AstSet::iterator it = hyps.begin(), en = hyps.end(); it != en; ++it){
	  ast hyp = *it;
	  rng = range_glb(rng,ast_scope(hyp));
	}
      }

      if(res == INT_MAX){
	if(range_is_empty(rng))
	  res = -1;
	else res = range_max(rng);
      }
      else {
	if(!in_range(res,rng))
	  res = -1;
      }
    }
    return res;
  }

  AstSet &get_hyps(ast proof){
    std::pair<ast,AstSet > foo(proof,AstSet());
    std::pair<AstToAstSet::iterator, bool> bar = hyp_map.insert(foo);
    AstSet &res = bar.first->second;
    if(!bar.second) return res;
    pfrule dk = pr(proof);
    if(dk == PR_HYPOTHESIS){
      ast con = conc(proof);
      res.insert(con);
    }
    else {
      unsigned nprems = num_prems(proof);
      for(unsigned i = 0; i < nprems; i++){
	ast arg = prem(proof,i);
	AstSet &arg_hyps = get_hyps(arg);
	res.insert(arg_hyps.begin(),arg_hyps.end());
      }
      if(dk == PR_LEMMA){
	ast con = conc(proof);
	res.erase(mk_not(con));
	if(is_or(con)){
	  int clause_size = num_args(con);
	  for(int i = 0; i < clause_size; i++){
	    ast neglit = mk_not(arg(con,i));
	    res.erase(neglit);
	  }
	}	    
      }
    }
#if 0
    AstSet::iterator it = res.begin(), en = res.end();
    if(it != en){
      AstSet::iterator old = it;
      ++it;
      for(; it != en; ++it, ++old)
	if(!(*old < *it))
	  std::cout << "foo!";
    }
#endif
    return res;
  }


  // Find all the judgements of the form p <-> q, where
  // p is local and q is non-local, recording them in "equivs"
  // the map equivs_visited is used to record the already visited proof terms

  void find_equivs(ast proof){
    if(equivs_visited.find(proof) != equivs_visited.end())
      return;
    equivs_visited.insert(proof);
    unsigned nprems = num_prems(proof);
    for(unsigned i = 0; i < nprems; i++) // do all the sub_terms
      find_equivs(prem(proof,i));
    ast con = conc(proof); // get the conclusion
    if(is_iff(con)){
      ast iff = con;
      for(int i = 0; i < 2; i++)
	if(!is_local(arg(iff,i)) && is_local(arg(iff,1-i))){
	  std::pair<ast,std::pair<ast,ast> > foo(arg(iff,i),std::pair<ast,ast>(arg(iff,1-i),proof));
	  equivs.insert(foo);
	}
    }
  }

  // get the lits of a Z3 clause as foci terms
  void get_Z3_lits(ast t, std::vector<ast> &lits){
    opr dk = op(t);
    if(dk == False)
      return; // false = empty clause
    if(dk == Or){
      unsigned nargs = num_args(t);
      lits.resize(nargs);
      for(unsigned i = 0; i < nargs; i++) // do all the sub_terms
	lits[i] = arg(t,i);
    }
    else {
      lits.push_back(t);
    }
  }

  // resolve two clauses represented as vectors of lits. replace first clause
  void resolve(ast pivot, std::vector<ast> &cls1, std::vector<ast> &cls2){
    ast neg_pivot = mk_not(pivot);
    for(unsigned i = 0; i < cls1.size(); i++){
      if(cls1[i] == pivot){
	cls1[i] = cls1.back();
	cls1.pop_back();
	bool found_pivot2 = false;
	for(unsigned j = 0; j < cls2.size(); j++){
	  if(cls2[j] == neg_pivot)
	    found_pivot2 = true;
	  else
	    cls1.push_back(cls2[j]);
	}
	assert(found_pivot2);
	return;
      }
    }
    assert(0 && "resolve failed");
  }

  // get lits resulting from unit resolution up to and including "position"
  // TODO: this is quadratic -- fix it
  void do_unit_resolution(ast proof, int position, std::vector<ast> &lits){
    ast orig_clause = conc(prem(proof,0));
    get_Z3_lits(orig_clause,lits);
    for(int i = 1; i <= position; i++){
      std::vector<ast> unit(1);
      unit[0] = conc(prem(proof,i));
      resolve(mk_not(unit[0]),lits,unit);
    }
  }
  

  // clear the localization variables
  void clear_localization(){
    localization_vars.clear();
    localization_map.clear();
  }
  
  // create a fresh variable for localization
  ast fresh_localization_var(ast term, int frame){
    std::ostringstream s;
    s << "%" << (localization_vars.size());
    ast var = make_var(s.str().c_str(),get_type(term));
    sym_range(sym(var)) = range_full(); // make this variable global
    localization_vars.push_back(LocVar(var,term,frame));
    return var;
  }
  

  // "localize" a term to a given frame range by 
  // creating new symbols to represent non-local subterms

  ast localize_term(ast e, const range &rng){
    if(ranges_intersect(ast_scope(e),rng))
      return e; // this term occurs in range, so it's O.K.
    AstToAst::iterator it = localization_map.find(e);
    if(it != localization_map.end())
      return it->second;

    // if is is non-local, we must first localize the arguments to
    // the range of its function symbol
    
    int nargs = num_args(e);
    if(nargs > 0 /*  && (!is_local(e) || flo <= hi || fhi >= lo) */){
      range frng = rng;
      if(op(e) == Uninterpreted){
	symb f = sym(e);
	range srng = sym_range(f);
	if(ranges_intersect(srng,rng)) // localize to desired range if possible
	  frng = range_glb(srng,rng);
      }
      std::vector<ast> largs(nargs);
      for(int i = 0; i < nargs; i++){
	largs[i] = localize_term(arg(e,i),frng);
	frng = range_glb(frng,ast_scope(largs[i]));
      }
      e = clone(e,largs);
      assert(is_local(e));
    }


    if(ranges_intersect(ast_scope(e),rng))
      return e; // this term occurs in range, so it's O.K.

    // choose a frame for the constraint that is close to range
    int frame = range_near(ast_scope(e),rng);

    ast new_var = fresh_localization_var(e,frame);
    localization_map[e] = new_var;
    ast cnst = make(Equal,new_var,e);
    antes.push_back(std::pair<ast,int>(cnst,frame));
    return new_var;
  }

  // some patterm matching functions

  // match logical or with nargs arguments
  // assumes AIG form
  bool match_or(ast e, ast *args, int nargs){
    if(op(e) != Or) return false;
    int n = num_args(e);
    if(n != nargs) return false;
    for(int i = 0; i < nargs; i++)
      args[i] = arg(e,i);
    return true;
  }

  // match operator f with exactly nargs arguments
  bool match_op(ast e, opr f, ast *args, int nargs){
    if(op(e) != f) return false;
    int n = num_args(e);
    if(n != nargs) return false;
    for(int i = 0; i < nargs; i++)
      args[i] = arg(e,i);
    return true;
  }

  // see if the given formula can be interpreted as
  // an axiom instance (e.g., an array axiom instance).
  // if so, add it to "antes" in an appropriate frame.
  // this may require "localization"
  
  void get_axiom_instance(ast e){

    // "store" axiom
    // (or (= w q) (= (select (store a1 w y) q) (select a1 q)))
    // std::cout << "ax: "; show(e);
    ast lits[2],eq_ops_l[2],eq_ops_r[2],sel_ops[2], sto_ops[3], sel_ops2[2] ; 
    if(match_or(e,lits,2))
      if(match_op(lits[0],Equal,eq_ops_l,2))
	if(match_op(lits[1],Equal,eq_ops_r,2))
	  for(int i = 0; i < 2; i++){ // try the second equality both ways
	    if(match_op(eq_ops_r[0],Select,sel_ops,2))
	      if(match_op(sel_ops[0],Store,sto_ops,3))
		if(match_op(eq_ops_r[1],Select,sel_ops2,2))
                  for(int j = 0; j < 2; j++){ // try the first equality both ways
                    if(eq_ops_l[0] == sto_ops[1]
                    && eq_ops_l[1] == sel_ops[1]
                    && eq_ops_l[1] == sel_ops2[1]
                    && sto_ops[0] == sel_ops2[0])
                      if(is_local(sel_ops[0])) // store term must be local
                      {    
                        ast sto = sel_ops[0];
                        ast addr = localize_term(eq_ops_l[1],ast_scope(sto));
                        ast res = make(Or,
                          make(Equal,eq_ops_l[0],addr),
                          make(Equal,
                          make(Select,sto,addr),
                          make(Select,sel_ops2[0],addr)));
                        int frame = range_min(ast_scope(res));
                        antes.push_back(std::pair<ast,int>(res,frame));
                        return;
                      }
                      std::swap(eq_ops_l[0],eq_ops_l[1]);
                  }
	    std::swap(eq_ops_r[0],eq_ops_r[1]);
	  }
  }

  // a quantifier instantation looks like (~ forall x. P) \/ P[z/x]
  // we need to find a time frame for P, then localize P[z/x] in this frame

  void get_quantifier_instance(ast e){
    ast disjs[2];
    if(match_or(e,disjs,2)){
      if(is_local(disjs[0])){
	ast res = localize_term(disjs[1], ast_scope(disjs[0]));
	int frame = range_min(ast_scope(res));
	antes.push_back(std::pair<ast,int>(res,frame));
	return;
      }
    }
  }

  ast get_judgement(ast proof){
    ast con = from_ast(conc(proof));
    AstSet &hyps = get_hyps(proof);
    std::vector<ast> hyps_vec;
    for(AstSet::iterator it = hyps.begin(), en = hyps.end(); it != en; ++it)
      hyps_vec.push_back(*it);
    if(hyps_vec.size() == 0) return con;
    con = make(Or,mk_not(make(And,hyps_vec)),con);
    return con;
  }

  // add the premises of a proof term to the "antes" list

  void add_antes(ast proof){
    if(antes_added.find(proof) != antes_added.end()) return;
    antes_added.insert(proof);
    int frame = get_locality(proof);
    if(frame != -1)
      if(1){
	ast e = get_judgement(proof);
	if(frame >= frames) frame = frames-1; // can happen if there are no symbols
	antes.push_back(std::pair<ast,int>(e,frame));
	return;
      }
    pfrule dk = pr(proof);
    if(dk == PR_ASSERTED){
      ast ass = conc(proof);
      frame = frame_of_assertion(ass);
      if(frame >= frames) frame = frames-1; // can happen if a theory fact
      antes.push_back(std::pair<ast,int>(ass,frame));
      return;
    }
    if(dk == PR_TH_LEMMA && num_prems(proof) == 0){
      get_axiom_instance(conc(proof));
    }
    if(dk == PR_QUANT_INST && num_prems(proof) == 0){
      get_quantifier_instance(conc(proof));
    }
    unsigned nprems = num_prems(proof);
    for(unsigned i = 0; i < nprems; i++){
      ast arg = prem(proof,i);
      add_antes(arg);
    }    
  }


  // add quantifiers over the localization vars
  // to an interpolant for frames lo-hi

  ast add_quants(ast e, int lo, int hi){
    for(int i = localization_vars.size() - 1; i >= 0; i--){
      LocVar &lv = localization_vars[i];
      opr quantifier = (lv.frame >= lo && lv.frame <= hi) ? Exists : Forall; 
      e = apply_quant(quantifier,lv.var,e);
    }
    return e;
  }

  int get_lits_locality(std::vector<ast> &lits){
    range rng = range_full();
    for(std::vector<ast>::iterator it = lits.begin(), en = lits.end(); it != en; ++it){
      ast lit = *it;
      rng = range_glb(rng,ast_scope(lit));
    }
    if(range_is_empty(rng)) return -1;
	int hi = range_max(rng);
    if(hi >= frames) return frames - 1;
    return hi;
  }


  struct invalid_lemma {};




  // prove a lemma (clause) using current antes list
  // return proof of the lemma
  // use the secondary prover

  int prove_lemma(std::vector<ast> &lits){
    

    // first try localization
    if(antes.size() == 0){
      int local_frame = get_lits_locality(lits);
      if(local_frame != -1)
	return iproof->make_assumption(local_frame,lits); // no proof needed for purely local fact
    }

    // group the assumptions by frame
    std::vector<ast> preds(frames);
    for(unsigned i = 0; i < preds.size(); i++)
      preds[i] = mk_true();
    for(unsigned i = 0; i < antes.size(); i++){
      int frame = antes[i].second;
      preds[frame] = mk_and(preds[frame],antes[i].first); // conjoin it to frame
    }

    for(unsigned i = 0; i < lits.size(); i++){
      int frame;
 if(!weak_mode()){
	frame = range_max(ast_scope(lits[i]));
	if(frame >= frames) frame = frames-1; // could happen if contains no symbols
      }
      else {
	frame = range_min(ast_scope(lits[i]));
	if(frame < 0){
	  frame = range_max(ast_scope(lits[i])); // could happen if contains no symbols
          if(frame >= frames) frame = frames-1; 
        }
      }
      preds[frame] = mk_and(preds[frame],mk_not(lits[i]));
    }


    std::vector<ast> itps; // holds interpolants


#if 1
    ++lemma_count;
    // std::cout << "lemma: " << lemma_count << std::endl;
    if(lemma_count == SHOW_LEMMA_COUNT){
      for(unsigned i = 0; i < lits.size(); i++)
        show_lit(lits[i]);
      std::cerr << "lemma written to file lemma.smt:\n";
      iz3base foo(*this,preds,std::vector<int>(),std::vector<ast>());
      foo.print("lemma.smt");
      throw invalid_lemma();
    }
#endif

#if 0
    std::cout << "\nLemma:\n";
    for(unsigned i = 0; i < lits.size(); i++)
      show_lit(lits[i]);
#endif 

    // interpolate using secondary prover
    profiling::timer_start("foci");
    int sat = secondary->interpolate(preds,itps);
    profiling::timer_stop("foci");

    std::cout << "lemma done" << std::endl;

    // if sat, lemma isn't valid, something is wrong
    if(sat){
#if 1
      std::cerr << "invalid lemma written to file invalid_lemma.smt:\n";
      iz3base foo(*this,preds,std::vector<int>(),std::vector<ast>());
      foo.print("invalid_lemma.smt");
#endif
      throw iz3_incompleteness();
    }
    assert(sat == 0); // if sat, lemma doesn't hold!

    // quantifiy the localization vars
    for(unsigned i = 0; i < itps.size(); i++)
      itps[i] = add_quants(itps[i],0,i);
    
    // Make a lemma, storing interpolants
    Iproof::node res = iproof->make_lemma(lits,itps);

#if 0
    std::cout << "Lemma interps\n";
    for(unsigned i = 0; i < itps.size(); i++)
      show(itps[i]);
#endif    

    // Reset state for the next lemma
    antes.clear();
    antes_added.clear();
    clear_localization(); // use a fresh localization for each lemma

    return res;
  }

  // sanity check: make sure that any non-local lit is really resolved
  // with something in the non_local_lits set

  void check_non_local(ast lit, non_local_lits *nll){
    if(nll)
      for(ResolventAppSet::iterator it = nll->proofs.begin(), en = nll->proofs.end(); it != en; ++it){
        ast con = (*it)->pivot;
        if(con == mk_not(lit)) return;
      }
    assert(0 && "bug in non-local resolution handling");
  }


  void get_local_conclusion_lits(ast proof, bool expect_clause, AstSet &lits){
    std::vector<ast> reslits;
    if(expect_clause)
      get_Z3_lits(conc(proof),reslits);
    else reslits.push_back(conc(proof));
    for(unsigned i = 0; i < reslits.size(); i++)
      if(is_local(reslits[i]))
	lits.insert(reslits[i]);
    AstSet &pfhyps = get_hyps(proof);
    for(AstSet::iterator hit = pfhyps.begin(), hen = pfhyps.end(); hit != hen; ++hit)
      if(is_local(*hit))
	lits.insert(mk_not(*hit));
  }


  void collect_resolvent_lits(Z3_resolvent *res, const AstSet &hyps, std::vector<ast> &lits){
    if(!res->is_unit){
      std::vector<ast> reslits;
      get_Z3_lits(conc(res->proof),reslits);
      for(unsigned i = 0; i < reslits.size(); i++)
	if(reslits[i] != res->pivot)
	  lits.push_back(reslits[i]);
    }
    AstSet &pfhyps = get_hyps(res->proof);
    for(AstSet::iterator hit = pfhyps.begin(), hen = pfhyps.end(); hit != hen; ++hit)
      if(hyps.find(*hit) == hyps.end())
	lits.push_back(mk_not(*hit));
  }

  void filter_resolvent_lits(non_local_lits *nll, std::vector<ast> &lits){
      std::vector<ast> orig_lits; orig_lits.swap(lits);
      std::set<ast> pivs;
      for(ResolventAppSet::iterator it = nll->proofs.begin(), en = nll->proofs.end(); it != en; ++it){
	Z3_resolvent *res = *it;
        pivs.insert(res->pivot);
        pivs.insert(mk_not(res->pivot));
      }
      for(unsigned i = 0; i < orig_lits.size(); i++)
        if(pivs.find(orig_lits[i]) == pivs.end())
          lits.push_back(orig_lits[i]);
  }

  void collect_all_resolvent_lits(non_local_lits *nll, std::vector<ast> &lits){
  if(nll){
      std::vector<ast> orig_lits; orig_lits.swap(lits);
      std::set<ast> pivs;
      for(ResolventAppSet::iterator it = nll->proofs.begin(), en = nll->proofs.end(); it != en; ++it){
	Z3_resolvent *res = *it;
        pivs.insert(res->pivot);
        pivs.insert(mk_not(res->pivot));
      }
      for(ResolventAppSet::iterator it = nll->proofs.begin(), en = nll->proofs.end(); it != en; ++it){
	Z3_resolvent *res = *it;
	{
          std::vector<ast> reslits;
          if(!res->is_unit) get_Z3_lits(conc(res->proof),reslits);
          else reslits.push_back(conc(res->proof));
          for(unsigned i = 0; i < reslits.size(); i++)
#if 0
	    if(reslits[i] != res->pivot && pivs.find(reslits[i]) == pivs.end())
#endif
            if(is_local(reslits[i]))
	      lits.push_back(reslits[i]);
        }
      }
      for(unsigned i = 0; i < orig_lits.size(); i++)
        if(pivs.find(orig_lits[i]) == pivs.end())
          lits.push_back(orig_lits[i]);
    }
  }

  void collect_proof_clause(ast proof, bool expect_clause, std::vector<ast> &lits){
    if(expect_clause)
      get_Z3_lits(conc(proof),lits);
    else
      lits.push_back(from_ast(conc(proof)));
    AstSet &hyps = get_hyps(proof);
    for(AstSet::iterator hit = hyps.begin(), hen = hyps.end(); hit != hen; ++hit)
      lits.push_back(mk_not(*hit));
  }


  // turn a bunch of literals into a lemma, replacing
  // non-local lits with their local equivalents
  // adds the accumulated antecedents (antes) as
  // proof obligations of the lemma

  Iproof::node fix_lemma(std::vector<ast> &con_lits, AstSet &hyps, non_local_lits *nll){
    std::vector<ast> lits(con_lits);
    for(AstSet::iterator it = hyps.begin(), en = hyps.end(); it != en; ++it)
      lits.push_back(mk_not(*it));
    if(nll){
      for(ResolventAppSet::iterator it = nll->proofs.begin(), en = nll->proofs.end(); it != en; ++it){
	Z3_resolvent *res = *it;
	collect_resolvent_lits(res,hyps,lits);
	add_antes(res->proof);
      }
      filter_resolvent_lits(nll,lits);
    }
    for(unsigned int i = 0; i < lits.size(); i++){
      EquivTab::iterator it = equivs.find(lits[i]);
      if(it != equivs.end()){
	lits[i] = it->second.first;  // replace with local equivalent
	add_antes(it->second.second); // collect the premises that prove this
      }
      else {
	if(!is_local(lits[i])){
	  check_non_local(lits[i],nll);
	  lits[i] = mk_false();
	}
      }
    }
    // TODO: should check here that derivation is local?
    Iproof::node res = prove_lemma(lits);
    return res;
  }

  int num_lits(ast ast){
    opr dk = op(ast);
    if(dk == False)
      return 0;
    if(dk == Or){
      unsigned nargs = num_args(ast);
      int n = 0;
      for(unsigned i = 0; i < nargs; i++) // do all the sub_terms
	n += num_lits(arg(ast,i));
      return n;
    }
    else 
      return 1;
  }

  struct non_lit_local_ante {};

  bool local_antes_simple;

  bool add_local_antes(ast proof, AstSet &hyps, bool expect_clause = false){
    if(antes_added.find(proof) != antes_added.end()) return true;
    antes_added.insert(proof);
    ast con = from_ast(conc(proof));
    pfrule dk = pr(proof);
    if(is_local(con) || equivs.find(con) != equivs.end()){
      if(!expect_clause || num_lits(conc(proof)) == 1){
	AstSet &this_hyps = get_hyps(proof);
	if(std::includes(hyps.begin(),hyps.end(),this_hyps.begin(),this_hyps.end())){
	  // if(hyps.find(con) == hyps.end())
#if 0
          if(/* lemma_count == SHOW_LEMMA_COUNT - 1 && */ !is_literal_or_lit_iff(conc(proof))){
             std::cout << "\nnon-lit local ante\n";
             show_step(proof);
             show(conc(proof));
             throw non_lit_local_ante();
          }
#endif
          local_antes.push_back(proof);
	  return true;
	}
	else
	  ; //std::cout << "bar!\n";
      }
    }
    if(dk == PR_ASSERTED
       //|| dk == PR_HYPOTHESIS
       //|| dk == PR_TH_LEMMA
       || dk == PR_QUANT_INST
       //|| dk == PR_UNIT_RESOLUTION
       //|| dk == PR_LEMMA
	   )
      return false;
    if(dk == PR_HYPOTHESIS && hyps.find(con) != hyps.end())
      ; //std::cout << "blif!\n";
    if(dk == PR_HYPOTHESIS
       || dk == PR_LEMMA)
      ; //std::cout << "foo!\n";
    if(dk == PR_TH_LEMMA && num_prems(proof) == 0){
      // Check if this is an axiom instance
      get_axiom_instance(conc(proof));
    }

    // #define SIMPLE_PROOFS    
#ifdef SIMPLE_PROOFS
    if(!(dk == PR_TRANSITIVITY
	 || dk == PR_MONOTONICITY))
      local_antes_simple = false;
#endif

    unsigned nprems = num_prems(proof);
    for(unsigned i = 0; i < nprems; i++){
      ast arg = prem(proof,i);
      try {
        if(!add_local_antes(arg, hyps, dk == PR_UNIT_RESOLUTION && i == 0))
          return false;
      }
      catch (non_lit_local_ante) {
        std::cout << "\n";
        show_step(proof);
        show(conc(proof));
        throw non_lit_local_ante();
      }
    }
    return true;
  }

  std::vector<ast> lit_trace;
  hash_set<ast> marked_proofs;

  bool proof_has_lit(const ast &proof, const ast &lit){
    AstSet &hyps = get_hyps(proof);
    if(hyps.find(mk_not(lit)) != hyps.end())
      return true;
    std::vector<ast> lits;
    ast con = conc(proof);
    get_Z3_lits(con, lits);
    for(unsigned i = 0; i < lits.size(); i++)
      if(lits[i] == lit)
        return true;
    return false;
  }


  void trace_lit_rec(const ast &lit, const ast &proof, AstHashSet &memo){
    if(memo.find(proof) == memo.end()){
      memo.insert(proof);
      AstSet &hyps = get_hyps(proof);
      std::vector<ast> lits;
      for(AstSet::iterator it = hyps.begin(), en = hyps.end(); it != en; ++it)
	lits.push_back(mk_not(*it));
      ast con = conc(proof);
      get_Z3_lits(con, lits);
      for(unsigned i = 0; i < lits.size(); i++){
	if(lits[i] == lit){
	  print_expr(std::cout,proof);
          std::cout << "\n";
          marked_proofs.insert(proof);
	  pfrule dk = pr(proof);
	  if(dk == PR_UNIT_RESOLUTION || dk == PR_LEMMA){
	    unsigned nprems = num_prems(proof);
	    for(unsigned i = 0; i < nprems; i++){
	      ast arg = prem(proof,i);
	      trace_lit_rec(lit,arg,memo);
	    }
	  }
	  else
	    lit_trace.push_back(proof);
	}
      }
    }
  }
  
  ast traced_lit;

  int trace_lit(const ast &lit, const ast &proof){
    marked_proofs.clear();
    lit_trace.clear();
    traced_lit = lit;
    AstHashSet memo;
    trace_lit_rec(lit,proof,memo);
    return lit_trace.size();
  }

  bool is_literal_or_lit_iff(const ast &lit){
    if(my_is_literal(lit)) return true;
    if(op(lit) == Iff){
      return my_is_literal(arg(lit,0)) && my_is_literal(arg(lit,1));
    }
    return false;
  }

  bool my_is_literal(const ast &lit){
    ast abslit = is_not(lit) ? arg(lit,0) : lit;
    int f = op(abslit);
    return !(f == And || f == Or || f == Iff);
  }

  void print_lit(const ast &lit){
    ast abslit = is_not(lit) ? arg(lit,0) : lit;
    if(!is_literal_or_lit_iff(lit)){
      if(is_not(lit)) std::cout << "~";
      std::cout << "[";
      print_expr(std::cout,abslit);
      std::cout << "]";
    }
    else
      print_expr(std::cout,lit);
  }

  void show_lit(const ast &lit){
    print_lit(lit);
    std::cout << "\n";
  }

  void print_z3_lit(const ast &a){
    print_lit(from_ast(a));
  }

  void show_z3_lit(const ast &a){
    print_z3_lit(a);
    std::cout << "\n";
  }

  
  void show_con(const ast &proof, bool brief){
    if(!traced_lit.null() && proof_has_lit(proof,traced_lit))
      std::cout << "(*) ";
    ast con = conc(proof);
    AstSet &hyps = get_hyps(proof);
    int count = 0;
    for(AstSet::iterator it = hyps.begin(), en = hyps.end(); it != en; ++it){
      if(brief && ++count > 5){
         std::cout << "... ";
         break;
      }
      print_lit(*it);
      std::cout << " ";
    }
    std::cout << "|- ";
    std::vector<ast> lits;
    get_Z3_lits(con,lits);
    for(unsigned i = 0; i < lits.size(); i++){
      print_lit(lits[i]);
      std::cout << " ";
    }
    std::cout << "\n";
  }

  void show_step(const  ast &proof){
    std::cout << "\n";
    unsigned nprems = num_prems(proof);
    for(unsigned i = 0; i < nprems; i++){
       std::cout << "(" << i << ") ";
       ast arg = prem(proof,i);
       show_con(arg,true);
    }
    std::cout << "|------ ";
    std::cout << string_of_symbol(sym(proof)) << "\n";
    show_con(proof,false);
  }

  void show_marked( const ast &proof){
    std::cout << "\n";
    unsigned nprems = num_prems(proof);
    for(unsigned i = 0; i < nprems; i++){
       ast arg = prem(proof,i);
       if(!traced_lit.null() && proof_has_lit(arg,traced_lit)){
          std::cout << "(" << i << ") ";
          show_con(arg,true);
       }
    }
  }

  std::vector<ast> pfhist;
  int pfhist_pos;
  
  void pfgoto(const ast &proof){
    if(pfhist.size() == 0)
      pfhist_pos = 0;
    else pfhist_pos++;
    pfhist.resize(pfhist_pos);
    pfhist.push_back(proof);
    show_step(proof);
  }

  void show_nll(non_local_lits *nll){
     if(!nll)return;
     for(ResolventAppSet::iterator it = nll->proofs.begin(), en = nll->proofs.end(); it != en; ++it){
       Z3_resolvent *res = *it;
       show_step(res->proof);
       std::cout << "Pivot: ";
       show(res->pivot);
       std::cout << std::endl;
     }
  }
  
  void pfback(){
    if(pfhist_pos > 0){
      pfhist_pos--;
      show_step(pfhist[pfhist_pos]);
    }
  }

  void pffwd(){
    if(pfhist_pos < ((int)pfhist.size()) - 1){
      pfhist_pos++;
      show_step(pfhist[pfhist_pos]);
    }
  }

  void pfprem(int i){
    if(pfhist.size() > 0){
      ast proof = pfhist[pfhist_pos];
      unsigned nprems = num_prems(proof);
      if(i >= 0 && i < (int)nprems)
	pfgoto(prem(proof,i));
    }
  }

  int extract_th_lemma_common(std::vector<ast> &lits, non_local_lits *nll, bool lemma_nll = true){
    std::vector<ast> la = local_antes;
    local_antes.clear();  // clear antecedents for next lemma
    antes_added.clear();
    // std::vector<int> lits;
    AstSet hyps; // no hyps
    for(unsigned i = 0; i < la.size(); i++)
      lits.push_back(mk_not(from_ast(conc(la[i]))));
    // lits.push_back(from_ast(conc(proof)));
    Iproof::node res =fix_lemma(lits,hyps, lemma_nll ? nll : 0);
    for(unsigned i = 0; i < la.size(); i++){
      Iproof::node q = translate_main(la[i],nll,false);
      ast pnode = from_ast(conc(la[i]));
      assert(is_local(pnode) ||  equivs.find(pnode) != equivs.end());
      Iproof::node neg = res;
      Iproof::node pos = q;
      if(is_not(pnode)){
	pnode = mk_not(pnode);
	std::swap(neg,pos);
      }
      try {
        res = iproof->make_resolution(pnode,neg,pos);
      }
      catch (const iz3proof::proof_error){
        std::cout << "\nresolution error in theory lemma\n";
        std::cout << "lits:\n";
        for(unsigned j = 0; j < lits.size(); j++)
          show_lit(lits[j]);
        std::cout << "\nstep:\n";
        show_step(la[i]);
        throw invalid_lemma();
      }
    }
    return res;
  }

  Iproof::node extract_simple_proof(const ast &proof, hash_set<ast> &leaves){
    if(leaves.find(proof) != leaves.end())
      return iproof->make_hypothesis(conc(proof));
    ast con = from_ast(conc(proof));
    pfrule dk = pr(proof);
    unsigned nprems = num_prems(proof);
    std::vector<Iproof::node> args(nprems);
    for(unsigned i = 0; i < nprems; i++){
      ast arg = prem(proof,i);
      args[i] = extract_simple_proof(arg,leaves);
    }

    switch(dk){
    case PR_TRANSITIVITY:
      return iproof->make_transitivity(con,args[0],args[1]);
    case PR_MONOTONICITY:
      return iproof->make_congruence(con,args);
    case PR_REFLEXIVITY:
      return iproof->make_reflexivity(con);
    case PR_SYMMETRY:
      return iproof->make_symmetry(con,args[0]);
    }
    assert(0 && "extract_simple_proof: unknown op");
    return 0;
  }

  int extract_th_lemma_simple(const ast &proof, std::vector<ast> &lits){
    std::vector<ast> la = local_antes;
    local_antes.clear();  // clear antecedents for next lemma
    antes_added.clear();

    hash_set<ast> leaves;
    for(unsigned i = 0; i < la.size(); i++)
      leaves.insert(la[i]);
    
    Iproof::node ipf = extract_simple_proof(proof,leaves);
    ast con = from_ast(conc(proof));
    Iproof::node hyp = iproof->make_hypothesis(mk_not(con));
    ipf = iproof->make_eqcontra(ipf,hyp);

    // std::vector<int> lits;
    AstSet hyps; // no hyps
    for(unsigned i = 0; i < la.size(); i++)
      lits.push_back(mk_not(from_ast(conc(la[i]))));
    // lits.push_back(from_ast(conc(proof)));

    Iproof::node res = iproof->make_contra(ipf,lits);

    for(unsigned i = 0; i < la.size(); i++){
      Iproof::node q = translate_main(la[i],0,false);
      ast pnode = from_ast(conc(la[i]));
      assert(is_local(pnode) ||  equivs.find(pnode) != equivs.end());
      Iproof::node neg = res;
      Iproof::node pos = q;
      if(is_not(pnode)){
	pnode = mk_not(pnode);
	std::swap(neg,pos);
      }
      try {
        res = iproof->make_resolution(pnode,neg,pos);
      }
      catch (const iz3proof::proof_error){
        std::cout << "\nresolution error in theory lemma\n";
        std::cout << "lits:\n";
        for(unsigned j = 0; j < lits.size(); j++)
          show_lit(lits[j]);
        std::cout << "\nstep:\n";
        show_step(la[i]);
        throw invalid_lemma();
      }
    }
    return res;
  }

  // #define NEW_EXTRACT_TH_LEMMA

  void get_local_hyps(const ast &proof, std::set<ast> &res){
    std::set<ast> hyps = get_hyps(proof);
    for(std::set<ast>::iterator it = hyps.begin(), en = hyps.end(); it != en; ++it){
      ast hyp = *it;
      if(is_local(hyp))
        res.insert(hyp);
    }
  }

  int extract_th_lemma(ast proof, std::vector<ast> &lits, non_local_lits *nll){
    pfrule dk = pr(proof);
    unsigned nprems = num_prems(proof);
#ifdef NEW_EXTRACT_TH_LEMMA
    if(nprems == 0 && !nll)
#else
    if(nprems == 0)
#endif
      return 0;
    if(nprems == 0 && dk == PR_TH_LEMMA)
      // Check if this is an axiom instance
      get_axiom_instance(conc(proof));

    local_antes_simple = true;
    for(unsigned i = 0; i < nprems; i++){
      ast arg = prem(proof,i);
      if(!add_local_antes(arg,get_hyps(proof))){
	local_antes.clear();  // clear antecedents for next lemma
	antes_added.clear();
	antes.clear();
	return 0;
      }
    }
#ifdef NEW_EXTRACT_TH_LEMMA
    bool lemma_nll = nprems > 1;
    if(nll && !lemma_nll){
      lemma_nll = false;
      // std::cout << "lemma count = " << nll_lemma_count << "\n";
      for(ResolventAppSet::iterator it = nll->proofs.begin(), en = nll->proofs.end(); it != en; ++it){
	Z3_resolvent *res = *it;
        ast arg = res->proof;
        std::set<ast> loc_hyps; get_local_hyps(arg,loc_hyps); 
        if(!add_local_antes(arg,loc_hyps)){
	  local_antes.clear();  // clear antecedents for next lemma
	  antes_added.clear();
	  antes.clear();
	  return 0;
        }
      }
      collect_all_resolvent_lits(nll,lits);
    }
    int my_count = nll_lemma_count++;
    int res;
    try {
      res = extract_th_lemma_common(lits,nll,lemma_nll);
    }
#if 1
    catch (const invalid_lemma &) {
      std::cout << "\n\nlemma: " << my_count;
      std::cout << "\n\nproof node: \n";
      show_step(proof);
      std::cout << "\n\nnon-local: \n";
      show_nll(nll);
      pfgoto(nll->proofs[0]->proof);
      show(conc(pfhist.back()));
      pfprem(1);
      show(conc(pfhist.back()));
      pfprem(0);
      show(conc(pfhist.back()));
      pfprem(0);
      show(conc(pfhist.back()));
      pfprem(0);
      show(conc(pfhist.back()));
      std::cout << "\n\nliterals: \n";
      for(int i = 0; i < lits.size(); i++)
        show_lit(lits[i]);
      throw invalid_lemma();
    }
#endif
    
    return res;
#else
#ifdef SIMPLE_PROOFS
    if(local_antes_simple && !nll)
      return extract_th_lemma_simple(proof, lits);
#endif
    return extract_th_lemma_common(lits,nll);
#endif
  }

  int extract_th_lemma_ur(ast proof, int position, std::vector<ast> &lits, non_local_lits *nll){
    for(int i = 0; i <= position; i++){
      ast arg = prem(proof,i);
      if(!add_local_antes(arg,get_hyps(proof),i==0)){
	local_antes.clear();  // clear antecedents for next lemma
	antes_added.clear();
	antes.clear();
	return 0;
      }
    }
    return extract_th_lemma_common(lits,nll);
  }

  // see if any of the pushed resolvents are resolutions
  // push the current proof into the latest such
  int push_into_resolvent(ast proof, std::vector<ast> &lits, non_local_lits *nll, bool expect_clause){
    if(!nll) return 0;
    if(num_args(proof) > 1) return 0;
    ResolventAppSet resos = nll->proofs;
    int pos = resos.size()-1;
    for( ResolventAppSet::reverse_iterator it = resos.rbegin(), en = resos.rend(); it != en; ++it, --pos){
      Z3_resolvent *reso = *it;
      ast ante = reso->proof;
      ast pivot = reso->pivot;
      bool is_unit = reso->is_unit;
      pfrule dk = pr(ante);
      bool pushable = dk == PR_UNIT_RESOLUTION || dk == PR_LEMMA;
      if(!pushable && num_args(ante) > 1){
#if 0
        if (!is_local(conc(ante)))
          std::cout << "non-local ";
        std::cout << "pushable!\n";
#endif
        pushable = true;
      }
      if(pushable){
	// remove the resolvent from list and add new clause as resolvent
	resos.erase((++it).base());
	for(; pos < (int)resos.size(); pos++){
          Z3_resolvent *r = resos[pos];
          resos[pos] = find_resolvent(r->proof,r->is_unit,mk_not(pivot));
        }
        resos.push_back(find_resolvent(proof,!expect_clause,mk_not(pivot)));
	non_local_lits *new_nll = find_nll(resos);
	try {
	  int res = translate_main(ante,new_nll,!is_unit);
	  return res;
	}
	catch (const invalid_lemma &) {
	  std::cout << "\n\npushing: \n";
	  std::cout << "nproof node: \n";
	  show_step(proof);
	  std::cout << "\n\nold non-local: \n";
	  show_nll(nll);
	  std::cout << "\n\nnew non-local: \n";
	  show_nll(new_nll);
	  throw invalid_lemma();
	}
      }
    }
    return 0; // no pushed resolvents are resolution steps
  }

  non_local_lits *find_nll(ResolventAppSet &proofs){
    if(proofs.empty())
      return (non_local_lits *)0;
    std::pair<non_local_lits,non_local_lits *> foo(non_local_lits(proofs),(non_local_lits *)0);
    std::pair<hash_map<non_local_lits, non_local_lits *>::iterator,bool> bar = 
      non_local_lits_unique.insert(foo);
    non_local_lits *&res = bar.first->second;
    if(bar.second)
      res = new non_local_lits(bar.first->first);
    return res;
  }

  Z3_resolvent *find_resolvent(ast proof, bool unit, ast pivot){
    std::pair<Z3_resolvent,Z3_resolvent *> foo(Z3_resolvent(proof,unit,pivot),(Z3_resolvent *)0);
    std::pair<hash_map<Z3_resolvent, Z3_resolvent *>::iterator,bool> bar = 
      Z3_resolvent_unique.insert(foo);
    Z3_resolvent *&res = bar.first->second;
    if(bar.second)
      res = new Z3_resolvent(bar.first->first);
    return res;
  }

  // translate a unit resolution at position pos of given app
  int translate_ur(ast proof, int position, non_local_lits *nll){
    ast ante =  prem(proof,position);
    if(position <= 0)
      return translate_main(ante, nll);
    ast pnode = conc(ante);
    ast pnode_abs = !is_not(pnode) ? pnode : mk_not(pnode);
    if(is_local(pnode) ||  equivs.find(pnode) != equivs.end()){
      Iproof::node neg = translate_ur(proof,position-1,nll);
      Iproof::node pos = translate_main(ante, nll, false);
      if(is_not(pnode)){
	pnode = mk_not(pnode);
	std::swap(neg,pos);
      }
      try {
         return iproof->make_resolution(pnode,neg,pos);
      }
      catch (const iz3proof::proof_error){
        std::cout << "resolution error in unit_resolution, position" << position << "\n";
	show_step(proof);
        throw invalid_lemma();
      }
    }
    else {
      // non-local pivot we have no local equivalent for
      if(true){
	// try pushing the non-local resolution up
        pfrule dk = pr(ante);
	non_local_lits *old_nll = nll;
        if(dk == PR_HYPOTHESIS)
	  ; //std::cout << "non-local hyp!\n";  // resolving with a hyp is a no-op 
        else {
          ResolventAppSet new_proofs;
	  if(nll) new_proofs = nll->proofs;
	  Z3_resolvent *reso = find_resolvent(ante,true,pnode);
	  new_proofs.push_back(reso);
	  nll = find_nll(new_proofs);
        }
	try {
 	  return translate_ur(proof,position-1,nll);
	}
	catch (const invalid_lemma &) {
	  if(old_nll != nll){
	    std::cout << "\n\nadded_nll: \n";
	    std::cout << "nproof node: \n";
	    show_step(proof);
	    std::cout << "\n\new non-local step: \n";
	    show_step(nll->proofs.back()->proof);
	  }
	  throw invalid_lemma();
	}

      }
      else {
	// just make a lemma
	std::vector<ast> lits;
	do_unit_resolution(proof,position,lits);
	int res;
	if(!(res = extract_th_lemma_ur(proof,position,lits,nll))){
	  for(int i = 0; i <= position; i++){
	    z3pf p = prem(proof,i);
	    add_antes(p);
	  }
	  res = fix_lemma(lits,get_hyps(proof),nll);
	}
	return res;
      }
    }
  }

  non_local_lits *update_nll(ast proof, bool expect_clause, non_local_lits *nll){
    std::vector<ast> lits;
    collect_proof_clause(proof,expect_clause,lits);
    AstSet litset;
    litset.insert(lits.begin(),lits.end());
    ResolventAppSet to_keep;
    for(int i = nll->proofs.size()-1; i >= 0; --i){
      ast traced_lit = (nll->proofs[i])->pivot;
      ast traced_lit_neg = mk_not(traced_lit);
      if(litset.find(traced_lit) != litset.end() || litset.find(traced_lit_neg) != litset.end()){
	to_keep.push_back(nll->proofs[i]);
	std::vector<ast> reslits;
	AstSet dummy;
	collect_resolvent_lits(nll->proofs[i],dummy,reslits);
	litset.insert(reslits.begin(),reslits.end());
      }	
    }
    if(to_keep.size() == nll->proofs.size()) return nll;
    ResolventAppSet new_proofs;
    for(int i = to_keep.size() - 1; i >= 0; --i)
      new_proofs.push_back(to_keep[i]);
    return find_nll(new_proofs);
  }

  // translate a Z3 proof term into a foci proof term

  Iproof::node translate_main(ast proof, non_local_lits *nll, bool expect_clause = true){
    non_local_lits *old_nll = nll;
    if(nll) nll = update_nll(proof,expect_clause,nll);
    AstToIpf &tr = nll ? non_local_translation[nll] : translation; 
    hash_map<ast,Iproof::node> &trc = expect_clause ? tr.first : tr.second;
    std::pair<ast,int> foo(proof,INT_MAX);
    std::pair<AstToInt::iterator, bool> bar = trc.insert(foo);
    int &res = bar.first->second;
    if(!bar.second) return res;


    try {
    int frame = get_locality(proof);
    if(frame != -1){
      ast e = from_ast(conc(proof));
      if(frame >= frames) frame = frames - 1;
      std::vector<ast> foo;
      if(expect_clause)
	get_Z3_lits(conc(proof),foo);
      else
	foo.push_back(e);
      AstSet &hyps = get_hyps(proof);
      for(AstSet::iterator it = hyps.begin(), en = hyps.end(); it != en; ++it)
	foo.push_back(mk_not(*it));
      res = iproof->make_assumption(frame,foo);
      return res;
    }

    pfrule dk = pr(proof);
    unsigned nprems = num_prems(proof);
    if(dk == PR_UNIT_RESOLUTION){
      res = translate_ur(proof, nprems - 1, nll);
    }
    else if(dk == PR_LEMMA){
      ast contra = prem(proof,0); // this is a proof of false from some hyps
      res = translate_main(contra, nll);
      if(!expect_clause){
	std::vector<ast> foo;  // the negations of the hyps form a clause
	foo.push_back(from_ast(conc(proof)));
	AstSet &hyps = get_hyps(proof);
	for(AstSet::iterator it = hyps.begin(), en = hyps.end(); it != en; ++it)
	  foo.push_back(mk_not(*it));
	res = iproof->make_contra(res,foo);
      }
    }
    else {
      std::vector<ast> lits;
      ast con = conc(proof);
      if(expect_clause)
	get_Z3_lits(con, lits);
      else
	lits.push_back(from_ast(con));
#ifdef NEW_EXTRACT_TH_LEMMA
      if(!(res = push_into_resolvent(proof,lits,nll,expect_clause))){
	if(!(res = extract_th_lemma(proof,lits,nll))){
#else
      if(!(res = extract_th_lemma(proof,lits,nll))){
	if(!(res = push_into_resolvent(proof,lits,nll,expect_clause))){
#endif
	  // std::cout << "extract theory lemma failed\n";
          add_antes(proof);
	  res = fix_lemma(lits,get_hyps(proof),nll);
	}
      }
    }
#ifdef CHECK_PROOFS

	if(0){
	  AstSet zpf_con_lits, ipf_con_lits;
	  get_local_conclusion_lits(proof, expect_clause, zpf_con_lits);
          if(nll){
            for(unsigned i = 0; i < nll->proofs.size(); i++)
              get_local_conclusion_lits(nll->proofs[i]->proof,!nll->proofs[i]->is_unit,zpf_con_lits);
          }
	  std::vector<ast> ipf_con;
	  iproof->get_conclusion(res,ipf_con);
	  for(unsigned i = 0; i < ipf_con.size(); i++)
	    ipf_con_lits.insert(ipf_con[i]);
	  if(!(ipf_con_lits == zpf_con_lits)){
	    std::cout << "proof error:\n";
	    std::cout << "expected lits:\n";
	    for(AstSet::iterator hit = zpf_con_lits.begin(), hen = zpf_con_lits.end(); hit != hen; ++hit)
	      show_lit(*hit);
	    std::cout << "got lits:\n";
	    for(AstSet::iterator hit = ipf_con_lits.begin(), hen = ipf_con_lits.end(); hit != hen; ++hit)
	      show_lit(*hit);
	    std::cout << "\nproof step:";
	    show_step(proof);
	    std::cout << "\n";
	    throw invalid_lemma();
	  }
	}
#endif

    return res;
  }

	catch (const invalid_lemma &) {
	  if(old_nll != nll){
	    std::cout << "\n\nupdated nll: \n";
	    std::cout << "nproof node: \n";
	    show_step(proof);
	    std::cout << "\n\new non-local: \n";
	    show_nll(nll);
	  }
	  throw invalid_lemma();
	}

  }

  // Proof translation is in two stages:
  // 1) Translate ast proof term to Zproof
  // 2) Translate Zproof to Iproof

  Iproof::node translate(ast proof, Iproof &dst){
    iproof = &dst;
    Iproof::node Ipf = translate_main(proof,0);  // builds result in dst
    return Ipf;
  }

  iz3translation_direct(iz3mgr &mgr,
			iz3secondary *_secondary,
			const std::vector<std::vector<ast> > &cnsts,
			const std::vector<int> &parents,
			const std::vector<ast> &theory)
    : iz3translation(mgr, cnsts, parents, theory)
  {
    secondary = _secondary;
    frames = cnsts.size();
    traced_lit = ast();
  }

  ~iz3translation_direct(){
    for(hash_map<non_local_lits, non_local_lits *>::iterator
	  it = non_local_lits_unique.begin(),
	  en = non_local_lits_unique.end();
	it != en;
	++it)
      delete it->second;

    for(hash_map<Z3_resolvent, Z3_resolvent *>::iterator
	  it = Z3_resolvent_unique.begin(),
	  en = Z3_resolvent_unique.end();
	it != en;
	++it)
      delete it->second;
  }
};




#ifdef IZ3_TRANSLATE_DIRECT

iz3translation *iz3translation::create(iz3mgr &mgr,
				       iz3secondary *secondary,
				       const std::vector<std::vector<ast> > &cnsts,
				       const std::vector<int> &parents,
				       const std::vector<ast> &theory){
  return new iz3translation_direct(mgr,secondary,cnsts,parents,theory);
}


#if 1

void iz3translation_direct_trace_lit(iz3translation_direct *p, iz3mgr::ast lit, iz3mgr::ast proof){
   p->trace_lit(lit, proof);
}

void iz3translation_direct_show_step(iz3translation_direct *p,  iz3mgr::ast proof){
   p->show_step(proof);
}

void iz3translation_direct_show_marked(iz3translation_direct *p,  iz3mgr::ast proof){
   p->show_marked(proof);
}

void iz3translation_direct_show_lit(iz3translation_direct *p,  iz3mgr::ast lit){
  p->show_lit(lit);
}

void iz3translation_direct_show_z3_lit(iz3translation_direct *p, iz3mgr::ast a){
  p->show_z3_lit(a);
}

void iz3translation_direct_pfgoto(iz3translation_direct *p, iz3mgr::ast proof){
  p->pfgoto(proof);
}
  
void iz3translation_direct_show_nll(iz3translation_direct *p, non_local_lits *nll){
  p->show_nll(nll);
}

void iz3translation_direct_pfback(iz3translation_direct *p ){
  p->pfback();
}

void iz3translation_direct_pffwd(iz3translation_direct *p ){
  p->pffwd();
}

void iz3translation_direct_pfprem(iz3translation_direct *p, int i){
  p->pfprem(i);
}


struct stdio_fixer {
  stdio_fixer(){
    std::cout.rdbuf()->pubsetbuf(0,0);
  }

} my_stdio_fixer;

#endif

#endif


