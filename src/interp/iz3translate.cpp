/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

   iz3translate.cpp

Abstract:

   Translate a Z3 proof to in interpolated proof.

Author:

    Ken McMillan (kenmcmil)

Revision History:

--*/

#include "iz3translate.h"
#include "iz3proof.h"
#include "iz3profiling.h"
#include "iz3interp.h"
#include "iz3proof_itp.h"

#include <assert.h>
#include <algorithm>
#include <stdio.h>
#include <fstream>
#include <sstream>
#include <iostream>
#include <set>

//using std::vector;
#ifndef WIN32
using namespace stl_ext;
#endif



/* This translator goes directly from Z3 proofs to interpolated
   proofs without an intermediate representation. No secondary
   prover is used.
*/

class iz3translation_full : public iz3translation {
public:


  typedef iz3proof_itp Iproof;
  
  Iproof *iproof;

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
  AstToIpf translation;                     // Z3 proof nodes to Iproof nodes
  
  AstToInt frame_map;                      // map assertions to frames
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
  AstToBool occurs_in_memo;                // memo of occurs_in function

  AstHashSet cont_eq_memo;                // memo of cont_eq function

  AstToAst subst_memo;                    // memo of subst function

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
      AstToInt::iterator it = frame_map.find(ass);
      assert(it != frame_map.end());
      res = it->second;
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

  // get the lits of a Z3 clause
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
    // antes.push_back(std::pair<ast,int>(cnst,frame));
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
                        // int frame = range_min(ast_scope(res)); TODO
                        // antes.push_back(std::pair<ast,int>(res,frame));
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
	// int frame = range_min(ast_scope(res)); TODO
	// antes.push_back(std::pair<ast,int>(res,frame));
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

  // does variable occur in expression?
  int occurs_in1(ast var, ast e){
    std::pair<ast,bool> foo(e,false);
    std::pair<AstToBool::iterator,bool> bar = occurs_in_memo.insert(foo);
    bool &res = bar.first->second;
    if(bar.second){
      if(e == var) res = true;
      int nargs = num_args(e);
      for(int i = 0; i < nargs; i++)
	res |= occurs_in1(var,arg(e,i));
    }
    return res;
  }

  int occurs_in(ast var, ast e){
    occurs_in_memo.clear();
    return occurs_in1(var,e);
  }
  
  // find a controlling equality for a given variable v in a term
  // a controlling equality is of the form v = t, which, being
  // false would force the formula to have the specifid truth value
  // returns t, or null if no such

  ast cont_eq(bool truth, ast v, ast e){
    if(is_not(e)) return cont_eq(!truth,v,arg(e,0));
    if(cont_eq_memo.find(e) != cont_eq_memo.end())
      return ast();
    cont_eq_memo.insert(e);
    if(!truth && op(e) == Equal){
      if(arg(e,0) == v) return(arg(e,1));
      if(arg(e,1) == v) return(arg(e,0));
    }
    if((!truth && op(e) == And) || (truth && op(e) == Or)){
      int nargs = num_args(e);
      for(int i = 0; i < nargs; i++){
	ast res = cont_eq(truth, v, arg(e,i));
	if(!res.null()) return res;
      }
    }
    return ast();
  }

  // substitute a term t for unbound occurrences of variable v in e
  
  ast subst(ast var, ast t, ast e){
    if(e == var) return t;
    std::pair<ast,ast> foo(e,ast());
    std::pair<AstToAst::iterator,bool> bar = subst_memo.insert(foo);
    ast &res = bar.first->second;
    if(bar.second){
      int nargs = num_args(e);
      std::vector<ast> args(nargs);
      for(int i = 0; i < nargs; i++)
	args[i] = subst(var,t,arg(e,i));
      opr f = op(e);
      if(f == Equal && args[0] == args[1]) res = mk_true();
      else res = clone(e,args);
    }
    return res;
  }

  // apply a quantifier to a formula, with some optimizations
  // 1) bound variable does not occur -> no quantifier
  // 2) bound variable must be equal to some term -> substitute

  ast apply_quant(opr quantifier, ast var, ast e){
    if(!occurs_in(var,e))return e;
    cont_eq_memo.clear();
    ast cterm = cont_eq(quantifier == Forall, var, e);
    if(!cterm.null()){
      subst_memo.clear();
      return subst(var,cterm,e);
    }
    std::vector<ast> bvs; bvs.push_back(var);
    return make_quant(quantifier,bvs,e);
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



  // translate a unit resolution sequence
  Iproof::node translate_ur(ast proof){
    ast prem0 = prem(proof,0);
    Iproof::node itp = translate_main(prem0,true);
    std::vector<ast> clause;
    get_Z3_lits(conc(prem0),clause);
    int nprems = num_prems(proof);
    for(int position = 1; position < nprems; position++){
      ast ante =  prem(proof,position);
      ast pnode = conc(ante);
      ast pnode_abs = !is_not(pnode) ? pnode : mk_not(pnode);
      Iproof::node neg = itp;
      Iproof::node pos = translate_main(ante, false);
      if(is_not(pnode)){
	pnode = mk_not(pnode);
	std::swap(neg,pos);
      }
      std::vector<ast> unit(1);
      unit[0] = conc(ante);
      resolve(mk_not(conc(ante)),clause,unit);
      itp = iproof->make_resolution(pnode,clause,neg,pos);
    }
    return itp;
  }

  // get an inequality in the form 0 <= t where t is a linear term
  ast rhs_normalize_inequality(const ast &ineq){
    ast zero = make_int("0");
    ast thing = make(Leq,zero,zero);
    linear_comb(thing,make_int("1"),ineq);
    thing = simplify_ineq(thing);
    return thing;
  }

  // get an inequality in the form t <= c or t < c, there t is affine and c constant
  ast normalize_inequality(const ast &ineq){
    ast zero = make_int("0");
    ast thing = make(Leq,zero,zero);
    linear_comb(thing,make_int("1"),ineq);
    thing = simplify_ineq(thing);
    ast lhs = arg(thing,0);
    ast rhs = arg(thing,1);
    opr o = op(rhs);
    if(o != Numeral){
      if(op(rhs) == Plus){
	int nargs = num_args(rhs);
	ast const_term = zero;
	int i = 0;
	if(nargs > 0 && op(arg(rhs,0)) == Numeral){
	  const_term = arg(rhs,0);
	  i++;
	}
	if(i < nargs){
	  std::vector<ast> non_const;
	  for(; i < nargs; i++)
	    non_const.push_back(arg(rhs,i));
	  lhs = make(Sub,lhs,make(Plus,non_const));
	}
	rhs = const_term;
      }
      else {
	lhs = make(Sub,lhs,make(Plus,rhs));
	rhs = zero;
      }
      lhs = z3_simplify(lhs);
      rhs = z3_simplify(rhs);
      thing = make(op(thing),lhs,rhs);
    }
    return thing;
  }

  void get_linear_coefficients(const ast &t, std::vector<rational> &coeffs){
    if(op(t) == Plus){
      int nargs = num_args(t);
      for(int i = 0; i < nargs; i++)
	coeffs.push_back(get_coeff(arg(t,i)));
    }
    else
      coeffs.push_back(get_coeff(t));
  }

  /* given an affine term t, get the GCD of the coefficients in t. */
  ast gcd_of_coefficients(const ast &t){
    std::vector<rational> coeffs;
    get_linear_coefficients(t,coeffs);
    if(coeffs.size() == 0)
      return make_int("1"); // arbitrary
    rational d = coeffs[0];
    for(unsigned i = 1; i < coeffs.size(); i++){
      d = gcd(d,coeffs[i]);
    }
    return make_int(d);
  }

  ast get_bounded_variable(const ast &ineq, bool &lb){
    ast nineq = normalize_inequality(ineq);
    ast lhs = arg(nineq,0);
    switch(op(lhs)){
    case Uninterpreted: 
      lb = false;
      return lhs;
    case Times:
      if(arg(lhs,0) == make_int(rational(1)))
	lb = false;
      else if(arg(lhs,0) == make_int(rational(-1)))
	lb = true;
      else 
	throw unsupported();
      return arg(lhs,1);
    default:
      throw unsupported();
    }
  }

  rational get_term_coefficient(const ast &t1, const ast &v){
    ast t = arg(normalize_inequality(t1),0);
    if(op(t) == Plus){
      int nargs = num_args(t);
      for(int i = 0; i < nargs; i++){
	if(get_linear_var(arg(t,i)) == v)
	  return get_coeff(arg(t,i));
      }
    }
    else
      if(get_linear_var(t) == v)
	return get_coeff(t);
    return rational(0);
  }


  Iproof::node GCDtoDivRule(const ast &proof, bool pol, std::vector<rational> &coeffs, std::vector<Iproof::node> &prems, ast &cut_con){
    // gather the summands of the desired polarity
    std::vector<Iproof::node>  my_prems;
    std::vector<ast>  my_coeffs;
    std::vector<Iproof::node>  my_prem_cons;
    for(unsigned i = 0; i < coeffs.size(); i++){
      rational &c = coeffs[i];
      if(pol ? c.is_pos() : c.is_neg()){
	my_prems.push_back(prems[i]);
	my_coeffs.push_back(pol ? make_int(c) : make_int(-c));
	my_prem_cons.push_back(conc(prem(proof,i)));
      }
    }
    ast my_con = sum_inequalities(my_coeffs,my_prem_cons);

    // handle generalized GCD test. sadly, we dont' get the coefficients...
    if(coeffs[0].is_zero()){
      bool lb;
      int xtra_prem = 0;
      ast bv = get_bounded_variable(conc(prem(proof,0)),lb);
      rational bv_coeff = get_term_coefficient(my_con,bv);
      if(bv_coeff.is_pos() != lb)
	xtra_prem = 1;
      if(bv_coeff.is_neg())
	bv_coeff = -bv_coeff;

      my_prems.push_back(prems[xtra_prem]);
      my_coeffs.push_back(make_int(bv_coeff));
      my_prem_cons.push_back(conc(prem(proof,xtra_prem)));
      my_con = sum_inequalities(my_coeffs,my_prem_cons);
    }

    my_con = normalize_inequality(my_con);
    Iproof::node hyp = iproof->make_hypothesis(mk_not(my_con));
    my_prems.push_back(hyp);
    my_coeffs.push_back(make_int("1"));
    my_prem_cons.push_back(mk_not(my_con));
    Iproof::node res = iproof->make_farkas(mk_false(),my_prems,my_prem_cons,my_coeffs);

    ast t = arg(my_con,0);
    ast c = arg(my_con,1);
    ast d = gcd_of_coefficients(t);
    t = z3_simplify(mk_idiv(t,d));
    c = z3_simplify(mk_idiv(c,d));
    cut_con = make(op(my_con),t,c);
    return iproof->make_cut_rule(my_con,d,cut_con,res);
  }


  ast divide_inequalities(const ast &x, const ast&y){
    std::vector<rational> xcoeffs,ycoeffs;
    get_linear_coefficients(arg(x,1),xcoeffs);
    get_linear_coefficients(arg(y,1),ycoeffs);
    if(xcoeffs.size() != ycoeffs.size() || xcoeffs.size() == 0)
      throw "bad assign-bounds lemma";
    rational ratio = xcoeffs[0]/ycoeffs[0];
    return make_int(ratio); // better be integer!
  }

  ast AssignBounds2Farkas(const ast &proof, const ast &con){
    std::vector<ast> farkas_coeffs;
    get_assign_bounds_coeffs(proof,farkas_coeffs);
    std::vector<ast> lits;
    int nargs = num_args(con);
    if(nargs != (int)(farkas_coeffs.size()))
      throw "bad assign-bounds theory lemma";
#if 0
    for(int i = 1; i < nargs; i++)
      lits.push_back(mk_not(arg(con,i)));
    ast sum = sum_inequalities(farkas_coeffs,lits);
    ast conseq = rhs_normalize_inequality(arg(con,0));
    ast d = divide_inequalities(sum,conseq);
    std::vector<ast> my_coeffs;
    my_coeffs.push_back(d);
    for(unsigned i = 0; i < farkas_coeffs.size(); i++)
      my_coeffs.push_back(farkas_coeffs[i]);
#else
    std::vector<ast> my_coeffs;
#endif
    std::vector<ast> my_cons;
    for(int i = 1; i < nargs; i++){
      my_cons.push_back(mk_not(arg(con,i)));
      my_coeffs.push_back(farkas_coeffs[i]);
    }
    ast farkas_con = normalize_inequality(sum_inequalities(my_coeffs,my_cons));
    my_cons.push_back(mk_not(farkas_con));
    my_coeffs.push_back(make_int("1"));
    std::vector<Iproof::node> my_hyps;
    for(int i = 0; i < nargs; i++)
      my_hyps.push_back(iproof->make_hypothesis(my_cons[i]));
    ast res = iproof->make_farkas(mk_false(),my_hyps,my_cons,my_coeffs);
    res = iproof->make_cut_rule(farkas_con,farkas_coeffs[0],arg(con,0),res);
    return res;
  }

  // translate a Z3 proof term into interpolating proof system

  Iproof::node translate_main(ast proof, bool expect_clause = true){
    AstToIpf &tr = translation; 
    hash_map<ast,Iproof::node> &trc = expect_clause ? tr.first : tr.second;
    std::pair<ast,Iproof::node> foo(proof,Iproof::node());
    std::pair<hash_map<ast,Iproof::node>::iterator, bool> bar = trc.insert(foo);
    Iproof::node &res = bar.first->second;
    if(!bar.second) return res;

    // Try the locality rule first

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

    // If the proof is not local, break it down by proof rule

    pfrule dk = pr(proof);
    unsigned nprems = num_prems(proof);
    if(dk == PR_UNIT_RESOLUTION){
      res = translate_ur(proof);
    }
    else if(dk == PR_LEMMA){
      ast contra = prem(proof,0); // this is a proof of false from some hyps
      res = translate_main(contra);
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

      // special case 
      if(dk == PR_MODUS_PONENS && pr(prem(proof,0)) == PR_QUANT_INST && pr(prem(proof,1)) == PR_REWRITE ) {
	res = iproof->make_axiom(lits);
	return res;
      }

      // translate all the premises
      std::vector<Iproof::node> args(nprems);
      for(unsigned i = 0; i < nprems; i++)
	args[i] = translate_main(prem(proof,i),false);

      switch(dk){
      case PR_TRANSITIVITY: {
	// assume the premises are x = y, y = z
	ast x = arg(conc(prem(proof,0)),0);
	ast y = arg(conc(prem(proof,0)),1);
	ast z = arg(conc(prem(proof,1)),1);
	res = iproof->make_transitivity(x,y,z,args[0],args[1]);
	break;
      }
      case PR_MONOTONICITY: {
	std::vector<ast> eqs; eqs.resize(args.size());
	for(unsigned i = 0; i < args.size(); i++)
	  eqs[i] = conc(prem(proof,i));
	res = iproof->make_congruence(eqs,con,args);
	break;
      }
      case PR_REFLEXIVITY: {
	res = iproof->make_reflexivity(con);
	break;
      }
      case PR_SYMMETRY: {
	res = iproof->make_symmetry(con,conc(prem(proof,0)),args[0]);
	break;
      }
      case PR_MODUS_PONENS: {
	res = iproof->make_mp(conc(prem(proof,1)),args[0],args[1]);
	break;
      }
      case PR_TH_LEMMA: {
	switch(get_theory_lemma_theory(proof)){
	case ArithTheory:
	  switch(get_theory_lemma_kind(proof)){
	  case FarkasKind: {
	    std::vector<ast> farkas_coeffs, prem_cons;
	    get_farkas_coeffs(proof,farkas_coeffs);
	    prem_cons.resize(nprems);
	    for(unsigned i = 0; i < nprems; i++)
	      prem_cons[i] = conc(prem(proof,i));
	    res = iproof->make_farkas(con,args,prem_cons,farkas_coeffs);
	    break;
	  }
	  case Leq2EqKind: {
	    // conc should be (or x = y (not (leq x y)) (not(leq y z)) )
	    ast xeqy = arg(conc(proof),0);
	    ast x = arg(xeqy,0);
	    ast y = arg(xeqy,1);
	    res = iproof->make_leq2eq(x,y,arg(arg(conc(proof),1),0),arg(arg(conc(proof),2),0));
	    break;
	  }
	  case Eq2LeqKind: {
	    // conc should be (or (not (= x y)) (leq x y))
	    ast xeqy = arg(arg(conc(proof),0),0);
	    ast xleqy = arg(conc(proof),1);
	    ast x = arg(xeqy,0);
	    ast y = arg(xeqy,1);
	    res = iproof->make_eq2leq(x,y,xleqy);
	    break;
	  }
	  case GCDTestKind: {
	    std::vector<rational> farkas_coeffs;
	    get_farkas_coeffs(proof,farkas_coeffs);
	    std::vector<Iproof::node> my_prems; my_prems.resize(2);
	    std::vector<ast> my_prem_cons; my_prem_cons.resize(2);
	    std::vector<ast> my_farkas_coeffs; my_farkas_coeffs.resize(2);
	    my_prems[0] = GCDtoDivRule(proof, true, farkas_coeffs, args, my_prem_cons[0]);
	    my_prems[1] = GCDtoDivRule(proof, false, farkas_coeffs, args, my_prem_cons[1]);
	    ast con = mk_false();
	    my_farkas_coeffs[0] = my_farkas_coeffs[1] = make_int("1");
	    res = iproof->make_farkas(con,my_prems,my_prem_cons,my_farkas_coeffs);
	    break;
	  }
	  case AssignBoundsKind: {
	    res = AssignBounds2Farkas(proof,conc(proof));
	    break;
	  }
	  default:
	    throw unsupported();
	  }
	  break;
	case ArrayTheory: // nothing fancy for this
	  res = iproof->make_axiom(lits);
	  break;
	default:
	  throw unsupported();
	}
	break;
      }
      case PR_HYPOTHESIS: {
	res = iproof->make_hypothesis(conc(proof));
	break;
      }
      case PR_QUANT_INST: {
	res = iproof->make_axiom(lits);
	break;
      }
      default:
	assert(0 && "translate_main: unsupported proof rule");
	throw unsupported();
      }
    }

    return res;
  }

  void clear_translation(){
    translation.first.clear();
    translation.second.clear();
  }

  // We actually compute the interpolant here and then produce a proof consisting of just a lemma

  iz3proof::node translate(ast proof, iz3proof &dst){
    std::vector<ast> itps;
    for(int i = 0; i < frames -1; i++){
      iproof = iz3proof_itp::create(this,range_downward(i),weak_mode());
      Iproof::node ipf = translate_main(proof);
      ast itp = iproof->interpolate(ipf);
      itps.push_back(itp);
      delete iproof;
      clear_translation();
    }
    // Very simple proof -- lemma of the empty clause with computed interpolation
    iz3proof::node Ipf = dst.make_lemma(std::vector<ast>(),itps);  // builds result in dst
    return Ipf;
  }

  iz3translation_full(iz3mgr &mgr,
			iz3secondary *_secondary,
			const std::vector<ast> &cnsts,
			const std::vector<int> &parents,
			const std::vector<ast> &theory)
    : iz3translation(mgr, cnsts, parents, theory)
  {
    for(unsigned i = 0; i < cnsts.size(); i++)
      frame_map[cnsts[i]] = i;
    for(unsigned i = 0; i < theory.size(); i++)
      frame_map[theory[i]] = INT_MAX;
    frames = cnsts.size();
    traced_lit = ast();
  }

  ~iz3translation_full(){
  }
};




#ifdef IZ3_TRANSLATE_FULL

iz3translation *iz3translation::create(iz3mgr &mgr,
				       iz3secondary *secondary,
				       const std::vector<ast> &cnsts,
				       const std::vector<int> &parents,
				       const std::vector<ast> &theory){
  return new iz3translation_full(mgr,secondary,cnsts,parents,theory);
}


#if 1

// This is just to make sure certain methods are compiled, so we can call then from the debugger.

void iz3translation_full_trace_lit(iz3translation_full *p, iz3mgr::ast lit, iz3mgr::ast proof){
   p->trace_lit(lit, proof);
}

void iz3translation_full_show_step(iz3translation_full *p,  iz3mgr::ast proof){
   p->show_step(proof);
}

void iz3translation_full_show_marked(iz3translation_full *p,  iz3mgr::ast proof){
   p->show_marked(proof);
}

void iz3translation_full_show_lit(iz3translation_full *p,  iz3mgr::ast lit){
  p->show_lit(lit);
}

void iz3translation_full_show_z3_lit(iz3translation_full *p, iz3mgr::ast a){
  p->show_z3_lit(a);
}

void iz3translation_full_pfgoto(iz3translation_full *p, iz3mgr::ast proof){
  p->pfgoto(proof);
}
  

void iz3translation_full_pfback(iz3translation_full *p ){
  p->pfback();
}

void iz3translation_full_pffwd(iz3translation_full *p ){
  p->pffwd();
}

void iz3translation_full_pfprem(iz3translation_full *p, int i){
  p->pfprem(i);
}


struct stdio_fixer {
  stdio_fixer(){
    std::cout.rdbuf()->pubsetbuf(0,0);
  }

} my_stdio_fixer;

#endif

#endif


