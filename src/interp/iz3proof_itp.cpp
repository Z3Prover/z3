/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    iz3proof.cpp

Abstract:

   This class defines a simple interpolating proof system.

Author:

    Ken McMillan (kenmcmil)

Revision History:

--*/

#include "iz3proof_itp.h"

#ifndef WIN32
using namespace stl_ext;
#endif


class iz3proof_itp_impl : public iz3proof_itp {

  prover *pv;
  prover::range rng;
  bool weak;

  enum LitType {LitA,LitB,LitMixed};

  hash_map<ast,ast> placeholders;
  symb farkas;

  ast get_placeholder(ast t){
    hash_map<ast,ast>::iterator it = placeholders.find(t);
    if(it != placeholders.end())
      return it->second;
    ast &res = placeholders[t];
    res = mk_fresh_constant("@p",get_type(t));
    std::cout << "placeholder ";
    print_expr(std::cout,res);
    std::cout << " = ";
    print_expr(std::cout,t);
    std::cout << std::endl;
    return res;
  }

  ast make_farkas(ast &coeff, ast &ineq){
    return make(farkas,coeff,ineq);
  }

  LitType get_term_type(const ast &lit){
    prover::range r = pv->ast_scope(lit);
    if(pv->range_is_empty(r))
      return LitMixed;
    if(weak) {
      if(pv->range_min(r) == SHRT_MIN)
	return pv->range_contained(r,rng) ? LitA : LitB;
      else
	return pv->ranges_intersect(r,rng) ? LitA : LitB;
    }
    else
      return pv->range_contained(r,rng) ? LitA : LitB;
  }

  /** Make a resolution node with given pivot literal and premises.
      The conclusion of premise1 should contain the negation of the
      pivot literal, while the conclusion of premise2 should contain the
      pivot literal.
   */
  node make_resolution(ast pivot, const std::vector<ast> &conc, node premise1, node premise2) {
    LitType lt = get_term_type(pivot);
    if(lt == LitA)
      return my_or(premise1,premise2);
    if(lt == LitB)
      return my_and(premise1,premise2);
    
    /* the mixed case is a bit complicated */

    ast atom = get_lit_atom(pivot);
    switch(op(atom)){
    case Equal:
      return resolve_equality(pivot,conc,premise1,premise2);
    case Leq:
    case Geq:
    case Lt:
    case Gt:
      return resolve_arith(pivot,conc,premise1,premise2);
      break;
    default:;
    }
    
    /* we can resolve on mixed equality and inequality literals,
       but nothing else. */
    throw proof_error();
  }

  /* Handles the case of resolution on a mixed equality atom.  */

  ast resolve_equality(const ast &pivot, const std::vector<ast> &conc, node premise1, node premise2){
    ast atom = get_lit_atom(pivot);
    
    /* Get the A term in the mixed equality. */
    ast A_term = arg(atom,0);
    if(get_term_type(A_term) != LitA)
      A_term = arg(atom,1);

    /* Resolve it out. */
    hash_map<ast,ast> memo;
    // ast neg_pivot_placeholder = get_placeholder(mk_not(atom));
    ast neg_pivot_placeholder = mk_not(atom);
    ast A_term_placeholder = get_placeholder(atom);
    if(op(pivot) != Not)
      std::swap(premise1,premise2);
    return resolve_equality_rec(memo, neg_pivot_placeholder, premise1, A_term_placeholder, premise2);
  }
  
  ast resolve_equality_rec(hash_map<ast,ast> &memo, const ast &neg_pivot_placeholder, const ast &premise1, 
					  const ast &A_term, const ast &premise2){
    ast &res = memo[premise1];
    if(!res.null())
      return res;
    
    if(op(premise1) == And
       && num_args(premise1) == 2
       && arg(premise1,1) == neg_pivot_placeholder){
      ast common_term = arg(arg(premise1,0),1);
      res = subst_term_and_simp(A_term,common_term,premise2);
    }
    else {
      switch(op(premise1)){
      case Or:
      case And: {
	unsigned nargs = num_args(premise1);
	std::vector<ast> args; args.resize(nargs);
	for(unsigned i = 0; i < nargs; i++)
	  args[i] = resolve_equality_rec(memo, neg_pivot_placeholder, arg(premise1,i), A_term, premise2);
	ast foo = premise1; // get rid of const
	res = clone(foo,args);
	break;
      }
      default:
	res = premise1;
      }
    }
    return res;
  }

  /* Handles the case of resolution on a mixed arith atom.  */

  ast resolve_arith(const ast &pivot, const std::vector<ast> &conc, node premise1, node premise2){
    ast atom = get_lit_atom(pivot);
    hash_map<ast,ast> memo;
    ast neg_pivot_lit = mk_not(atom);
    if(op(pivot) != Not)
      std::swap(premise1,premise2);
    return resolve_arith_rec1(memo, neg_pivot_lit, premise1, premise2);
  }
  
  void collect_farkas_resolvents(const ast &pivot, const ast &coeff, const ast &conj, std::vector<ast> &res){
    int nargs = num_args(conj);
    for(int i = 1; i < nargs; i++){
      ast f = arg(conj,i);
      if(!(f == pivot)){
	ast newf = make(farkas,make(Times,arg(f,0),coeff),arg(f,1));
	res.push_back(newf);
      }
    }
  }

  ast sum_ineq(const ast &coeff1, const ast &ineq1, const ast &coeff2, const ast &ineq2){
    opr sum_op = Leq;
    if(op(ineq1) == Lt || op(ineq2) == Lt)
      sum_op = Lt;
    ast sum_sides[2];
    for(int i = 0; i < 2; i++){
      sum_sides[i] = make(Plus,make(Times,coeff1,arg(ineq1,i)),make(Times,coeff2,arg(ineq2,i)));
      sum_sides[i] = z3_simplify(sum_sides[i]);
    }
    return make(sum_op,sum_sides[0],sum_sides[1]);
  }
  

  ast resolve_farkas(const ast &pivot1, const ast &conj1, const ast &pivot2, const ast &conj2){
    std::vector<ast> resolvent;
    ast coeff1 = get_farkas_coeff(pivot1);
    ast coeff2 = get_farkas_coeff(pivot2);
    resolvent.push_back(sum_ineq(coeff2,arg(conj1,0),coeff1,arg(conj2,0)));
    collect_farkas_resolvents(pivot1,coeff2,conj1,resolvent);
    collect_farkas_resolvents(pivot2,coeff1,conj2,resolvent);
    return make(And,resolvent);
  }
   
  bool is_farkas_itp(const ast &pivot1, const ast &itp2, ast &pivot2){
    if(op(itp2) == And){
      int nargs = num_args(itp2);
      for(int i = 1; i < nargs; i++){
	ast foo = arg(itp2,i);
	if(op(foo) == Uninterpreted && sym(foo) == farkas){
	  if(arg(foo,1) == pivot1){
	    pivot2 = foo;
	    return true;
	  }
	}
	else break;
      }
    }
    return false;
  }

  ast resolve_arith_rec2(hash_map<ast,ast> &memo, const ast &pivot1, const ast &conj1, const ast &itp2){
    ast &res = memo[itp2];
    if(!res.null())
      return res;
    
    ast pivot2;
    if(is_farkas_itp(mk_not(arg(pivot1,1)),itp2,pivot2))
      res = resolve_farkas(pivot1,conj1,pivot2,itp2);
    else {
      switch(op(itp2)){
      case Or:
      case And: {
	unsigned nargs = num_args(itp2);
	std::vector<ast> args; args.resize(nargs);
	for(unsigned i = 0; i < nargs; i++)
	  args[i] = resolve_arith_rec2(memo, pivot1, conj1, arg(itp2,i));
	ast foo = itp2; // get rid of const
	res = clone(foo,args);
	break;
      }
      default:
	res = itp2;
      }
    }
    return res;
  }

  ast resolve_arith_rec1(hash_map<ast,ast> &memo, const ast &neg_pivot_lit, const ast &itp1, const ast &itp2){
    ast &res = memo[itp1];
    if(!res.null())
      return res;
    ast pivot1;
    if(is_farkas_itp(neg_pivot_lit,itp1,pivot1)){
      hash_map<ast,ast> memo2;
      res = resolve_arith_rec2(memo2,pivot1,itp1,itp2);
      res = resolve_arith_placeholders(pivot1,itp1,res);
    }
    else {
      switch(op(itp1)){
      case Or:
      case And: {
	unsigned nargs = num_args(itp1);
	std::vector<ast> args; args.resize(nargs);
	for(unsigned i = 0; i < nargs; i++)
	  args[i] = resolve_arith_rec1(memo, neg_pivot_lit, arg(itp1,i), itp2);
	ast foo = itp1; // get rid of const
	res = clone(foo,args);
	break;
      }
      default:
	res = itp1;
      }
    }
    return res;
  }

  ast resolve_arith_placeholders(const ast &pivot1, const ast &conj1, const ast &itp2){
    ast coeff = arg(pivot1,0);
    coeff = z3_simplify(coeff);
    ast soln = mk_idiv(arg(arg(conj1,0),1),coeff);
    int nargs = num_args(conj1);
    for(int i = 1; i < nargs; i++){
      ast c = arg(conj1,i);
      if(!(c == pivot1)){
	soln = make(Plus,soln,get_placeholder(mk_not(c)));
      }
    }
    ast pl = get_placeholder(mk_not(arg(pivot1,1)));
    ast res = subst_term_and_simp(pl,soln,itp2);
    return res;
  }

  hash_map<ast,ast> subst_memo;                    // memo of subst function

  ast subst_term_and_simp(const ast &var, const ast &t, const ast &e){
    subst_memo.clear();
    return subst_term_and_simp_rec(var,t,e);
  }

  ast subst_term_and_simp_rec(const ast &var, const ast &t, const ast &e){
    if(e == var) return t;
    std::pair<ast,ast> foo(e,ast());
    std::pair<hash_map<ast,ast>::iterator,bool> bar = subst_memo.insert(foo);
    ast &res = bar.first->second;
    if(bar.second){
      int nargs = num_args(e);
      std::vector<ast> args(nargs);
      for(int i = 0; i < nargs; i++)
	args[i] = subst_term_and_simp_rec(var,t,arg(e,i));
      opr f = op(e);
      if(f == Equal && args[0] == args[1]) res = mk_true();
      else if(f == And) res = my_and(args);
      else if(f == Or) res = my_or(args);
      else if(f == Idiv) res = mk_idiv(args[0],args[1]);
      else res = clone(e,args);
    }
    return res;
  }


  /** Make an assumption node. The given clause is assumed in the given frame. */
  virtual node make_assumption(int frame, const std::vector<ast> &assumption){
    if(pv->in_range(frame,rng)){
      std::vector<ast> itp_clause;
      for(unsigned i = 0; i < assumption.size(); i++)
	if(get_term_type(assumption[i]) != LitA)
	  itp_clause.push_back(assumption[i]);
      ast res = my_or(itp_clause);
      return res;
    }
    else {
      return mk_true();
    }
}

  /** Make a modus-ponens node. This takes derivations of |- x
      and |- x = y and produces |- y */

  virtual node make_mp(const ast &p, const ast &q, const ast &prem1, const ast &prem2){

    /* Interpolate the axiom p, p=q -> q */
    ast itp;
    if(get_term_type(p) == LitA){
      if(get_term_type(q) == LitA)
	itp = mk_false();
      else {
	if(get_term_type(make(Equal,p,q)) == LitA)
	  itp = q;
	else
	  itp = get_placeholder(make(Equal,p,q));
      }
    }
    else {
      if(get_term_type(q) == LitA){
	if(get_term_type(make(Equal,p,q)) == LitA)
	  itp = mk_not(p);
	else
	  itp = mk_not(get_placeholder(make(Equal,p,q)));
      }
      else
	itp = mk_true();
    }
    
    /* Resolve it with the premises */
    std::vector<ast> conc; conc.push_back(q); conc.push_back(mk_not(make(Equal,p,q)));
    itp = make_resolution(p,conc,itp,prem1);
    conc.pop_back();
    itp = make_resolution(make(Equal,p,q),conc,itp,prem2);
    return itp;
  }

  /** Make an axiom node. The conclusion must be an instance of an axiom. */
  virtual node make_axiom(const std::vector<ast> &conclusion){
    throw proof_error();
}

  /** Make a Contra node. This rule takes a derivation of the form
     Gamma |- False and produces |- \/~Gamma. */

  virtual node make_contra(node prem, const std::vector<ast> &conclusion){
    return prem;
  }

  /** Make hypothesis. Creates a node of the form P |- P. */

  virtual node make_hypothesis(const ast &P){
    if(is_not(P))
      return make_hypothesis(arg(P,0));
    switch(get_term_type(P)){
    case LitA:
      return mk_false();
    case LitB:
      return mk_true();
    default: // mixed hypothesis
      switch(op(P)){
      case Equal:
	{
	  ast x = arg(P,0);
	  ast y = arg(P,1);
	  ast A_term = (get_term_type(y) == LitA) ? y : x;
	  ast res = make(And,make(Equal,A_term,get_placeholder(P)),mk_not(P));
	  return res;
	}
      case Geq: 
      case Leq: 
      case Gt: 
      case Lt: {
	ast zleqz = make(Leq,make_int("0"),make_int("0"));
	ast fark1 = make(farkas,make_int("1"),P);
	ast fark2 = make(farkas,make_int("1"),mk_not(P));
	ast res = make(And,zleqz,fark1,fark2);
	return res;
      }
      default:
	throw proof_error();
      }
    }
  }

  /** Make a Reflexivity node. This rule produces |- x = x */
  
  virtual node make_reflexivity(ast con){
    throw proof_error();
}
  
  /** Make a Symmetry node. This takes a derivation of |- x = y and
      produces | y = x */

  virtual node make_symmetry(ast con, node prem){
    ast x = arg(con,0);
    ast y = arg(con,1);
    ast p = make(Equal,y,x);
    LitType xt = get_term_type(x);
    LitType yt = get_term_type(y);
    ast A_term;
    if(xt == LitA && yt == LitB)
      A_term = x;
    else if(yt == LitA && xt == LitB)
      A_term = y;
    else
      return prem; // symmetry shmymmetry...
    ast itp = make(And,make(Equal,A_term,get_placeholder(p)),mk_not(con));
    std::vector<ast> conc; conc.push_back(con);
    itp = make_resolution(p,conc,itp,prem);
    return itp;
  }

  /** Make a transitivity node. This takes derivations of |- x = y
      and |- y = z produces | x = z */

  virtual node make_transitivity(const ast &x, const ast &y, const ast &z, node prem1, node prem2){

    /* Interpolate the axiom x=y,y=z,-> x=z */
    ast p = make(Equal,x,y);
    ast q = make(Equal,y,z);
    ast r = make(Equal,x,z);
    ast itp;
    if(get_term_type(p) == LitA){
      if(get_term_type(q) == LitA){
	if(get_term_type(r) == LitA)
	  itp = mk_false();
	else 
	  itp = r;
      }
      else {
	if(get_term_type(r) == LitA)
	  itp = mk_not(q);
	else { 
	  if(get_term_type(r) == LitB)
	    itp = make(Equal,x,get_placeholder(q));
	  else {
	    ast mid = (get_term_type(y) == LitA) ? get_placeholder(q) : y;
	    itp = make(And,make(Equal,x,mid),mk_not(r));
	  }
	}
      }
    }
    else {
      if(get_term_type(q) == LitA){
	if(get_term_type(r) == LitA)
	  itp = mk_not(p);
	else {
	  if(get_term_type(r) == LitB)
	    itp = make(Equal,get_placeholder(p),z);
	  else {
	    ast mid = (get_term_type(y) == LitA) ? get_placeholder(p) : y;
	    itp = make(And,make(Equal,z,mid),mk_not(r));
	  }
	}
      }
      else {
	if(get_term_type(r) == LitA){
	  ast xr = (get_term_type(x) == LitA) ? get_placeholder(p) : x;
	  ast zr = (get_term_type(z) == LitA) ? get_placeholder(q) : z;
	  itp = mk_not(make(Equal,xr,zr));
	}
	else {
	  LitType xt = get_term_type(x);
	  LitType zt = get_term_type(z);
	  if(xt == LitA && zt == LitB)
	    itp = make(And,make(Equal,x,get_placeholder(p)),mk_not(r));
	  else if(zt == LitA && xt == LitB)
	    itp = make(And,make(Equal,z,get_placeholder(q)),mk_not(r));
	  else
	    itp = mk_true();
	}
      }
    }
    
    /* Resolve it with the premises */
    std::vector<ast> conc; conc.push_back(r); conc.push_back(mk_not(q));
    itp = make_resolution(p,conc,itp,prem1);
    conc.pop_back();
    itp = make_resolution(q,conc,itp,prem2);
    return itp;
    
  }
  
  /** Make a congruence node. This takes derivations of |- x_i = y_i
      and produces |- f(x_1,...,x_n) = f(y_1,...,y_n) */
  
  virtual node make_congruence(const ast &x, const ast &y, const ast &con, const std::vector<ast> &hyps, const ast &prem1){
    ast p = make(Equal,x,y);
    ast itp;
    if(get_term_type(p) == LitA){
      if(get_term_type(con) == LitA)
	itp = mk_false();
      else
	throw proof_error(); // itp = p;
    }
    else {
      if(get_term_type(con) == LitA)
	itp = mk_not(p);
      else{
	if(get_term_type(con) == LitB)
	  itp = mk_true();
	else
	  itp = make_mixed_congruence(x, y, con, hyps, prem1);
      }
    }
    std::vector<ast> conc; conc.push_back(con);
    itp = make_resolution(p,conc,itp,prem1);
    return itp;
  }

  /* Interpolate a mixed congruence axiom. */

  virtual ast make_mixed_congruence(const ast &x, const ast &y, const ast &con, const std::vector<ast> &hyps, const ast &prem1){
    ast A_term = x;
    ast f_A_term = arg(con,0);
    if(get_term_type(y) == LitA){
      A_term = y;
      f_A_term = arg(con,1);
    }

    // find the argument position of x and y
    int pos = -1;
    int nargs = num_args(arg(con,0));
    for(int i = 0; i < nargs; i++)
      if(x == arg(arg(con,0),i) && y == arg(arg(con,1),i))
	pos = i;
    if(pos == -1)
      throw proof_error();

    ast res = make(Equal,f_A_term,subst_in_arg_pos(pos,get_placeholder(make(Equal,x,y)),f_A_term));
    res = make(And,res,mk_not(con));
    return res;
  }

  ast subst_in_arg_pos(int pos, ast term, ast app){
    std::vector<ast> args;
    get_args(app,args);
    args[pos] = term;
    return clone(app,args);
  }

  /** Make a farkas proof node. */

  virtual node make_farkas(ast con, const std::vector<node> &prems, const std::vector<ast> &prem_cons,
			   const std::vector<ast> &coeffs){

    /* Compute the interpolant for the clause */

    ast zero = make_int("0");
    std::vector<ast> conjs; conjs.resize(1);
    ast thing = make(Leq,zero,zero);
    for(unsigned i = 0; i < prem_cons.size(); i++){
      const ast &lit = prem_cons[i];
      if(get_term_type(lit) == LitA)
	linear_comb(thing,coeffs[i],lit);
      else if(get_term_type(lit) != LitB)
	conjs.push_back(make(farkas,coeffs[i],prem_cons[i]));
    }
    thing = simplify_ineq(thing);
    if(conjs.size() > 1){
      conjs[0] = thing;
      thing = make(And,conjs);
    }

    /* Resolve it with the premises */
    std::vector<ast> conc; conc.resize(prem_cons.size());
    for(unsigned i = 0; i < prem_cons.size(); i++)
      conc[prem_cons.size()-i-1] = prem_cons[i];
    for(unsigned i = 0; i < prem_cons.size(); i++){
      thing = make_resolution(prem_cons[i],conc,thing,prems[i]);
      conc.pop_back();
    }
    return thing;
  }

  /** Set P to P + cQ, where P and Q are linear inequalities. Assumes P is 0 <= y or 0 < y. */

  void linear_comb(ast &P, const ast &c, const ast &Q){
    ast Qrhs;
    bool strict = op(P) == Lt;
    if(is_not(Q)){
      ast nQ = arg(Q,0);
      switch(op(nQ)){
      case Gt:
	Qrhs = make(Sub,arg(nQ,1),arg(nQ,0));
	break;
      case Lt: 
	Qrhs = make(Sub,arg(nQ,0),arg(nQ,1));
	break;
      case Geq:
	Qrhs = make(Sub,arg(nQ,1),arg(nQ,0));
	strict = true;
	break;
      case Leq: 
	Qrhs = make(Sub,arg(nQ,0),arg(nQ,1));
	strict = true;
	break;
      default:
	throw proof_error();
      }
    }
    else {
      switch(op(Q)){
      case Leq:
	Qrhs = make(Sub,arg(Q,1),arg(Q,0));
	break;
      case Geq: 
	Qrhs = make(Sub,arg(Q,0),arg(Q,1));
	break;
      case Lt:
	Qrhs = make(Sub,arg(Q,1),arg(Q,0));
	strict = true;
	break;
      case Gt: 
	Qrhs = make(Sub,arg(Q,0),arg(Q,1));
	strict = true;
	break;
      default:
	throw proof_error();
      }
    }
    Qrhs = make(Times,c,Qrhs);
    if(strict)
      P = make(Lt,arg(P,0),make(Plus,arg(P,1),Qrhs));
    else
      P = make(Leq,arg(P,0),make(Plus,arg(P,1),Qrhs));
  }
  
  /* Make an axiom instance of the form |- x<=y, y<= x -> x =y */
  virtual node make_leq2eq(ast x, ast y, const ast &xleqy, const ast &yleqx){
    ast con = make(Equal,x,y);
    ast itp;
    switch(get_term_type(con)){
    case LitA:
      itp =  mk_false();
      break;
    case LitB:
      itp =  mk_true();
      break;
    default: { // mixed equality
      ast mid,ante;
      if(get_term_type(y) == LitA){
	std::swap(x,y);
	mid = make(Plus,x,get_placeholder(yleqx));
      }
      else {
	mid = make(Plus,x,get_placeholder(xleqy));
      }
      ante = make(Uminus,make(Plus,get_placeholder(xleqy),get_placeholder(yleqx)));
      ante = mk_not(make(Leq,make_int("0"),ante));
#if 0
      ast zleqz = make(Leq,make_int("0"),make_int("0"));
      ast fark1 = make(farkas,make_int("1"),xleqy);
      ast fark2 = make(farkas,make_int("1"),yleqx);
      ast ante = make(And,zleqz,fark1,fark2);
#endif
      ast conc = make(And,make(Equal,x,mid),mk_not(con));
      itp = my_or(ante,conc);
    }
    }
    return itp;
  }

  /* Make an axiom instance of the form |- x = y -> x <= y */
  virtual node make_eq2leq(ast x, ast y, const ast &xleqy){
    ast itp;
    switch(get_term_type(xleqy)){
    case LitA:
      itp =  mk_false();
      break;
    case LitB:
      itp =  mk_true();
      break;
    default: { // mixed equality
      ast mid = get_placeholder(make(Equal,x,y));
      if(get_term_type(y) == LitA){
	std::swap(x,y);
	mid = make(Sub,x,mid);
      }
      else {
	mid = make(Sub,mid,x);
      }
      ast zleqmid = make(Leq,make_int("0"),mid);
      ast fark = make(farkas,make_int("1"),mk_not(xleqy));
      itp = make(And,zleqmid,fark);
    }
    }
    return itp;
  }


  /* Make an inference of the form t <= c |- t/d <= floor(c/d) where t
     is an affine term divisble by d and c is an integer constant */
  virtual node make_cut_rule(const ast &tleqc, const ast &d, const ast &con, const ast &prem){
    ast itp = mk_false();
    switch(get_term_type(con)){
    case LitA:
      itp =  mk_false();
      break;
    case LitB:
      itp =  mk_true();
      break;
    default: {
      ast t = arg(tleqc,0);
      ast c = arg(tleqc,1);
      ast thing = make(farkas,make_int("1"),mk_not(con));
      itp = make(And,make(Leq,make_int("0"),make(Idiv,get_placeholder(tleqc),d)),thing);
    }
    }
    std::vector<ast> conc; conc.push_back(con);
    itp = make_resolution(tleqc,conc,itp,prem);
    return itp;
  }

  ast get_farkas_coeff(const ast &f){
    ast c = arg(f,0);
    // if(!is_not(arg(f,1)))
    // c = make(Uminus,c);
    return c;
  }

  ast my_or(const ast &a, const ast &b){
    return mk_or(a,b);
  }

  ast my_and(const ast &a, const ast &b){
    return mk_and(a,b);
  }

  ast my_or(const std::vector<ast> &a){
    return mk_or(a);
  }

  ast my_and(const std::vector<ast> &a){
    return mk_and(a);
  }

  ast get_lit_atom(const ast &l){
    if(op(l) == Not)
      return arg(l,0);
    return l;
  }

public:
  iz3proof_itp_impl(prover *p, const prover::range &r, bool w)
    : iz3proof_itp(*p)
  {
    pv = p;
    rng = r;
    weak = w;
    type domain[2] = {int_type(),bool_type()};
    farkas = function("@farkas",2,domain,bool_type());
  }

};

iz3proof_itp *iz3proof_itp::create(prover *p, const prover::range &r, bool w){
  return new iz3proof_itp_impl(p,r,w);
}

