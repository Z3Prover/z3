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

#ifdef _WINDOWS
#pragma warning(disable:4996)
#pragma warning(disable:4800)
#pragma warning(disable:4267)
#pragma warning(disable:4101)
#endif

#include "iz3proof_itp.h"

using namespace stl_ext;

// #define INVARIANT_CHECKING

class iz3proof_itp_impl : public iz3proof_itp {

  prover *pv;
  prover::range rng;
  bool weak;

  enum LitType {LitA,LitB,LitMixed};

  hash_map<ast,ast> placeholders;

  // These symbols represent deduction rules

  /* This symbol represents a proof by contradiction. That is,
     contra(p,l1 /\ ... /\ lk) takes a proof p of

     l1,...,lk |- false

     and returns a proof of 

     |- ~l1,...,~l2
  */
  symb contra;

  /* The summation rule. The term sum(p,c,i) takes a proof p of an
     inequality i', an integer coefficient c and an inequality i, and
     yieds a proof of i' + ci. */
  symb sum;

  /* Proof rotation. The proof term rotate(q,p) takes a
     proof p of:

     Gamma, q |- false

     and yields a proof of:

     Gamma |- ~q
  */
  symb rotate_sum;

  /* Inequalities to equality. leq2eq(p, q, r) takes a proof
     p of ~x=y, a proof q of x <= y and a proof r of y <= x
     and yields a proof of false. */
  symb leq2eq;

  /* Equality to inequality. eq2leq(p, q) takes a proof p of x=y, and
     a proof q ~(x <= y) and and yields a proof of false. */
  symb eq2leq;

  /* Proof term cong(p,q) takes a proof p of x=y and a proof
     q of t != t<y/x> and returns a proof of false. */
  symb cong;


  /* Excluded middle. exmid(phi,p,q) takes a proof p of phi and a
     proof q of ~\phi and returns a proof of false. */
  symb exmid;

  /* Symmetry. symm(p) takes a proof p of x=y and produces
     a proof of y=x. */
  symb symm;

  /* Modus ponens. modpon(p,e,q) takes proofs p of P, e of P=Q
     and q of ~Q and returns a proof of false. */
  symb modpon;

  /* This oprerator represents a concatenation of rewrites.  The term
     a=b;c=d represents an A rewrite from a to b, followed by a B
     rewrite fron b to c, followed by an A rewrite from c to d.
   */
  symb concat;

  /* This represents a lack of a proof */
  ast no_proof;

  // This is used to represent an infinitessimal value
  ast epsilon;

  // Represents the top position of a term
  ast top_pos;

  // add_pos(i,pos) represents position pos if the ith argument
  symb add_pos;

  // rewrite proof rules

  /* rewrite_A(pos,cond,x=y) derives A |- cond => t[x]_p = t[y]_p
     where t is an arbitrary term */
  symb rewrite_A;

  /* rewrite_B(pos,cond,x=y) derives B |- cond => t[x]_p = t[y]_p,
     where t is an arbitrary term */
  symb rewrite_B;

  /* a normalization step is of the form (lhs=rhs) : proof, where "proof"
     is a proof of lhs=rhs and lhs is a mixed term. If rhs is a mixed term
     then it must have a greater index than lhs. */
  symb normal_step;

  /* A chain of normalization steps is either "true" (the null chain)
     or normal_chain(<step> <tail>), where step is a normalization step
     and tail is a normalization chain. The lhs of <step> must have
     a less term index than any lhs in the chain. Moreover, the rhs of
     <step> may not occur as the lhs of step in <tail>. If we wish to
     add lhs=rhs to the beginning of <tail> and rhs=rhs' occurs in <tail>
     we must apply transitivity, transforming <step> to lhs=rhs'. */

  symb normal_chain;

  /* If p is a proof of Q and c is a normalization chain, then normal(p,c)
     is a proof of Q(c) (that is, Q with all substitutions in c performed). */
  
  symb normal;

  /** Stand-ins for quantifiers */

  symb sforall, sexists;


  ast get_placeholder(ast t){
    hash_map<ast,ast>::iterator it = placeholders.find(t);
    if(it != placeholders.end())
      return it->second;
    ast &res = placeholders[t];
    res = mk_fresh_constant("@p",get_type(t));
#if 0
    std::cout << "placeholder ";
    print_expr(std::cout,res);
    std::cout << " = ";
    print_expr(std::cout,t);
    std::cout << std::endl;
#endif
    return res;
  }

  ast make_contra_node(const ast &pf, const std::vector<ast> &lits, int pfok = -1){
    if(lits.size() == 0)
      return pf;
    std::vector<ast> reslits;
    reslits.push_back(make(contra,pf,mk_false()));
    for(unsigned i = 0; i < lits.size(); i++){
      ast bar;
      if(pfok & (1 << i)) bar = make(rotate_sum,lits[i],pf);
      else bar = no_proof;
      ast foo = make(contra,bar,lits[i]);
      reslits.push_back(foo);
    }
    return make(And,reslits);
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

  bool term_common(const ast &t){
    prover::range r = pv->ast_scope(t);
    return pv->ranges_intersect(r,rng) && !pv->range_contained(r,rng);
  }

  bool term_in_vocab(LitType ty, const ast &lit){
    prover::range r = pv->ast_scope(lit);
    if(ty == LitA){
      return pv->ranges_intersect(r,rng);
    }
    return !pv->range_contained(r,rng);
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

    static int non_local_count = 0;
    ast res = resolve_arith(pivot,conc,premise1,premise2);
#ifdef INVARIANT_CHECKING
    check_contra(conc,res);
#endif
    non_local_count++;
    return res;
  }


  /* Handles the case of resolution on a mixed arith atom.  */

  ast resolve_arith(const ast &pivot, const std::vector<ast> &conc, node premise1, node premise2){
    ast atom = get_lit_atom(pivot);
    hash_map<ast,ast> memo;
    ast neg_pivot_lit = mk_not(atom);
    if(op(pivot) != Not)
      std::swap(premise1,premise2);
    if(op(pivot) == Equal && op(arg(pivot,0)) == Select && op(arg(pivot,1)) == Select){
      neg_pivot_lit = mk_not(neg_pivot_lit);
      std::swap(premise1,premise2);
    }      
    return resolve_arith_rec1(memo, neg_pivot_lit, premise1, premise2);
  }
  

  ast apply_coeff(const ast &coeff, const ast &t){
#if 0
    rational r;
    if(!is_integer(coeff,r))
      throw "ack!";
    ast n = make_int(r.numerator());
    ast res = make(Times,n,t);
    if(!r.is_int()) {
      ast d = make_int(r.numerator());
      res = mk_idiv(res,d);
    }
    return res;
#endif
    return make(Times,coeff,t);
  }

  ast sum_ineq(const ast &coeff1, const ast &ineq1, const ast &coeff2, const ast &ineq2){
    opr sum_op = Leq;
    if(op(ineq1) == Lt || op(ineq2) == Lt)
      sum_op = Lt;
    ast sum_sides[2];
    for(int i = 0; i < 2; i++){
      sum_sides[i] = make(Plus,apply_coeff(coeff1,arg(ineq1,i)),apply_coeff(coeff2,arg(ineq2,i)));
      sum_sides[i] = z3_simplify(sum_sides[i]);
    }
    return make(sum_op,sum_sides[0],sum_sides[1]);
  }
  

  void collect_contra_resolvents(int from, const ast &pivot1, const ast &pivot, const ast &conj, std::vector<ast> &res){
    int nargs = num_args(conj);
    for(int i = from; i < nargs; i++){
      ast f = arg(conj,i);
      if(!(f == pivot)){
	ast ph = get_placeholder(mk_not(arg(pivot1,1)));
	ast pf = arg(pivot1,0);
	ast thing = pf == no_proof ? no_proof : subst_term_and_simp(ph,pf,arg(f,0));
	ast newf = make(contra,thing,arg(f,1));
	res.push_back(newf);
      }
    }
  }
  
  bool is_negative_equality(const ast &e){
    if(op(e) == Not){
      opr o = op(arg(e,0));
      return o == Equal || o == Iff;
    }
    return false;
  }

  int count_negative_equalities(const std::vector<ast> &resolvent){
    int res = 0;
    for(unsigned i = 0; i < resolvent.size(); i++)
      if(is_negative_equality(arg(resolvent[i],1)))
	res++;
    return res;
  }

  ast resolve_contra_nf(const ast &pivot1, const ast &conj1,
		     const ast &pivot2, const ast &conj2){
    std::vector<ast> resolvent;
    collect_contra_resolvents(0,pivot1,pivot2,conj2,resolvent);
    collect_contra_resolvents(1,pivot2,pivot1,conj1,resolvent);
    if(count_negative_equalities(resolvent) > 1)
      throw proof_error();
    if(resolvent.size() == 1) // we have proved a contradiction
      return simplify(arg(resolvent[0],0)); // this is the proof -- get interpolant
    return make(And,resolvent);
  }

  ast resolve_contra(const ast &pivot1, const ast &conj1,
			  const ast &pivot2, const ast &conj2){
    if(arg(pivot1,0) != no_proof)
      return resolve_contra_nf(pivot1, conj1, pivot2, conj2);
    if(arg(pivot2,0) != no_proof)
      return resolve_contra_nf(pivot2, conj2, pivot1, conj1);
    return resolve_with_quantifier(pivot1, conj1, pivot2, conj2);
  }


  bool is_contra_itp(const ast &pivot1, ast itp2, ast &pivot2){
    if(op(itp2) == And){
      int nargs = num_args(itp2);
      for(int i = 1; i < nargs; i++){
	ast foo = arg(itp2,i);
	if(op(foo) == Uninterpreted && sym(foo) == contra){
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
    if(is_contra_itp(mk_not(arg(pivot1,1)),itp2,pivot2))
      res = resolve_contra(pivot1,conj1,pivot2,itp2);
    else {
      switch(op(itp2)){
      case Or:
      case And:
      case Implies: {
	unsigned nargs = num_args(itp2);
	std::vector<ast> args; args.resize(nargs);
	for(unsigned i = 0; i < nargs; i++)
	  args[i] = resolve_arith_rec2(memo, pivot1, conj1, arg(itp2,i));
	ast foo = itp2; // get rid of const
	res = clone(foo,args);
	break;
      }
      default:
	{
	  opr o = op(itp2);
	  if(o == Uninterpreted){
	    symb s = sym(itp2);
	    if(s == sforall || s == sexists)
	      res = make(s,arg(itp2,0),resolve_arith_rec2(memo, pivot1, conj1, arg(itp2,1)));
	    else
	      res = itp2;
	  }
	  else {
	    res = itp2;
	  }
	}
      }
    }
    return res;
  }


  ast resolve_arith_rec1(hash_map<ast,ast> &memo, const ast &neg_pivot_lit, const ast &itp1, const ast &itp2){
    ast &res = memo[itp1];
    if(!res.null())
      return res;
    ast pivot1;
    if(is_contra_itp(neg_pivot_lit,itp1,pivot1)){
      hash_map<ast,ast> memo2;
      res = resolve_arith_rec2(memo2,pivot1,itp1,itp2);
    }
    else {
      switch(op(itp1)){
      case Or:
      case And:
      case Implies: {
	unsigned nargs = num_args(itp1);
	std::vector<ast> args; args.resize(nargs);
	for(unsigned i = 0; i < nargs; i++)
	  args[i] = resolve_arith_rec1(memo, neg_pivot_lit, arg(itp1,i), itp2);
	ast foo = itp1; // get rid of const
	res = clone(foo,args);
	break;
      }
      default:
	{
	  opr o = op(itp1);
	  if(o == Uninterpreted){
	    symb s = sym(itp1);
	    if(s == sforall || s == sexists)
	      res = make(s,arg(itp1,0),resolve_arith_rec1(memo, neg_pivot_lit, arg(itp1,1), itp2));
	    else
	      res = itp1;
	  }
	  else {
	    res = itp1;
	  }
	}
      }
    }
    return res;
  }

  void check_contra(hash_set<ast> &memo, hash_set<ast> &neg_lits, const ast &foo){
    if(memo.find(foo) != memo.end())
      return;
    memo.insert(foo);
    if(op(foo) == Uninterpreted && sym(foo) == contra){
      ast neg_lit = arg(foo,1);
      if(!is_false(neg_lit) && neg_lits.find(neg_lit) == neg_lits.end())
	throw "lost a literal";
      return;
    }
    else {
      switch(op(foo)){
      case Or:
      case And:
      case Implies: {
	unsigned nargs = num_args(foo);
	std::vector<ast> args; args.resize(nargs);
	for(unsigned i = 0; i < nargs; i++)
	  check_contra(memo, neg_lits, arg(foo,i));
	break;
      }
      default: break;
      }
    }
  }

  void check_contra(const std::vector<ast> &neg_lits, const ast &foo){
    hash_set<ast> memo;
    hash_set<ast> neg_lits_set;
    for(unsigned i = 0; i < neg_lits.size(); i++)
      if(get_term_type(neg_lits[i]) == LitMixed)
	neg_lits_set.insert(mk_not(neg_lits[i]));
    check_contra(memo,neg_lits_set,foo);
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
      if(op(e) == Uninterpreted){
	symb g = sym(e);
	if(g == rotate_sum){
	  if(var == get_placeholder(arg(e,0))){
	    res = e;
	  }
	  else 
	    res = make(rotate_sum,arg(e,0),subst_term_and_simp_rec(var,t,arg(e,1)));
	  return res;
	}
	if(g == concat){
	  res = e;
	  return res;
	}
      }
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

  /* This is where the real work happens. Here, we simplify the
     proof obtained by cut elimination, obtaining an interpolant. */

  struct cannot_simplify {};
  hash_map<ast,ast> simplify_memo;

  ast simplify(const ast &t){
    ast res = normalize(simplify_rec(t));
#ifdef BOGUS_QUANTS
    if(localization_vars.size())
      res = add_quants(z3_simplify(res));
#endif
    return res;
  }

  ast simplify_rec(const ast &e){
    std::pair<ast,ast> foo(e,ast());
    std::pair<hash_map<ast,ast>::iterator,bool> bar = simplify_memo.insert(foo);
    ast &res = bar.first->second;
    if(bar.second){
      int nargs = num_args(e);
      std::vector<ast> args(nargs);
      bool placeholder_arg = false;
      symb g = sym(e);
      if(g == concat){
	res = e;
	return res;
      }
      for(int i = 0; i < nargs; i++){
	if(i == 0 && g == rotate_sum)
	  args[i] = arg(e,i);
	else
	  args[i] = simplify_rec(arg(e,i));
	placeholder_arg |= is_placeholder(args[i]);
      }
      try {
	opr f = op(e);
	if(f == Equal && args[0] == args[1]) res = mk_true();
	else if(f == And) res = my_and(args);
	else if(f == Or)
	  res = my_or(args);
	else if(f == Idiv) res = mk_idiv(args[0],args[1]);
	else if(f == Uninterpreted && !placeholder_arg){
	  if(g == rotate_sum) res = simplify_rotate(args);
	  else if(g == symm) res = simplify_symm(args);
	  else if(g == modpon) res = simplify_modpon(args);
	  else if(g == sum) res = simplify_sum(args);
	  else if(g == exmid) res = simplify_exmid(args);
	  else if(g == cong) res = simplify_cong(args);
#if 0
	  else if(g == modpon) res = simplify_modpon(args);
	  else if(g == leq2eq) res = simplify_leq2eq(args);
	  else if(g == eq2leq) res = simplify_eq2leq(args);
#endif
	  else res = clone(e,args);
	}
	else res = clone(e,args);
      }
      catch (const cannot_simplify &){
	res = clone(e,args);
      }
    }
    return res;
  }


  ast simplify_rotate(const std::vector<ast> &args){
    const ast &pf = args[1];
    ast pl = get_placeholder(args[0]);
    if(op(pf) == Uninterpreted){
      symb g = sym(pf);
      if(g == sum) return simplify_rotate_sum(pl,pf);
      if(g == leq2eq) return simplify_rotate_leq2eq(pl,args[0],pf);
      if(g == eq2leq) return simplify_rotate_eq2leq(pl,args[0],pf);
      if(g == cong) return simplify_rotate_cong(pl,args[0],pf);
      if(g == modpon) return simplify_rotate_modpon(pl,args[0],pf);
      // if(g == symm) return simplify_rotate_symm(pl,args[0],pf);
    }
    if(op(pf) == Leq)
      throw "foo!";
    throw cannot_simplify();
  }

  bool is_normal_ineq(const ast &ineq){
    if(sym(ineq) == normal)
      return is_ineq(arg(ineq,0));
    return is_ineq(ineq);
  }

  ast destruct_cond_ineq(const ast &ineq, ast &Aproves, ast &Bproves){
    ast res = ineq;
    opr o = op(res);
    if(o == And){
      Aproves = my_and(Aproves,arg(res,0));
      res = arg(res,1);
      o = op(res);
    }
    if(o == Implies){
      Bproves = my_and(Bproves,arg(res,0));
      res = arg(res,1);
    }
    return res;
  }

  ast distribute_coeff(const ast &coeff, const ast &s){
    if(sym(s) == sum){
      if(sym(arg(s,2)) == sum)
	return make(sum,
		    distribute_coeff(coeff,arg(s,0)),
		    make_int(rational(1)),
		    distribute_coeff(make(Times,coeff,arg(s,1)), arg(s,2)));
      else
	return make(sum,
		    distribute_coeff(coeff,arg(s,0)),
		    make(Times,coeff,arg(s,1)),
		    arg(s,2));
    }
    if(op(s) == Leq && arg(s,1) == make_int(rational(0)) && arg(s,2) == make_int(rational(0)))
      return s;
    return make(sum,make(Leq,make_int(rational(0)),make_int(rational(0))),coeff,s);
  }

  ast simplify_sum(std::vector<ast> &args){
    if(args[1] != make_int(rational(1))){
      if(sym(args[2]) == sum)
	return make(sum,args[0],make_int(rational(1)),distribute_coeff(args[1],args[2]));
    }
    ast Aproves = mk_true(), Bproves = mk_true();
    ast ineq = destruct_cond_ineq(args[0],Aproves,Bproves);
    if(!is_normal_ineq(ineq)) throw cannot_simplify();
    sum_cond_ineq(ineq,args[1],args[2],Aproves,Bproves);
    return my_and(Aproves,my_implies(Bproves,ineq));
  }

  ast simplify_rotate_sum(const ast &pl, const ast &pf){
    ast Aproves = mk_true(), Bproves = mk_true();
    ast ineq = make(Leq,make_int("0"),make_int("0"));
    ineq = rotate_sum_rec(pl,pf,Aproves,Bproves,ineq);
    if(is_true(Aproves) && is_true(Bproves))
      return ineq;
    return my_and(Aproves,my_implies(Bproves,ineq));
  }

  bool is_rewrite_chain(const ast &chain){
    return sym(chain) == concat;
  }
  
#if 0
  ast ineq_from_chain_simple(const ast &chain, ast &cond){
    if(is_true(chain))
      return chain;
    ast last = chain_last(chain);
    ast rest = chain_rest(chain);
    if(is_true(rest) && is_rewrite_side(LitA,last)
       && is_true(rewrite_lhs(last))){
      cond = my_and(cond,rewrite_cond(last));
      return rewrite_rhs(last);
    }
    if(is_rewrite_side(LitB,last) && is_true(rewrite_cond(last)))
      return ineq_from_chain_simple(rest,cond);
    return chain;
  }
#endif

  ast ineq_from_chain(const ast &chain, ast &Aproves, ast &Bproves){
    if(is_rewrite_chain(chain))
      return rewrite_chain_to_normal_ineq(chain,Aproves,Bproves);
    return chain;
  }


  void sum_cond_ineq(ast &ineq, const ast &coeff2, const ast &ineq2, ast &Aproves, ast &Bproves){
    opr o = op(ineq2);
    if(o == And){
      sum_cond_ineq(ineq,coeff2,arg(ineq2,1),Aproves,Bproves);
      Aproves = my_and(Aproves,arg(ineq2,0));
    }
    else if(o == Implies){
      sum_cond_ineq(ineq,coeff2,arg(ineq2,1),Aproves,Bproves);
      Bproves = my_and(Bproves,arg(ineq2,0));
    }
    else {
      ast the_ineq = ineq_from_chain(ineq2,Aproves,Bproves);
      if(sym(ineq) == normal || sym(the_ineq) == normal){
	sum_normal_ineq(ineq,coeff2,the_ineq,Aproves,Bproves);
	return;
      }
      if(is_ineq(the_ineq))
	linear_comb(ineq,coeff2,the_ineq);
      else 
	throw cannot_simplify();
    }
  }
  
  void destruct_normal(const ast &pf, ast &p, ast &n){
    if(sym(pf) == normal){
      p = arg(pf,0);
      n = arg(pf,1);
    }
    else {
      p = pf;
      n = mk_true();
    }
  }

  void sum_normal_ineq(ast &ineq, const ast &coeff2, const ast &ineq2, ast &Aproves, ast &Bproves){
    ast in1,in2,n1,n2;
    destruct_normal(ineq,in1,n1);
    destruct_normal(ineq2,in2,n2);
    ast dummy1, dummy2;
    sum_cond_ineq(in1,coeff2,in2,dummy1,dummy2);
    n1 = merge_normal_chains(n1,n2, Aproves, Bproves);
    ineq = is_true(n1) ? in1 : make_normal(in1,n1);
  }

  bool is_ineq(const ast &ineq){
    opr o = op(ineq);
    if(o == Not) o = op(arg(ineq,0));
    return o == Leq || o == Lt || o == Geq || o == Gt;
  }

  // divide both sides of inequality by a non-negative integer divisor
  ast idiv_ineq(const ast &ineq1, const ast &divisor){
    if(sym(ineq1) == normal){
      ast in1,n1;
      destruct_normal(ineq1,in1,n1);
      in1 = idiv_ineq(in1,divisor);
      return make_normal(in1,n1);
    }
    if(divisor == make_int(rational(1)))
      return ineq1;
    ast ineq = ineq1;
    if(op(ineq) == Lt)
      ineq = simplify_ineq(make(Leq,arg(ineq,0),make(Sub,arg(ineq,1),make_int("1"))));
    return make(op(ineq),mk_idiv(arg(ineq,0),divisor),mk_idiv(arg(ineq,1),divisor));
  }
  
  ast rotate_sum_rec(const ast &pl, const ast &pf, ast &Aproves, ast &Bproves, ast &ineq){
    if(pf == pl){
      if(sym(ineq) == normal)
	return ineq;
      return simplify_ineq(ineq);
    }
    if(op(pf) == Uninterpreted && sym(pf) == sum){
      if(arg(pf,2) == pl){
	sum_cond_ineq(ineq,make_int("1"),arg(pf,0),Aproves,Bproves);
	ineq = idiv_ineq(ineq,arg(pf,1));
	return ineq;
      }
      sum_cond_ineq(ineq,arg(pf,1),arg(pf,2),Aproves,Bproves);
      return rotate_sum_rec(pl,arg(pf,0),Aproves,Bproves,ineq);
    }
    throw cannot_simplify();
  }

  ast simplify_rotate_leq2eq(const ast &pl, const ast &neg_equality, const ast &pf){
    if(pl == arg(pf,0)){
      ast equality = arg(neg_equality,0);
      ast x = arg(equality,0);
      ast y = arg(equality,1);
      ast Aproves1 = mk_true(), Bproves1 = mk_true();
      ast pf1 = destruct_cond_ineq(arg(pf,1), Aproves1, Bproves1);
      ast pf2 = destruct_cond_ineq(arg(pf,2), Aproves1, Bproves1);
      ast xleqy = round_ineq(ineq_from_chain(pf1,Aproves1,Bproves1));
      ast yleqx = round_ineq(ineq_from_chain(pf2,Aproves1,Bproves1));
      ast ineq1 = make(Leq,make_int("0"),make_int("0"));
      sum_cond_ineq(ineq1,make_int("-1"),xleqy,Aproves1,Bproves1);
      sum_cond_ineq(ineq1,make_int("-1"),yleqx,Aproves1,Bproves1);
      ast Acond  = my_implies(Aproves1,my_and(Bproves1,z3_simplify(ineq1)));
      ast Aproves2 = mk_true(), Bproves2 = mk_true();
      ast ineq2 = make(Leq,make_int("0"),make_int("0"));
      sum_cond_ineq(ineq2,make_int("1"),xleqy,Aproves2,Bproves2);
      sum_cond_ineq(ineq2,make_int("1"),yleqx,Aproves2,Bproves2);
      ast Bcond = my_implies(Bproves1,my_and(Aproves1,z3_simplify(ineq2)));
      //      if(!is_true(Aproves1) || !is_true(Bproves1))
      //	std::cout << "foo!\n";;
      if(y == make_int(rational(0)) && op(x) == Plus && num_args(x) == 2){
	if(get_term_type(arg(x,0)) == LitA){
	  ast iter = z3_simplify(make(Plus,arg(x,0),get_ineq_rhs(xleqy)));
	  ast rewrite1 = make_rewrite(LitA,pos_add(0,top_pos),Acond,make(Equal,arg(x,0),iter));
	  iter = make(Plus,iter,arg(x,1));
	  ast rewrite2 = make_rewrite(LitB,top_pos,Bcond,make(Equal,iter,y));
	  return chain_cons(chain_cons(mk_true(),rewrite1),rewrite2);
	}
	if(get_term_type(arg(x,1)) == LitA){
	  ast iter = z3_simplify(make(Plus,arg(x,1),get_ineq_rhs(xleqy)));
	  ast rewrite1 = make_rewrite(LitA,pos_add(1,top_pos),Acond,make(Equal,arg(x,1),iter));
	  iter = make(Plus,arg(x,0),iter);
	  ast rewrite2 = make_rewrite(LitB,top_pos,Bcond,make(Equal,iter,y));
	  return chain_cons(chain_cons(mk_true(),rewrite1),rewrite2);
	}
      }
      if(get_term_type(x) == LitA){
	ast iter = z3_simplify(make(Plus,x,get_ineq_rhs(xleqy)));
	ast rewrite1 = make_rewrite(LitA,top_pos,Acond,make(Equal,x,iter));
	ast rewrite2 = make_rewrite(LitB,top_pos,Bcond,make(Equal,iter,y));
	return chain_cons(chain_cons(mk_true(),rewrite1),rewrite2);
      }
      if(get_term_type(y) == LitA){
	ast iter = z3_simplify(make(Plus,y,get_ineq_rhs(yleqx)));
	ast rewrite2 = make_rewrite(LitA,top_pos,Acond,make(Equal,iter,y));
	ast rewrite1 = make_rewrite(LitB,top_pos,Bcond,make(Equal,x,iter));
	return chain_cons(chain_cons(mk_true(),rewrite1),rewrite2);
      }
      throw cannot_simplify();
    }
    throw cannot_simplify();
  }

  ast round_ineq(const ast &ineq){
    if(sym(ineq) == normal)
      return make_normal(round_ineq(arg(ineq,0)),arg(ineq,1));
    if(!is_ineq(ineq))
      throw cannot_simplify();
    ast res = simplify_ineq(ineq);
    if(op(res) == Lt)
      res = make(Leq,arg(res,0),make(Sub,arg(res,1),make_int("1")));
    return res;
  }

  ast unmixed_eq2ineq(const ast &lhs, const ast &rhs, opr comp_op, const ast &equa, ast &cond){
    ast ineqs= chain_ineqs(comp_op,LitA,equa,lhs,rhs); // chain must be from lhs to rhs
    cond = my_and(cond,chain_conditions(LitA,equa)); 
    ast Bconds = z3_simplify(chain_conditions(LitB,equa)); 
    if(is_true(Bconds) && op(ineqs) != And)
      return my_implies(cond,ineqs);
    if(op(ineqs) != And)
      return my_and(Bconds,my_implies(cond,ineqs));
    throw "help!";
  }

  ast add_mixed_eq2ineq(const ast &lhs, const ast &rhs, const ast &equa, const ast &itp){
    if(is_true(equa))
      return itp;
     std::vector<ast> args(3);
     args[0] = itp;
     args[1] = make_int("1");
     ast ineq = make(Leq,make_int(rational(0)),make_int(rational(0)));
     args[2] = make_normal(ineq,cons_normal(fix_normal(lhs,rhs,equa),mk_true()));
     return simplify_sum(args);
  }


  ast simplify_rotate_eq2leq(const ast &pl, const ast &neg_equality, const ast &pf){
    if(pl == arg(pf,1)){
      ast cond = mk_true();
      ast equa = sep_cond(arg(pf,0),cond);
      if(is_equivrel_chain(equa)){
	ast lhs,rhs; eq_from_ineq(arg(neg_equality,0),lhs,rhs); // get inequality we need to prove
	if(!rewrites_from_to(equa,lhs,rhs)){
	  lhs = arg(arg(neg_equality,0),0); // the equality proved is ambiguous, sadly
	  rhs = arg(arg(neg_equality,0),1);
	}
	LitType lhst = get_term_type(lhs), rhst = get_term_type(rhs);
	if(lhst != LitMixed && rhst != LitMixed)
	  return unmixed_eq2ineq(lhs, rhs, op(arg(neg_equality,0)), equa, cond);
	else {
	  ast left, left_term, middle, right_term, right;
	  left = get_left_movers(equa,lhs,middle,left_term);
	  middle = get_right_movers(middle,rhs,right,right_term);
	  ast itp = unmixed_eq2ineq(left_term, right_term, op(arg(neg_equality,0)), middle, cond);
	  // itp = my_implies(cond,itp);
	  itp = add_mixed_eq2ineq(lhs, left_term, left, itp);
	  itp = add_mixed_eq2ineq(right_term, rhs, right, itp);
	  return itp;
	}
      }
    }
    throw "help!";
  }

  void reverse_modpon(std::vector<ast> &args){
    std::vector<ast> sargs(1); sargs[0] = args[1];
    args[1] = simplify_symm(sargs);
    if(is_equivrel_chain(args[2]))
      args[1] = down_chain(args[1]);
    std::swap(args[0],args[2]);
  }

  ast simplify_rotate_modpon(const ast &pl, const ast &neg_equality, const ast &pf){
    std::vector<ast> args; args.resize(3);
    args[0] = arg(pf,0);
    args[1] = arg(pf,1);
    args[2] = arg(pf,2);
    if(pl == args[0])
      reverse_modpon(args);
    if(pl == args[2]){
      ast cond = mk_true();
      ast chain = simplify_modpon_fwd(args, cond);
      return my_implies(cond,chain);
    }    
    throw cannot_simplify();
  }

  ast get_ineq_rhs(const ast &ineq2){
    opr o = op(ineq2);
    if(o == Implies)
      return get_ineq_rhs(arg(ineq2,1));
    else if(o == Leq || o == Lt)
      return arg(ineq2,1);
    throw cannot_simplify();
  }

  ast simplify_rotate_cong(const ast &pl, const ast &neg_equality, const ast &pf){
    if(pl == arg(pf,2)){
      if(op(arg(pf,0)) == True)
	return mk_true();
      rational pos;
      if(is_numeral(arg(pf,1),pos)){
	int ipos = pos.get_unsigned();
	ast cond = mk_true();
	ast equa = sep_cond(arg(pf,0),cond);
#if 0	  
	if(op(equa) == Equal){
	  ast pe = mk_not(neg_equality);
	  ast lhs = subst_in_arg_pos(ipos,arg(equa,0),arg(pe,0));
	  ast rhs = subst_in_arg_pos(ipos,arg(equa,1),arg(pe,1));
	  ast res = make(Equal,lhs,rhs);
	  return my_implies(cond,res);
	}
#endif
	ast res = chain_pos_add(ipos,equa);
	return my_implies(cond,res);
      }
    }
    throw cannot_simplify();
  }

  ast simplify_symm(const std::vector<ast> &args){
    if(op(args[0]) == True)
      return mk_true();
    ast cond = mk_true();
    ast equa = sep_cond(args[0],cond);
    if(is_equivrel_chain(equa))
      return my_implies(cond,reverse_chain(equa));
    if(is_negation_chain(equa))
      return commute_negation_chain(equa);
    throw cannot_simplify();
  }

  ast simplify_modpon_fwd(const std::vector<ast> &args, ast &cond){
    ast P = sep_cond(args[0],cond);
    ast PeqQ = sep_cond(args[1],cond);
    ast chain;
    if(is_equivrel_chain(P)){
      try {
	ast split[2];
	split_chain(PeqQ,split);
	chain = reverse_chain(split[0]);
	chain = concat_rewrite_chain(chain,P);
	chain = concat_rewrite_chain(chain,split[1]);
      }
      catch(const cannot_split &){
	static int this_count = 0;
	this_count++;
	ast tail, pref = get_head_chain(PeqQ,tail,false); // pref  is x=y, tail is x=y -> x'=y'
	ast split[2]; split_chain(tail,split); // rewrites from x to x' and y to y'
	ast head = chain_last(pref);
	ast prem = make_rewrite(rewrite_side(head),top_pos,rewrite_cond(head),make(Iff,mk_true(),mk_not(rewrite_lhs(head))));
	ast back_chain = chain_cons(mk_true(),prem);
	back_chain = concat_rewrite_chain(back_chain,chain_pos_add(0,reverse_chain(chain_rest(pref))));
	ast cond = contra_chain(back_chain,P);
	if(is_rewrite_side(LitA,head))
	  cond = mk_not(cond);
	ast fwd_rewrite = make_rewrite(rewrite_side(head),top_pos,cond,rewrite_rhs(head));
	P = chain_cons(mk_true(),fwd_rewrite);
	chain = reverse_chain(split[0]);
	chain = concat_rewrite_chain(chain,P);
	chain = concat_rewrite_chain(chain,split[1]);
      }
    }
    else { // if not an equivalence, must be of form T <-> pred
      chain = concat_rewrite_chain(P,PeqQ);
    }
    return chain;
  }

  struct subterm_normals_failed {};

  void get_subterm_normals(const ast &ineq1, const ast &ineq2, const ast &chain, ast &normals,
			   const ast &pos, hash_set<ast> &memo, ast &Aproves, ast &Bproves){
    opr o1 = op(ineq1);
    opr o2 = op(ineq2);
    if(o1 == Not || o1 == Leq || o1 == Lt || o1 == Geq || o1 == Gt || o1 == Plus || o1 == Times){
      int n = num_args(ineq1);
      if(o2 != o1 || num_args(ineq2) != n)
	throw "bad inequality rewriting";
      for(int i = 0; i < n; i++){
	ast new_pos = add_pos_to_end(pos,i);
	get_subterm_normals(arg(ineq1,i), arg(ineq2,i), chain, normals, new_pos, memo, Aproves, Bproves);
      }
    }
    else if(get_term_type(ineq2) == LitMixed){
      if(memo.find(ineq2) == memo.end()){
	memo.insert(ineq2);
	ast sub_chain = extract_rewrites(chain,pos);
	if(is_true(sub_chain))
	  throw "bad inequality rewriting";
	ast new_normal = make_normal_step(ineq2,ineq1,reverse_chain(sub_chain));
	normals = merge_normal_chains(normals,cons_normal(new_normal,mk_true()), Aproves, Bproves);
      }
    } 
    else if(!(ineq1 == ineq2))
      throw subterm_normals_failed();
  }

  ast rewrites_to_normals(const ast &ineq1, const ast &chain, ast &normals, ast &Aproves, ast &Bproves, ast &Aineqs){
    if(is_true(chain))
      return ineq1;
    ast last = chain_last(chain);
    ast rest = chain_rest(chain);
    ast new_ineq1 = rewrites_to_normals(ineq1, rest, normals, Aproves, Bproves, Aineqs);
    ast p1 = rewrite_pos(last);
    ast term1;
    ast coeff = arith_rewrite_coeff(new_ineq1,p1,term1);
    ast res = subst_in_pos(new_ineq1,rewrite_pos(last),rewrite_rhs(last));
    ast rpos;
    pos_diff(p1,rewrite_pos(last),rpos);
    ast term2 = subst_in_pos(term1,rpos,rewrite_rhs(last));
    if(get_term_type(term1) != LitMixed && get_term_type(term2) != LitMixed){
      if(is_rewrite_side(LitA,last))
	linear_comb(Aineqs,coeff,make(Leq,make_int(rational(0)),make(Sub,term2,term1)));
    }
    else {
      ast pf = extract_rewrites(make(concat,mk_true(),last),p1);
      ast new_normal = fix_normal(term1,term2,pf);
      normals = merge_normal_chains(normals,cons_normal(new_normal,mk_true()), Aproves, Bproves);
    }
    return res;
  }

  ast arith_rewrite_coeff(const ast &ineq, ast &p1, ast &term){
    ast coeff = make_int(rational(1));
    if(p1 == top_pos){
      term = ineq;
      return coeff;
    }
    int argpos = pos_arg(p1);
    opr o = op(ineq);
    switch(o){
    case Leq: 
    case Lt: 
      coeff = argpos ? make_int(rational(1)) : make_int(rational(-1));
      break;
    case Geq: 
    case Gt: 
      coeff = argpos ? make_int(rational(-1)) : make_int(rational(1));
      break;
    case Not:
      coeff = make_int(rational(-1));
    case Plus:
      break;
    case Times:
      coeff = arg(ineq,0);
      break;
    default:
      p1 = top_pos;
      term = ineq;
      return coeff;
    }
    p1 = arg(p1,1);
    ast res = arith_rewrite_coeff(arg(ineq,argpos),p1,term);
    p1 = pos_add(argpos,p1);
    return coeff == make_int(rational(1)) ? res : make(Times,coeff,res);
  }

  ast rewrite_chain_to_normal_ineq(const ast &chain, ast &Aproves, ast &Bproves){
    ast tail, pref = get_head_chain(chain,tail,false); // pref  is x=y, tail is x=y -> x'=y'
    ast head = chain_last(pref);
    ast ineq1 = rewrite_rhs(head);
    ast ineq2 = apply_rewrite_chain(ineq1,tail);
    ast nc = mk_true();
    hash_set<ast> memo;
    ast itp = make(Leq,make_int(rational(0)),make_int(rational(0)));
    ast Aproves_save = Aproves, Bproves_save = Bproves; try {
      get_subterm_normals(ineq1,ineq2,tail,nc,top_pos,memo, Aproves, Bproves);
    }
    catch (const subterm_normals_failed &){ Aproves = Aproves_save; Bproves = Bproves_save; nc = mk_true();
      rewrites_to_normals(ineq1, tail, nc, Aproves, Bproves, itp);
    }
    if(is_rewrite_side(LitA,head)){
      linear_comb(itp,make_int("1"),ineq1); // make sure it is normal form
      //itp = ineq1;
      ast mc = z3_simplify(chain_side_proves(LitB,pref));
      Bproves = my_and(Bproves,mc);
    }
    else {
      ast mc = z3_simplify(chain_side_proves(LitA,pref));
      Aproves = my_and(Aproves,mc);
    }
    if(is_true(nc))
      return itp;
    return make_normal(itp,nc);
  }

  /* Given a chain rewrite chain deriving not P and a rewrite chain deriving P, return an interpolant. */
  ast contra_chain(const ast &neg_chain, const ast &pos_chain){
    // equality is a special case. we use the derivation of x=y to rewrite not(x=y) to not(y=y)
    if(is_equivrel_chain(pos_chain)){
      ast tail, pref = get_head_chain(neg_chain,tail); // pref  is not(x=y), tail is not(x,y) -> not(x',y')
      ast split[2]; split_chain(down_chain(tail),split); // rewrites from x to x' and y to y'
      ast chain = split[0];
      chain = concat_rewrite_chain(chain,pos_chain); // rewrites from x to y'
      chain = concat_rewrite_chain(chain,reverse_chain(split[1])); // rewrites from x to y
      chain = concat_rewrite_chain(pref,chain_pos_add(0,chain_pos_add(0,chain))); // rewrites t -> not(y=y)
      ast head = chain_last(pref);
      if(is_rewrite_side(LitB,head)){
	ast condition = chain_conditions(LitB,chain);
	return my_and(my_implies(chain_conditions(LitA,chain),chain_formulas(LitA,chain)),condition);
      }
      else {
	ast condition = chain_conditions(LitA,chain);
	return my_and(chain_conditions(LitB,chain),my_implies(condition,mk_not(chain_formulas(LitB,chain))));
      }
      // ast chain = concat_rewrite_chain(neg_chain,chain_pos_add(0,chain_pos_add(0,pos_chain)));
      // return my_and(my_implies(chain_conditions(LitA,chain),chain_formulas(LitA,chain)),chain_conditions(LitB,chain));
    }
    // otherwise, we reverse the derivation of t = P and use it to rewrite not(P) to not(t)
    ast chain = concat_rewrite_chain(neg_chain,chain_pos_add(0,reverse_chain(pos_chain)));
    return my_and(my_implies(chain_conditions(LitA,chain),chain_formulas(LitA,chain)),chain_conditions(LitB,chain));
  }

  ast simplify_modpon(const std::vector<ast> &args){
    ast Aproves = mk_true(), Bproves = mk_true();
    ast chain = simplify_modpon_fwd(args,Bproves);
    ast Q2 = destruct_cond_ineq(args[2],Aproves,Bproves);
    ast interp;
    if(is_normal_ineq(Q2)){ // inequalities are special
      ast nQ2 = rewrite_chain_to_normal_ineq(chain,Aproves,Bproves);
      sum_cond_ineq(nQ2,make_int(rational(1)),Q2,Aproves,Bproves);
      interp = normalize(nQ2);
    }
    else 
      interp = is_negation_chain(chain) ? contra_chain(chain,Q2) : contra_chain(Q2,chain);
    return my_and(Aproves,my_implies(Bproves,interp));
  }


  ast simplify_exmid(const std::vector<ast> &args){
    if(is_equivrel(args[0])){
      ast Aproves = mk_true(), Bproves = mk_true();
      ast chain = destruct_cond_ineq(args[1],Aproves,Bproves);
      ast Q2 = destruct_cond_ineq(args[2],Aproves,Bproves);
      ast interp = contra_chain(Q2,chain);
      return my_and(Aproves,my_implies(Bproves,interp));
    }
    throw "bad exmid";
  }

  ast simplify_cong(const std::vector<ast> &args){
    ast Aproves = mk_true(), Bproves = mk_true();
    ast chain = destruct_cond_ineq(args[0],Aproves,Bproves);
    rational pos;
    if(is_numeral(args[1],pos)){
      int ipos = pos.get_unsigned();
      chain = chain_pos_add(ipos,chain);
      ast Q2 = destruct_cond_ineq(args[2],Aproves,Bproves);
      ast interp = contra_chain(Q2,chain);
      return my_and(Aproves,my_implies(Bproves,interp));
    }
    throw "bad cong";
  }

  bool is_equivrel(const ast &p){
    opr o = op(p);
    return o == Equal || o == Iff;
  }
  
  struct rewrites_failed{};

  /* Suppose p in Lang(B) and A |- p -> q and B |- q -> r. Return a z in Lang(B) such that
     B |- p -> z and A |- z -> q. Collect any side conditions in "rules". */

  ast commute_rewrites(const ast &p, const ast &q, const ast &r, ast &rules){
    if(q == r)
      return p;
    if(p == q)
      return r;
    else {
      ast rew = make(Equal,q,r);
      if(get_term_type(rew) == LitB){
	apply_common_rewrites(p,p,q,rules); // A rewrites must be over comon vocab
	return r;
      }
    }
    if(sym(p) != sym(q) || sym(q) != sym(r))
      throw rewrites_failed();
    int nargs = num_args(p);
    if(nargs != num_args(q) || nargs != num_args(r))
      throw rewrites_failed();
    std::vector<ast> args; args.resize(nargs);
    for(int i = 0; i < nargs; i++)
      args[i] = commute_rewrites(arg(p,i),arg(q,i),arg(r,i),rules);
    return clone(p,args);
  }

  ast apply_common_rewrites(const ast &p, const ast &q, const ast &r, ast &rules){
    if(q == r)
      return p;
    ast rew = make(Equal,q,r);
    if(term_common(rew)){
      if(p != q)
	throw rewrites_failed();
      rules = my_and(rules,rew);
      return r;
    }
    if(sym(p) != sym(q) || sym(q) != sym(r))
      return p;
    int nargs = num_args(p);
    if(nargs != num_args(q) || nargs != num_args(r))
      return p;
    std::vector<ast> args; args.resize(nargs);
    for(int i = 0; i < nargs; i++)
      args[i] = apply_common_rewrites(arg(p,i),arg(q,i),arg(r,i),rules);
    return clone(p,args);
  }

  ast apply_all_rewrites(const ast &p, const ast &q, const ast &r){
    if(q == r)
      return p;
    if(p == q)
      return r;
    if(sym(p) != sym(q) || sym(q) != sym(r))
      throw rewrites_failed();
    int nargs = num_args(p);
    if(nargs != num_args(q) || nargs != num_args(r))
      throw rewrites_failed();
    std::vector<ast> args; args.resize(nargs);
    for(int i = 0; i < nargs; i++)
      args[i] = apply_all_rewrites(arg(p,i),arg(q,i),arg(r,i));
    return clone(p,args);
  }

  ast delta(const ast &x, const ast &y){
    if(op(x) != op(y) || (op(x) == Uninterpreted && sym(x) != sym(y)) || num_args(x) != num_args(y))
      return make(Equal,x,y);
    ast res = mk_true();
    int nargs = num_args(x);
    for(int i = 0; i < nargs; i++)
      res = my_and(res,delta(arg(x,i),arg(y,i)));
    return res;
  }

  bool diff_rec(LitType t, const ast &p, const ast &q, ast &pd, ast &qd){
    if(p == q)
      return false;
    if(term_in_vocab(t,p) && term_in_vocab(t,q)){
      pd = p;
      qd = q;
      return true;
    }
    else {
      if(sym(p) != sym(q)) return false;
      int nargs = num_args(p);
      if(num_args(q) != nargs) return false;
      for(int i = 0; i < nargs; i++)
	if(diff_rec(t,arg(p,i),arg(q,i),pd,qd))
	  return true;
      return false;
    }
  }

  void diff(LitType t, const ast &p, const ast &q, ast &pd, ast &qd){
    if(!diff_rec(t,p,q,pd,qd))
      throw cannot_simplify();
  }

  bool apply_diff_rec(LitType t, const ast &inp, const ast &p, const ast &q, ast &out){
    if(p == q)
      return false;
    if(term_in_vocab(t,p) && term_in_vocab(t,q)){
      if(inp != p)
	throw cannot_simplify();
      out = q;
      return true;
    }
    else {
      int nargs = num_args(p);
      if(sym(p) != sym(q)) throw cannot_simplify();
      if(num_args(q) != nargs) throw cannot_simplify();
      if(sym(p) != sym(inp)) throw cannot_simplify();
      if(num_args(inp) != nargs) throw cannot_simplify();
      for(int i = 0; i < nargs; i++)
	if(apply_diff_rec(t,arg(inp,i),arg(p,i),arg(q,i),out))
	  return true;
      return false;
    }
  }

  ast apply_diff(LitType t, const ast &inp, const ast &p, const ast &q){
    ast out;
    if(!apply_diff_rec(t,inp,p,q,out))
      throw cannot_simplify();
    return out;
  }

  bool merge_A_rewrites(const ast &A1, const ast &A2, ast &merged) {
    if(arg(A1,1) == arg(A2,0)){
      merged = make(op(A1),arg(A1,0),arg(A2,1));
      return true;
    }
    ast diff1l, diff1r, diff2l, diff2r,diffBl,diffBr;
    diff(LitA,arg(A1,0),arg(A1,1),diff1l,diff1r);
    diff(LitA,arg(A2,0),arg(A2,1),diff2l,diff2r);
    diff(LitB,arg(A1,1),arg(A2,0),diffBl,diffBr);
    if(!term_common(diff2l) && !term_common(diffBr)){
      ast A1r = apply_diff(LitB,arg(A2,1),arg(A2,0),arg(A1,1));
      merged = make(op(A1),arg(A1,0),A1r);
      return true;
    }
    if(!term_common(diff1r) && !term_common(diffBl)){
      ast A2l = apply_diff(LitB,arg(A1,0),arg(A1,1),arg(A2,0));
      merged = make(op(A1),A2l,arg(A2,1));
      return true;
    }
    return false;
  }

  void collect_A_rewrites(const ast &t, std::vector<ast> &res){
    if(is_true(t))
      return;
    if(sym(t) == concat){
      res.push_back(arg(t,0));
      collect_A_rewrites(arg(t,0),res);
      return;
    }
    res.push_back(t);
  }

  ast concat_A_rewrites(const std::vector<ast> &rew){
    if(rew.size() == 0)
      return mk_true();
    ast res = rew[0];
    for(unsigned i = 1; i < rew.size(); i++)
      res = make(concat,res,rew[i]);
    return res;
  }

  ast merge_concat_rewrites(const ast &A1, const ast &A2){
    std::vector<ast> rew;
    collect_A_rewrites(A1,rew);
    int first = rew.size(), last = first; // range that might need merging 
    collect_A_rewrites(A2,rew);
    while(first > 0 && first < (int)rew.size() && first <= last){
      ast merged;
      if(merge_A_rewrites(rew[first-1],rew[first],merged)){
	rew[first] = merged;
	first--;
	rew.erase(rew.begin()+first);
	last--;
	if(first >= last) last = first+1;
      }
      else
	first++;
    }
    return concat_A_rewrites(rew);
  }

  ast sep_cond(const ast &t, ast &cond){
    if(op(t) == Implies){
      cond = my_and(cond,arg(t,0));
      return arg(t,1);
    }
    return t;
  }


  /* operations on term positions */

  /** Finds the difference between two positions. If p1 < p2 (p1 is a
      position below p2), returns -1 and sets diff to p2-p1 (the psath
      from position p2 to position p1).  If p2 < p1 (p2 is a position
      below p1), returns 1 and sets diff to p1-p2 (the psath from
      position p1 to position p2). If equal, return 0 and set diff to
      top_pos.  Else (if p1 and p2 are independent) returns 2 and
      leaves diff unchanged. */

  int pos_diff(const ast &p1, const ast &p2, ast &diff){
    if(p1 == top_pos && p2 != top_pos){
      diff = p2;
      return 1;
    }
    if(p2 == top_pos && p1 != top_pos){
      diff = p1;
      return -1;
    }
    if(p1 == top_pos && p2 == top_pos){
      diff = p1;
      return 0;
    }
    if(arg(p1,0) == arg(p2,0)) // same argument position, recur
      return pos_diff(arg(p1,1),arg(p2,1),diff);
    return 2;
  }

  /* return the position of pos in the argth argument */
  ast pos_add(int arg, const ast &pos){
    return make(add_pos,make_int(rational(arg)),pos);
  }

  ast add_pos_to_end(const ast &pos, int i){
    if(pos == top_pos)
      return pos_add(i,pos);
    return make(add_pos,arg(pos,0),add_pos_to_end(arg(pos,1),i));
  }

  /* return the argument number of position, if not top */
  int pos_arg(const ast &pos){
    rational r;
    if(is_numeral(arg(pos,0),r))
      return r.get_unsigned();
    throw "bad position!";
  }

  /* substitute y into position pos in x */
  ast subst_in_pos(const ast &x, const ast &pos, const ast &y){
    if(pos == top_pos)
      return y;
    int p = pos_arg(pos);
    int nargs = num_args(x);
    if(p >= 0 && p < nargs){
      std::vector<ast> args(nargs);
      for(int i = 0; i < nargs; i++)
	args[i] = i == p ? subst_in_pos(arg(x,i),arg(pos,1),y) : arg(x,i);
      return clone(x,args);
    }
    throw "bad term position!";
  }

  ast diff_chain(LitType t, const ast &pos, const ast &x, const ast &y, const ast &prefix){
    int nargs = num_args(x);
    if(x == y) return prefix;
    if(sym(x) == sym(y) && nargs == num_args(y)){
      ast res = prefix;
      for(int i = 0; i < nargs; i++)
	res = diff_chain(t,pos_add(i,pos),arg(x,i),arg(y,i),res);
      return res;
    }
    return chain_cons(prefix,make_rewrite(t,pos,mk_true(),make_equiv_rel(x,y)));
  }

  /* operations on rewrites */
  ast make_rewrite(LitType t, const ast &pos, const ast &cond, const ast &equality){
#if 0
    if(pos == top_pos && op(equality) == Iff && !is_true(arg(equality,0)))
      throw "bad rewrite";
#endif
    if(!is_equivrel(equality))
      throw "bad rewrite";
    return make(t == LitA ? rewrite_A : rewrite_B, pos, cond, equality);
  }

  ast rewrite_pos(const ast &rew){
    return arg(rew,0);
  }

  ast rewrite_cond(const ast &rew){
    return arg(rew,1);
  }

  ast rewrite_equ(const ast &rew){
    return arg(rew,2);
  }

  ast rewrite_lhs(const ast &rew){
    return arg(arg(rew,2),0);
  }

  ast rewrite_rhs(const ast &rew){
    return arg(arg(rew,2),1);
  }

  /* operations on rewrite chains */

  ast chain_cons(const ast &chain, const ast &elem){
    return make(concat,chain,elem);
  }

  ast chain_rest(const ast &chain){
    return arg(chain,0);
  }

  ast chain_last(const ast &chain){
    return arg(chain,1);
  }

  ast rewrite_update_rhs(const ast &rew, const ast &pos, const ast &new_rhs, const ast &new_cond){
    ast foo = subst_in_pos(rewrite_rhs(rew),pos,new_rhs);
    ast equality = arg(rew,2);
    return make(sym(rew),rewrite_pos(rew),my_and(rewrite_cond(rew),new_cond),make(op(equality),arg(equality,0),foo));
  }

  ast rewrite_update_lhs(const ast &rew, const ast &pos, const ast &new_lhs, const ast &new_cond){
    ast foo = subst_in_pos(rewrite_lhs(rew),pos,new_lhs);
    ast equality = arg(rew,2);
    return make(sym(rew),rewrite_pos(rew),my_and(rewrite_cond(rew),new_cond),make(op(equality),foo,arg(equality,1)));
  }

  bool is_common_rewrite(const ast &rew){
    return term_common(arg(rew,2));
  }
  
  bool is_right_mover(const ast &rew){
    return term_common(rewrite_lhs(rew)) && !term_common(rewrite_rhs(rew));
  }

  bool is_left_mover(const ast &rew){
    return term_common(rewrite_rhs(rew)) && !term_common(rewrite_lhs(rew));
  }
  
  bool same_side(const ast &rew1, const ast &rew2){
    return sym(rew1) == sym(rew2);
  }

  bool is_rewrite_side(LitType t, const ast &rew){
    if(t == LitA)
      return sym(rew) == rewrite_A;
    return sym(rew) == rewrite_B;
  }

  LitType rewrite_side(const ast &rew){
    return (sym(rew) == rewrite_A) ? LitA : LitB;
  }

  ast rewrite_to_formula(const ast &rew){
    return my_implies(arg(rew,1),arg(rew,2));
  }
  
  // make rewrite rew conditon on rewrite cond 
  ast rewrite_conditional(const ast &cond, const ast &rew){
    ast cf = rewrite_to_formula(cond);
    return make(sym(rew),arg(rew,0),my_and(arg(rew,1),cf),arg(rew,2));
  }

  ast reverse_rewrite(const ast &rew){
    ast equ = arg(rew,2);
    return make(sym(rew),arg(rew,0),arg(rew,1),make(op(equ),arg(equ,1),arg(equ,0)));
  }

  ast rewrite_pos_add(int apos, const ast &rew){
    return make(sym(rew),pos_add(apos,arg(rew,0)),arg(rew,1),arg(rew,2));
  }

  ast rewrite_pos_set(const ast &pos, const ast &rew){
    return make(sym(rew),pos,arg(rew,1),arg(rew,2));
  }

  ast rewrite_up(const ast &rew){
    return make(sym(rew),arg(arg(rew,0),1),arg(rew,1),arg(rew,2));
  }

  /** Adds a rewrite to a chain of rewrites, keeping the chain in
      normal form. An empty chain is represented by true.*/

  ast add_rewrite_to_chain(const ast &chain, const ast &rewrite){
    if(is_true(chain))
      return chain_cons(chain,rewrite);
    ast last = chain_last(chain);
    ast rest = chain_rest(chain);
    if(same_side(last,rewrite)){
      ast p1 = rewrite_pos(last);
      ast p2 = rewrite_pos(rewrite);
      ast diff;
      switch(pos_diff(p1,p2,diff)){
      case 1: {
	ast absorb = rewrite_update_rhs(last,diff,rewrite_rhs(rewrite),rewrite_cond(rewrite));
	return add_rewrite_to_chain(rest,absorb);
      }
      case 0:
      case -1: {
	ast absorb = rewrite_update_lhs(rewrite,diff,rewrite_lhs(last),rewrite_cond(last));
	return add_rewrite_to_chain(rest,absorb);
      }
      default: {// independent case
	bool rm = is_right_mover(last);
	bool lm = is_left_mover(rewrite);
	if((lm && !rm) || (rm && !lm))
	  return chain_swap(rest,last,rewrite);
      }
      }
    }
    else {
      if(is_left_mover(rewrite)){
	if(is_common_rewrite(last))
	  return add_rewrite_to_chain(chain_cons(rest,flip_rewrite(last)),rewrite);
	if(!is_left_mover(last))
	  return chain_swap(rest,last,rewrite);
      }
      if(is_right_mover(last)){
	if(is_common_rewrite(rewrite))
	  return add_rewrite_to_chain(chain,flip_rewrite(rewrite));
	if(!is_right_mover(rewrite))
	  return chain_swap(rest,last,rewrite);
      }
    }
    return chain_cons(chain,rewrite);
  }  
  
  ast chain_swap(const ast &rest, const ast &last, const ast &rewrite){
    return chain_cons(add_rewrite_to_chain(rest,rewrite),last);
  }

  ast flip_rewrite(const ast &rew){
    symb flip_sym = (sym(rew) == rewrite_A) ? rewrite_B : rewrite_A;
    ast cf = rewrite_to_formula(rew);
    return make(flip_sym,arg(rew,0),my_implies(arg(rew,1),cf),arg(rew,2));
  }

  /** concatenates two rewrite chains, keeping result in normal form. */

  ast concat_rewrite_chain(const ast &chain1, const ast &chain2){
    if(is_true(chain2)) return chain1;
    if(is_true(chain1)) return chain2;
    ast foo = concat_rewrite_chain(chain1,chain_rest(chain2));
    return add_rewrite_to_chain(foo,chain_last(chain2));
  }

  /** reverse a chain of rewrites */

  ast reverse_chain_rec(const ast &chain, const ast &prefix){
    if(is_true(chain))
      return prefix;
    ast last = reverse_rewrite(chain_last(chain));
    ast rest = chain_rest(chain);
    return reverse_chain_rec(rest,chain_cons(prefix,last));
  }

  ast reverse_chain(const ast &chain){
    return reverse_chain_rec(chain,mk_true());
  }

  bool is_equivrel_chain(const ast &chain){
    if(is_true(chain))
      return true;
    ast last = chain_last(chain);
    ast rest = chain_rest(chain);
    if(is_true(rest))
      return !is_true(rewrite_lhs(last));
    return is_equivrel_chain(rest);
  }

  bool is_negation_chain(const ast &chain){
    if(is_true(chain))
      return false;
    ast last = chain_last(chain);
    ast rest = chain_rest(chain);
    if(is_true(rest))
      return op(rewrite_rhs(last)) == Not;
    return is_negation_chain(rest);
  }

  ast commute_negation_chain(const ast &chain){
    if(is_true(chain))
      return chain;
    ast last = chain_last(chain);
    ast rest = chain_rest(chain);
    if(is_true(rest)){
      ast old = rewrite_rhs(last);
      if(!(op(old) == Not))
	throw "bad negative equality chain";
      ast equ = arg(old,0);
      if(!is_equivrel(equ))
	throw "bad negative equality chain";
      last = rewrite_update_rhs(last,top_pos,make(Not,make(op(equ),arg(equ,1),arg(equ,0))),make(True));
      return chain_cons(rest,last);
    }
    ast pos = rewrite_pos(last);
    if(pos == top_pos)
      throw "bad negative equality chain";
    int idx = pos_arg(pos);
    if(idx != 0)
      throw "bad negative equality chain";
    pos = arg(pos,1);
    if(pos == top_pos){
      ast lhs = rewrite_lhs(last);
      ast rhs = rewrite_rhs(last);
      if(op(lhs) != Equal || op(rhs) != Equal)
	throw "bad negative equality chain";
      last = make_rewrite(rewrite_side(last),rewrite_pos(last),rewrite_cond(last),
			  make(Iff,make(Equal,arg(lhs,1),arg(lhs,0)),make(Equal,arg(rhs,1),arg(rhs,0))));
    }
    else {
      idx = pos_arg(pos);
      if(idx == 0)
	idx = 1;
      else if(idx == 1)
	idx = 0;
      else
	throw "bad negative equality chain";
      pos = pos_add(0,pos_add(idx,arg(pos,1)));
      last = make_rewrite(rewrite_side(last),pos,rewrite_cond(last),rewrite_equ(last));
    }
    return chain_cons(commute_negation_chain(rest),last);
  }

  // split a rewrite chain into head and tail at last top-level rewrite
  ast get_head_chain(const ast &chain, ast &tail, bool is_not = true){
    ast last = chain_last(chain);
    ast rest = chain_rest(chain);
    ast pos = rewrite_pos(last);
    if(pos == top_pos || (is_not && arg(pos,1) == top_pos)){
      tail = mk_true();
      return chain;
    }
    if(is_true(rest))
      throw "bad rewrite chain";
    ast head = get_head_chain(rest,tail,is_not);
    tail = chain_cons(tail,last);
    return head;
  }

  bool has_mixed_summands(const ast &e){
    if(op(e) == Plus){
      int nargs = num_args(e);
      for(int i = 0; i < nargs; i++)
	if(has_mixed_summands(arg(e,i)))
	  return true;
      return false;
    }
    return get_term_type(e) == LitMixed;
  }
  
  // split a rewrite chain into head and tail at last sum with no mixed sumands
  ast get_right_movers(const ast &chain, const ast &rhs, ast &tail, ast &mid){
    if(is_true(chain) || !has_mixed_summands(rhs)){
      mid = rhs;
      tail = mk_true();
      return chain;
    }
    ast last = chain_last(chain);
    ast rest = chain_rest(chain);
    ast mm = subst_in_pos(rhs,rewrite_pos(last),rewrite_lhs(last));
    ast res = get_right_movers(rest,mm,tail,mid);
    tail = chain_cons(tail,last);
    return res;
  }
  
  // split a rewrite chain into head and tail at first sum with no mixed sumands
  ast get_left_movers(const ast &chain, const ast &lhs, ast &tail, ast &mid){
    if(is_true(chain)){
      mid = lhs; 
      if(!has_mixed_summands(lhs)){
	tail = mk_true();
	return chain;
      }
      return ast();
    }
    ast last = chain_last(chain);
    ast rest = chain_rest(chain);
    ast res = get_left_movers(rest,lhs,tail,mid);
    if(res.null()){
      mid = subst_in_pos(mid,rewrite_pos(last),rewrite_rhs(last));
      if(get_term_type(mid) != LitMixed){
	tail = mk_true();
	return chain;
      }
      return ast();
    }      
    tail = chain_cons(tail,last);
    return res;
  }


  struct cannot_split {};

  /** Split a chain of rewrites two chains, operating on positions 0 and 1.
      Fail if any rewrite in the chain operates on top position. */
  void split_chain_rec(const ast &chain, ast *res){
    if(is_true(chain))
      return;
    ast last = chain_last(chain);
    ast rest = chain_rest(chain);
    split_chain_rec(rest,res);
    ast pos = rewrite_pos(last);
    if(pos == top_pos){
      if(rewrite_lhs(last) == rewrite_rhs(last))
	return; // skip if it's a noop
      throw cannot_split();
    }
    int arg = pos_arg(pos);
    if(arg<0 || arg > 1)
      throw cannot_split();
    res[arg] = chain_cons(res[arg],rewrite_up(last));
  }

  void split_chain(const ast &chain, ast *res){
    res[0] = res[1] = mk_true();
    split_chain_rec(chain,res);
  }

  ast extract_rewrites(const ast &chain, const ast &pos){
    if(is_true(chain))
      return chain;
    ast last = chain_last(chain);
    ast rest = chain_rest(chain);
    ast new_rest = extract_rewrites(rest,pos);
    ast p1 = rewrite_pos(last);
    ast diff;
    switch(pos_diff(p1,pos,diff)){
    case -1: {
      ast new_last = rewrite_pos_set(diff, last);
      return chain_cons(new_rest,new_last);
    }
    case 1:
      if(rewrite_lhs(last) != rewrite_rhs(last))
	throw "bad rewrite chain";
      break;
    default:;
    }
    return new_rest;
  }

  ast down_chain(const ast &chain){
    ast split[2];
    split_chain(chain,split);
    return split[0];
  }

  ast chain_conditions(LitType t, const ast &chain){
    if(is_true(chain))
      return mk_true();
    ast last = chain_last(chain);
    ast rest = chain_rest(chain);
    ast cond = chain_conditions(t,rest);
    if(is_rewrite_side(t,last))
      cond = my_and(cond,rewrite_cond(last));
    return cond;
  }

  ast chain_formulas(LitType t, const ast &chain){
    if(is_true(chain))
      return mk_true();
    ast last = chain_last(chain);
    ast rest = chain_rest(chain);
    ast cond = chain_formulas(t,rest);
    if(is_rewrite_side(t,last))
      cond = my_and(cond,rewrite_equ(last));
    return cond;
  }


  bool rewrites_from_to(const ast &chain, const ast &lhs, const ast &rhs){
    if(is_true(chain))
      return lhs == rhs;
    ast last = chain_last(chain);
    ast rest = chain_rest(chain);
    ast mid = subst_in_pos(rhs,rewrite_pos(last),rewrite_lhs(last));
    return rewrites_from_to(rest,lhs,mid);
  }

  struct bad_ineq_inference {};

  ast chain_ineqs(opr comp_op, LitType t, const ast &chain, const ast &lhs, const ast &rhs){
    if(is_true(chain)){
      if(lhs != rhs)
	throw bad_ineq_inference();
      return make(Leq,make_int(rational(0)),make_int(rational(0)));
    }
    ast last = chain_last(chain);
    ast rest = chain_rest(chain);
    ast mid = subst_in_pos(rhs,rewrite_pos(last),rewrite_lhs(last));
    ast cond = chain_ineqs(comp_op,t,rest,lhs,mid);
    if(is_rewrite_side(t,last)){
      ast diff;
      if(comp_op == Leq) diff = make(Sub,rhs,mid);
      else diff = make(Sub,mid,rhs);
      ast foo = make(Leq,make_int("0"),z3_simplify(diff));
      if(is_true(cond))
	cond = foo;
      else {
	linear_comb(cond,make_int(rational(1)),foo);
	cond = simplify_ineq(cond);
      }
    }
    return cond;
  }

  ast ineq_to_lhs(const ast &ineq){ 
    ast s = make(Leq,make_int(rational(0)),make_int(rational(0)));
    linear_comb(s,make_int(rational(1)),ineq);
    return simplify_ineq(s);
  }

  void eq_from_ineq(const ast &ineq, ast &lhs, ast &rhs){
    //    ast s = ineq_to_lhs(ineq);
    // ast srhs = arg(s,1);
    ast srhs = arg(ineq,0);
    if(op(srhs) == Plus && num_args(srhs) == 2 && arg(ineq,1) == make_int(rational(0))){
      lhs = arg(srhs,0);
      rhs = arg(srhs,1);
      // if(op(lhs) == Times)
      //   std::swap(lhs,rhs);
      if(op(rhs) == Times){
	rhs = arg(rhs,1);
	// if(op(ineq) == Leq)
	//  std::swap(lhs,rhs);
	return;
      }
    }
    if(op(ineq) == Leq || op(ineq) == Geq){
      lhs = srhs;
      rhs = arg(ineq,1);
      return;
    }
    throw "bad ineq";
  }

  ast chain_pos_add(int arg, const ast &chain){
    if(is_true(chain))
      return mk_true();
    ast last = rewrite_pos_add(arg,chain_last(chain));
    ast rest = chain_pos_add(arg,chain_rest(chain));
    return chain_cons(rest,last);
  }

  ast apply_rewrite_chain(const ast &t, const ast &chain){
    if(is_true(chain))
      return t;
    ast last = chain_last(chain);
    ast rest = chain_rest(chain);
    ast mid = apply_rewrite_chain(t,rest);
    ast res = subst_in_pos(mid,rewrite_pos(last),rewrite_rhs(last));
    return res;
  }

  ast drop_rewrites(LitType t, const ast &chain, ast &remainder){
    if(!is_true(chain)){
      ast last = chain_last(chain);
      ast rest = chain_rest(chain);
      if(is_rewrite_side(t,last)){
	ast res = drop_rewrites(t,rest,remainder);
	remainder = chain_cons(remainder,last);
	return res;
      }
    }
    remainder = mk_true();
    return chain;
  }

  // Normalization chains

  ast cons_normal(const ast &first, const ast &rest){
    return make(normal_chain,first,rest);
  }
  
  ast normal_first(const ast &t){
    return arg(t,0);
  }

  ast normal_rest(const ast &t){
    return arg(t,1);
  }

  ast normal_lhs(const ast &t){
    return arg(arg(t,0),0);
  }

  ast normal_rhs(const ast &t){
    return arg(arg(t,0),1);
  }

  ast normal_proof(const ast &t){
    return arg(t,1);
  }

  ast make_normal_step(const ast &lhs, const ast &rhs, const ast &proof){
    return make(normal_step,make_equiv(lhs,rhs),proof);
  }

  ast make_normal(const ast &ineq, const ast &nrml){
    if(!is_ineq(ineq))
      throw "what?";
    return make(normal,ineq,nrml);
  }

  ast fix_normal(const ast &lhs, const ast &rhs, const ast &proof){
    LitType lhst = get_term_type(lhs);
    LitType rhst = get_term_type(rhs);
    if(lhst == LitMixed && (rhst != LitMixed || ast_id(lhs) < ast_id(rhs)))
      return make_normal_step(lhs,rhs,proof);
    if(rhst == LitMixed && (lhst != LitMixed || ast_id(rhs) < ast_id(lhs)))
      return make_normal_step(rhs,lhs,reverse_chain(proof));
    throw "help!";
  }

  ast chain_side_proves(LitType side, const ast &chain){
    LitType other_side = side == LitA ? LitB : LitA;
    return my_and(chain_conditions(other_side,chain),my_implies(chain_conditions(side,chain),chain_formulas(side,chain)));
  }

  // Merge two normalization chains
  ast merge_normal_chains_rec(const ast &chain1, const ast &chain2, hash_map<ast,ast> &trans, ast &Aproves, ast &Bproves){
    if(is_true(chain1))
      return chain2;
    if(is_true(chain2))
      return chain1;
    ast f1 = normal_first(chain1);
    ast f2 = normal_first(chain2);
    ast lhs1 = normal_lhs(f1);
    ast lhs2 = normal_lhs(f2);
    int id1 = ast_id(lhs1);
    int id2 = ast_id(lhs2);
    if(id1 < id2)
      return cons_normal(f1,merge_normal_chains_rec(normal_rest(chain1),chain2,trans,Aproves,Bproves));
    if(id2 < id1)
      return cons_normal(f2,merge_normal_chains_rec(chain1,normal_rest(chain2),trans,Aproves,Bproves));
    ast rhs1 = normal_rhs(f1);
    ast rhs2 = normal_rhs(f2);
    LitType t1 = get_term_type(rhs1);
    LitType t2 = get_term_type(rhs2);
    int tid1 = ast_id(rhs1);
    int tid2 = ast_id(rhs2);
    ast pf1 = normal_proof(f1);
    ast pf2 = normal_proof(f2);
    ast new_normal;
    if(t1 == LitMixed && (t2 != LitMixed || tid2 > tid1)){
      ast new_proof = concat_rewrite_chain(reverse_chain(pf1),pf2);
      new_normal = f2;
      trans[rhs1] = make_normal_step(rhs1,rhs2,new_proof);
    }
    else if(t2 == LitMixed && (t1 != LitMixed || tid1 > tid2))
      return merge_normal_chains_rec(chain2,chain1,trans,Aproves,Bproves);
    else if(t1 == LitA && t2 == LitB){
      ast new_proof = concat_rewrite_chain(reverse_chain(pf1),pf2);
      ast Bproof, Aproof = drop_rewrites(LitB,new_proof,Bproof);
      ast mcA = chain_side_proves(LitB,Aproof);
      Bproves = my_and(Bproves,mcA);
      ast mcB = chain_side_proves(LitA,Bproof);
      Aproves = my_and(Aproves,mcB);
      ast rep = apply_rewrite_chain(rhs1,Aproof);
      new_proof = concat_rewrite_chain(pf1,Aproof);
      new_normal = make_normal_step(lhs1,rep,new_proof);
      ast A_normal = make_normal_step(rhs1,rep,Aproof);
      ast res = cons_normal(new_normal,merge_normal_chains_rec(normal_rest(chain1),normal_rest(chain2),trans,Aproves,Bproves));
      res = merge_normal_chains_rec(res,cons_normal(A_normal,make(True)),trans,Aproves,Bproves);
      return res;
    }
    else if(t1 == LitB && t2 == LitA)
      return merge_normal_chains_rec(chain2,chain1,trans,Aproves,Bproves);
    else if(t1 == LitA) {
      ast new_proof = concat_rewrite_chain(reverse_chain(pf1),pf2);
      ast mc = chain_side_proves(LitB,new_proof);
      Bproves = my_and(Bproves,mc);
      new_normal = f1; // choice is arbitrary
    }
    else { /* t1 = t2 = LitB */
      ast new_proof = concat_rewrite_chain(reverse_chain(pf1),pf2);
      ast mc = chain_side_proves(LitA,new_proof);
      Aproves = my_and(Aproves,mc);
      new_normal = f1; // choice is arbitrary
    }
    return cons_normal(new_normal,merge_normal_chains_rec(normal_rest(chain1),normal_rest(chain2),trans,Aproves,Bproves));
  }

  ast trans_normal_chain(const ast &chain, hash_map<ast,ast> &trans){
    if(is_true(chain))
      return chain;
    ast f = normal_first(chain);
    ast r = normal_rest(chain);
    r = trans_normal_chain(r,trans);
    ast rhs = normal_rhs(f);
    hash_map<ast,ast>::iterator it = trans.find(rhs);
    ast new_normal;
    if(it != trans.end() && get_term_type(normal_lhs(f)) == LitMixed){
      const ast &f2 = it->second;
      ast pf = concat_rewrite_chain(normal_proof(f),normal_proof(f2));
      new_normal = make_normal_step(normal_lhs(f),normal_rhs(f2),pf);
    }
    else
      new_normal = f;
    if(get_term_type(normal_lhs(f)) == LitMixed)
      trans[normal_lhs(f)] = new_normal;
    return cons_normal(new_normal,r);
  }

  ast merge_normal_chains(const ast &chain1, const ast &chain2, ast &Aproves, ast &Bproves){
    hash_map<ast,ast> trans;
    ast res = merge_normal_chains_rec(chain1,chain2,trans,Aproves,Bproves);
    res = trans_normal_chain(res,trans);
    return res;
  }
      
  bool destruct_cond_ineq(ast t, ast &Aproves, ast &Bproves, ast&ineq){
    if(op(t) == And){
      Aproves = arg(t,0);
      t = arg(t,1);
    }
    else
      Aproves = mk_true();
    if(op(t) == Implies){
      Bproves = arg(t,0);
      t = arg(t,1);
    }
    else
      Bproves = mk_true();
    if(is_normal_ineq(t)){
      ineq = t;
      return true;
    }
    return false;
  }

  ast cons_cond_ineq(const ast &Aproves, const ast &Bproves, const ast &ineq){
    return my_and(Aproves,my_implies(Bproves,ineq));
  }

  ast normalize(const ast &ct){
    ast Aproves,Bproves,t;
    if(!destruct_cond_ineq(ct,Aproves,Bproves,t))
      return ct;
    if(sym(t) != normal)
      return ct;
    ast chain = arg(t,1);
    hash_map<ast,ast> map;
    for(ast c = chain; !is_true(c); c = normal_rest(c)){
      ast first = normal_first(c);
      ast lhs = normal_lhs(first);
      ast rhs = normal_rhs(first);
      map[lhs] = rhs;
    }
    ast res = subst(map,arg(t,0));
    return cons_cond_ineq(Aproves,Bproves,res);
  }
  
  /** Make an assumption node. The given clause is assumed in the given frame. */
  virtual node make_assumption(int frame, const std::vector<ast> &assumption){
    if(!weak){
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
    else {
      if(pv->in_range(frame,rng)){
	return mk_false();
      }
      else {
	std::vector<ast> itp_clause;
	for(unsigned i = 0; i < assumption.size(); i++)
	  if(get_term_type(assumption[i]) != LitB)
	    itp_clause.push_back(assumption[i]);
	ast res = my_or(itp_clause);
	return mk_not(res);
      }
    }
  }

  ast make_local_rewrite(LitType t, const ast &p){
    ast rew = is_equivrel(p) ? p : make(Iff,mk_true(),p);
#if 0
    if(op(rew) == Iff && !is_true(arg(rew,0)))
      return diff_chain(t,top_pos,arg(rew,0),arg(rew,1), mk_true());
#endif
    return chain_cons(mk_true(),make_rewrite(t, top_pos, mk_true(), rew));
  }

  ast triv_interp(const symb &rule, const std::vector<ast> &premises, int mask_in){
    std::vector<ast> ps; ps.resize(premises.size());
    std::vector<ast> conjs;
    int mask = 0;
    for(unsigned i = 0; i < ps.size(); i++){
      ast p = premises[i];
      LitType t = get_term_type(p);
      switch(t){
      case LitA:
      case LitB:
	ps[i] = make_local_rewrite(t,p);
	break;
      default:
	ps[i] = get_placeholder(p); // can only prove consequent!
	if(mask_in & (1 << i))
	  mask |= (1 << conjs.size());
	conjs.push_back(p);
      }
    }
    ast ref = make(rule,ps);
    ast res = make_contra_node(ref,conjs,mask);
    return res;
  }

  ast triv_interp(const symb &rule, const ast &p0, const ast &p1, const ast &p2, int mask){
    std::vector<ast> ps; ps.resize(3);
    ps[0] = p0;
    ps[1] = p1;
    ps[2] = p2;
    return triv_interp(rule,ps,mask);
  }
  
  /** Make a modus-ponens node. This takes derivations of |- x
      and |- x = y and produces |- y */
  
  virtual node make_mp(const ast &p_eq_q, const ast &prem1, const ast &prem2){
    
    /* Interpolate the axiom p, p=q -> q */
    ast p = arg(p_eq_q,0);
    ast q = arg(p_eq_q,1);
    ast itp;
    if(get_term_type(p_eq_q) == LitMixed){
      int mask = 1 << 2;
      if(op(p) == Not && is_equivrel(arg(p,0)))
	mask |= 1; // we may need to run this rule backward if first premise is negative equality
      itp = triv_interp(modpon,p,p_eq_q,mk_not(q),mask);
    }
    else {
      if(get_term_type(p) == LitA){
	if(get_term_type(q) == LitA)
	  itp = mk_false();
	else {
	  if(get_term_type(p_eq_q) == LitA)
	    itp = q;
	  else
	    throw proof_error();
	}
      }
      else {
	if(get_term_type(q) == LitA){
	  if(get_term_type(make(Equal,p,q)) == LitA)
	    itp = mk_not(p);
	  else
	    throw proof_error();
      }
      else
	itp = mk_true();
      }
    }
    
    /* Resolve it with the premises */
    std::vector<ast> conc; conc.push_back(q); conc.push_back(mk_not(p_eq_q));
    itp = make_resolution(p,conc,itp,prem1);
    conc.pop_back();
    itp = make_resolution(p_eq_q,conc,itp,prem2);
    return itp;
  }

  ast capture_localization(ast e){
    // #define CAPTURE_LOCALIZATION
#ifdef CAPTURE_LOCALIZATION
    for(int i = localization_vars.size() - 1; i >= 0; i--){
      LocVar &lv = localization_vars[i];
      if(occurs_in(lv.var,e)){
	symb q = (pv->in_range(lv.frame,rng)) ? sexists : sforall; 
	e = make(q,make(Equal,lv.var,lv.term),e); // use Equal because it is polymorphic
      }
    }
#endif
    return e;
  }

  /** Make an axiom node. The conclusion must be an instance of an axiom. */
  virtual node make_axiom(const std::vector<ast> &conclusion, prover::range frng){
    int nargs = conclusion.size();
    std::vector<ast> largs(nargs);
    std::vector<ast> eqs;
    std::vector<ast> pfs;
    
    for(int i = 0; i < nargs; i++){
      ast argpf;
      ast lit = conclusion[i];
      largs[i] = localize_term(lit,frng,argpf);
      frng = pv->range_glb(frng,pv->ast_scope(largs[i]));
      if(largs[i] != lit){
	eqs.push_back(make_equiv(largs[i],lit));
	pfs.push_back(argpf);
      }
    }
    
    int frame = pv->range_max(frng);
    ast itp = make_assumption(frame,largs);
    
    for(unsigned i = 0; i < eqs.size(); i++)
      itp = make_mp(eqs[i],itp,pfs[i]);
    return capture_localization(itp);
  }

  virtual node make_axiom(const std::vector<ast> &conclusion){
    return make_axiom(conclusion,pv->range_full());
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
      case Geq: 
      case Leq: 
      case Gt: 
      case Lt: {
	ast zleqz = make(Leq,make_int("0"),make_int("0"));
	ast fark1 = make(sum,zleqz,make_int("1"),get_placeholder(P));
	ast fark2 = make(sum,fark1,make_int("1"),get_placeholder(mk_not(P)));
	ast res = make(And,make(contra,fark2,mk_false()),
		       make(contra,get_placeholder(mk_not(P)),P),
		       make(contra,get_placeholder(P),mk_not(P)));
	return res;
      }
      default: {
	ast em = make(exmid,P,get_placeholder(P),get_placeholder(mk_not(P)));
	ast res = make(And,make(contra,em,mk_false()),
		       make(contra,get_placeholder(mk_not(P)),P),
		       make(contra,get_placeholder(P),mk_not(P)));
	return res;
      }
      }
    }
  }

  /** Make a Reflexivity node. This rule produces |- x = x */
  
  virtual node make_reflexivity(ast con){
    if(get_term_type(con) == LitA)
      return mk_false();
    if(get_term_type(con) == LitB)
      return mk_true();
    ast itp = make(And,make(contra,no_proof,mk_false()),
		   make(contra,mk_true(),mk_not(con)));
    return itp;
  }
  
  /** Make a Symmetry node. This takes a derivation of |- x = y and
      produces | y = x. Ditto for ~(x=y) */

  virtual node make_symmetry(ast con, const ast &premcon, node prem){
#if 0
    ast x = arg(con,0);
    ast y = arg(con,1);
    ast p = make(op(con),y,x);
#endif
    if(get_term_type(con) != LitMixed)
      return prem; // symmetry shmymmetry...
    ast em = make(exmid,con,make(symm,get_placeholder(premcon)),get_placeholder(mk_not(con)));
    ast itp = make(And,make(contra,em,mk_false()),
		   make(contra,make(symm,get_placeholder(mk_not(con))),premcon),
		   make(contra,make(symm,get_placeholder(premcon)),mk_not(con)));
    
    std::vector<ast> conc; conc.push_back(con);
    itp = make_resolution(premcon,conc,itp,prem);
    return itp;
  }

  ast make_equiv_rel(const ast &x, const ast &y){
    if(is_bool_type(get_type(x)))
      return make(Iff,x,y);
    return make(Equal,x,y);
  }

  /** Make a transitivity node. This takes derivations of |- x = y
      and |- y = z produces | x = z */

  virtual node make_transitivity(const ast &x, const ast &y, const ast &z, node prem1, node prem2){

    /* Interpolate the axiom x=y,y=z,-> x=z */
    ast p = make_equiv_rel(x,y);
    ast q = make_equiv_rel(y,z);
    ast r = make_equiv_rel(x,z);
    ast equiv = make(Iff,p,r);
    ast itp;

    itp = make_congruence(q,equiv,prem2);
    itp = make_mp(equiv,prem1,itp);

    return itp;

  }
  
  /** Make a congruence node. This takes derivations of |- x_i = y_i
      and produces |- f(x_1,...,x_n) = f(y_1,...,y_n) */
  
  virtual node make_congruence(const ast &p, const ast &con, const ast &prem1){
    ast x = arg(p,0), y = arg(p,1);
    ast itp;
    LitType con_t = get_term_type(con);
    if(get_term_type(p) == LitA){
      if(con_t == LitA)
	itp = mk_false();
      else if(con_t == LitB)
	itp = p;
      else
	itp = make_mixed_congruence(x, y, p, con, prem1);
    }
    else {
      if(con_t == LitA)
	itp = mk_not(p);
      else{
	if(con_t == LitB)
	  itp = mk_true();
	else
	  itp = make_mixed_congruence(x, y, p, con, prem1);
      }
    }
    std::vector<ast> conc; conc.push_back(con);
    itp = make_resolution(p,conc,itp,prem1);
    return itp;
  }

  int find_congruence_position(const ast &p, const ast &con){
      // find the argument position of x and y
    const ast &x = arg(p,0);
    const ast &y = arg(p,1);
    int nargs = num_args(arg(con,0));
    for(int i = 0; i < nargs; i++)
      if(x == arg(arg(con,0),i) && y == arg(arg(con,1),i))
	return i;
    throw proof_error();
  }

  /** Make a congruence node. This takes derivations of |- x_i1 = y_i1, |- x_i2 = y_i2,...
      and produces |- f(...x_i1...x_i2...) = f(...y_i1...y_i2...) */
  
  node make_congruence(const std::vector<ast> &p, const ast &con, const std::vector<ast> &prems){
    if(p.size() == 0)
      throw proof_error();
    if(p.size() == 1)
      return make_congruence(p[0],con,prems[0]);
    ast thing = con;
    ast res = mk_true();
    for(unsigned i = 0; i < p.size(); i++){
      int pos = find_congruence_position(p[i],thing);
      ast next = subst_in_arg_pos(pos,arg(p[i],1),arg(thing,0));
      ast goal = make(op(thing),arg(thing,0),next);
      ast equa = make_congruence(p[i],goal,prems[i]);
      if(i == 0)
	res = equa;
      else {
	ast trace = make(op(con),arg(con,0),arg(thing,0));
	ast equiv = make(Iff,trace,make(op(trace),arg(trace,0),next));
	ast foo = make_congruence(goal,equiv,equa);
	res = make_mp(equiv,res,foo);
      }
      thing = make(op(thing),next,arg(thing,1));
    }
    return res;
  }

  /* Interpolate a mixed congruence axiom. */

  virtual ast make_mixed_congruence(const ast &x, const ast &y, const ast &p, const ast &con, const ast &prem1){
    ast foo = p;
    std::vector<ast> conjs;
    LitType t = get_term_type(foo);
    switch(t){
    case LitA:
    case LitB:
      foo = make_local_rewrite(t,foo);
      break;
    case LitMixed:
      conjs.push_back(foo);
      foo = get_placeholder(foo);
    }
    // find the argument position of x and y
    int pos = -1;
    int nargs = num_args(arg(con,0));
    for(int i = 0; i < nargs; i++)
      if(x == arg(arg(con,0),i) && y == arg(arg(con,1),i))
	pos = i;
    if(pos == -1)
      throw proof_error();
    ast bar = make(cong,foo,make_int(rational(pos)),get_placeholder(mk_not(con)));
    conjs.push_back(mk_not(con));
    return make_contra_node(bar,conjs);
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
    std::vector<ast> conjs;
    ast thing = make(Leq,zero,zero);
    for(unsigned i = 0; i < prem_cons.size(); i++){
      const ast &lit = prem_cons[i];
      if(get_term_type(lit) == LitA)
	// Farkas rule seems to assume strict integer inequalities are rounded
	linear_comb(thing,coeffs[i],lit,true /*round_off*/);
    }
    thing = simplify_ineq(thing);
    for(unsigned i = 0; i < prem_cons.size(); i++){
      const ast &lit = prem_cons[i];
      if(get_term_type(lit) == LitMixed){
	thing = make(sum,thing,coeffs[i],get_placeholder(lit));
	conjs.push_back(lit);
      }
    }
    thing = make_contra_node(thing,conjs);

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

  void linear_comb(ast &P, const ast &c, const ast &Q, bool round_off = false){
    ast Qrhs;
    bool qstrict = false;
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
	qstrict = true;
	break;
      case Leq: 
	Qrhs = make(Sub,arg(nQ,0),arg(nQ,1));
	qstrict = true;
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
	qstrict = true;
	break;
      case Gt: 
	Qrhs = make(Sub,arg(Q,0),arg(Q,1));
	qstrict = true;
	break;
      default:
	throw proof_error();
      }
    }
#if 0
    bool pstrict = op(P) == Lt, strict = pstrict || qstrict;
    if(pstrict && qstrict && round_off)
      Qrhs = make(Sub,Qrhs,make_int(rational(1)));
#else
    bool pstrict = op(P) == Lt;
    if(qstrict && round_off && (pstrict || !(c == make_int(rational(1))))){
      Qrhs = make(Sub,Qrhs,make_int(rational(1)));
      qstrict = false;
    }
    Qrhs = make(Times,c,Qrhs);
    bool strict = pstrict || qstrict;
#endif
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
      if(get_term_type(x) == LitMixed || get_term_type(y) == LitMixed){
	if(y == make_int(rational(0)) && op(x) == Plus && num_args(x) == 2){
	  // std::cerr << "WARNING: untested case in leq2eq\n";
	}
	else {
	  // std::cerr << "WARNING: mixed term in leq2eq\n"; 
	  std::vector<ast> lits;
	  lits.push_back(con);
	  lits.push_back(make(Not,xleqy));
	  lits.push_back(make(Not,yleqx));
	  return make_axiom(lits);
	}
      }
      std::vector<ast> conjs; conjs.resize(3);
      conjs[0] = mk_not(con);
      conjs[1] = xleqy;
      conjs[2] = yleqx;
      itp = make_contra_node(make(leq2eq,
			     get_placeholder(mk_not(con)),
			     get_placeholder(xleqy),
			     get_placeholder(yleqx)),
			     conjs,1);
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
      std::vector<ast> conjs; conjs.resize(2);
      conjs[0] = make(Equal,x,y);
      conjs[1] = mk_not(xleqy);
      itp = make(eq2leq,get_placeholder(conjs[0]),get_placeholder(conjs[1]));
      itp = make_contra_node(itp,conjs,2);
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
      std::vector<ast> conjs; conjs.resize(2);
      conjs[0] = tleqc;
      conjs[1] = mk_not(con);
      itp = make(sum,get_placeholder(conjs[0]),d,get_placeholder(conjs[1]));
      itp = make_contra_node(itp,conjs);
    }
    }
    std::vector<ast> conc; conc.push_back(con);
    itp = make_resolution(tleqc,conc,itp,prem);
    return itp;
  }


  
  // create a fresh variable for localization
  ast fresh_localization_var(const ast &term, int frame){
    std::ostringstream s;
    s << "%" << (localization_vars.size());
    ast var = make_var(s.str().c_str(),get_type(term));
    pv->sym_range(sym(var)) = pv->range_full(); // make this variable global
    localization_vars.push_back(LocVar(var,term,frame));
    return var;
  }
  
  struct LocVar {                           // localization vars
    ast var;                                // a fresh variable
    ast term;                               // term it represents
    int frame;                              // frame in which it's defined
    LocVar(ast v, ast t, int f){var=v;term=t;frame=f;}
  };

  std::vector<LocVar> localization_vars;         // localization vars in order of creation

  struct locmaps {
    hash_map<ast,ast> localization_map;            // maps terms to their localization vars
    hash_map<ast,ast> localization_pf_map;         // maps terms to proofs of their localizations
  };
  
  hash_map<prover::range,locmaps> localization_maps_per_range;

  /* "localize" a term e to a given frame range, creating new symbols to
     represent non-local subterms. This returns the localized version e_l,
     as well as a proof thet e_l = l. 
  */

  ast make_refl(const ast &e){
    if(get_term_type(e) == LitA)
      return mk_false();
    return mk_true(); // TODO: is this right?
  }


  ast make_equiv(const ast &x, const ast &y){
    if(get_type(x) == bool_type())
      return make(Iff,x,y);
    else
      return make(Equal,x,y);
  }

  bool range_is_global(const prover::range &r){
    if(pv->range_contained(r,rng))
      return false;
    if(!pv->ranges_intersect(r,rng))
      return false;
    return true;
  }

  ast localize_term(ast e, const prover::range &rng, ast &pf){

    // we need to memoize this function separately for A, B and global
    prover::range map_range = rng;
    if(range_is_global(map_range))
      map_range = pv->range_full();
    locmaps &maps = localization_maps_per_range[map_range];
    hash_map<ast,ast> &localization_map = maps.localization_map;
    hash_map<ast,ast> &localization_pf_map = maps.localization_pf_map;

    ast orig_e = e;
    pf = make_refl(e);  // proof that e = e

    // prover::range erng = 
    pv->ast_scope(e);
#if 0
    if(!(erng.lo > erng.hi) && pv->ranges_intersect(pv->ast_scope(e),rng)){
      return e; // this term occurs in range, so it's O.K.
    }
#endif

    hash_map<ast,ast>::iterator it = localization_map.find(e);

    if(it != localization_map.end() && is_bool_type(get_type(e)) 
       && !pv->ranges_intersect(pv->ast_scope(it->second),rng))
      it = localization_map.end();  // prevent quantifiers over booleans

    if(it != localization_map.end()){
      pf = localization_pf_map[e];
      e = it->second;
    }

    else {
      // if it is non-local, we must first localize the arguments to
      // the range of its function symbol
      
      int nargs = num_args(e);
      if(nargs > 0 /*  && (!is_local(e) || flo <= hi || fhi >= lo) */){
	prover::range frng = rng;
	opr o = op(e);
	if(o == Uninterpreted){
	  symb f = sym(e);
	  prover::range srng = pv->sym_range(f);
	  if(pv->ranges_intersect(srng,rng)) // localize to desired range if possible
	    frng = pv->range_glb(srng,rng);
	  else
	    frng = srng; // this term will be localized
	}
	else if(o == Plus || o == Times){ // don't want bound variables inside arith ops
	  // std::cout << "WARNING: non-local arithmetic\n";
	  //	  frng = erng; // this term will be localized
	}
	else if(o == Select){ // treat the array term like a function symbol
	  prover::range srng = pv->ast_scope(arg(e,0)); 
	  if(!(srng.lo > srng.hi) &&  pv->ranges_intersect(srng,rng)) // localize to desired range if possible
	    frng = pv->range_glb(srng,rng);
	  else
	    frng = srng; // this term will be localized
	}
	std::vector<ast> largs(nargs);
	std::vector<ast> eqs;
	std::vector<ast> pfs;
	for(int i = 0; i < nargs; i++){
	  ast argpf;
	  largs[i] = localize_term(arg(e,i),frng,argpf);
	  frng = pv->range_glb(frng,pv->ast_scope(largs[i]));
	  if(largs[i] != arg(e,i)){
	    eqs.push_back(make_equiv(largs[i],arg(e,i)));
	    pfs.push_back(argpf);
	  }
	}
	
	e = clone(e,largs);
	if(pfs.size())
	  pf = make_congruence(eqs,make_equiv(e,orig_e),pfs);
	// assert(is_local(e));
      }
      
      localization_pf_map[orig_e] = pf;
      localization_map[orig_e] = e;
    }

    if(pv->ranges_intersect(pv->ast_scope(e),rng))
      return e; // this term occurs in range, so it's O.K.

    if(is_array_type(get_type(e)))
      std::cerr << "WARNING: array quantifier\n";

    // choose a frame for the constraint that is close to range
    int frame = pv->range_near(pv->ast_scope(e),rng);

    ast new_var = fresh_localization_var(e,frame);
    localization_map[orig_e] = new_var;
    std::vector<ast> foo; foo.push_back(make_equiv(new_var,e));
    ast bar = make_assumption(frame,foo);
    pf = make_transitivity(new_var,e,orig_e,bar,pf);
    localization_pf_map[orig_e] = pf;

    // HACK: try to bias this term in the future
    if(!pv->range_is_full(rng)){
      prover::range rf = pv->range_full();
      locmaps &fmaps = localization_maps_per_range[rf];
      hash_map<ast,ast> &flocalization_map = fmaps.localization_map;
      hash_map<ast,ast> &flocalization_pf_map = fmaps.localization_pf_map;
      // if(flocalization_map.find(orig_e) == flocalization_map.end())
	{
	  flocalization_map[orig_e] = new_var;
	  flocalization_pf_map[orig_e] = pf;
	}
    }
      
    
    return new_var;
  }

  ast delete_quant(hash_map<ast,ast> &memo, const ast &v, const ast &e){
    std::pair<ast,ast> foo(e,ast());
    std::pair<hash_map<ast,ast>::iterator,bool> bar = memo.insert(foo);
    ast &res = bar.first->second;
    if(bar.second){
      opr o = op(e);
      switch(o){
      case Or:
      case And:
      case Implies: {
	unsigned nargs = num_args(e);
	std::vector<ast> args; args.resize(nargs);
	for(unsigned i = 0; i < nargs; i++)
	  args[i] = delete_quant(memo, v, arg(e,i));
	res = make(o,args);
	break;
      }
      case Uninterpreted: {
	symb s = sym(e);
	ast w = arg(arg(e,0),0);
	if(s == sforall || s == sexists){
	  res = delete_quant(memo,v,arg(e,1));
	  if(w != v)
	    res = make(s,w,res);
	  break;
	}
      }
      default:
	res = e;
      }
    }
    return res;
  }

  ast insert_quants(hash_map<ast,ast> &memo, const ast &e){
    std::pair<ast,ast> foo(e,ast());
    std::pair<hash_map<ast,ast>::iterator,bool> bar = memo.insert(foo);
    ast &res = bar.first->second;
    if(bar.second){
      opr o = op(e);
      switch(o){
      case Or:
      case And:
      case Implies: {
	unsigned nargs = num_args(e);
	std::vector<ast> args; args.resize(nargs);
	for(unsigned i = 0; i < nargs; i++)
	  args[i] = insert_quants(memo, arg(e,i));
	res = make(o,args);
	break;
      }
      case Uninterpreted: {
	symb s = sym(e);
	if(s == sforall || s == sexists){
	  opr q = (s == sforall) ? Forall : Exists;
	  ast v = arg(arg(e,0),0);
	  hash_map<ast,ast> dmemo;
	  ast body = delete_quant(dmemo,v,arg(e,1));
	  body = insert_quants(memo,body);
	  res = apply_quant(q,v,body);
	  break;
	}
      }
      default:
	res = e;
      }
    }
    return res;
  }

  ast add_quants(ast e){
#ifdef CAPTURE_LOCALIZATION
    if(!localization_vars.empty()){
      hash_map<ast,ast> memo;
      e = insert_quants(memo,e);
    }
#else
    for(int i = localization_vars.size() - 1; i >= 0; i--){
      LocVar &lv = localization_vars[i];
      opr quantifier = (pv->in_range(lv.frame,rng)) ? Exists : Forall; 
      e = apply_quant(quantifier,lv.var,e);
    }
#endif
    return e;
  }

  node make_resolution(ast pivot, node premise1, node premise2) {
    std::vector<ast> lits;
    return make_resolution(pivot,lits,premise1,premise2);
  }  

  /* Return an interpolant from a proof of false */
  ast interpolate(const node &pf){
    // proof of false must be a formula, with quantified symbols
#ifndef BOGUS_QUANTS
    return add_quants(z3_simplify(pf));
#else
    return z3_simplify(pf);
#endif
  }

  ast resolve_with_quantifier(const ast &pivot1, const ast &conj1,
			      const ast &pivot2, const ast &conj2){
   if(is_not(arg(pivot1,1)))
      return resolve_with_quantifier(pivot2,conj2,pivot1,conj1);
    ast eqpf;
    ast P = arg(pivot1,1);
    ast Ploc = localize_term(P, rng, eqpf);
    ast pPloc = make_hypothesis(Ploc);
    ast pP = make_mp(make(Iff,Ploc,P),pPloc,eqpf);
    ast rP = make_resolution(P,conj1,pP);
    ast nP = mk_not(P);
    ast nPloc = mk_not(Ploc);
    ast neqpf = make_congruence(make(Iff,Ploc,P),make(Iff,nPloc,nP),eqpf);
    ast npPloc = make_hypothesis(nPloc);
    ast npP = make_mp(make(Iff,nPloc,nP),npPloc,neqpf);
    ast nrP = make_resolution(nP,conj2,npP);
    ast res = make_resolution(Ploc,rP,nrP);
    return capture_localization(res);
  }

  ast get_contra_coeff(const ast &f){
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
  
  ast my_implies(const ast &a, const ast &b){
    return mk_implies(a,b);
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

  bool is_placeholder(const ast &e){
    if(op(e) == Uninterpreted){
      std::string name = string_of_symbol(sym(e));
      if(name.size() > 2 && name[0] == '@' && name[1] == 'p')
	return true;
    }
    return false;
  }

public:
  iz3proof_itp_impl(prover *p, const prover::range &r, bool w)
    : iz3proof_itp(*p)
  {
    pv = p;
    rng = r;
    weak = false ; //w;
    type boolintbooldom[3] = {bool_type(),int_type(),bool_type()};
    type booldom[1] = {bool_type()};
    type boolbooldom[2] = {bool_type(),bool_type()};
    type boolboolbooldom[3] = {bool_type(),bool_type(),bool_type()};
    type intbooldom[2] = {int_type(),bool_type()};
    contra = function("@contra",2,boolbooldom,bool_type());
    m().inc_ref(contra);
    sum = function("@sum",3,boolintbooldom,bool_type());
    m().inc_ref(sum);
    rotate_sum = function("@rotsum",2,boolbooldom,bool_type());
    m().inc_ref(rotate_sum);
    leq2eq = function("@leq2eq",3,boolboolbooldom,bool_type());
    m().inc_ref(leq2eq);
    eq2leq = function("@eq2leq",2,boolbooldom,bool_type());
    m().inc_ref(eq2leq);
    cong = function("@cong",3,boolintbooldom,bool_type());
    m().inc_ref(cong);
    exmid = function("@exmid",3,boolboolbooldom,bool_type());
    m().inc_ref(exmid);
    symm = function("@symm",1,booldom,bool_type());
    m().inc_ref(symm);
    epsilon = make_var("@eps",int_type());
    modpon = function("@mp",3,boolboolbooldom,bool_type());
    m().inc_ref(modpon);
    no_proof = make_var("@nop",bool_type());
    concat = function("@concat",2,boolbooldom,bool_type());
    m().inc_ref(concat);
    top_pos = make_var("@top_pos",bool_type());
    add_pos = function("@add_pos",2,intbooldom,bool_type());
    m().inc_ref(add_pos);
    rewrite_A = function("@rewrite_A",3,boolboolbooldom,bool_type());
    m().inc_ref(rewrite_A);
    rewrite_B = function("@rewrite_B",3,boolboolbooldom,bool_type());
    m().inc_ref(rewrite_B);
    normal_step = function("@normal_step",2,boolbooldom,bool_type());
    m().inc_ref(normal_step);
    normal_chain = function("@normal_chain",2,boolbooldom,bool_type());
    m().inc_ref(normal_chain);
    normal = function("@normal",2,boolbooldom,bool_type());
    m().inc_ref(normal);
    sforall = function("@sforall",2,boolbooldom,bool_type());
    m().inc_ref(sforall);
    sexists = function("@sexists",2,boolbooldom,bool_type());
    m().inc_ref(sexists);
  }

  ~iz3proof_itp_impl(){
    m().dec_ref(contra);
    m().dec_ref(sum);
    m().dec_ref(rotate_sum);
    m().dec_ref(leq2eq);
    m().dec_ref(eq2leq);
    m().dec_ref(cong);
    m().dec_ref(exmid);
    m().dec_ref(symm);
    m().dec_ref(modpon);
    m().dec_ref(concat);
    m().dec_ref(add_pos);
    m().dec_ref(rewrite_A);
    m().dec_ref(rewrite_B);
    m().dec_ref(normal_step);
    m().dec_ref(normal_chain);
    m().dec_ref(normal);
    m().dec_ref(sforall);
    m().dec_ref(sexists);
  }
};

iz3proof_itp *iz3proof_itp::create(prover *p, const prover::range &r, bool w){
  return new iz3proof_itp_impl(p,r,w);
}

