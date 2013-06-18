/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    duality_rpfp.h

Abstract:

   implements relational post-fixedpoint problem
   (RPFP) data structure.

Author:

    Ken McMillan (kenmcmil)

Revision History:


--*/



#include "duality.h"
#include "duality_profiling.h"
#include <algorithm>
#include <fstream>

#ifndef WIN32
// #define Z3OPS
#endif

// TODO: do we need these?
#ifdef Z3OPS

class Z3_subterm_truth {
 public:
  virtual bool eval(Z3_ast f) = 0;
  ~Z3_subterm_truth(){}
};

Z3_subterm_truth *Z3_mk_subterm_truth(Z3_context ctx, Z3_model model);

#endif

#include <stdio.h>

// TODO: use something official for this
int debug_gauss = 0;

namespace Duality {

  static char string_of_int_buffer[20];

  const char *Z3User::string_of_int(int n){
    sprintf(string_of_int_buffer,"%d",n);
    return string_of_int_buffer;
  }

  RPFP::Term RPFP::SuffixVariable(const Term &t, int n)
  {
    std::string name = t.decl().name().str() + "_" + string_of_int(n);
    return ctx.constant(name.c_str(), t.get_sort());
  }

  RPFP::Term RPFP::HideVariable(const Term &t, int n)
  {
    std::string name = std::string("@p_") + t.decl().name().str() + "_" + string_of_int(n);
    return ctx.constant(name.c_str(), t.get_sort());
  }

  void RPFP::RedVars(Node *node, Term &b, std::vector<Term> &v)
  {
    int idx = node->number;
    if(HornClauses)
      b = ctx.bool_val(true);
    else {
      std::string name = std::string("@b_") + string_of_int(idx);
      symbol sym = ctx.str_symbol(name.c_str());
      b = ctx.constant(sym,ctx.bool_sort());
    }
    // ctx.constant(name.c_str(), ctx.bool_sort());
    v = node->Annotation.IndParams;
    for(unsigned i = 0; i < v.size(); i++)
      v[i] = SuffixVariable(v[i],idx);
  }

  void Z3User::SummarizeRec(hash_set<ast> &memo, std::vector<expr> &lits, int &ops, const Term &t){
    if(memo.find(t) != memo.end())
      return;
    memo.insert(t);
    decl_kind k = t.decl().get_decl_kind();
    if(k == And || k == Or || k == Not || k == Implies || k == Iff){
      ops++;
      int nargs = t.num_args();
      for(int i = 0; i < nargs; i++)
	SummarizeRec(memo,lits,ops,t.arg(i));
    }
    else
      lits.push_back(t);
  }

  int Z3User::CumulativeDecisions(){
#if 0
    std::string stats = Z3_statistics_to_string(ctx);
    int pos = stats.find("decisions:");
    pos += 10;
    int end = stats.find('\n',pos);
    std::string val = stats.substr(pos,end-pos);
    return atoi(val.c_str());
#endif
    return slvr.get_num_decisions();
  }


  void Z3User::Summarize(const Term &t){
    hash_set<ast> memo; std::vector<expr> lits; int ops = 0;
    SummarizeRec(memo, lits, ops, t);
    std::cout << ops << ": ";
    for(unsigned i = 0; i < lits.size(); i++){
      if(i > 0) std::cout << ", ";
      std::cout << lits[i];
    }
  }

  Z3User::Term Z3User::conjoin(const std::vector<Term> &args){
    return ctx.make(And,args);
  }
  
  Z3User::Term Z3User::sum(const std::vector<Term> &args){
    return ctx.make(Plus,args);
  }

  RPFP::Term RPFP::RedDualRela(Edge *e, std::vector<Term> &args, int idx){
    Node *child = e->Children[idx];
    Term b(ctx);
    std::vector<Term> v;
    RedVars(child, b, v);
    for (unsigned i = 0; i < args.size(); i++)
      {
	if (eq(args[i].get_sort(),ctx.bool_sort()))
	  args[i] = ctx.make(Iff,args[i], v[i]);
	else
	  args[i] = args[i] == v[i];
      }
    return args.size() > 0 ? (b && conjoin(args)) : b;
  }

  Z3User::Term Z3User::CloneQuantifier(const Term &t, const Term &new_body){
#if 0
    Z3_context c = ctx;
    Z3_ast a = t;
    std::vector<Z3_pattern> pats;
    int num_pats = Z3_get_quantifier_num_patterns(c,a);
    for(int i = 0; i < num_pats; i++)
      pats.push_back(Z3_get_quantifier_pattern_ast(c,a,i));
    std::vector<Z3_ast> no_pats;
    int num_no_pats = Z3_get_quantifier_num_patterns(c,a);
    for(int i = 0; i < num_no_pats; i++)
      no_pats.push_back(Z3_get_quantifier_no_pattern_ast(c,a,i));
    int bound = Z3_get_quantifier_num_bound(c,a);
    std::vector<Z3_sort> sorts;
    std::vector<Z3_symbol> names;
    for(int i = 0; i < bound; i++){
      sorts.push_back(Z3_get_quantifier_bound_sort(c,a,i));
      names.push_back(Z3_get_quantifier_bound_name(c,a,i));
    }
    Z3_ast foo = Z3_mk_quantifier_ex(c,
				     Z3_is_quantifier_forall(c,a),
				     Z3_get_quantifier_weight(c,a),
				     0,
				     0,
				     num_pats,
				     &pats[0],
				     num_no_pats,
				     &no_pats[0],
				     bound,
				     &sorts[0],
				     &names[0],
				     new_body);
    return expr(ctx,foo);
#endif
    return clone_quantifier(t,new_body);
  }

  RPFP::Term RPFP::LocalizeRec(Edge *e,  hash_map<ast,Term> &memo, const Term &t)
  {
    std::pair<ast,Term> foo(t,expr(ctx));
    std::pair<hash_map<ast,Term>::iterator, bool> bar = memo.insert(foo);
    Term &res = bar.first->second;
    if(!bar.second) return res;
    hash_map<ast,Term>::iterator it = e->varMap.find(t);
    if (it != e->varMap.end()){
      res = it->second;
      return res;
    }
    if (t.is_app())
      {
	func_decl f = t.decl();
	std::vector<Term> args;
	int nargs = t.num_args();
	for(int i = 0; i < nargs; i++)
	  args.push_back(LocalizeRec(e, memo, t.arg(i)));
	hash_map<func_decl,int>::iterator rit = e->relMap.find(f);                 
	if(rit != e->relMap.end())
	  res = RedDualRela(e,args,(rit->second));
	else {
	  if (args.size() == 0 && f.get_decl_kind() == Uninterpreted && !ls->is_constant(f))
	    {
	      res = HideVariable(t,e->number);
	    }
	  else
	    {
	      res = f(args.size(),&args[0]);
	    }
	}
      }
    else if (t.is_quantifier())
      {
	std::vector<expr> pats;
	t.get_patterns(pats);
	for(unsigned i = 0; i < pats.size(); i++)
	  pats[i] = LocalizeRec(e,memo,pats[i]);
	Term body = LocalizeRec(e,memo,t.body());
	res = clone_quantifier(t, body, pats);
      }
    else res = t;
    return res;
  }

  void RPFP::SetEdgeMaps(Edge *e){
    timer_start("SetEdgeMaps");
    e->relMap.clear();
    e->varMap.clear();
    for(unsigned i = 0; i < e->F.RelParams.size(); i++){
      e->relMap[e->F.RelParams[i]] = i;
    }
    Term b(ctx);
    std::vector<Term> v;
    RedVars(e->Parent, b, v);
    for(unsigned i = 0; i < e->F.IndParams.size(); i++){
      // func_decl parentParam = e->Parent.Annotation.IndParams[i];
      expr oldname = e->F.IndParams[i];
      expr newname = v[i];
      e->varMap[oldname] = newname;
    }
    timer_stop("SetEdgeMaps");

  }


  RPFP::Term RPFP::Localize(Edge *e, const Term &t){
    timer_start("Localize");
    hash_map<ast,Term> memo;
    if(e->F.IndParams.size() > 0 && e->varMap.empty())
      SetEdgeMaps(e); // TODO: why is this needed?
    Term res = LocalizeRec(e,memo,t);
    timer_stop("Localize");
    return res;
  }


  RPFP::Term RPFP::ReducedDualEdge(Edge *e)
  {
    SetEdgeMaps(e);
    timer_start("RedVars");
    Term b(ctx);
    std::vector<Term> v;
    RedVars(e->Parent, b, v);
    timer_stop("RedVars");
    // ast_to_track = (ast)b;
    return implies(b, Localize(e, e->F.Formula));
  }

  TermTree *RPFP::ToTermTree(Node *root)
  {
    Edge *e = root->Outgoing;
    if(!e) return new TermTree(ctx.bool_val(true), std::vector<TermTree *>());
    std::vector<TermTree *> children(e->Children.size());
    for(unsigned i = 0; i < children.size(); i++)
      children[i] = ToTermTree(e->Children[i]);
    // Term top = ReducedDualEdge(e);
    Term top = e->dual.null() ? ctx.bool_val(true) : e->dual;
    return new TermTree(top, children);
  }

  TermTree *RPFP::GetGoalTree(Node *root){
     std::vector<TermTree *> children(1);
     children[0] = ToGoalTree(root);
     return new TermTree(ctx.bool_val(false),children);
  }

  TermTree *RPFP::ToGoalTree(Node *root)
  {
    Term b(ctx);
    std::vector<Term> v;
    RedVars(root, b, v);
    Term goal = root->Name(v);
    Edge *e = root->Outgoing;
    if(!e) return new TermTree(goal, std::vector<TermTree *>());
    std::vector<TermTree *> children(e->Children.size());
    for(unsigned i = 0; i < children.size(); i++)
      children[i] = ToGoalTree(e->Children[i]);
    // Term top = ReducedDualEdge(e);
    return new TermTree(goal, children);
  }

  Z3User::Term Z3User::SubstRec(hash_map<ast, Term> &memo, const Term &t)
  {
    std::pair<ast,Term> foo(t,expr(ctx));
    std::pair<hash_map<ast,Term>::iterator, bool> bar = memo.insert(foo);
    Term &res = bar.first->second;
    if(!bar.second) return res;
    if (t.is_app())
      {
	func_decl f = t.decl();
	std::vector<Term> args;
	int nargs = t.num_args();
	for(int i = 0; i < nargs; i++)
	  args.push_back(SubstRec(memo, t.arg(i)));
	res = f(args.size(),&args[0]);
      }
    else if (t.is_quantifier())
      res = CloneQuantifier(t,SubstRec(memo, t.body()));
    else res = t;
    return res;
  }

  Z3User::Term Z3User::SubstRecHide(hash_map<ast, Term> &memo, const Term &t, int number)
  {
    std::pair<ast,Term> foo(t,expr(ctx));
    std::pair<hash_map<ast,Term>::iterator, bool> bar = memo.insert(foo);
    Term &res = bar.first->second;
    if(!bar.second) return res;
    if (t.is_app())
      {
	func_decl f = t.decl();
	std::vector<Term> args;
	int nargs = t.num_args();
	if (nargs == 0 && f.get_decl_kind() == Uninterpreted){
	  std::string name = std::string("@q_") + t.decl().name().str() + "_" + string_of_int(number);
	  res = ctx.constant(name.c_str(), t.get_sort());
	  return res;
	}
	for(int i = 0; i < nargs; i++)
	  args.push_back(SubstRec(memo, t.arg(i)));
	res = f(args.size(),&args[0]);
      }
    else if (t.is_quantifier())
      res = CloneQuantifier(t,SubstRec(memo, t.body()));
    else res = t;
    return res;
  }

  RPFP::Term RPFP::SubstParams(const std::vector<Term> &from,
			       const std::vector<Term> &to, const Term &t){
    hash_map<ast, Term> memo;
    bool some_diff = false;
    for(unsigned i = 0; i < from.size(); i++)
      if(i < to.size() && !eq(from[i],to[i])){
	memo[from[i]] = to[i];
	some_diff = true;
      }
    return some_diff ? SubstRec(memo,t) : t;
  }


  void Z3User::Strengthen(Term &x, const Term &y)
  {
    if (eq(x,ctx.bool_val(true)))
      x = y;
    else
      x = x && y;
  }

  void RPFP::DecodeTree(Node *root, TermTree *interp, int persist)
  {
    std::vector<TermTree *> &ic = interp->getChildren();
    if (ic.size() > 0)
      {
	std::vector<Node *> &nc = root->Outgoing->Children;
	for (unsigned i = 0; i < nc.size(); i++)
	  DecodeTree(nc[i], ic[i], persist);
      }
    hash_map<ast, Term> memo;
    Term b;
    std::vector<Term> v;
    RedVars(root, b, v);
    memo[b] = ctx.bool_val(true);
    for (unsigned i = 0; i < v.size(); i++)
      memo[v[i]] = root->Annotation.IndParams[i];
    Term annot = SubstRec(memo, interp->getTerm());
    // Strengthen(ref root.Annotation.Formula, annot);
    root->Annotation.Formula = annot;
#if 0
    if(persist != 0)
      Z3_persist_ast(ctx,root->Annotation.Formula,persist);
#endif
  }
  
  RPFP::Term RPFP::GetUpperBound(Node *n)
  {
    // TODO: cache this
    Term b(ctx); std::vector<Term> v;
    RedVars(n, b, v);
    hash_map<ast, Term> memo;
    for (unsigned int i = 0; i < v.size(); i++)
      memo[n->Bound.IndParams[i]] = v[i];
    Term cnst = SubstRec(memo, n->Bound.Formula);
    return b && !cnst;
  }

  RPFP::Term RPFP::GetAnnotation(Node *n)
  {
    if(eq(n->Annotation.Formula,ctx.bool_val(true)))
      return n->Annotation.Formula;
    // TODO: cache this
    Term b(ctx); std::vector<Term> v;
    RedVars(n, b, v);
    hash_map<ast, Term> memo;
    for (unsigned i = 0; i < v.size(); i++)
      memo[n->Annotation.IndParams[i]] = v[i];
    Term cnst = SubstRec(memo, n->Annotation.Formula);
    return !b || cnst;
  }

  RPFP::Term RPFP::GetUnderapprox(Node *n)
  {
    // TODO: cache this
    Term b(ctx); std::vector<Term> v;
    RedVars(n, b, v);
    hash_map<ast, Term> memo;
    for (unsigned i = 0; i < v.size(); i++)
      memo[n->Underapprox.IndParams[i]] = v[i];
    Term cnst = SubstRecHide(memo, n->Underapprox.Formula, n->number);
    return !b || cnst;
  }

  TermTree *RPFP::AddUpperBound(Node *root, TermTree *t)
  {
    Term f = !((ast)(root->dual)) ? ctx.bool_val(true) : root->dual;
    std::vector<TermTree *> c(1); c[0] = t;
    return new TermTree(f, c);
  }

#if 0
  void RPFP::WriteInterps(System.IO.StreamWriter f, TermTree t)
  {
    foreach (var c in t.getChildren())
      WriteInterps(f, c);
    f.WriteLine(t.getTerm());
  }
#endif    


  /** For incremental solving, asserts the constraint associated
   * with this edge in the SMT context. If this edge is removed,
   * you must pop the context accordingly. The second argument is
   * the number of pushes we are inside. The constraint formula
   * will survive "persist" pops of the context. If you plan
   * to reassert the edge after popping the context once,
   * you can save time re-constructing the formula by setting
   * "persist" to one. If you set "persist" too high, however,
   * you could have a memory leak.
   *
   * The flag "with children" causes the annotations of the children
   * to be asserted. The flag underapprox causes the underapproximations
   * of the children to be asserted *conditionally*. See Check() on
   * how to actually enforce these constraints.
   *
   */

  void RPFP::AssertEdge(Edge *e, int persist, bool with_children, bool underapprox)
  {
    if(eq(e->F.Formula,ctx.bool_val(true)) && (!with_children || e->Children.empty()))
      return;
    if (e->dual.null())
      {
	timer_start("ReducedDualEdge");
	e->dual = ReducedDualEdge(e);
	timer_stop("ReducedDualEdge");
	timer_start("getting children");
	if(with_children)
	  for(unsigned i = 0; i < e->Children.size(); i++)
	    e->dual = e->dual && GetAnnotation(e->Children[i]);
	if(underapprox){
	  std::vector<expr> cus(e->Children.size());
	  for(unsigned i = 0; i < e->Children.size(); i++)
	    cus[i] = !UnderapproxFlag(e->Children[i]) || GetUnderapprox(e->Children[i]);
	  expr cnst =  conjoin(cus);
	  e->dual = e->dual && cnst;
	}
	timer_stop("getting children");
	timer_start("Persisting");
	std::list<stack_entry>::reverse_iterator it = stack.rbegin();
	for(int i = 0; i < persist && it != stack.rend(); i++)
	  it++;
	if(it != stack.rend())
	  it->edges.push_back(e);
#if 0
	if(persist != 0)
	  Z3_persist_ast(ctx,e->dual,persist);
#endif
	timer_stop("Persisting");
	//Console.WriteLine("{0}", cnst);
      }
    timer_start("solver add");
    slvr.add(e->dual);
    timer_stop("solver add");
  }

        
  /** For incremental solving, asserts the negation of the upper bound associated
   * with a node.
   * */

  void RPFP::AssertNode(Node *n)
  {
    if (n->dual.null())
      {
	n->dual = GetUpperBound(n);
	stack.back().nodes.push_back(n);
	slvr.add(n->dual);
      }
  }

  /** Declare a constant in the background theory. */

  void RPFP::DeclareConstant(const FuncDecl &f){
    ls->declare_constant(f);
  }

  /** Assert a background axiom. Background axioms can be used to provide the
   *  theory of auxilliary functions or relations. All symbols appearing in
   *  background axioms are considered global, and may appear in both transformer
   *  and relational solutions. Semantically, a solution to the RPFP gives
   *  an interpretation of the unknown relations for each interpretation of the
   *  auxilliary symbols that is consistent with the axioms. Axioms should be
   *  asserted before any calls to Push. They cannot be de-asserted by Pop. */

  void RPFP::AssertAxiom(const Term &t)
  {
    ls->assert_axiom(t);
    axioms.push_back(t); // for printing only
  }

#if 0
  /** Do not call this. */

  void RPFP::RemoveAxiom(const Term &t)
  {
    slvr.RemoveInterpolationAxiom(t);
  }
#endif
  
  /** Solve an RPFP graph. This means either strengthen the annotation
   *  so that the bound at the given root node is satisfied, or
   *  show that this cannot be done by giving a dual solution 
   *  (i.e., a counterexample). 
   *  
   * In the current implementation, this only works for graphs that
   * are:
   * - tree-like
   * 
   * - closed.
   * 
   * In a tree-like graph, every nod has out most one incoming and one out-going edge,
   * and there are no cycles. In a closed graph, every node has exactly one out-going
   * edge. This means that the leaves of the tree are all hyper-edges with no
   * children. Such an edge represents a relation (nullary transformer) and thus
   * a lower bound on its parent. The parameter root must be the root of this tree.
   * 
   * If Solve returns LBool.False, this indicates success. The annotation of the tree
   * has been updated to satisfy the upper bound at the root. 
   * 
   * If Solve returns LBool.True, this indicates a counterexample. For each edge,
   * you can then call Eval to determine the values of symbols in the transformer formula.
   * You can also call Empty on a node to determine if its value in the counterexample
   * is the empty relation.
   * 
   *    \param root The root of the tree
   *    \param persist Number of context pops through which result should persist 
   * 
   * 
   */

  lbool RPFP::Solve(Node *root, int persist)
  {
    timer_start("Solve");
    TermTree *tree = GetConstraintTree(root);
    TermTree *interpolant = NULL;
    TermTree *goals = NULL;
    if(ls->need_goals)
      goals = GetGoalTree(root);

    // if (dualModel != null) dualModel.Dispose();
    // if (dualLabels != null) dualLabels.Dispose();
    
    timer_start("interpolate_tree");
    lbool res = ls->interpolate_tree(tree, interpolant, dualModel,goals,true);
    timer_stop("interpolate_tree");
    if (res == l_false)
      {
	DecodeTree(root, interpolant->getChildren()[0], persist);
	delete interpolant;
      }

    delete tree;
    if(goals)
      delete goals;
    
    timer_stop("Solve");
    return res;
  }
  
  /** Get the constraint tree (but don't solve it) */
  
  TermTree *RPFP::GetConstraintTree(Node *root)
  {
    return AddUpperBound(root, ToTermTree(root));
  }
  
  /** Dispose of the dual model (counterexample) if there is one. */

  void RPFP::DisposeDualModel()
  {
    dualModel = model(ctx,NULL);
  }
  
  RPFP::Term RPFP::UnderapproxFlag(Node *n){
    expr flag = ctx.constant((std::string("@under") +  string_of_int(n->number)).c_str(), ctx.bool_sort());
    underapprox_flag_rev[flag] = n;
    return flag;
  }

  RPFP::Node *RPFP::UnderapproxFlagRev(const Term &flag){
    return underapprox_flag_rev[flag];
  }

  /** Check satisfiability of asserted edges and nodes. Same functionality as
   * Solve, except no primal solution (interpolant) is generated in the unsat case.
   * The vector underapproxes gives the set of node underapproximations to be enforced
   * (assuming these were conditionally asserted by AssertEdge).
   * 
   */ 

  check_result RPFP::Check(Node *root, std::vector<Node *> underapproxes, std::vector<Node *> *underapprox_core )
        {
	  // if (dualModel != null) dualModel.Dispose();
	  check_result res;
	  if(!underapproxes.size())
	    res = slvr.check();
	  else {
	    std::vector<expr> us(underapproxes.size());
	    for(unsigned i = 0; i < underapproxes.size(); i++)
	      us[i] = UnderapproxFlag(underapproxes[i]);
            slvr.check(); // TODO: no idea why I need to do this
	    if(underapprox_core){
	      std::vector<expr> unsat_core(us.size());
	      unsigned core_size = 0;
	      res = slvr.check(us.size(),&us[0],&core_size,&unsat_core[0]);
	      underapprox_core->resize(core_size);
	      for(unsigned i = 0; i < core_size; i++)
		(*underapprox_core)[i] = UnderapproxFlagRev(unsat_core[i]);
	    }
	    else {
	      res = slvr.check(us.size(),&us[0]);
	      bool dump = false;
	      if(dump){
		std::vector<expr> cnsts;
		// cnsts.push_back(axioms[0]);
		cnsts.push_back(root->dual);
		cnsts.push_back(root->Outgoing->dual);
		ls->write_interpolation_problem("temp.smt",cnsts,std::vector<expr>());
	      }
	    }
            // check_result temp = slvr.check();
	  }
	  dualModel = slvr.get_model();
	  return res;
        }

  check_result RPFP::CheckUpdateModel(Node *root, std::vector<expr> assumps){
    // check_result temp1 = slvr.check(); // no idea why I need to do this
    check_result res = slvr.check_keep_model(assumps.size(),&assumps[0]);
    dualModel = slvr.get_model();
    return res;
  }      

  /** Determines the value in the counterexample of a symbol occuring in the transformer formula of
   *  a given edge. */

  RPFP::Term RPFP::Eval(Edge *e, Term t)
  {
    Term tl = Localize(e, t);
    return dualModel.eval(tl);
  }

        

  /** Returns true if the given node is empty in the primal solution. For proecudure summaries,
      this means that the procedure is not called in the current counter-model. */
  
  bool RPFP::Empty(Node *p)
  {
    Term b; std::vector<Term> v;
    RedVars(p, b, v);
    // dualModel.show_internals();
    // std::cout << "b: " << b << std::endl;
    expr bv = dualModel.eval(b);
    // std::cout << "bv: " << bv << std::endl; 
    bool res = !eq(bv,ctx.bool_val(true));
    return res;
  }

  RPFP::Term RPFP::EvalNode(Node *p)
  {
    Term b; std::vector<Term> v;
    RedVars(p, b, v);
    std::vector<Term> args;
    for(unsigned i = 0; i < v.size(); i++)
      args.push_back(dualModel.eval(v[i]));
    return (p->Name)(args);
  }

  void RPFP::EvalArrayTerm(const RPFP::Term &t, ArrayValue &res){
    if(t.is_app()){
      decl_kind k = t.decl().get_decl_kind();
      if(k == AsArray){
	func_decl fd = t.decl().get_func_decl_parameter(0);
	func_interp r = dualModel.get_func_interp(fd);
	int num = r.num_entries();
	res.defined = true;
	for(int i = 0; i < num; i++){
	  expr arg = r.get_arg(i,0);
	  expr value = r.get_value(i);
	  res.entries[arg] = value;
	}
	res.def_val = r.else_value();
	return;
      }
      else if(k == Store){
	EvalArrayTerm(t.arg(0),res);
	if(!res.defined)return;
	expr addr = t.arg(1);
	expr val = t.arg(2);
	if(addr.is_numeral() && val.is_numeral()){
	  if(eq(val,res.def_val))
	    res.entries.erase(addr);
	  else
	    res.entries[addr] = val;
	}
	else
	  res.defined = false;
	return;
      }
    }
    res.defined = false;
  }

  int eae_count = 0;

  RPFP::Term RPFP::EvalArrayEquality(const RPFP::Term &f){
    ArrayValue lhs,rhs;
    eae_count++;
    EvalArrayTerm(f.arg(0),lhs);
    EvalArrayTerm(f.arg(1),rhs);
    if(lhs.defined && rhs.defined){
      if(eq(lhs.def_val,rhs.def_val))
	if(lhs.entries == rhs.entries)
	  return ctx.bool_val(true);
      return ctx.bool_val(false);
    }
    return f;
  }

  /** Compute truth values of all boolean subterms in current model.
      Assumes formulas has been simplified by Z3, so only boolean ops
      ands and, or, not. Returns result in memo. 
  */

  int RPFP::SubtermTruth(hash_map<ast,int> &memo, const Term &f){
    if(memo.find(f) != memo.end()){
      return memo[f];
    }
    int res;
    if(f.is_app()){
      int nargs = f.num_args();
      decl_kind k = f.decl().get_decl_kind();
      if(k == Implies){
	res = SubtermTruth(memo,!f.arg(0) || f.arg(1));
	goto done;
      }
      if(k == And) {
	res = 1; 
	for(int i = 0; i < nargs; i++){
	  int ar = SubtermTruth(memo,f.arg(i));
	  if(ar == 0){
	    res = 0;
	    goto done;
	  }
	  if(ar == 2)res = 2; 
	}
	goto done;
      }
      else if(k == Or) {
	res = 0;
	for(int i = 0; i < nargs; i++){
	  int ar = SubtermTruth(memo,f.arg(i));
	  if(ar == 1){
	    res = 1;
	    goto done;
	  }
	  if(ar == 2)res = 2; 
	}
	goto done;
      }
      else if(k == Not) {
	int ar = SubtermTruth(memo,f.arg(0));
	res = (ar == 0) ? 1 : ((ar == 1) ? 0 : 2);
	goto done;
      }
    }
    {
      bool pos; std::vector<symbol> names;
      if(f.is_label(pos,names)){
	res = SubtermTruth(memo,f.arg(0));
	goto done;
      }
    }
    {
      expr bv = dualModel.eval(f);
      if(bv.is_app() && bv.decl().get_decl_kind() == Equal && 
	 bv.arg(0).is_array()){
	bv = EvalArrayEquality(bv);
      }
      // Hack!!!! array equalities can occur negatively!
      if(bv.is_app() && bv.decl().get_decl_kind() == Not && 
	 bv.arg(0).decl().get_decl_kind() == Equal &&
	 bv.arg(0).arg(0).is_array()){
	bv = dualModel.eval(!EvalArrayEquality(bv.arg(0)));
      }
      if(eq(bv,ctx.bool_val(true)))
	res = 1;
      else if(eq(bv,ctx.bool_val(false)))
	res = 0;
      else
	res = 2;
    }
  done:
    memo[f] = res;
    return res;
  }

  int RPFP::EvalTruth(hash_map<ast,int> &memo, Edge *e, const Term &f){
    Term tl = Localize(e, f);
    return SubtermTruth(memo,tl);
  }

  /** Compute truth values of all boolean subterms in current model.
      Assumes formulas has been simplified by Z3, so only boolean ops
      ands and, or, not. Returns result in memo. 
  */

#if 0
  int RPFP::GetLabelsRec(hash_map<ast,int> *memo, const Term &f, std::vector<symbol> &labels, bool labpos){
    if(memo[labpos].find(f) != memo[labpos].end()){
      return memo[labpos][f];
    }
    int res;
    if(f.is_app()){
      int nargs = f.num_args();
      decl_kind k = f.decl().get_decl_kind();
      if(k == Implies){
	res = GetLabelsRec(memo,f.arg(1) || !f.arg(0), labels, labpos);
	goto done;
      }
      if(k == And) {
	res = 1; 
	for(int i = 0; i < nargs; i++){
	  int ar = GetLabelsRec(memo,f.arg(i), labels, labpos);
	  if(ar == 0){
	    res = 0;
	    goto done;
	  }
	  if(ar == 2)res = 2; 
	}
	goto done;
      }
      else if(k == Or) {
	res = 0;
	for(int i = 0; i < nargs; i++){
	  int ar = GetLabelsRec(memo,f.arg(i), labels, labpos);
	  if(ar == 1){
	    res = 1;
	    goto done;
	  }
	  if(ar == 2)res = 2; 
	}
	goto done;
      }
      else if(k == Not) {
	int ar = GetLabelsRec(memo,f.arg(0), labels, !labpos);
	res = (ar == 0) ? 1 : ((ar == 1) ? 0 : 2);
	goto done;
      }
    }
    {
      bool pos; std::vector<symbol> names;
      if(f.is_label(pos,names)){
	res = GetLabelsRec(memo,f.arg(0), labels, labpos);
	if(pos == labpos && res == (pos ? 1 : 0))
	  for(unsigned i = 0; i < names.size(); i++)
	    labels.push_back(names[i]);
	goto done;
      }
    }
    {
      expr bv = dualModel.eval(f);
      if(bv.is_app() && bv.decl().get_decl_kind() == Equal && 
	 bv.arg(0).is_array()){
	bv = EvalArrayEquality(bv);
      }
      // Hack!!!! array equalities can occur negatively!
      if(bv.is_app() && bv.decl().get_decl_kind() == Not && 
	 bv.arg(0).decl().get_decl_kind() == Equal &&
	 bv.arg(0).arg(0).is_array()){
	bv = dualModel.eval(!EvalArrayEquality(bv.arg(0)));
      }
      if(eq(bv,ctx.bool_val(true)))
	res = 1;
      else if(eq(bv,ctx.bool_val(false)))
	res = 0;
      else
	res = 2;
    }
  done:
    memo[labpos][f] = res;
    return res;
  }
#endif

  void RPFP::GetLabelsRec(hash_map<ast,int> &memo, const Term &f, std::vector<symbol> &labels,
			  hash_set<ast> *done, bool truth){
    if(done[truth].find(f) != done[truth].end())
      return; /* already processed */
    if(f.is_app()){
      int nargs = f.num_args();
      decl_kind k = f.decl().get_decl_kind();
      if(k == Implies){
	GetLabelsRec(memo,f.arg(1) || !f.arg(0) ,labels,done,truth);
	goto done;
      }
      if(k == Iff){
	int b = SubtermTruth(memo,f.arg(0));
	if(b == 2)
	  throw "disaster in GetLabelsRec";
	GetLabelsRec(memo,f.arg(1),labels,done,truth ? b : !b);
	goto done;
      }
      if(truth ? k == And : k == Or) {
	for(int i = 0; i < nargs; i++)
	  GetLabelsRec(memo,f.arg(i),labels,done,truth);
	goto done;
      }
      if(truth ? k == Or : k == And) {
	for(int i = 0; i < nargs; i++){
	  Term a = f.arg(i);
	  timer_start("SubtermTruth");
	  int b = SubtermTruth(memo,a);
	  timer_stop("SubtermTruth");
	  if(truth ? (b == 1) : (b == 0)){
	    GetLabelsRec(memo,a,labels,done,truth);
	    goto done;
	  }
	}
	/* Unreachable! */
	throw "error in RPFP::GetLabelsRec";
	goto done;
      }
      else if(k == Not) {
	GetLabelsRec(memo,f.arg(0),labels,done,!truth);
	goto done;
      }
      else {
	bool pos; std::vector<symbol> names;
	if(f.is_label(pos,names)){
	  GetLabelsRec(memo,f.arg(0), labels, done, truth);
	  if(pos == truth)
	    for(unsigned i = 0; i < names.size(); i++)
	      labels.push_back(names[i]);
	  goto done;
	}
      }
    }
  done:
    done[truth].insert(f);
  }

  void RPFP::GetLabels(Edge *e, std::vector<symbol> &labels){
    if(!e->map || e->map->labeled.null())
      return;
    Term tl = Localize(e, e->map->labeled);
    hash_map<ast,int> memo;
    hash_set<ast> done[2];
    GetLabelsRec(memo,tl,labels,done,true);
  }

#ifdef Z3OPS
  static Z3_subterm_truth *stt;
#endif

  int ir_count = 0;

  void RPFP::ImplicantRed(hash_map<ast,int> &memo, const Term &f, std::vector<Term> &lits,
			  hash_set<ast> *done, bool truth, hash_set<ast> &dont_cares){
    if(done[truth].find(f) != done[truth].end())
      return; /* already processed */
#if 0
    int this_count = ir_count++;
    if(this_count == 50092)
      std::cout << "foo!\n";
#endif
    if(f.is_app()){
      int nargs = f.num_args();
      decl_kind k = f.decl().get_decl_kind();
      if(k == Implies){
	ImplicantRed(memo,f.arg(1) || !f.arg(0) ,lits,done,truth,dont_cares);
	goto done;
      }
      if(k == Iff){
	int b = SubtermTruth(memo,f.arg(0));
	if(b == 2)
	  throw "disaster in ImplicantRed";
	ImplicantRed(memo,f.arg(1),lits,done,truth ? b : !b,dont_cares);
	goto done;
      }
      if(truth ? k == And : k == Or) {
	for(int i = 0; i < nargs; i++)
	  ImplicantRed(memo,f.arg(i),lits,done,truth,dont_cares);
	goto done;
      }
      if(truth ? k == Or : k == And) {
	for(int i = 0; i < nargs; i++){
	  Term a = f.arg(i);
#if 0
	  if(i == nargs - 1){ // last chance!
 	    ImplicantRed(memo,a,lits,done,truth,dont_cares);
	    goto done;
	  }
#endif
	  timer_start("SubtermTruth");
#ifdef Z3OPS
	  bool b = stt->eval(a);
#else
	  int b = SubtermTruth(memo,a);
#endif
	  timer_stop("SubtermTruth");
	  if(truth ? (b == 1) : (b == 0)){
	    ImplicantRed(memo,a,lits,done,truth,dont_cares);
	    goto done;
	  }
	}
	/* Unreachable! */
	throw "error in RPFP::ImplicantRed";
	goto done;
      }
      else if(k == Not) {
	ImplicantRed(memo,f.arg(0),lits,done,!truth,dont_cares);
	goto done;
      }
    }
    {
      if(dont_cares.find(f) == dont_cares.end()){
	expr rf = ResolveIte(memo,f,lits,done,dont_cares);
	expr bv = truth ? rf : !rf;
	lits.push_back(bv);
      }
    }
  done:
    done[truth].insert(f);
  }

  RPFP::Term RPFP::ResolveIte(hash_map<ast,int> &memo, const Term &t, std::vector<Term> &lits,
			hash_set<ast> *done, hash_set<ast> &dont_cares){
    if(resolve_ite_memo.find(t) != resolve_ite_memo.end())
      return resolve_ite_memo[t];
    Term res;
    if (t.is_app())
      {
	func_decl f = t.decl();
	std::vector<Term> args;
	int nargs = t.num_args();
	if(f.get_decl_kind() == Ite){
	  timer_start("SubtermTruth");
#ifdef Z3OPS
	  bool sel = stt->eval(t.arg(0));
#else
	  int xval = SubtermTruth(memo,t.arg(0));
	  bool sel;
	  if(xval == 0)sel = false;
	  else if(xval == 1)sel = true;
	  else
	    throw "unresolved ite in model";
#endif
	  timer_stop("SubtermTruth");
	  ImplicantRed(memo,t.arg(0),lits,done,sel,dont_cares);
	  res = ResolveIte(memo,t.arg(sel?1:2),lits,done,dont_cares);
	}
	else {
	  for(int i = 0; i < nargs; i++)
	    args.push_back(ResolveIte(memo,t.arg(i),lits,done,dont_cares));
	  res = f(args.size(),&args[0]);
	}
      }
    else res = t;
    resolve_ite_memo[t] = res;
    return res;
  }

  void RPFP::Implicant(hash_map<ast,int> &memo, const Term &f, std::vector<Term> &lits, hash_set<ast> &dont_cares){
    hash_set<ast> done[2];
    ImplicantRed(memo,f,lits,done,true, dont_cares);
  }


  /** Underapproximate a formula using current counterexample. */

  RPFP::Term RPFP::UnderapproxFormula(const Term &f, hash_set<ast> &dont_cares){
    /* first compute truth values of subterms */
    hash_map<ast,int> memo;
    #ifdef Z3OPS
    stt = Z3_mk_subterm_truth(ctx,dualModel);
    #endif
    // SubtermTruth(memo,f);
    /* now compute an implicant */
    std::vector<Term> lits;
    Implicant(memo,f,lits, dont_cares);
#ifdef Z3OPS
    delete stt; stt = 0;
#endif
    /* return conjunction of literals */
    return conjoin(lits);
  }

  struct VariableProjector : Z3User {
  
    struct elim_cand {
      Term var;
      int sup;
      Term val;
    };
    
    typedef expr Term;

    hash_set<ast> keep;
    hash_map<ast,int> var_ord; 
    int num_vars;
    std::vector<elim_cand> elim_cands;
    hash_map<ast,std::vector<int> > sup_map;
    hash_map<ast,Term> elim_map;
    std::vector<int> ready_cands;
    hash_map<ast,int> cand_map;
    params simp_params;

    VariableProjector(Z3User &_user, std::vector<Term> &keep_vec) : 
      Z3User(_user), simp_params()
    {
      num_vars = 0;
      for(unsigned i = 0; i < keep_vec.size(); i++){
	keep.insert(keep_vec[i]);
	var_ord[keep_vec[i]] = num_vars++;
      }
    }
    
    int VarNum(const Term &v){
      if(var_ord.find(v) == var_ord.end())
	var_ord[v] = num_vars++;
      return var_ord[v];
    }

    bool IsVar(const Term &t){
      return t.is_app() && t.num_args() == 0 && t.decl().get_decl_kind() == Uninterpreted;
    }
    
    bool IsPropLit(const Term &t, Term &a){
      if(IsVar(t)){
	a = t;
	return true;
      }
      else if(t.is_app() && t.decl().get_decl_kind() == Not)
	return IsPropLit(t.arg(0),a);
      return false;
    }
    
    void CountOtherVarsRec(hash_map<ast,int> &memo,
			   const Term &t,
			   int id,
			   int &count){
      std::pair<ast,int> foo(t,0);
      std::pair<hash_map<ast,int>::iterator, bool> bar = memo.insert(foo);
      // int &res = bar.first->second;
      if(!bar.second) return;
      if (t.is_app())
      {
	func_decl f = t.decl();
	std::vector<Term> args;
	int nargs = t.num_args();
	if (nargs == 0 && f.get_decl_kind() == Uninterpreted){
	  if(cand_map.find(t) != cand_map.end()){
	    count++;
	    sup_map[t].push_back(id);
	  }
	}
	for(int i = 0; i < nargs; i++)
	  CountOtherVarsRec(memo, t.arg(i), id, count);
      }
      else if (t.is_quantifier())
	CountOtherVarsRec(memo, t.body(), id, count);
    }  
    
    void NewElimCand(const Term &lhs, const Term &rhs){
      if(debug_gauss){
	std::cout << "mapping " << lhs << " to " << rhs << std::endl;
      }
	elim_cand cand;
	cand.var = lhs;
	cand.sup = 0;
	cand.val = rhs;
	elim_cands.push_back(cand);
	cand_map[lhs] = elim_cands.size()-1;
    }

    void MakeElimCand(const Term &lhs, const Term &rhs){
      if(eq(lhs,rhs))
	return;
      if(!IsVar(lhs)){
	if(IsVar(rhs)){
	  MakeElimCand(rhs,lhs);
	  return;
	}
	else{
	  std::cout << "would have mapped a non-var\n";
	  return;
	}
      }
      if(IsVar(rhs) && VarNum(rhs) > VarNum(lhs)){
	MakeElimCand(rhs,lhs);
	return;
      }
      if(keep.find(lhs) != keep.end())
	return;
      if(cand_map.find(lhs) == cand_map.end())
	NewElimCand(lhs,rhs);
      else {
        int cand_idx = cand_map[lhs];
	if(IsVar(rhs) && cand_map.find(rhs) == cand_map.end()
	   && keep.find(rhs) == keep.end())
	  NewElimCand(rhs,elim_cands[cand_idx].val);
	elim_cands[cand_idx].val = rhs;
      }
    }

    Term FindRep(const Term &t){
      if(cand_map.find(t) == cand_map.end())
	return t;
      Term &res = elim_cands[cand_map[t]].val;
      if(IsVar(res)){
	assert(VarNum(res) < VarNum(t));
	res = FindRep(res);
	return res;
      }
      return t;
    }

    void GaussElimCheap(const std::vector<Term> &lits_in,
			std::vector<Term> &lits_out){
      for(unsigned i = 0; i < lits_in.size(); i++){
	Term lit = lits_in[i];
	if(lit.is_app()){
	  decl_kind k = lit.decl().get_decl_kind();
          if(k == Equal || k == Iff)
	    MakeElimCand(FindRep(lit.arg(0)),FindRep(lit.arg(1)));
	}
      }
      
      for(unsigned i = 0; i < elim_cands.size(); i++){
	elim_cand &cand = elim_cands[i];
	hash_map<ast,int> memo;
	CountOtherVarsRec(memo,cand.val,i,cand.sup);
	if(cand.sup == 0)
	  ready_cands.push_back(i);
      }
      
      while(!ready_cands.empty()){
	elim_cand &cand = elim_cands[ready_cands.back()];
	ready_cands.pop_back();
	Term rep = FindRep(cand.var);
	if(!eq(rep,cand.var))
	  if(cand_map.find(rep) != cand_map.end()){
	    int rep_pos = cand_map[rep];
	    cand.val = elim_cands[rep_pos].val;
	  }
	Term val = SubstRec(elim_map,cand.val);
      if(debug_gauss){
	std::cout << "subbing " << cand.var << " --> " << val << std::endl;
      }
	elim_map[cand.var] = val;
	std::vector<int> &sup = sup_map[cand.var];
	for(unsigned i = 0; i < sup.size(); i++){
	  int c = sup[i];
	  if((--elim_cands[c].sup) == 0)
	    ready_cands.push_back(c);
	}
      }
      
      for(unsigned i = 0; i < lits_in.size(); i++){
	Term lit = lits_in[i];
	lit = SubstRec(elim_map,lit);
	lit = lit.simplify();
	if(eq(lit,ctx.bool_val(true)))
	  continue;
	Term a;
	if(IsPropLit(lit,a))
	  if(keep.find(lit) == keep.end())
	    continue;
	lits_out.push_back(lit);
      }
    }

    // maps variables to constrains in which the occur pos, neg
    hash_map<ast,int> la_index[2];
    hash_map<ast,Term> la_coeffs[2];
    std::vector<Term> la_pos_vars;
    bool fixing;
    
    void IndexLAcoeff(const Term &coeff1, const Term &coeff2, Term t, int id){
      Term coeff = coeff1 * coeff2;
      coeff = coeff.simplify();
      Term is_pos = (coeff >= ctx.int_val(0));
      is_pos = is_pos.simplify();
      if(eq(is_pos,ctx.bool_val(true)))
	IndexLA(true,coeff,t, id);
      else
	IndexLA(false,coeff,t, id);
    }

    void IndexLAremove(const Term &t){
      if(IsVar(t)){
	la_index[0][t] = -1;  // means ineligible to be eliminated
	la_index[1][t] = -1;  // (more that one occurrence, or occurs not in linear comb)
      }
      else if(t.is_app()){
	int nargs = t.num_args();
	for(int i = 0; i < nargs; i++)
	  IndexLAremove(t.arg(i));
      }
      // TODO: quantifiers?
    }


    void IndexLA(bool pos, const Term &coeff, const Term &t, int id){
      if(t.is_numeral())
	return;
      if(t.is_app()){
	int nargs = t.num_args();
	switch(t.decl().get_decl_kind()){
	case Plus:
	  for(int i = 0; i < nargs; i++)
	    IndexLA(pos,coeff,t.arg(i), id);
	  break;
	case Sub:
	  IndexLA(pos,coeff,t.arg(0), id);
	  IndexLA(!pos,coeff,t.arg(1), id);
	  break;
	case Times:
	  if(t.arg(0).is_numeral())
	    IndexLAcoeff(coeff,t.arg(0),t.arg(1), id);
	  else if(t.arg(1).is_numeral())
	    IndexLAcoeff(coeff,t.arg(1),t.arg(0), id);
	  break;
	default:
	  if(IsVar(t) && (fixing || la_index[pos].find(t) == la_index[pos].end())){
	    la_index[pos][t] = id;
	    la_coeffs[pos][t] = coeff;
	    if(pos && !fixing)
	      la_pos_vars.push_back(t);  // this means we only add a var once
	  }
	  else
	    IndexLAremove(t);
	}
      }
    }

    void IndexLAstart(bool pos, const Term &t, int id){
      IndexLA(pos,(pos ? ctx.int_val(1) : ctx.int_val(-1)), t, id);
    }

    void IndexLApred(bool pos, const Term &p, int id){
      if(p.is_app()){
	switch(p.decl().get_decl_kind()){
	case Not:
	  IndexLApred(!pos, p.arg(0),id);
	  break;
	case Leq:
	case Lt:
	  IndexLAstart(!pos, p.arg(0), id);
	  IndexLAstart(pos, p.arg(1), id);
	  break;
	case Geq:
	case Gt:
	  IndexLAstart(pos,p.arg(0), id);
	  IndexLAstart(!pos,p.arg(1), id);
	  break;
	default:
	  IndexLAremove(p);
	}
      }
    }

    void IndexLAfix(const Term &p, int id){
      fixing = true;
      IndexLApred(true,p,id);
      fixing = false;
    }

    bool IsCanonIneq(const Term &lit, Term &term, Term &bound){
      // std::cout << Z3_simplify_get_help(ctx) << std::endl;
      bool pos = lit.decl().get_decl_kind() != Not;
      Term atom = pos ? lit : lit.arg(0);
      if(atom.decl().get_decl_kind() == Leq){
	if(pos){
	  bound = atom.arg(0);
	  term = atom.arg(1).simplify(simp_params);
#if Z3_MAJOR_VERSION < 4
	  term = SortSum(term);
#endif
	}
	else {
	  bound = (atom.arg(1) + ctx.int_val(1));
	  term = atom.arg(0);
	  // std::cout << "simplifying bound: " << bound << std::endl;
	  bound = bound.simplify();
	  term = term.simplify(simp_params);
#if Z3_MAJOR_VERSION < 4
	  term = SortSum(term);
#endif
	}
	return true;
      }
      else if(atom.decl().get_decl_kind() == Geq){
	if(pos){
	  bound = atom.arg(1);  // integer axiom
	  term = atom.arg(0).simplify(simp_params);
#if Z3_MAJOR_VERSION < 4
	  term = SortSum(term);
#endif
	  return true;
	}
	else{
	  bound = -(atom.arg(1) - ctx.int_val(1));  // integer axiom
	  term = -atom.arg(0);
	  bound = bound.simplify();
	  term = term.simplify(simp_params);
#if Z3_MAJOR_VERSION < 4
	  term = SortSum(term);
#endif
	}
	return true;
      }
      return false;
    }

    Term CanonIneqTerm(const Term &p){
      Term term,bound;
      Term ps = p.simplify();
      bool ok = IsCanonIneq(ps,term,bound);
      assert(ok);
      return term - bound;
    }

    void ElimRedundantBounds(std::vector<Term> &lits){
      hash_map<ast,int> best_bound;
      for(unsigned i = 0; i < lits.size(); i++){
	lits[i] = lits[i].simplify(simp_params);
	Term term,bound;
	if(IsCanonIneq(lits[i],term,bound)){
	  if(best_bound.find(term) == best_bound.end())
	    best_bound[term] = i;
	  else {
	    int best = best_bound[term];
	    Term bterm,bbound;
	    IsCanonIneq(lits[best],bterm,bbound);
	    Term comp = bound > bbound;
	    comp = comp.simplify();
	    if(eq(comp,ctx.bool_val(true))){
	      lits[best] = ctx.bool_val(true);
	      best_bound[term] = i;
	    }
	    else {
	      lits[i] = ctx.bool_val(true);
	    }
	  }
	}
      }
    }

    void FourierMotzkinCheap(const std::vector<Term> &lits_in,
			     std::vector<Term> &lits_out){
      simp_params.set(":som",true);
      simp_params.set(":sort-sums",true);
      fixing = false; lits_out = lits_in;
      ElimRedundantBounds(lits_out);
      for(unsigned i = 0; i < lits_out.size(); i++)
	IndexLApred(true,lits_out[i],i);

      for(unsigned i = 0; i < la_pos_vars.size(); i++){
	Term var = la_pos_vars[i];
	if(la_index[false].find(var) != la_index[false].end()){
	  int pos_idx = la_index[true][var];
	  int neg_idx = la_index[false][var];
	  if(pos_idx >= 0 && neg_idx >= 0){
	    if(keep.find(var) != keep.end()){
	      std::cout << "would have eliminated keep var\n";
	      continue;
	    }
	    Term tpos = CanonIneqTerm(lits_out[pos_idx]);
	    Term tneg = CanonIneqTerm(lits_out[neg_idx]);
	    Term pos_coeff = la_coeffs[true][var];
	    Term neg_coeff = -la_coeffs[false][var];
	    Term comb = neg_coeff * tpos + pos_coeff * tneg;
	    Term ineq = ctx.int_val(0) <= comb;
	    ineq = ineq.simplify();
	    lits_out[pos_idx] = ineq;
	    lits_out[neg_idx] = ctx.bool_val(true);
	    IndexLAfix(ineq,pos_idx);
	  }
	}
      }
    }

    Term ProjectFormula(const Term &f){
      std::vector<Term> lits, new_lits1, new_lits2;
      CollectConjuncts(f,lits);
      timer_start("GaussElimCheap");
      GaussElimCheap(lits,new_lits1);
      timer_stop("GaussElimCheap");
      timer_start("FourierMotzkinCheap");
      FourierMotzkinCheap(new_lits1,new_lits2);
      timer_stop("FourierMotzkinCheap");
      return conjoin(new_lits2);
    }
  }; 
    
  void Z3User::CollectConjuncts(const Term &f, std::vector<Term> &lits, bool pos){
    if(f.is_app() && f.decl().get_decl_kind() == Not)
      CollectConjuncts(f.arg(0), lits, !pos);
    else if(pos && f.is_app() && f.decl().get_decl_kind() == And){
      int num_args = f.num_args();
      for(int i = 0; i < num_args; i++)
	CollectConjuncts(f.arg(i),lits,true);
    }
    else if(!pos && f.is_app() && f.decl().get_decl_kind() == Or){
      int num_args = f.num_args();
      for(int i = 0; i < num_args; i++)
	CollectConjuncts(f.arg(i),lits,false);
    }
    else if(pos)
      lits.push_back(f);
    else
      lits.push_back(!f);
  }

  struct TermLt {
    bool operator()(const expr &x, const expr &y){
      unsigned xid = x.get_id();
      unsigned yid = y.get_id();
      return xid < yid;
    }
  };

  void Z3User::SortTerms(std::vector<Term> &terms){
    TermLt foo;
    std::sort(terms.begin(),terms.end(),foo);
  }

  Z3User::Term Z3User::SortSum(const Term &t){
    if(!(t.is_app() && t.decl().get_decl_kind() == Plus))
      return t;
    int nargs = t.num_args();
    if(nargs < 2) return t;
    std::vector<Term> args(nargs);
    for(int i = 0; i < nargs; i++)
      args[i] = t.arg(i);
    SortTerms(args);
    if(nargs == 2)
      return args[0] + args[1];
    return sum(args);
  }
  

  RPFP::Term RPFP::ProjectFormula(std::vector<Term> &keep_vec, const Term &f){
    VariableProjector vp(*this,keep_vec);
    return vp.ProjectFormula(f);
  }

  /** Compute an underapproximation of every node in a tree rooted at "root",
      based on a previously computed counterexample. The underapproximation
      may contain free variables that are implicitly existentially quantified.
  */

  RPFP::Term RPFP::ComputeUnderapprox(Node *root, int persist){
    /* if terminated underapprox is empty set (false) */
    bool show_model = false;
    if(show_model)
      std::cout << dualModel << std::endl;
    if(!root->Outgoing){
      root->Underapprox.SetEmpty();
      return ctx.bool_val(true);
    }
    /* if not used in cex, underapprox is empty set (false) */
    if(Empty(root)){
      root->Underapprox.SetEmpty();
      return ctx.bool_val(true);
    }
    /* compute underapprox of children first */
    std::vector<Node *> &chs = root->Outgoing->Children;
    std::vector<Term> chu(chs.size());
    for(unsigned i = 0; i < chs.size(); i++)
      chu[i] = ComputeUnderapprox(chs[i],persist);

    Term b; std::vector<Term> v;
    RedVars(root, b, v);
    /* underapproximate the edge formula */
    hash_set<ast> dont_cares;
    dont_cares.insert(b);
    resolve_ite_memo.clear();
    timer_start("UnderapproxFormula");
    Term eu = UnderapproxFormula(root->Outgoing->dual,dont_cares);
    timer_stop("UnderapproxFormula");
    /* combine with children */
    chu.push_back(eu);
    eu = conjoin(chu);
    /* project onto appropriate variables */
    eu = ProjectFormula(v,eu);
    eu = eu.simplify();

#if 0
    /* check the result is consistent */
    {
      hash_map<ast,int> memo;
      int res = SubtermTruth(memo, eu);
      if(res != 1)
	throw "inconsistent projection";
    }
#endif

    /* rename to appropriate variable names */
    hash_map<ast,Term> memo;
    for (unsigned i = 0; i < v.size(); i++)
      memo[v[i]] = root->Annotation.IndParams[i];  /* copy names from annotation */
    Term funder = SubstRec(memo, eu);
    root->Underapprox = CreateRelation(root->Annotation.IndParams,funder);
#if 0
    if(persist)
      Z3_persist_ast(ctx,root->Underapprox.Formula,persist);
#endif
    return eu;
  }


  RPFP::Term RPFP::ModelValueAsConstraint(const Term &t){
    if(t.is_array()){
      ArrayValue arr;
      Term e = dualModel.eval(t);
      EvalArrayTerm(e, arr);
      if(arr.defined){
	std::vector<expr> cs;
	for(std::map<ast,ast>::iterator it = arr.entries.begin(), en = arr.entries.end(); it != en; ++it){
	  expr foo = select(t,expr(ctx,it->first)) == expr(ctx,it->second);
	  cs.push_back(foo);
	}
	return conjoin(cs);
      }
    }
    else {
      expr r = dualModel.get_const_interp(t.decl());
      if(!r.null()){
	expr res = t == expr(ctx,r);
	return res;
      }
    }
    return ctx.bool_val(true);
  }

  void RPFP::EvalNodeAsConstraint(Node *p, Transformer &res)
  {
    Term b; std::vector<Term> v;
    RedVars(p, b, v);
    std::vector<Term> args;
    for(unsigned i = 0; i < v.size(); i++){
      expr val = ModelValueAsConstraint(v[i]);
      if(!eq(val,ctx.bool_val(true)))
	args.push_back(val);
    }
    expr cnst = conjoin(args);
    hash_map<ast,Term> memo;
    for (unsigned i = 0; i < v.size(); i++)
      memo[v[i]] = p->Annotation.IndParams[i];  /* copy names from annotation */
    Term funder = SubstRec(memo, cnst);
    res = CreateRelation(p->Annotation.IndParams,funder);
  }


  /** Push a scope. Assertions made after Push can be undone by Pop. */

  void RPFP::Push()
  {
    stack.push_back(stack_entry());
    slvr.push();
  }
  
  /** Pop a scope (see Push). Note, you cannot pop axioms. */

  void RPFP::Pop(int num_scopes)
  {
    slvr.pop(num_scopes);
    for (int i = 0; i < num_scopes; i++)
      {
	stack_entry &back = stack.back();
	for(std::list<Edge *>::iterator it = back.edges.begin(), en = back.edges.end(); it != en; ++it)
	  (*it)->dual = expr(ctx,NULL);
	for(std::list<Node *>::iterator it = back.nodes.begin(), en = back.nodes.end(); it != en; ++it)
	  (*it)->dual = expr(ctx,NULL);
	stack.pop_back();
      }
  }
  
  
  
  
  // This returns a new FuncDel with same sort as top-level function
  // of term t, but with numeric suffix appended to name.

  Z3User::FuncDecl Z3User::SuffixFuncDecl(Term t, int n)
        {
            std::string name = t.decl().name().str() + "_" + string_of_int(n);
            std::vector<sort> sorts;
            int nargs = t.num_args();
            for(int i = 0; i < nargs; i++)
              sorts.push_back(t.arg(i).get_sort());
            return ctx.function(name.c_str(), nargs, &sorts[0], t.get_sort());
        }

  // Scan the clause body for occurrences of the predicate unknowns

  RPFP::Term RPFP::ScanBody(hash_map<ast,Term> &memo, 
		      const Term &t,
		      hash_map<func_decl,Node *> &pmap,
		      std::vector<func_decl> &parms,
                      std::vector<Node *> &nodes)
  {
    if(memo.find(t) != memo.end())
      return memo[t];
    Term res(ctx);
    if (t.is_app()) {
      func_decl f = t.decl();
      if(pmap.find(f) != pmap.end()){
	nodes.push_back(pmap[f]);
	f = SuffixFuncDecl(t,parms.size());
	parms.push_back(f);
      }
      int nargs = t.num_args();
      std::vector<Term> args;
      for(int i = 0; i < nargs; i++)
	args.push_back(ScanBody(memo,t.arg(i),pmap,parms,nodes));
      res = f(nargs,&args[0]);
    }
    else if (t.is_quantifier())
      res = CloneQuantifier(t,ScanBody(memo,t.body(),pmap,parms,nodes));
    else
      res = t;
    memo[t] = res;
    return res;
  }

  // return the func_del of an app if it is uninterpreted

  bool Z3User::get_relation(const Term &t, func_decl &R){
    if(!t.is_app())
      return false;
    R = t.decl();
    return R.get_decl_kind() == Uninterpreted;
  }

  // return true if term is an individual variable
  // TODO: have to check that it is not a background symbol

  bool Z3User::is_variable(const Term &t){
    if(!t.is_app())
      return false;
    return t.decl().get_decl_kind() == Uninterpreted
      && t.num_args() == 0;
  }

  RPFP::Term RPFP::RemoveLabelsRec(hash_map<ast,Term> &memo, const Term &t, 
				   std::vector<label_struct > &lbls){
    if(memo.find(t) != memo.end())
      return memo[t];
    Term res(ctx);
    if (t.is_app()){
      func_decl f = t.decl();
      std::vector<symbol> names;
      bool pos;
      if(t.is_label(pos,names)){
	res = RemoveLabelsRec(memo,t.arg(0),lbls);
	for(unsigned i = 0; i < names.size(); i++)
	  lbls.push_back(label_struct(names[i],res,pos));
      }
      else {
	int nargs = t.num_args();
	std::vector<Term> args;
	for(int i = 0; i < nargs; i++)
	  args.push_back(RemoveLabelsRec(memo,t.arg(i),lbls));
	res = f(nargs,&args[0]);
      }
    }
    else if (t.is_quantifier())
      res = CloneQuantifier(t,RemoveLabelsRec(memo,t.body(),lbls));
    else
      res = t;
    memo[t] = res;
    return res;
  }

  RPFP::Term RPFP::RemoveLabels(const Term &t, std::vector<label_struct > &lbls){
    hash_map<ast,Term> memo ;
    return RemoveLabelsRec(memo,t,lbls);
  }

  RPFP::Term RPFP::SubstBoundRec(hash_map<int,hash_map<ast,Term> > &memo, hash_map<int,Term> &subst, int level, const Term &t)
  {
    std::pair<ast,Term> foo(t,expr(ctx));
    std::pair<hash_map<ast,Term>::iterator, bool> bar = memo[level].insert(foo);
    Term &res = bar.first->second;
    if(!bar.second) return res;
    if (t.is_app())
      {
	func_decl f = t.decl();
	std::vector<Term> args;
	int nargs = t.num_args();
	if(nargs == 0)
	  ls->declare_constant(f);  // keep track of background constants
	for(int i = 0; i < nargs; i++)
	  args.push_back(SubstBoundRec(memo, subst, level, t.arg(i)));
	res = f(args.size(),&args[0]);
      }
    else if (t.is_quantifier()){
      int bound = t.get_quantifier_num_bound();
      std::vector<expr> pats;
      t.get_patterns(pats);
      for(unsigned i = 0; i < pats.size(); i++)
	pats[i] = SubstBoundRec(memo, subst, level + bound, pats[i]);
      res = clone_quantifier(t, SubstBoundRec(memo, subst, level + bound, t.body()), pats);
    }
    else if (t.is_var()) {
      int idx = t.get_index_value();
      if(idx >= level && subst.find(idx-level) != subst.end()){
	res = subst[idx-level];
      }
      else res = t;
    }
    else res = t;
    return res;
  }

  RPFP::Term RPFP::SubstBound(hash_map<int,Term> &subst, const Term &t){
    hash_map<int,hash_map<ast,Term> > memo;
    return SubstBoundRec(memo, subst, 0, t);
  }

  /** Convert a collection of clauses to Nodes and Edges in the RPFP.

      Predicate unknowns are uninterpreted predicates not
      occurring in the background theory.
            
      Clauses are of the form 
              
      B => P(t_1,...,t_k)

      where P is a predicate unknown and predicate unknowns
      occur only positivey in H and only under existential
      quantifiers in prenex form.

      Each predicate unknown maps to a node. Each clause maps to
      an edge. Let C be a clause B => P(t_1,...,t_k) where the
      sequence of predicate unknowns occurring in B (in order
      of occurrence) is P_1..P_n. The clause maps to a transformer
      T where:

      T.Relparams = P_1..P_n
      T.Indparams = x_1...x+k
      T.Formula = B /\ t_1 = x_1 /\ ... /\ t_k = x_k

      Throws exception bad_clause(msg,i) if a clause i is
      in the wrong form.

  */

                
  static bool canonical_clause(const expr &clause){
    if(clause.decl().get_decl_kind() != Implies)
      return false;
    expr arg = clause.arg(1);
    return arg.is_app() && (arg.decl().get_decl_kind() == False ||
			    arg.decl().get_decl_kind() == Uninterpreted);
  }

  void RPFP::FromClauses(const std::vector<Term> &unskolemized_clauses){
    hash_map<func_decl,Node *> pmap;
    func_decl fail_pred = ctx.fresh_func_decl("@Fail", ctx.bool_sort());
    
    std::vector<expr> clauses(unskolemized_clauses);
    // first, skolemize the clauses

    for(unsigned i = 0; i < clauses.size(); i++){
      expr &t = clauses[i];
      if (t.is_quantifier() && t.is_quantifier_forall()) {
	int bound = t.get_quantifier_num_bound();
	std::vector<sort> sorts;
	std::vector<symbol> names;
	hash_map<int,expr> subst;
	for(int j = 0; j < bound; j++){
	  sort the_sort = t.get_quantifier_bound_sort(j);
	  symbol name = t.get_quantifier_bound_name(j);
	  expr skolem = ctx.constant(symbol(ctx,name),sort(ctx,the_sort));
	  subst[bound-1-j] = skolem;
	}
	t = SubstBound(subst,t.body());
      }
    }    

    // create the nodes from the heads of the clauses

    for(unsigned i = 0; i < clauses.size(); i++){
      Term &clause = clauses[i];
      if(!canonical_clause(clause))
	clause = implies((!clause).simplify(),ctx.bool_val(false));
      Term head = clause.arg(1);
      func_decl R(ctx);
      bool is_query = false;
      if (eq(head,ctx.bool_val(false))){
	R = fail_pred;
	// R = ctx.constant("@Fail", ctx.bool_sort()).decl();
	is_query = true;
      }
      else if(!get_relation(head,R))
	 throw bad_clause("rhs must be a predicate application",i);
      if(pmap.find(R) == pmap.end()){

	// If the node doesn't exitst, create it. The Indparams
	// are arbitrary, but we use the rhs arguments if they
	// are variables for mnomonic value.

	hash_set<ast> seen;
        std::vector<Term> Indparams;
	for(unsigned j = 0; j < head.num_args(); j++){
	  Term arg = head.arg(j);
	  if(!is_variable(arg) || seen.find(arg) != seen.end()){
	    std::string name = std::string("@a_") + string_of_int(j);
            arg = ctx.constant(name.c_str(),arg.get_sort());
	  }
	  seen.insert(arg);
	  Indparams.push_back(arg);
	}
        Node *node = CreateNode(R(Indparams.size(),&Indparams[0]));
	//nodes.push_back(node);
	pmap[R] = node;
        if (is_query)
          node->Bound = CreateRelation(std::vector<Term>(), ctx.bool_val(false));
      }
    }

    // create the edges

    for(unsigned i = 0; i < clauses.size(); i++){
      Term clause = clauses[i];
      Term body = clause.arg(0);
      Term head = clause.arg(1);
      func_decl R(ctx);
      if (eq(head,ctx.bool_val(false)))
	R = fail_pred;
	//R = ctx.constant("@Fail", ctx.bool_sort()).decl();
      else get_relation(head,R);
      Node *Parent = pmap[R];
      std::vector<Term> Indparams;
      hash_set<ast> seen;
      for(unsigned j = 0; j < head.num_args(); j++){
	Term arg = head.arg(j);
	if(!is_variable(arg) || seen.find(arg) != seen.end()){
	  std::string name = std::string("@a_") + string_of_int(j);
	  Term var = ctx.constant(name.c_str(),arg.get_sort());
	  body = body && (arg == var);
	  arg = var;
	}
        seen.insert(arg);
	Indparams.push_back(arg);
      }

      // We extract the relparams positionally

      std::vector<func_decl> Relparams;
      hash_map<ast,Term> scan_memo;
      std::vector<Node *> Children;
      body = ScanBody(scan_memo,body,pmap,Relparams,Children);
      Term labeled = body;
      std::vector<label_struct > lbls;  // TODO: throw this away for now
      body = RemoveLabels(body,lbls);
      body = body.simplify();

      // Create the edge
      Transformer T = CreateTransformer(Relparams,Indparams,body);
      Edge *edge = CreateEdge(Parent,T,Children);
      edge->labeled = labeled;; // remember for label extraction
      // edges.push_back(edge);
    }
  }



  void RPFP::WriteSolution(std::ostream &s){
    for(unsigned i = 0; i < nodes.size(); i++){
      Node *node = nodes[i];
      Term asgn = (node->Name)(node->Annotation.IndParams) == node->Annotation.Formula;
      s << asgn << std::endl;
    }
  }
  
  void RPFP::WriteEdgeVars(Edge *e,  hash_map<ast,int> &memo, const Term &t, std::ostream &s)
  {
    std::pair<ast,int> foo(t,0);
    std::pair<hash_map<ast,int>::iterator, bool> bar = memo.insert(foo);
    // int &res = bar.first->second;
    if(!bar.second) return;
    hash_map<ast,Term>::iterator it = e->varMap.find(t);
    if (it != e->varMap.end()){
      return;
    }
    if (t.is_app())
      {
	func_decl f = t.decl();
	// int idx;
	int nargs = t.num_args();
	for(int i = 0; i < nargs; i++)
	  WriteEdgeVars(e, memo, t.arg(i),s);
	if (nargs == 0 && f.get_decl_kind() == Uninterpreted && !ls->is_constant(f)){
	  Term rename = HideVariable(t,e->number);
	  Term value = dualModel.eval(rename);
	  s << " (= " << t << " " << value << ")\n";
	}
      }
    else if (t.is_quantifier())
      WriteEdgeVars(e,memo,t.body(),s);
    return;
  }

  void RPFP::WriteEdgeAssignment(std::ostream &s, Edge *e){
    s << "(\n";
    hash_map<ast, int> memo;
    WriteEdgeVars(e, memo, e->F.Formula ,s);
    s << ")\n";
  }

  void RPFP::WriteCounterexample(std::ostream &s, Node *node){
    for(unsigned i = 0; i < node->Outgoing->Children.size(); i++){
      Node *child = node->Outgoing->Children[i];
      if(!Empty(child))
	WriteCounterexample(s,child);
    }
    s << "(" << node->number << " : " << EvalNode(node) << " <- ";
    for(unsigned i = 0; i < node->Outgoing->Children.size(); i++){
      Node *child = node->Outgoing->Children[i];
      if(!Empty(child))
	s << " " << node->Outgoing->Children[i]->number;
    }
    s << ")" << std::endl;
    WriteEdgeAssignment(s,node->Outgoing);
  }

  RPFP::Term RPFP::ToRuleRec(Edge *e,  hash_map<ast,Term> &memo, const Term &t, std::vector<expr> &quants)
  {
    std::pair<ast,Term> foo(t,expr(ctx));
    std::pair<hash_map<ast,Term>::iterator, bool> bar = memo.insert(foo);
    Term &res = bar.first->second;
    if(!bar.second) return res;
    if (t.is_app())
      {
	func_decl f = t.decl();
	// int idx;
	std::vector<Term> args;
	int nargs = t.num_args();
	for(int i = 0; i < nargs; i++)
	  args.push_back(ToRuleRec(e, memo, t.arg(i),quants));
	hash_map<func_decl,int>::iterator rit = e->relMap.find(f);                 
	if(rit != e->relMap.end()){
	  Node* child = e->Children[rit->second];
	  FuncDecl op = child->Name;
	  res = op(args.size(),&args[0]);
	}
	else {
	  res = f(args.size(),&args[0]);
	  if(nargs == 0 && t.decl().get_decl_kind() == Uninterpreted)
	    quants.push_back(t);
	}
      }
    else if (t.is_quantifier())
      {
	Term body = ToRuleRec(e,memo,t.body(),quants);
	res = CloneQuantifier(t,body);
      }
    else res = t;
    return res;
  }

  
  void RPFP::ToClauses(std::vector<Term> &cnsts, FileFormat format){
    cnsts.resize(edges.size());
    for(unsigned i = 0; i < edges.size(); i++){
      Edge *edge = edges[i];
      SetEdgeMaps(edge);
      std::vector<expr> quants;
      hash_map<ast,Term> memo;
      Term lhs = ToRuleRec(edge, memo, edge->F.Formula,quants);
      Term rhs = (edge->Parent->Name)(edge->F.IndParams.size(),&edge->F.IndParams[0]);
      for(unsigned j = 0; j < edge->F.IndParams.size(); j++)
	ToRuleRec(edge,memo,edge->F.IndParams[j],quants); // just to get quants
      Term cnst = implies(lhs,rhs);
#if 0
      for(unsigned i = 0; i < quants.size(); i++){
        std::cout << expr(ctx,(Z3_ast)quants[i]) << " : " << sort(ctx,Z3_get_sort(ctx,(Z3_ast)quants[i])) << std::endl;
      }
#endif
      if(format != DualityFormat)
	cnst= forall(quants,cnst);
      cnsts[i] = cnst;
    }
    // int num_rules = cnsts.size();
    
    for(unsigned i = 0; i < nodes.size(); i++){
      Node *node = nodes[i];
      if(!node->Bound.IsFull()){
	Term lhs = (node->Name)(node->Bound.IndParams) && !node->Bound.Formula;
	Term cnst = implies(lhs,ctx.bool_val(false));
	if(format != DualityFormat){
	  std::vector<expr> quants;
	  for(unsigned j = 0; j < node->Bound.IndParams.size(); j++)
	    quants.push_back(node->Bound.IndParams[j]);
	  if(format == HornFormat)
	    cnst= exists(quants,!cnst);
	  else
	    cnst= forall(quants, cnst);
	}
	cnsts.push_back(cnst);
      }
    }
    
  }


RPFP::~RPFP(){
    for(unsigned i = 0; i < nodes.size(); i++)
      delete nodes[i];
    for(unsigned i = 0; i < edges.size(); i++)
      delete edges[i];
  }
}

#if 0
void show_ast(expr *a){
  std::cout << *a;
}
#endif
