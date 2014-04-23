/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    wrapper.cpp

Abstract:

   wrap various objects in the style expected by duality

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

#include "duality_wrapper.h"
#include <iostream>
#include "smt_solver.h"
#include "iz3interp.h"
#include "statistics.h"
#include "expr_abstract.h"
#include "stopwatch.h"
#include "model_smt2_pp.h"
#include "qe_lite.h"

namespace Duality {

  solver::solver(Duality::context& c, bool _extensional, bool models) : object(c), the_model(c) {
    params_ref p;
    p.set_bool("proof", true); // this is currently useless
    if(models)
      p.set_bool("model", true); 
    p.set_bool("unsat_core", true); 
    bool mbqi = c.get_config().get().get_bool("mbqi",true);
    p.set_bool("mbqi",mbqi); // just to test
    p.set_str("mbqi.id","itp"); // use mbqi for quantifiers in interpolants
    p.set_uint("mbqi.max_iterations",1); // use mbqi for quantifiers in interpolants
    extensional = mbqi && (true || _extensional);
    if(extensional)
      p.set_bool("array.extensional",true);
    scoped_ptr<solver_factory> sf = mk_smt_solver_factory();
    m_solver = (*sf)(m(), p, true, true, true, ::symbol::null);
    m_solver->updt_params(p); // why do we have to do this?
    canceled = false;
    m_mode = m().proof_mode();
  }

expr context::constant(const std::string &name, const sort &ty){ 
  symbol s = str_symbol(name.c_str());
  return cook(m().mk_const(m().mk_const_decl(s, ty)));
}

expr context::make(decl_kind op, int n, ::expr **args){
  switch(op) {
  case True:     return mki(m_basic_fid,OP_TRUE,n,args);
  case False:    return mki(m_basic_fid,OP_FALSE,n,args);
  case Equal:    return mki(m_basic_fid,OP_EQ,n,args);
  case Distinct: return mki(m_basic_fid,OP_DISTINCT,n,args);
  case Ite:      return mki(m_basic_fid,OP_ITE,n,args);
  case And:      return mki(m_basic_fid,OP_AND,n,args);
  case Or:       return mki(m_basic_fid,OP_OR,n,args);
  case Iff:      return mki(m_basic_fid,OP_IFF,n,args);
  case Xor:      return mki(m_basic_fid,OP_XOR,n,args);
  case Not:      return mki(m_basic_fid,OP_NOT,n,args);
  case Implies:  return mki(m_basic_fid,OP_IMPLIES,n,args);
  case Oeq:      return mki(m_basic_fid,OP_OEQ,n,args);
  case Interp:   return mki(m_basic_fid,OP_INTERP,n,args);
  case Leq:      return mki(m_arith_fid,OP_LE,n,args);
  case Geq:      return mki(m_arith_fid,OP_GE,n,args);
  case Lt:       return mki(m_arith_fid,OP_LT,n,args);
  case Gt:       return mki(m_arith_fid,OP_GT,n,args);
  case Plus:     return mki(m_arith_fid,OP_ADD,n,args);
  case Sub:      return mki(m_arith_fid,OP_SUB,n,args);
  case Uminus:   return mki(m_arith_fid,OP_UMINUS,n,args);
  case Times:    return mki(m_arith_fid,OP_MUL,n,args);
  case Div:      return mki(m_arith_fid,OP_DIV,n,args);
  case Idiv:     return mki(m_arith_fid,OP_IDIV,n,args);
  case Rem:      return mki(m_arith_fid,OP_REM,n,args);
  case Mod:      return mki(m_arith_fid,OP_MOD,n,args);
  case Power:    return mki(m_arith_fid,OP_POWER,n,args);
  case ToReal:   return mki(m_arith_fid,OP_TO_REAL,n,args);
  case ToInt:    return mki(m_arith_fid,OP_TO_INT,n,args);
  case IsInt:    return mki(m_arith_fid,OP_IS_INT,n,args);
  case Store:    return mki(m_array_fid,OP_STORE,n,args);
  case Select:   return mki(m_array_fid,OP_SELECT,n,args);
  case ConstArray: return mki(m_array_fid,OP_CONST_ARRAY,n,args);
  case ArrayDefault: return mki(m_array_fid,OP_ARRAY_DEFAULT,n,args);
  case ArrayMap: return mki(m_array_fid,OP_ARRAY_MAP,n,args);
  case SetUnion: return mki(m_array_fid,OP_SET_UNION,n,args);
  case SetIntersect: return mki(m_array_fid,OP_SET_INTERSECT,n,args);
  case SetDifference: return mki(m_array_fid,OP_SET_DIFFERENCE,n,args);
  case SetComplement: return mki(m_array_fid,OP_SET_COMPLEMENT,n,args);
  case SetSubSet: return mki(m_array_fid,OP_SET_SUBSET,n,args);
  case AsArray:   return mki(m_array_fid,OP_AS_ARRAY,n,args);
  default:
    assert(0);
    return expr(*this);
  }
}

  expr context::mki(family_id fid, ::decl_kind dk, int n, ::expr **args){
    return cook(m().mk_app(fid, dk, 0, 0, n, (::expr **)args));        
}

expr context::make(decl_kind op, const std::vector<expr> &args){
  static std::vector< ::expr*> a(10);
  if(a.size() < args.size())
    a.resize(args.size());
  for(unsigned i = 0; i < args.size(); i++)
    a[i] = to_expr(args[i].raw());
  return make(op,args.size(), args.size() ? &a[0] : 0);
}

expr context::make(decl_kind op){
  return make(op,0,0);
}

expr context::make(decl_kind op, const expr &arg0){
  ::expr *a = to_expr(arg0.raw());
  return make(op,1,&a);
}

expr context::make(decl_kind op, const expr &arg0, const expr &arg1){
  ::expr *args[2];
  args[0] = to_expr(arg0.raw());
  args[1] = to_expr(arg1.raw());
  return make(op,2,args);
}

expr context::make(decl_kind op, const expr &arg0, const expr &arg1, const expr &arg2){
  ::expr *args[3];
  args[0] = to_expr(arg0.raw());
  args[1] = to_expr(arg1.raw());
  args[2] = to_expr(arg2.raw());
  return make(op,3,args);
}

expr context::make_quant(decl_kind op, const std::vector<expr> &bvs, const expr &body){
  if(bvs.size() == 0) return body;
  std::vector< ::expr *> foo(bvs.size());


  std::vector< ::symbol> names;
  std::vector< ::sort *> types;
  std::vector< ::expr *>  bound_asts;
  unsigned num_bound = bvs.size();

  for (unsigned i = 0; i < num_bound; ++i) {
    app* a = to_app(bvs[i].raw());
    ::symbol s(to_app(a)->get_decl()->get_name());
    names.push_back(s);
    types.push_back(m().get_sort(a));
    bound_asts.push_back(a);
  }
  expr_ref abs_body(m());
  expr_abstract(m(), 0, num_bound, &bound_asts[0], to_expr(body.raw()), abs_body);
  expr_ref result(m());
  result = m().mk_quantifier(
			     op == Forall, 
			     names.size(), &types[0], &names[0], abs_body.get(),            
			     0, 
			     ::symbol(),
			     ::symbol(),
			     0, 0,
			     0, 0
			     );
  return cook(result.get());
}

expr context::make_quant(decl_kind op, const std::vector<sort> &_sorts, const std::vector<symbol> &_names, const expr &body){
  if(_sorts.size() == 0) return body;


  std::vector< ::symbol> names;
  std::vector< ::sort *> types;
  std::vector< ::expr *>  bound_asts;
  unsigned num_bound = _sorts.size();

  for (unsigned i = 0; i < num_bound; ++i) {
    names.push_back(_names[i]);
    types.push_back(to_sort(_sorts[i].raw()));
  }
  expr_ref result(m());
  result = m().mk_quantifier(
			     op == Forall, 
			     names.size(), &types[0], &names[0], to_expr(body.raw()),            
			     0, 
			     ::symbol(),
			     ::symbol(),
			     0, 0,
			     0, 0
			     );
  return cook(result.get());
}


  decl_kind func_decl::get_decl_kind() const {
    return ctx().get_decl_kind(*this);
  }

  decl_kind context::get_decl_kind(const func_decl &t){
    ::func_decl *d = to_func_decl(t.raw());
    if (null_family_id == d->get_family_id())
      return Uninterpreted;
    // return (opr)d->get_decl_kind();
    if (m_basic_fid == d->get_family_id()) {
      switch(d->get_decl_kind()) {
      case OP_TRUE:     return True;
      case OP_FALSE:    return False;
      case OP_EQ:       return Equal;
      case OP_DISTINCT: return Distinct;
      case OP_ITE:      return Ite;
      case OP_AND:      return And;
      case OP_OR:       return Or;
      case OP_IFF:      return Iff;
      case OP_XOR:      return Xor;
      case OP_NOT:      return Not;
      case OP_IMPLIES:  return Implies;
      case OP_OEQ:      return Oeq;
      case OP_INTERP:   return Interp;
      default:
	return OtherBasic;
      }
    }
    if (m_arith_fid == d->get_family_id()) {
      switch(d->get_decl_kind()) {
      case OP_LE: return Leq;
      case OP_GE: return Geq;
      case OP_LT: return Lt;
      case OP_GT: return Gt;
      case OP_ADD: return Plus;
      case OP_SUB: return Sub;
      case OP_UMINUS: return Uminus;
      case OP_MUL: return Times;
      case OP_DIV: return Div;
      case OP_IDIV: return Idiv;
      case OP_REM: return Rem;
      case OP_MOD: return Mod;
      case OP_POWER: return Power;
      case OP_TO_REAL: return ToReal;
      case OP_TO_INT: return ToInt;
      case OP_IS_INT: return IsInt;
      default:
	return OtherArith;
      }
    }
    if (m_array_fid == d->get_family_id()) {
      switch(d->get_decl_kind()) {
      case OP_STORE: return Store;
      case OP_SELECT: return Select;
      case OP_CONST_ARRAY: return ConstArray;
      case OP_ARRAY_DEFAULT: return ArrayDefault;
      case OP_ARRAY_MAP: return ArrayMap;
      case OP_SET_UNION: return SetUnion;
      case OP_SET_INTERSECT: return SetIntersect;
      case OP_SET_DIFFERENCE: return SetDifference;
      case OP_SET_COMPLEMENT: return SetComplement;
      case OP_SET_SUBSET: return SetSubSet;
      case OP_AS_ARRAY: return AsArray;
      default:
	return OtherArray;
      }
    }
    
    return Other;
  }


  sort_kind context::get_sort_kind(const sort &s){
    family_id fid = to_sort(s.raw())->get_family_id();
    ::decl_kind k   = to_sort(s.raw())->get_decl_kind();
    if (m().is_uninterp(to_sort(s.raw()))) {
      return UninterpretedSort;
    }
    else if (fid == m_basic_fid && k == BOOL_SORT) {
      return BoolSort;
    }
    else if (fid == m_arith_fid && k == INT_SORT) {
      return IntSort;
    }
    else if (fid == m_arith_fid && k == REAL_SORT) {
      return RealSort;
    }
    else if (fid == m_array_fid && k == ARRAY_SORT) {
      return ArraySort;
    }
    else {
      return UnknownSort;
    }
  }

  expr func_decl::operator()(unsigned n, expr const * args) const {
    std::vector< ::expr *> _args(n);
    for(unsigned i = 0; i < n; i++)
      _args[i] = to_expr(args[i].raw());
    return ctx().cook(m().mk_app(to_func_decl(raw()),n,&_args[0]));
  }

  int solver::get_num_decisions(){
    ::statistics st;
    m_solver->collect_statistics(st);
    std::ostringstream ss;
    st.display(ss);
    std::string stats = ss.str();
    int pos = stats.find("decisions:");
    if(pos < 0) return 0; // for some reason, decisions are not reported if there are none
    pos += 10;
    int end = stats.find('\n',pos);
    std::string val = stats.substr(pos,end-pos);
    return atoi(val.c_str());
  }

  void context::print_expr(std::ostream &s, const ast &e){
    s << mk_pp(e.raw(), m());
  }


  expr expr::simplify(const params &_p) const {
    ::expr * a = to_expr(raw());
    params_ref p = _p.get();
    th_rewriter m_rw(m(), p);
    expr_ref    result(m());
    m_rw(a, result);
    return ctx().cook(result);
  }

  expr expr::simplify() const {
    params p;
    return simplify(p);
  }
  
  expr context::make_var(int idx, const sort &s){
    ::sort * a = to_sort(s.raw());
    return cook(m().mk_var(idx,a));
  }


  expr expr::qe_lite() const {
    ::qe_lite qe(m());
    expr_ref result(to_expr(raw()),m());
    proof_ref pf(m());
    qe(result,pf);
    return ctx().cook(result);
  }

  expr expr::qe_lite(const std::set<int> &idxs, bool index_of_bound) const {
    ::qe_lite qe(m());
    expr_ref result(to_expr(raw()),m());
    proof_ref pf(m());
    uint_set uis;
    for(std::set<int>::const_iterator it=idxs.begin(), en = idxs.end(); it != en; ++it)
      uis.insert(*it);
    qe(uis,index_of_bound,result);
    return ctx().cook(result);
  }

  expr clone_quantifier(const expr &q, const expr &b){
    return q.ctx().cook(q.m().update_quantifier(to_quantifier(q.raw()), to_expr(b.raw())));
  }

  expr clone_quantifier(const expr &q, const expr &b, const std::vector<expr> &patterns){
    quantifier *thing = to_quantifier(q.raw());
    bool is_forall = thing->is_forall();
    unsigned num_patterns = patterns.size();
    std::vector< ::expr *> _patterns(num_patterns);
    for(unsigned i = 0; i < num_patterns; i++)
      _patterns[i] = to_expr(patterns[i].raw());
    return q.ctx().cook(q.m().update_quantifier(thing, is_forall, num_patterns, &_patterns[0], to_expr(b.raw())));
  }

  expr clone_quantifier(decl_kind dk, const expr &q, const expr &b){
    quantifier *thing = to_quantifier(q.raw());
    bool is_forall = dk == Forall;
    return q.ctx().cook(q.m().update_quantifier(thing, is_forall, to_expr(b.raw())));
  }

  void expr::get_patterns(std::vector<expr> &pats) const {
    quantifier *thing = to_quantifier(raw());
    unsigned num_patterns = thing->get_num_patterns();
    :: expr * const *it = thing->get_patterns();
    pats.resize(num_patterns);
    for(unsigned i = 0; i < num_patterns; i++)
      pats[i] = expr(ctx(),it[i]);
  }


  unsigned func_decl::arity() const {
    return (to_func_decl(raw())->get_arity());
  }

  sort func_decl::domain(unsigned i) const {
    return sort(ctx(),(to_func_decl(raw())->get_domain(i)));
  }

  sort func_decl::range() const {
    return sort(ctx(),(to_func_decl(raw())->get_range()));
  }

  func_decl context::fresh_func_decl(char const * prefix, const std::vector<sort> &domain, sort const & range){
    std::vector < ::sort * > _domain(domain.size());
    for(unsigned i = 0; i < domain.size(); i++)
      _domain[i] = to_sort(domain[i].raw());
    ::func_decl* d = m().mk_fresh_func_decl(prefix, 
					     _domain.size(), 
					     &_domain[0],
					     to_sort(range.raw()));
    return func_decl(*this,d);
  }

  func_decl context::fresh_func_decl(char const * prefix, sort const & range){
    ::func_decl* d = m().mk_fresh_func_decl(prefix, 
					    0, 
					    0,
					    to_sort(range.raw()));
    return func_decl(*this,d);
  }



#if 0


  lbool interpolating_solver::interpolate(
					   const std::vector<expr> &assumptions,
					   std::vector<expr> &interpolants,
					   model &model,
					   Z3_literals &labels,
					   bool incremental)
  {
    Z3_model _model = 0;
    Z3_literals _labels = 0;
    Z3_lbool lb;
    std::vector<Z3_ast> _assumptions(assumptions.size());
    std::vector<Z3_ast> _interpolants(assumptions.size()-1);
    for(unsigned i = 0; i < assumptions.size(); i++)
      _assumptions[i] = assumptions[i];
    std::vector<Z3_ast> _theory(theory.size());
    for(unsigned i = 0; i < theory.size(); i++)
      _theory[i] = theory[i];

    lb = Z3_interpolate(
			ctx(),
			_assumptions.size(),
			&_assumptions[0],
			0,
			0,
			&_interpolants[0],
			&_model,
			&_labels,
			incremental,
			_theory.size(),
			&_theory[0]
			);
    
    if(lb == Z3_L_FALSE){
      interpolants.resize(_interpolants.size());
      for (unsigned i = 0; i < _interpolants.size(); ++i) {
	interpolants[i] = expr(ctx(),_interpolants[i]);
      }
    }      
    
    if (_model) {
      model = iz3wrapper::model(ctx(), _model);
    }
    
    if(_labels){
      labels = _labels;
    }
    
    return lb;
  }

#endif
  
  static int linearize_assumptions(int num,
				   TermTree *assumptions,
				   std::vector<std::vector <expr> > &linear_assumptions, 
				   std::vector<int> &parents){
    for(unsigned i = 0; i < assumptions->getChildren().size(); i++)
      num = linearize_assumptions(num, assumptions->getChildren()[i], linear_assumptions, parents);
    // linear_assumptions[num].push_back(assumptions->getTerm());
    for(unsigned i = 0; i < assumptions->getChildren().size(); i++)
      parents[assumptions->getChildren()[i]->getNumber()] = num;
    parents[num] = SHRT_MAX; // in case we have no parent
    linear_assumptions[num].push_back(assumptions->getTerm());
    std::vector<expr> &ts = assumptions->getTerms();
    for(unsigned i = 0; i < ts.size(); i++)
      linear_assumptions[num].push_back(ts[i]);
    return num + 1;
  }

  static int unlinearize_interpolants(int num,
				      TermTree* assumptions, 
				      const std::vector<expr> &interpolant,
				      TermTree * &tree_interpolant)
  {
    std::vector<TermTree *> chs(assumptions->getChildren().size());
    for(unsigned i = 0; i < assumptions->getChildren().size(); i++)
      num = unlinearize_interpolants(num, assumptions->getChildren()[i], interpolant,chs[i]);
    expr f;
    if(num < (int)interpolant.size()) // last interpolant is missing, presumed false
      f = interpolant[num];
    tree_interpolant = new TermTree(f,chs);
    return num + 1;
  }


  lbool interpolating_solver::interpolate_tree(TermTree *assumptions,
						TermTree *&interpolant,
						model &model,
						literals &labels,
						bool incremental
						)
  
  {
    int size = assumptions->number(0);
    std::vector<std::vector<expr> > linear_assumptions(size);
    std::vector<int> parents(size);
    linearize_assumptions(0,assumptions,linear_assumptions,parents);

    ptr_vector< ::ast> _interpolants(size-1);
    vector<ptr_vector< ::ast> >_assumptions(size);
    for(int i = 0; i < size; i++)
      for(unsigned j = 0; j < linear_assumptions[i].size(); j++)
	_assumptions[i].push_back(linear_assumptions[i][j]);
    ::vector<int> _parents; _parents.resize(parents.size());
    for(unsigned i = 0; i < parents.size(); i++)
      _parents[i] = parents[i];
    ptr_vector< ::ast> _theory(theory.size());
    for(unsigned i = 0; i < theory.size(); i++)
      _theory[i] = theory[i];
    
    
    if(!incremental){
      push();
      for(unsigned i = 0; i < linear_assumptions.size(); i++)
	for(unsigned j = 0; j < linear_assumptions[i].size(); j++)
	  add(linear_assumptions[i][j]);
    }
    
    check_result res = unsat;

    if(!m_solver->get_proof())
      res = check();
    
    if(res == unsat){

      interpolation_options_struct opts;
      if(weak_mode)
	opts.set("weak","1"); 
      
      ::ast *proof = m_solver->get_proof();
      iz3interpolate(m(),proof,_assumptions,_parents,_interpolants,_theory,&opts);
      
      std::vector<expr> linearized_interpolants(_interpolants.size());
      for(unsigned i = 0; i < _interpolants.size(); i++)
	linearized_interpolants[i] = expr(ctx(),_interpolants[i]);

      // since iz3interpolant returns interpolants with one ref count, we decrement here
      for(unsigned i = 0; i < _interpolants.size(); i++)
	m().dec_ref(_interpolants[i]);

      unlinearize_interpolants(0,assumptions,linearized_interpolants,interpolant);
      interpolant->setTerm(ctx().bool_val(false));
    }

    model_ref _m;
    m_solver->get_model(_m);
    model = Duality::model(ctx(),_m.get());
    
#if 0
    if(_labels){
      labels = _labels;
    }
#endif
    
    if(!incremental)
      pop();

    return (res == unsat) ? l_false : ((res == sat) ? l_true : l_undef);

  }


  void interpolating_solver::SetWeakInterpolants(bool weak){
    weak_mode = weak;
  }
  

  void interpolating_solver::SetPrintToFile(const std::string &filename){
    print_filename = filename;
  }

  void interpolating_solver::AssertInterpolationAxiom(const expr & t){
    add(t);
    theory.push_back(t);
  }


  void interpolating_solver::RemoveInterpolationAxiom(const expr & t){
    // theory.remove(t);
  }
  

  const char *interpolating_solver::profile(){
    // return Z3_interpolation_profile(ctx());
    return "";
  }

  
  static void get_assumptions_rec(stl_ext::hash_set<ast> &memo, const proof &pf, std::vector<expr> &assumps){
    if(memo.find(pf) != memo.end())return;
    memo.insert(pf);
    pfrule dk = pf.rule();
    if(dk == PR_ASSERTED){
      expr con = pf.conc();
      assumps.push_back(con);
    }
    else {
      unsigned nprems = pf.num_prems();
      for(unsigned i = 0; i < nprems; i++){
	proof arg = pf.prem(i);
	get_assumptions_rec(memo,arg,assumps);
      }
    }
  }

  void proof::get_assumptions(std::vector<expr> &assumps){
    stl_ext::hash_set<ast> memo;
    get_assumptions_rec(memo,*this,assumps);
  }


  void ast::show() const{
    std::cout << mk_pp(raw(), m()) << std::endl;
  }

  void model::show() const {
    model_smt2_pp(std::cout, m(), *m_model, 0);
    std::cout << std::endl;
  }
  
  void model::show_hash() const {
    std::ostringstream ss;
    model_smt2_pp(ss, m(), *m_model, 0);
    hash_space::hash<std::string> hasher;
    unsigned h = hasher(ss.str());
    std::cout << "model hash: " << h << "\n";
  }

  void solver::show() {
    unsigned n = m_solver->get_num_assertions();
    if(!n)
      return;
    ast_smt_pp pp(m());
    for (unsigned i = 0; i < n-1; ++i)
      pp.add_assumption(m_solver->get_assertion(i));
    pp.display_smt2(std::cout, m_solver->get_assertion(n-1));
  }

  void solver::print(const char *filename) {
    std::ofstream f(filename);
    unsigned n = m_solver->get_num_assertions();
    if(!n)
      return;
    ast_smt_pp pp(m());
    for (unsigned i = 0; i < n-1; ++i)
      pp.add_assumption(m_solver->get_assertion(i));
    pp.display_smt2(f, m_solver->get_assertion(n-1));
  }


  void solver::show_assertion_ids() {
#if 0
    unsigned n = m_solver->get_num_assertions();
    std::cerr << "assertion ids: ";
    for (unsigned i = 0; i < n-1; ++i)
      std::cerr << " " << m_solver->get_assertion(i)->get_id();
    std::cerr << "\n";
#else
    unsigned n = m_solver->get_num_assertions();
    std::cerr << "assertion ids hash: ";
    unsigned h = 0;
    for (unsigned i = 0; i < n-1; ++i)
      h += m_solver->get_assertion(i)->get_id();
    std::cerr << h << "\n";
#endif
  }

  void include_ast_show(ast &a){
    a.show();
  }

  void include_model_show(model &a){
    a.show();
  }

  void show_ast(::ast *a, ast_manager &m) {
    std::cout << mk_pp(a, m) << std::endl;
  }

  bool expr::is_label (bool &pos,std::vector<symbol> &names) const {
    buffer< ::symbol> _names;
    bool res = m().is_label(to_expr(raw()),pos,_names);
    if(res)
      for(unsigned i = 0; i < _names.size(); i++)
	names.push_back(symbol(ctx(),_names[i]));
    return res;
  }

  double current_time()
  {
    static stopwatch sw;
    static bool started = false;
    if(!started){
      sw.start();
	  started = true;
	}
    return sw.get_current_seconds();
  }

}




