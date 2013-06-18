/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    duality_dl_interface.cpp

Abstract:

    SMT2 interface for Duality

Author:

    Krystof Hoder (t-khoder) 2011-9-22.
    Modified by Ken McMIllan (kenmcmil) 2013-4-18.

Revision History:

--*/

#include "dl_cmds.h"
#include "dl_context.h"
#include "dl_mk_coi_filter.h"
#include "dl_mk_interp_tail_simplifier.h"
#include "dl_mk_subsumption_checker.h"
#include "dl_mk_rule_inliner.h"
#include "dl_rule.h"
#include "dl_rule_transformer.h"
#include "dl_mk_extract_quantifiers.h"
#include "smt2parser.h"
#include "duality_dl_interface.h"
#include "dl_rule_set.h"
#include "dl_mk_slice.h"
#include "dl_mk_unfold.h"
#include "dl_mk_coalesce.h"
#include "expr_abstract.h"
#include "model_smt2_pp.h"
#include "model_v2_pp.h"

// template class symbol_table<family_id>;


#include "duality.h"
#include "duality_profiling.h"

// using namespace Duality;

namespace Duality {

  enum DualityStatus {StatusModel, StatusRefutation, StatusUnknown, StatusNull};

  class duality_data {
  public:
    context ctx;
    RPFP::LogicSolver *ls;
    RPFP *rpfp;
    
    DualityStatus status;
    std::vector<expr> clauses;
    std::vector<std::vector<RPFP::label_struct> > clause_labels;
    hash_map<RPFP::Edge *,int> map;  // edges to clauses
    Solver::Counterexample cex;

    duality_data(ast_manager &_m) : ctx(_m,config(params_ref())) {
      ls = 0;
      rpfp = 0;
      status = StatusNull;
    }
    ~duality_data(){
      if(rpfp)
	dealloc(rpfp);
      if(ls)
	dealloc(ls);
      if(cex.tree)
	delete cex.tree;
    }
  };


dl_interface::dl_interface(datalog::context& dl_ctx) :  m_ctx(dl_ctx)

{
  _d = 0;
}


dl_interface::~dl_interface() {
  if(_d)
    dealloc(_d);
}


//
// Check if the new rules are weaker so that we can 
// re-use existing context.
// 
#if 0
void dl_interface::check_reset() {
  // TODO
    datalog::rule_ref_vector const& new_rules = m_ctx.get_rules().get_rules();
    datalog::rule_ref_vector const& old_rules = m_old_rules.get_rules();  
    bool is_subsumed = !old_rules.empty();
    for (unsigned i = 0; is_subsumed && i < new_rules.size(); ++i) {
        is_subsumed = false;
        for (unsigned j = 0; !is_subsumed && j < old_rules.size(); ++j) {
            if (m_ctx.check_subsumes(*old_rules[j], *new_rules[i])) {
                is_subsumed = true;
            }
        }
        if (!is_subsumed) {
            TRACE("pdr", new_rules[i]->display(m_ctx, tout << "Fresh rule "););
            m_context->reset();
        }
    }
    m_old_rules.reset();
    m_old_rules.add_rules(new_rules.size(), new_rules.c_ptr());
}
#endif


lbool dl_interface::query(::expr * query) {

  // we restore the initial state in the datalog context
  m_ctx.ensure_opened();

  // if there is old data, get the cex and dispose (later)
  Solver::Counterexample old_cex;
  duality_data *old_data = _d;
  if(old_data)
    old_cex = old_data->cex;

  // make a new problem and solver
  _d = alloc(duality_data,m_ctx.get_manager());
  _d->ls = alloc(RPFP::iZ3LogicSolver,_d->ctx);
  _d->rpfp = alloc(RPFP,_d->ls);



  expr_ref_vector rules(m_ctx.get_manager());
  svector< ::symbol> names;  
  // m_ctx.get_rules_as_formulas(rules, names);
   m_ctx.get_raw_rule_formulas(rules, names);

  // get all the rules as clauses
  std::vector<expr> &clauses = _d->clauses;
  clauses.clear();
  for (unsigned i = 0; i < rules.size(); ++i) {
    expr e(_d->ctx,rules[i].get());
    clauses.push_back(e);
  }
  
  // turn the query into a clause
  expr q(_d->ctx,m_ctx.bind_variables(query,false));
  
  std::vector<sort> b_sorts;
  std::vector<symbol> b_names;
  if (q.is_quantifier() && !q.is_quantifier_forall()) {
    int bound = q.get_quantifier_num_bound();
    for(int j = 0; j < bound; j++){
      b_sorts.push_back(q.get_quantifier_bound_sort(j));
      b_names.push_back(q.get_quantifier_bound_name(j));
    }
    q = q.arg(0);
  }

  expr qc = implies(q,_d->ctx.bool_val(false));
  qc = _d->ctx.make_quant(Forall,b_sorts,b_names,qc);
  clauses.push_back(qc);
  
  // get the background axioms
  unsigned num_asserts = m_ctx.get_num_assertions();
  for (unsigned i = 0; i < num_asserts; ++i) {
    expr e(_d->ctx,m_ctx.get_assertion(i));
    _d->rpfp->AssertAxiom(e);
  }
  
  // creates 1-1 map between clauses and rpfp edges
  _d->rpfp->FromClauses(clauses);

  // populate the edge-to-clause map
  for(unsigned i = 0; i < _d->rpfp->edges.size(); ++i)
    _d->map[_d->rpfp->edges[i]] = i;
     
  // create a solver object

  Solver *rs = Solver::Create("duality", _d->rpfp);

  rs->LearnFrom(old_cex); // new solver gets hints from old cex

  // set its options
  IF_VERBOSE(1, rs->SetOption("report","1"););
  rs->SetOption("full_expand",m_ctx.get_params().full_expand() ? "1" : "0");
  rs->SetOption("no_conj",m_ctx.get_params().no_conj() ? "1" : "0");
  rs->SetOption("feasible_edges",m_ctx.get_params().feasible_edges() ? "1" : "0");
  rs->SetOption("use_underapprox",m_ctx.get_params().use_underapprox() ? "1" : "0");
  rs->SetOption("stratified_inlining",m_ctx.get_params().stratified_inlining() ? "1" : "0");
  unsigned rb = m_ctx.get_params().recursion_bound();
  if(rb != UINT_MAX){
    std::ostringstream os; os << rb;
    rs->SetOption("recursion_bound", os.str());
  }

  // Solve!
  bool ans;
  try {
    ans = rs->Solve();
  }
  catch (Duality::solver::cancel_exception &exn){
    throw default_exception("duality canceled");
  }
  
  // profile!

  if(m_ctx.get_params().profile())
    print_profile(std::cout);

  // save the result and counterexample if there is one
  _d->status = ans ? StatusModel : StatusRefutation;
  _d->cex = rs->GetCounterexample();
  
  if(old_data){
    old_data->cex.tree = 0; // we own it now
    dealloc(old_data);
  }


  dealloc(rs);

  // true means the RPFP problem is SAT, so the query is UNSAT
  return ans ? l_false : l_true;
}

expr_ref dl_interface::get_cover_delta(int level, ::func_decl* pred_orig) {
    SASSERT(false);
    return expr_ref(m_ctx.get_manager());
}

  void dl_interface::add_cover(int level, ::func_decl* pred, ::expr* property) {
    SASSERT(false);
}

  unsigned dl_interface::get_num_levels(::func_decl* pred) {
    SASSERT(false);
    return 0;
}

  void dl_interface::collect_statistics(::statistics& st) const {
}

void dl_interface::reset_statistics() {
}

static hash_set<func_decl> *local_func_decls;

static void print_proof(dl_interface *d, std::ostream& out, Solver::Counterexample &cex) {
  context &ctx = d->dd()->ctx;
  RPFP::Node &node = *cex.root;
  RPFP::Edge &edge = *node.Outgoing;
  
  // first, prove the children (that are actually used)

  for(unsigned i = 0; i < edge.Children.size(); i++){
    if(!cex.tree->Empty(edge.Children[i])){
      Solver::Counterexample foo = cex;
      foo.root = edge.Children[i];
      print_proof(d,out,foo);
    }
  }

  // print the label and the proved fact

  out << "(step s!" << node.number;
  out << " (" << node.Name.name();
  for(unsigned i = 0; i < edge.F.IndParams.size(); i++)
    out << " " << cex.tree->Eval(&edge,edge.F.IndParams[i]);
  out << ")\n";

  // print the rule number

  out << " rule!" << node.Outgoing->map->number;

  // print the substitution

  out << "  (subst\n";
  RPFP::Edge *orig_edge = edge.map;
  int orig_clause = d->dd()->map[orig_edge];
  expr &t = d->dd()->clauses[orig_clause];
  if (t.is_quantifier() && t.is_quantifier_forall()) {
    int bound = t.get_quantifier_num_bound();
    std::vector<sort> sorts;
    std::vector<symbol> names;
    hash_map<int,expr> subst;
    for(int j = 0; j < bound; j++){
      sort the_sort = t.get_quantifier_bound_sort(j);
      symbol name = t.get_quantifier_bound_name(j);
      expr skolem = ctx.constant(symbol(ctx,name),sort(ctx,the_sort));
      out << "    (= " << skolem << " " << cex.tree->Eval(&edge,skolem) << ")\n";
      expr local_skolem = cex.tree->Localize(&edge,skolem);
      (*local_func_decls).insert(local_skolem.decl());
    }
  }
  out << "  )\n";
  
  out << "  (labels";
  std::vector<symbol> labels;
  cex.tree->GetLabels(&edge,labels);
  for(unsigned j = 0; j < labels.size(); j++){
    out << " " << labels[j];
  }
  
  out << "  )\n";

  // reference the proofs of all the children, in syntactic order
  // "true" means the child is not needed
  
  out << "  (ref ";
  for(unsigned i = 0; i < edge.Children.size(); i++){
    if(!cex.tree->Empty(edge.Children[i]))
      out << " s!" << edge.Children[i]->number;
    else
      out << " true";
  }
  out << "  )";
  out << ")\n";
}


void dl_interface::display_certificate(std::ostream& out) {
  if(_d->status == StatusModel){
    ast_manager &m = m_ctx.get_manager();
    model_ref md = get_model();
    model_smt2_pp(out, m, *md.get(), 0); 
  }
  else if(_d->status == StatusRefutation){
    out << "(derivation\n";
    // negation of the query is the last clause -- prove it
    hash_set<func_decl> locals;
    local_func_decls = &locals;
    print_proof(this,out,_d->cex);
    out << ")\n";
    out << "(model \n\"";
    ::model mod(m_ctx.get_manager());
    model orig_model = _d->cex.tree->dualModel;
    for(unsigned i = 0; i < orig_model.num_consts(); i++){
      func_decl cnst = orig_model.get_const_decl(i);
      if(locals.find(cnst) == locals.end()){
	expr thing = orig_model.get_const_interp(cnst);
	mod.register_decl(to_func_decl(cnst.raw()),to_expr(thing.raw()));
      }
    }
    for(unsigned i = 0; i < orig_model.num_funcs(); i++){
      func_decl cnst = orig_model.get_func_decl(i);
      if(locals.find(cnst) == locals.end()){
	func_interp thing = orig_model.get_func_interp(cnst);
	::func_interp *thing_raw = thing;
	mod.register_decl(to_func_decl(cnst.raw()),thing_raw->copy());
      }
    }
    model_v2_pp(out,mod);
    out << "\")\n";
  }
}

expr_ref dl_interface::get_answer() {
    SASSERT(false);
    return expr_ref(m_ctx.get_manager());
}

void dl_interface::cancel() {
  if(_d && _d->ls)
    _d->ls->cancel();
}

void dl_interface::cleanup() {
}

void dl_interface::updt_params() {
}

model_ref dl_interface::get_model() {
  ast_manager &m = m_ctx.get_manager();
  model_ref md(alloc(::model, m));
  std::vector<RPFP::Node *> &nodes = _d->rpfp->nodes;
  expr_ref_vector conjs(m);
  for (unsigned i = 0; i < nodes.size(); ++i) {
    RPFP::Node *node = nodes[i];
    func_decl &pred = node->Name;
    expr_ref prop(m);
    prop = to_expr(node->Annotation.Formula);
    std::vector<expr> &params = node->Annotation.IndParams;
    expr_ref q(m);
    expr_ref_vector sig_vars(m);
    for (unsigned j = 0; j < params.size(); ++j)
      sig_vars.push_back(params[params.size()-j-1]); // TODO: why backwards?
    expr_abstract(m, 0, sig_vars.size(), sig_vars.c_ptr(), prop, q);
    if (params.empty()) {
      md->register_decl(pred, q);
    }
    else {
      ::func_interp* fi = alloc(::func_interp, m, params.size());
      fi->set_else(q);
      md->register_decl(pred, fi);
    }
  }
  return md;
}
  
proof_ref dl_interface::get_proof() {
  return proof_ref(m_ctx.get_manager());
}
}
