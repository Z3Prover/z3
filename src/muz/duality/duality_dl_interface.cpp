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

#include "dl_context.h"
#include "dl_mk_coi_filter.h"
#include "dl_mk_interp_tail_simplifier.h"
#include "dl_mk_subsumption_checker.h"
#include "dl_mk_rule_inliner.h"
#include "dl_rule.h"
#include "dl_rule_transformer.h"
#include "smt2parser.h"
#include "duality_dl_interface.h"
#include "dl_rule_set.h"
#include "dl_mk_slice.h"
#include "dl_mk_unfold.h"
#include "dl_mk_coalesce.h"
#include "expr_abstract.h"
#include "model_smt2_pp.h"
#include "model_v2_pp.h"
#include "fixedpoint_params.hpp"
#include "used_vars.h"
#include "func_decl_dependencies.h"
#include "dl_transforms.h"

// template class symbol_table<family_id>;

#ifdef WIN32
#pragma warning(disable:4996)
#pragma warning(disable:4800)
#pragma warning(disable:4267)
#pragma warning(disable:4101)
#endif

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
        Solver *old_rs;
        Solver::Counterexample cex;

        duality_data(ast_manager &_m) : ctx(_m,config(params_ref())) {
            ls = 0;
            rpfp = 0;
            status = StatusNull;
            old_rs = 0;
        }
        ~duality_data(){
            if(old_rs)
                dealloc(old_rs);
            if(rpfp)
                dealloc(rpfp);
            if(ls)
                dealloc(ls);
        }
    };


    dl_interface::dl_interface(datalog::context& dl_ctx) :
        engine_base(dl_ctx.get_manager(), "duality"),
        m_ctx(dl_ctx)

    {
        _d = 0;
        //   dl_ctx.get_manager().toggle_proof_mode(PGM_FINE);
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
        duality_data *old_data = _d;
        Solver *old_rs = 0;
        if(old_data){
            old_rs = old_data->old_rs;
            old_rs->GetCounterexample().swap(old_data->cex);
        }

        scoped_proof generate_proofs_please(m_ctx.get_manager());

        // make a new problem and solver
        _d = alloc(duality_data,m_ctx.get_manager());
        _d->ctx.set("mbqi",m_ctx.get_params().duality_mbqi());
        _d->ls = alloc(RPFP::iZ3LogicSolver,_d->ctx);
        _d->rpfp = alloc(RPFP,_d->ls);



        expr_ref_vector rules(m_ctx.get_manager());
        svector< ::symbol> names;
        unsigned_vector bounds;
        // m_ctx.get_rules_as_formulas(rules, names);


        // If using SAS 2013 abstractiion, we need to perform some transforms
        expr_ref query_ref(m_ctx.get_manager());
        if(m_ctx.quantify_arrays()){
            datalog::rule_manager& rm = m_ctx.get_rule_manager();
            rm.mk_query(query, m_ctx.get_rules());
            apply_default_transformation(m_ctx);
            datalog::rule_set &rs = m_ctx.get_rules();
            if(m_ctx.get_rules().get_output_predicates().empty())
                query_ref = m_ctx.get_manager().mk_false();
            else {
                func_decl_ref query_pred(m_ctx.get_manager());
                query_pred = m_ctx.get_rules().get_output_predicate();
                ptr_vector<sort> sorts;
                unsigned nargs = query_pred.get()->get_arity();
                expr_ref_vector vars(m_ctx.get_manager());
                for(unsigned i = 0; i < nargs; i++){
                    ::sort *s = query_pred.get()->get_domain(i);
                    vars.push_back(m_ctx.get_manager().mk_var(nargs-1-i,s));
                }
                query_ref = m_ctx.get_manager().mk_app(query_pred.get(),nargs,vars.c_ptr());
                query = query_ref.get();
            }
            unsigned nrules = rs.get_num_rules();
            for(unsigned i = 0; i < nrules; i++){
                expr_ref f(m_ctx.get_manager());
                rm.to_formula(*rs.get_rule(i), f);
                rules.push_back(f);
            }
        }
        else
            m_ctx.get_raw_rule_formulas(rules, names, bounds);

        // get all the rules as clauses
        std::vector<expr> &clauses = _d->clauses;
        clauses.clear();
        for (unsigned i = 0; i < rules.size(); ++i) {
            expr e(_d->ctx,rules[i].get());
            clauses.push_back(e);
        }

        std::vector<sort> b_sorts;
        std::vector<symbol> b_names;
        used_vars uv;
        uv.process(query);
        unsigned nuv = uv.get_max_found_var_idx_plus_1();
        for(int i = nuv-1; i >= 0; i--){ // var indices are backward
            ::sort * s = uv.get(i);
            if(!s)
                s = _d->ctx.m().mk_bool_sort(); // missing var, whatever
            b_sorts.push_back(sort(_d->ctx,s));
            b_names.push_back(symbol(_d->ctx,::symbol(i))); // names?
        }

#if 0
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
#else
        expr q(_d->ctx,query);
#endif

        expr qc = implies(q,_d->ctx.bool_val(false));
        qc = _d->ctx.make_quant(Forall,b_sorts,b_names,qc);
        clauses.push_back(qc);
        bounds.push_back(UINT_MAX);

        // get the background axioms
        unsigned num_asserts = m_ctx.get_num_assertions();
        for (unsigned i = 0; i < num_asserts; ++i) {
            expr e(_d->ctx,m_ctx.get_assertion(i));
            _d->rpfp->AssertAxiom(e);
        }

        // make sure each predicate is the head of at least one clause
        func_decl_set heads;
        for(unsigned i = 0; i < clauses.size(); i++){
            expr cl = clauses[i];

            while(true){
                if(cl.is_app()){
                    decl_kind k = cl.decl().get_decl_kind();
                    if(k == Implies)
                        cl = cl.arg(1);
                    else {
                        heads.insert(cl.decl());
                        break;
                    }
                }
                else if(cl.is_quantifier())
                    cl = cl.body();
                else break;
            }
        }
        ast_ref_vector const &pinned = m_ctx.get_pinned();
        for(unsigned i = 0; i < pinned.size(); i++){
            ::ast *fa = pinned[i];
            if(is_func_decl(fa)){
                ::func_decl *fd = to_func_decl(fa);
                if (m_ctx.is_predicate(fd)) {
                    func_decl f(_d->ctx, fd);
                    if (!heads.contains(fd)) {
                        int arity = f.arity();
                        std::vector<expr> args;
                        for (int j = 0; j < arity; j++)
                            args.push_back(_d->ctx.fresh_func_decl("X", f.domain(j))());
                        expr c = implies(_d->ctx.bool_val(false), f(args));
                        c = _d->ctx.make_quant(Forall, args, c);
                        clauses.push_back(c);
                        bounds.push_back(UINT_MAX);
                    }
                }
            }
        }
        unsigned rb = m_ctx.get_params().duality_recursion_bound();
        std::vector<unsigned> std_bounds;
        for(unsigned i = 0; i < bounds.size(); i++){
            unsigned b = bounds[i];
            if (b == UINT_MAX) b = rb;
            std_bounds.push_back(b);
        }

        // creates 1-1 map between clauses and rpfp edges
        _d->rpfp->FromClauses(clauses,&std_bounds);

        // populate the edge-to-clause map
        for(unsigned i = 0; i < _d->rpfp->edges.size(); ++i)
            _d->map[_d->rpfp->edges[i]] = i;

        // create a solver object

        Solver *rs = Solver::Create("duality", _d->rpfp);

        if(old_rs)
            rs->LearnFrom(old_rs); // new solver gets hints from old solver

        // set its options
        IF_VERBOSE(1, rs->SetOption("report","1"););
        rs->SetOption("full_expand",m_ctx.get_params().duality_full_expand() ? "1" : "0");
        rs->SetOption("no_conj",m_ctx.get_params().duality_no_conj() ? "1" : "0");
        rs->SetOption("feasible_edges",m_ctx.get_params().duality_feasible_edges() ? "1" : "0");
        rs->SetOption("use_underapprox",m_ctx.get_params().duality_use_underapprox() ? "1" : "0");
        rs->SetOption("stratified_inlining",m_ctx.get_params().duality_stratified_inlining() ? "1" : "0");
        rs->SetOption("batch_expand",m_ctx.get_params().duality_batch_expand() ? "1" : "0");
        rs->SetOption("conjecture_file",m_ctx.get_params().duality_conjecture_file());
        rs->SetOption("enable_restarts",m_ctx.get_params().duality_enable_restarts() ? "1" : "0");
#if 0
        if(rb != UINT_MAX){
            std::ostringstream os; os << rb;
            rs->SetOption("recursion_bound", os.str());
        }
#endif

        // Solve!
        bool ans;
        try {
            ans = rs->Solve();
        }
        catch (Duality::solver::cancel_exception &exn){
            throw default_exception(Z3_CANCELED_MSG);
        }
        catch (Duality::Solver::Incompleteness &exn){
            throw default_exception("incompleteness");
        }

        // profile!

        if(m_ctx.get_params().duality_profile())
            print_profile(std::cout);

        // save the result and counterexample if there is one
        _d->status = ans ? StatusModel : StatusRefutation;
        _d->cex.swap(rs->GetCounterexample()); // take ownership of cex
        _d->old_rs = rs; // save this for later hints

        if(old_data){
            dealloc(old_data); // this deallocates the old solver if there is one
        }

        // dealloc(rs); this is now owned by data

        // true means the RPFP problem is SAT, so the query is UNSAT
        // but we return undef if the UNSAT result is bounded
        if(ans){
            if(rs->IsResultRecursionBounded()){
#if 0
                m_ctx.set_status(datalog::BOUNDED);
                return l_undef;
#else
                return l_false;
#endif
            }
            return l_false;
        }
        return l_true;
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

    static void print_proof(dl_interface *d, std::ostream& out, RPFP *tree, RPFP::Node *root) {
        context &ctx = d->dd()->ctx;
        RPFP::Node &node = *root;
        RPFP::Edge &edge = *node.Outgoing;

        // first, prove the children (that are actually used)

        for(unsigned i = 0; i < edge.Children.size(); i++){
            if(!tree->Empty(edge.Children[i])){
                print_proof(d,out,tree,edge.Children[i]);
            }
        }

        // print the label and the proved fact

        out << "(step s!" << node.number;
        out << " (" << node.Name.name();
        for(unsigned i = 0; i < edge.F.IndParams.size(); i++)
            out << " " << tree->Eval(&edge,edge.F.IndParams[i]);
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
                out << "    (= " << skolem << " " << tree->Eval(&edge,skolem) << ")\n";
                expr local_skolem = tree->Localize(&edge,skolem);
                (*local_func_decls).insert(local_skolem.decl());
            }
        }
        out << "  )\n";

        out << "  (labels";
        std::vector<symbol> labels;
        tree->GetLabels(&edge,labels);
        for(unsigned j = 0; j < labels.size(); j++){
            out << " " << labels[j];
        }

        out << "  )\n";

        // reference the proofs of all the children, in syntactic order
        // "true" means the child is not needed

        out << "  (ref ";
        for(unsigned i = 0; i < edge.Children.size(); i++){
            if(!tree->Empty(edge.Children[i]))
                out << " s!" << edge.Children[i]->number;
            else
                out << " true";
        }
        out << "  )";
        out << ")\n";
    }


    void dl_interface::display_certificate(std::ostream& out) const {
        ((dl_interface *)this)->display_certificate_non_const(out);
    }

    void dl_interface::display_certificate_non_const(std::ostream& out) {
        if(_d->status == StatusModel){
            ast_manager &m = m_ctx.get_manager();
            model_ref md = get_model();
            out << "(fixedpoint \n";
            model_smt2_pp(out, m, *md.get(), 0);
            out << ")\n";
        }
        else if(_d->status == StatusRefutation){
            out << "(derivation\n";
            // negation of the query is the last clause -- prove it
            hash_set<func_decl> locals;
            local_func_decls = &locals;
            print_proof(this,out,_d->cex.get_tree(),_d->cex.get_root());
            out << ")\n";
            out << "(model \n\"";
            ::model mod(m_ctx.get_manager());
            model orig_model = _d->cex.get_tree()->dualModel;
            for(unsigned i = 0; i < orig_model.num_consts(); i++){
                func_decl cnst = orig_model.get_const_decl(i);
                if (locals.find(cnst) == locals.end()) {
                    expr thing = orig_model.get_const_interp(cnst);
                    mod.register_decl(to_func_decl(cnst.raw()), to_expr(thing.raw()));
                }
            }
            for(unsigned i = 0; i < orig_model.num_funcs(); i++){
                func_decl cnst = orig_model.get_func_decl(i);
                if (locals.find(cnst) == locals.end()) {
                    func_interp thing = orig_model.get_func_interp(cnst);
                    ::func_interp *thing_raw = thing;
                    mod.register_decl(to_func_decl(cnst.raw()), thing_raw->copy());
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
#if 0
        if(_d && _d->ls)
            _d->ls->cancel();
#else
        // HACK: duality can't cancel at all times, we just exit here
        std::cout << "(error \"duality canceled\")\nunknown\n";
        abort();
#endif
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

    static proof_ref extract_proof(dl_interface *d, RPFP *tree, RPFP::Node *root) {
        context &ctx = d->dd()->ctx;
        ast_manager &mgr = ctx.m();
        RPFP::Node &node = *root;
        RPFP::Edge &edge = *node.Outgoing;
        RPFP::Edge *orig_edge = edge.map;

        // first, prove the children (that are actually used)

        proof_ref_vector prems(mgr);
        ::vector<expr_ref_vector> substs;
        int orig_clause = d->dd()->map[orig_edge];
        expr &t = d->dd()->clauses[orig_clause];
        prems.push_back(mgr.mk_asserted(ctx.uncook(t)));

        substs.push_back(expr_ref_vector(mgr));
        if (t.is_quantifier() && t.is_quantifier_forall()) {
            int bound = t.get_quantifier_num_bound();
            std::vector<sort> sorts;
            std::vector<symbol> names;
            hash_map<int,expr> subst;
            for(int j = 0; j < bound; j++){
                sort the_sort = t.get_quantifier_bound_sort(j);
                symbol name = t.get_quantifier_bound_name(j);
                expr skolem = ctx.constant(symbol(ctx,name),sort(ctx,the_sort));
                expr val = tree->Eval(&edge,skolem);
                expr_ref thing(ctx.uncook(val),mgr);
                substs[0].push_back(thing);
                expr local_skolem = tree->Localize(&edge,skolem);
                (*local_func_decls).insert(local_skolem.decl());
            }
        }

        svector<std::pair<unsigned, unsigned> > pos;
        for(unsigned i = 0; i < edge.Children.size(); i++){
            if(!tree->Empty(edge.Children[i])){
                pos.push_back(std::pair<unsigned,unsigned>(i+1,0));
                proof_ref prem = extract_proof(d,tree,edge.Children[i]);
                prems.push_back(prem);
                substs.push_back(expr_ref_vector(mgr));
            }
        }

        func_decl f = node.Name;
        std::vector<expr> args;
        for(unsigned i = 0; i < edge.F.IndParams.size(); i++)
            args.push_back(tree->Eval(&edge,edge.F.IndParams[i]));
        expr conc = f(args);


        ::vector< ::proof *> pprems;
        for(unsigned i = 0; i < prems.size(); i++)
            pprems.push_back(prems[i].get());

        proof_ref res(mgr.mk_hyper_resolve(pprems.size(),&pprems[0], ctx.uncook(conc), pos, substs),mgr);
        return res;

    }

    proof_ref dl_interface::get_proof() {
        if(_d->status == StatusRefutation){
            hash_set<func_decl> locals;
            local_func_decls = &locals;
            return extract_proof(this,_d->cex.get_tree(),_d->cex.get_root());
        }
        else
            return proof_ref(m_ctx.get_manager());
    }
}
