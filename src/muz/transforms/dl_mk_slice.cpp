/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_mk_slice.cpp

Abstract:

    <abstract>

Author:

    Nikolaj Bjorner (nbjorner) 2012-9-12.

Revision History:

    Consider a rule:

    P(x,y) :- R(x,z), phi(x,y,z)
    
    input:  x, z
    output: x, y

    Let x_i, y_i, z_i be indices into the vectors x, y, z.

    Suppose that positions in P and R are annotated with what is
    slicable.

    Sufficient conditions for sliceability:

      x_i is sliceable if x_i does not appear in phi(x,y,z)
      and the positions where x_i is used in P and R are sliceable
   
      y_i is sliceable if y_i does not occur in phi(x,y,z), or
      if it occurs in phi(x,y,z) it is only in one conjunct of the form
      y_i = t[x_j,y_j,z_j]
      and the positions where y_i is used in P and R are sliceable

      z_i is sliceable if z_i does not occur in phi(x,y,z), or
      if it occurs in phi(x,y,z) it is only in one conjunct of the form
      y_i = t[x_j,y_j,z_i] where y_i is sliceable
      and the positions where z_i is used in P and R are sliceable


    A more refined approach may be using Gaussean elimination based
    on x,z and eliminating variables from x,y (expressing them in terms
    of a disjoint subeset of x,z).


--*/

#include "muz/transforms/dl_mk_slice.h"
#include "ast/ast_pp.h"
#include "ast/ast_util.h"
#include "ast/expr_functors.h"
#include "muz/transforms/dl_mk_rule_inliner.h"
#include "model/model_smt2_pp.h"

namespace datalog {

    /**
       Convert from sliced proofs to original proofs.
       Given sliced rule 
          fml0: forall x y z u. p(x,y) & z = f(x,y) & phi(x,u) => p(u, z)
       into
          fml1: forall a b . q(a) & phi(a,b) => q(b)
       It induces mappings:
          theta: a |-> x, b |-> u
          vars:  x y z u.
          predicates: -q(a) |-> p(x,y)
                      +q(b) |-> z = f(x,y) => p(u,z)
          fml1 |-> fml0

       The mapping theta is an injective function from variable indices
       to variable indices. We can apply it as a substitution on expressions,
       but we can also apply it as a transformation on substitutions. We
       write theta[subst] when applying theta on substitution 'subst' such
       that if [x |-> t] is in subst, then [theta(x) |-> theta(t)] is in 
       the result.
       
       Given hyper-resolvent: fml1 subst1 fml2 subst2 |- fml3
       where fml1 |-> fml1' with theta1
             fml2 |-> fml2' with theta2
       Perform the following steps:
       1. [Convert fml1' fml2' to datalog rules because we have resolution routines]
       2. Create subst1' := theta1[subst1] 
                 subst2' := theta2[subst2]
       3. Set    fml1''  := subst1'(fml1')
                 fml2''  := subst2'(fml2')
       4. Resolve fml1'' and fml2'' 
                 extract subst1'', subst2'' from resolvents.
                 extract goal fml3'
       5. Create subst1''' := subst1'' o subst1'
                 subst2''' := subst2'' o subst2'
       6. Return fml1'' subst1''' fml2'' subst2''' |- fml3'
       7. Attach to fml3' the transformation ...?

    */
    class mk_slice::slice_proof_converter : public proof_converter {
        context&             m_ctx;
        ast_manager&         m;
        rule_manager&        rm;
        rule_ref_vector      m_pinned_rules;
        expr_ref_vector      m_pinned_exprs;
        obj_map<rule, rule*> m_rule2slice;              // rule to sliced rule
        obj_map<rule, unsigned_vector> m_renaming;      // rule to renaming
        obj_map<expr, rule*> m_sliceform2rule;          // sliced formula to rule.
        ptr_vector<proof>    m_todo;
        obj_map<proof, proof*> m_new_proof;
        rule_unifier           m_unifier;


        slice_proof_converter(slice_proof_converter const& other);

        void init_form2rule() {
            if (!m_sliceform2rule.empty()) {
                return;
            }
            obj_map<rule, rule*>::iterator it  = m_rule2slice.begin();
            obj_map<rule, rule*>::iterator end = m_rule2slice.end();
            expr_ref fml(m);
            for (; it != end; ++it) {
                rm.to_formula(*it->m_value, fml);
                m_pinned_exprs.push_back(fml);
                TRACE("dl", 
                      tout << "orig: " << mk_pp(fml, m) << "\n";
                      it->m_value->display(m_ctx, tout << "new:\n"););                
                m_sliceform2rule.insert(fml, it->m_key);                
            }
        }

        void translate_proof(proof_ref& pr) {
            m_todo.reset();
            m_new_proof.reset();
            m_todo.push_back(pr);
            while (!m_todo.empty()) {
                proof* p = m_todo.back();
                if (m_new_proof.contains(p)) {
                    m_todo.pop_back();
                }
                else if (translate_asserted(p)) {
                    // done
                }
                else if (translate_hyper_res(p)) {
                    // done
                }
                else {
                    m_new_proof.insert(p, p);
                    m_todo.pop_back();
                    TRACE("dl", tout << "unhandled proof term\n" << mk_pp(p, m) << "\n";);
                }
            }
            pr = m_new_proof.find(pr);
        }

        bool translate_asserted(proof* p) {
            expr* fact = nullptr;
            rule* r = nullptr;
            if (!m.is_asserted(p, fact)) {
                return false;   
            }
            if (!m_sliceform2rule.find(fact, r)) {
                TRACE("dl", tout << "does not have fact\n" << mk_pp(fact, m) << "\n";);
                return false;
            }
            proof_ref new_p(m);
            new_p = r->get_proof();
            m_pinned_exprs.push_back(new_p);
            m_todo.pop_back();
            m_new_proof.insert(p, new_p);
            return true;
        }

        bool translate_hyper_res(proof* p) {
            dl_decl_util util(m);
            svector<std::pair<unsigned, unsigned> > positions;
            expr_ref concl(m), slice_concl(m);
            proof_ref_vector premises0(m);
            vector<expr_ref_vector> substs, substs0;

            if (!m.is_hyper_resolve(p, premises0, slice_concl, positions, substs0)) {
                return false;
            }
            unsigned num_args = p->get_num_args();
            SASSERT(num_args >= 2);
            bool all_found = true;
            for (unsigned i = 0; i < num_args-1; ++i) {
                proof* arg = to_app(p->get_arg(i));
                SASSERT(m.is_proof(arg));
                if (!m_new_proof.contains(arg)) {
                    m_todo.push_back(arg);
                    all_found = false;
                }
            }
            if (!all_found) {
                return true;
            }
            ptr_vector<proof> premises;
            
            proof* p0     = to_app(p->get_arg(0));
            proof* p0_new = m_new_proof.find(p0);            
            expr* fact0   = m.get_fact(p0);
            TRACE("dl", tout << "fact0: " << mk_pp(fact0, m) << "\n";);
            rule* orig0;
            if (!m_sliceform2rule.find(fact0, orig0)) {
                return false;
            }
            premises.push_back(p0_new);
            rule_ref r1(rm), r2(rm), r3(rm);
            r1 = orig0;
            substs.push_back(expr_ref_vector(m));
            for (unsigned i = 1; i < num_args-1; ++i) {
                proof* p1     = to_app(p->get_arg(i));
                proof* p1_new = m_new_proof.find(p1);
                expr* fact1   = m.get_fact(p1);
                TRACE("dl", tout << "fact1: " << mk_pp(fact1, m) << "\n";);
                rule* orig1 = nullptr;
                if (!m_sliceform2rule.find(fact1, orig1)) {
                    return false;
                }
                premises.push_back(p1_new);

                // TODO: work with substitutions.
                r2 = orig1;
                unsigned idx = 0; // brittle. TBD get index from positions.
                
                VERIFY(m_unifier.unify_rules(*r1, idx, *r2)); 
                m_unifier.apply(*r1.get(), idx, *r2.get(), r3); 
                expr_ref_vector const sub1 = m_unifier.get_rule_subst(*r1.get(), true);
                for (unsigned j = 0; j < substs.size(); ++j) {
                    apply_subst(substs[j], sub1);
                    // size of substitutions may have grown...substs[j].resize(num_args[j]);
                }
                substs.push_back(m_unifier.get_rule_subst(*r2.get(), false));   
                TRACE("dl", 
                    r1->display(m_ctx, tout << "rule1:");
                    r2->display(m_ctx, tout << "rule2:");
                    r3->display(m_ctx, tout << "res:"););
                r1 = r3;
            }
            rm.to_formula(*r1.get(), concl);
            proof* new_p = m.mk_hyper_resolve(premises.size(), premises.c_ptr(), concl, positions, substs);
            m_pinned_exprs.push_back(new_p);
            m_pinned_rules.push_back(r1.get());
            TRACE("dl", 
                  tout << "orig: " << mk_pp(slice_concl, m) << "\n";
                  r1->display(m_ctx, tout << "new:"););
            m_sliceform2rule.insert(slice_concl, r1.get());
            m_rule2slice.insert(r1.get(), 0);
            m_renaming.insert(r1.get(), unsigned_vector());
            m_new_proof.insert(p, new_p);
            m_todo.pop_back();
            TRACE("dl", tout << "translated:\n" << mk_pp(p, m) << "\nto\n" << mk_pp(new_p, m) << "\n";);
            return true;
        }

    public:
        slice_proof_converter(context& ctx): 
            m_ctx(ctx), 
            m(ctx.get_manager()),
            rm(ctx.get_rule_manager()),
            m_pinned_rules(rm),
            m_pinned_exprs(m),
            m_unifier(ctx) {}

        void insert(rule* orig_rule, rule* slice_rule, unsigned sz, unsigned const* renaming) {
            m_rule2slice.insert(orig_rule, slice_rule);
            m_pinned_rules.push_back(orig_rule);
            m_pinned_rules.push_back(slice_rule);
            m_renaming.insert(orig_rule, unsigned_vector(sz, renaming));
        }

        proof_ref operator()(ast_manager& m, unsigned num_source, proof * const * source) override {
            SASSERT(num_source == 1);
            proof_ref result(source[0], m);
            init_form2rule();
            translate_proof(result);
            return result;
        }        

        proof_converter * translate(ast_translation & translator) override {
            UNREACHABLE();
            // this would require implementing translation for the dl_context.
            return nullptr;
        }

        void display(std::ostream& out) override { out << "(slice-proof-converter)\n"; }
    };

    class mk_slice::slice_model_converter : public model_converter {
        ast_manager& m;
        obj_map<func_decl, func_decl*> m_slice2old;
        obj_map<func_decl, bit_vector> m_sliceable;
        ast_ref_vector m_pinned;
        
    public:
        slice_model_converter(mk_slice& parent, ast_manager& m): m(m), m_pinned(m) {}

        void add_predicate(func_decl* old_f, func_decl* slice_f) {
            m_pinned.push_back(old_f);
            m_pinned.push_back(slice_f);
            m_slice2old.insert(slice_f, old_f);
        }

        void add_sliceable(func_decl* f, bit_vector const& bv) {
            m_pinned.push_back(f);
            m_sliceable.insert(f, bv);
        }

        void get_units(obj_map<expr, bool>& units) override {}

        void operator()(model_ref & md) override {
            if (m_slice2old.empty()) {
                return;
            }
            TRACE("dl", model_smt2_pp(tout, m, *md, 0); );
            model_ref old_model = alloc(model, m);
            obj_map<func_decl, func_decl*>::iterator it  = m_slice2old.begin();
            obj_map<func_decl, func_decl*>::iterator end = m_slice2old.end();
            for (; it != end; ++it) {
                func_decl* old_p = it->m_value;
                func_decl* new_p = it->m_key;
                bit_vector const& is_sliced = m_sliceable.find(old_p);
                SASSERT(is_sliced.size() == old_p->get_arity());
                SASSERT(is_sliced.size() > new_p->get_arity());
                func_interp* old_fi = alloc(func_interp, m, is_sliced.size());

                TRACE("dl", tout << mk_pp(old_p, m) << " " << mk_pp(new_p, m) << "\n";
                            for (unsigned j = 0; j < is_sliced.size(); ++j) {
                                tout << (is_sliced.get(j)?"1":"0");
                            }
                            tout << "\n";);
                
                if (new_p->get_arity() == 0) {
                    old_fi->set_else(md->get_const_interp(new_p));
                }
                else {
                    expr_ref_vector subst(m);
                    expr_ref tmp(m);
                    var_subst vs(m, false);
                    for (unsigned i = 0; i < is_sliced.size(); ++i) {
                        if (!is_sliced.get(i)) {
                            subst.push_back(m.mk_var(i, old_p->get_domain(i)));
                        }
                    }                                      
                    func_interp* new_fi = md->get_func_interp(new_p);
                    if (!new_fi) {
                        TRACE("dl", tout << new_p->get_name() << " has no value in the current model\n";);
                        dealloc(old_fi);
                        continue;
                    }
                    if (!new_fi->is_partial()) {
                        TRACE("dl", tout << mk_pp(new_fi->get_else(), m) << "\n";);
                        vs(new_fi->get_else(), subst.size(), subst.c_ptr(), tmp);
                        old_fi->set_else(tmp);
                    }
                    unsigned num_entries = new_fi->num_entries();
                    for (unsigned j = 0; j < num_entries; ++j) {
                        expr_ref res(m);
                        expr_ref_vector args(m);
                        func_entry const* e = new_fi->get_entry(j);
                        for (unsigned k = 0, l = 0; k < old_p->get_arity(); ++k) {
                            if (!is_sliced.get(k)) {
                                vs(e->get_arg(l++), subst.size(), subst.c_ptr(), tmp);
                                args.push_back(tmp);
                            }
                            else {
                                args.push_back(m.mk_var(k, old_p->get_domain(k)));
                            }
                            SASSERT(l <= new_p->get_arity());
                        }
                        vs(e->get_result(), subst.size(), subst.c_ptr(), res);
                        old_fi->insert_entry(args.c_ptr(), res.get());
                    }
                    old_model->register_decl(old_p, old_fi);
                }
            }
            // register values that have not been sliced.
            unsigned sz = md->get_num_constants();
            for (unsigned i = 0; i < sz; ++i) {
                func_decl* c = md->get_constant(i);
                if (!m_slice2old.contains(c)) {
                    old_model->register_decl(c, md->get_const_interp(c));
                }
            }
            sz = md->get_num_functions();
            for (unsigned i = 0; i < sz; ++i) {
                func_decl* f = md->get_function(i);
                if (!m_slice2old.contains(f)) {
                    func_interp* fi = md->get_func_interp(f);
                    old_model->register_decl(f, fi->copy());
                }
            }   
            md = old_model;
            TRACE("dl", model_smt2_pp(tout, m, *md, 0); );
        }
     
        model_converter * translate(ast_translation & translator) override {
            UNREACHABLE();
            return nullptr;
        }

        void display(std::ostream& out) override { out << "(slice-model-converter)\n"; }

    };
   
    mk_slice::mk_slice(context & ctx):
        plugin(1), 
        m_ctx(ctx), 
        m(ctx.get_manager()), 
        rm(ctx.get_rule_manager()), 
        m_solved_vars(m),
        m_pinned(m),
        m_pc(nullptr),
        m_mc(nullptr)
    {}


    bit_vector& mk_slice::get_predicate_slice(func_decl* h) {
        if (!m_sliceable.contains(h)) {
            bit_vector bv;
            bv.resize(h->get_arity(), true);
            m_sliceable.insert(h, bv);
        }
        return m_sliceable.find(h);
    }
    
    /**
       \brief Saturate set of rules with respect to slicing criteria.
    */
    void mk_slice::saturate(rule_set const& src) {
        bool change = true;
        while (change) {
            change = false;
            for (rule* r : src) {
                change = prune_rule(*r) || change;
            }
        }
    }

    void mk_slice::filter_unique_vars(rule& r) {
        // 
        // Variables that occur in multiple uinterpreted predicates are not sliceable.
        // 
        uint_set used_vars;
        for (unsigned j = 0; j < r.get_uninterpreted_tail_size(); ++j) {
            app* p = r.get_tail(j);
            for (unsigned i = 0; i < p->get_num_args(); ++i) {
                expr* v = p->get_arg(i);
                if (is_var(v)) {
                    unsigned vi = to_var(v)->get_idx();
                    add_var(vi);
                    if (used_vars.contains(vi)) {
                        m_var_is_sliceable[vi] = false;
                    }
                    else {
                        used_vars.insert(vi);
                    }
                }
            }
        }
    }

    void mk_slice::solve_vars(rule& r, uint_set& used_vars, uint_set& parameter_vars) {
        expr_ref_vector conjs = get_tail_conjs(r);
        for (expr * e : conjs) {
            expr_ref r(m);
            unsigned v;
            if (is_eq(e, v, r) && is_output(v) && m_var_is_sliceable[v]) {
                TRACE("dl", tout << "is_eq: " << mk_pp(e, m) << " " << (m_solved_vars[v].get()?"solved":"new") << "\n";);
                add_var(v);
                if (!m_solved_vars[v].get()) { 
                    TRACE("dl", tout << v << " is solved\n";);
                    add_free_vars(parameter_vars, r);
                    m_solved_vars[v] = r;
                }
                else {
                    TRACE("dl", tout << v << " is used\n";);
                    // variables can only be solved once.
                    add_free_vars(used_vars, e);
                    add_free_vars(used_vars, m_solved_vars[v].get());
                    used_vars.insert(v);
                }
            }
            else {
                add_free_vars(used_vars, e);
            }
        }
    }


    bool mk_slice::prune_rule(rule& r) {
        TRACE("dl", r.display(m_ctx, tout << "prune:\n"); );
        bool change = false;
        init_vars(r);
        //
        // if a predicate in the body takes a constant as argument, 
        // the corresponding position is not sliceable.
        //
        for (unsigned j = 0; j < r.get_uninterpreted_tail_size(); ++j) {
            app* p = r.get_tail(j);
            bit_vector& bv = get_predicate_slice(p);
            for (unsigned i = 0; i < p->get_num_args(); ++i) {
                if (!is_var(p->get_arg(i)) && bv.get(i)) {
                    bv.unset(i);
                    change = true;                    
                    TRACE("dl", tout << "argument " << i << " is not a variable " << p->get_decl()->get_name() << "\n";);
                }
            }
        }   
        filter_unique_vars(r);
        //
        // Collect the set of variables that are solved.
        // Collect the occurrence count of the variables per conjunct.
        // 
        uint_set used_vars, parameter_vars;
        solve_vars(r, used_vars, parameter_vars);
        for (unsigned uv : used_vars) {
            if (uv < m_var_is_sliceable.size()) {
                m_var_is_sliceable[uv] = false;
            }
        }
        //
        // Check if sliceable variables are either solved 
        // or are used to solve output sliceable variables, or
        // don't occur in interpreted tail.
        // 
        for (unsigned i = 0; i < num_vars(); ++i) {
            if (!m_var_is_sliceable[i]) {
                continue;
            }
            if (used_vars.contains(i)) {
                m_var_is_sliceable[i] = false;
                continue;
            }
            bool is_input = m_input[i];
            bool is_output = m_output[i];
            if (is_input && is_output) {
                if (m_solved_vars[i].get()) {
                    m_var_is_sliceable[i] = false;
                }
                if (parameter_vars.contains(i)) {
                    m_var_is_sliceable[i] = false;
                }
            }
            else if (is_output) {
                if (parameter_vars.contains(i)) {
                    m_var_is_sliceable[i] = false;
                }
            }
            else if (is_input) {
                // I can be a parameter var, but not in used_vars.               
            }
            else {
                // variable does not correspond to
                // any position in predicates.
            }
        }
        // 
        // Update sliceable predicates based on slicing information of variables.
        //
        change = finalize_vars(r.get_head()) || change;
        for (unsigned j = 0; j < r.get_uninterpreted_tail_size(); ++j) {
            change = finalize_vars(r.get_tail(j)) || change;
        }
        return change;
    }

    bool mk_slice::is_eq(expr* e, unsigned& v, expr_ref& r) {
        expr* c, *th, *el, *e1, *e2;
        unsigned v1, v2;
        expr_ref r1(m), r2(m);
        if (m.is_ite(e, c, th, el)) {
            if (is_eq(th, v1, r1) && is_eq(el, v2, r2) && v1 == v2) {
                v = v1;
                r = m.mk_ite(c, r1, r2);
                return true;
            }
        }
        if (is_var(e)) {
            v = to_var(e)->get_idx();
            r = m.mk_true();
            return true;
        }
        if (m.is_not(e,e) && is_var(e)) {
            v = to_var(e)->get_idx();
            r = m.mk_false();
            return true;
        }
        if (m.is_eq(e, e1, e2) && is_var(e1)) {
            v = to_var(e1)->get_idx();
            r = e2;
            return true;
        }
        if (m.is_eq(e, e1, e2) && is_var(e2)) {
            v = to_var(e2)->get_idx();
            r = e1;
            return true;
        }
        return false;
    }

    bool mk_slice::is_output(unsigned idx) {
        return idx < m_output.size() && m_output[idx] && !m_input[idx];
    }

    bool mk_slice::is_output(expr* e) {
        if (is_var(e)) {
            return is_output(to_var(e)->get_idx());
        }
        else {
            return false;
        }
    }

    void mk_slice::init_vars(rule& r) {
        m_input.reset();
        m_output.reset();
        m_var_is_sliceable.reset();
        m_solved_vars.reset();
        init_vars(r.get_head(), true, false);
        for (unsigned j = 0; j < r.get_uninterpreted_tail_size(); ++j) {
            init_vars(r.get_tail(j), false, r.is_neg_tail(j));
        }        
    }

    expr_ref_vector mk_slice::get_tail_conjs(rule const& r) {
        expr_ref_vector conjs(m);
        for (unsigned j = r.get_uninterpreted_tail_size(); j < r.get_tail_size(); ++j) {
            conjs.push_back(r.get_tail(j));
        }
        flatten_and(conjs);
        return conjs;
    }

    void mk_slice::add_var(unsigned idx) {
        if (idx >= m_input.size()) {
             m_input.resize(idx+1, false);
             m_output.resize(idx+1, false);
             m_var_is_sliceable.resize(idx+1, true);
             m_solved_vars.resize(idx+1);
        }
    }

    void mk_slice::init_vars(app* p, bool is_output, bool is_neg_tail) {
        bit_vector& bv = get_predicate_slice(p);
        for (unsigned i = 0; i < p->get_num_args(); ++i) {
            if (is_neg_tail) {
                TRACE("dl", tout << "negated " << i << " in " << p->get_decl()->get_name() << "\n";);
                bv.unset(i);
            }
            expr* arg = p->get_arg(i);
            if (is_var(arg)) {
                unsigned idx = to_var(arg)->get_idx();
                add_var(idx);
                if (is_output) {
                    m_output[idx] = true;
                }
                else {
                    m_input[idx] = true;
                }
                m_var_is_sliceable[idx] &= bv.get(i);
            }
            else {
                SASSERT(m.is_value(arg));
                if (!is_output) {
                    TRACE("dl", tout << "input  " << i << " in " << p->get_decl()->get_name() << "\n";);
                    bv.unset(i);
                }
            }
        }
    }

    bool mk_slice::finalize_vars(app* p) {
        bool change = false;
        bit_vector& bv = get_predicate_slice(p);
        for (unsigned i = 0; i < p->get_num_args(); ++i) {
            expr* arg = p->get_arg(i);
            if (is_var(arg) && !m_var_is_sliceable[to_var(arg)->get_idx()] && bv.get(i)) {
                bv.unset(i);
                change = true;
                TRACE("dl", tout << "variable is unslicable " << mk_pp(arg, m) << " for index " << i << " in " << p->get_decl()->get_name() << "\n";);
            }
        }
        return change;
    }

    void mk_slice::add_free_vars(uint_set& result, expr* e) {
        expr_free_vars fv;
        fv(e);
        for (unsigned i = 0; i < fv.size(); ++i) {
            if (fv[i]) {
                result.insert(i);
            }
        }
    }

    void mk_slice::display(std::ostream& out) {
        for (auto const& kv : m_sliceable) {
            out << kv.m_key->get_name() << " ";
            bit_vector const& bv = kv.m_value;
            for (unsigned i = 0; i < bv.size(); ++i) {
                out << (bv.get(i)?"1":"0");
            }
            out << "\n";
        }
    }

    void mk_slice::reset() {
        m_input.reset();
        m_output.reset();
        m_var_is_sliceable.reset();
        m_solved_vars.reset();
        m_predicates.reset();
        m_pinned.reset();
    }
        
    void mk_slice::declare_predicates(rule_set const& src, rule_set& dst) {
        obj_map<func_decl, bit_vector>::iterator it = m_sliceable.begin(), end = m_sliceable.end();
        ptr_vector<sort> domain;
        bool has_output = false;
        func_decl* f;
        for (; it != end; ++it) {
            domain.reset();
            func_decl* p = it->m_key;
            bit_vector const& bv = it->m_value;
            for (unsigned i = 0; i < bv.size(); ++i) {
                if (!bv.get(i)) {
                    domain.push_back(p->get_domain(i));
                }
            }
            if (domain.size() < bv.size()) {
                f = m_ctx.mk_fresh_head_predicate(p->get_name(), symbol("slice"), domain.size(), domain.c_ptr(), p);
                m_pinned.push_back(f);
                m_predicates.insert(p, f);
                dst.inherit_predicate(src, p, f);
                if (m_mc) {
                    m_mc->add_predicate(p, f);
                }
            }
            else if (src.is_output_predicate(p)) {
                dst.set_output_predicate(p);
                has_output = true;
            }
        }
        // disable slicing if the output predicates don't occur in rules.
        if (!has_output) {
            m_predicates.reset();
        }
    }

    bool mk_slice::rule_updated(rule const& r) {
        if (m_predicates.contains(r.get_decl())) return true;
        for (unsigned i = 0; i < r.get_uninterpreted_tail_size(); ++i) {
            if (m_predicates.contains(r.get_decl(i))) return true;
        }
        return false;
    }

    void mk_slice::update_predicate(app* p, app_ref& q) {
        func_decl* qd;
        if (m_predicates.find(p->get_decl(), qd)) {
            bit_vector const& bv = get_predicate_slice(p->get_decl());
            ptr_vector<expr> args;
            for (unsigned i = 0; i < bv.size(); ++i) {
                if (!bv.get(i)) {
                    args.push_back(p->get_arg(i));
                }
            }
            q = m.mk_app(qd, args.size(), args.c_ptr());
        }
        else {
            q = p;
        }
    }


    void mk_slice::update_rule(rule& r, rule_set& dst) {
        rule_ref new_rule(rm);
        if (rule_updated(r)) {
            init_vars(r);
            app_ref_vector tail(m);
            app_ref head(m);
            update_predicate(r.get_head(), head);
            for (unsigned i = 0; i < r.get_uninterpreted_tail_size(); ++i) {
                app_ref t(m);
                update_predicate(r.get_tail(i), t);
                tail.push_back(t);
            }
            expr_ref_vector conjs = get_tail_conjs(r);
            
            m_solved_vars.reset();

            for (unsigned i = 0; i < conjs.size(); ++i) {
                expr* e = conjs[i].get();
                tail.push_back(to_app(e));                
            }
                        
            new_rule = rm.mk(head.get(), tail.size(), tail.c_ptr(), (const bool*) nullptr, r.name());

            rm.fix_unbound_vars(new_rule, false);

            TRACE("dl", r.display(m_ctx, tout << "replacing:\n"); new_rule->display(m_ctx, tout << "by:\n"););
            if (m_ctx.generate_proof_trace()) {
                rm.mk_rule_asserted_proof(*new_rule.get());
            }
        }
        else {
            new_rule = &r;
        }
        dst.add_rule(new_rule.get());

        if (m_pc) {
            m_pc->insert(&r, new_rule.get(), 0, nullptr);
        }
    }

    void mk_slice::update_rules(rule_set const& src, rule_set& dst) {
        for (unsigned i = 0; i < src.get_num_rules(); ++i) {
            update_rule(*src.get_rule(i), dst);
        }
    }

    rule_set * mk_slice::operator()(rule_set const & src) { 
        rule_manager& rm = m_ctx.get_rule_manager();       
        for (unsigned i = 0; i < src.get_num_rules(); ++i) {
            if (rm.has_quantifiers(*src.get_rule(i))) {
                return nullptr;
            }
        }
        ref<slice_proof_converter> spc;
        ref<slice_model_converter> smc;
        if (m_ctx.generate_proof_trace()) {
            spc = alloc(slice_proof_converter, m_ctx);        
        }
        if (m_ctx.get_model_converter()) {
            smc = alloc(slice_model_converter, *this, m);
        }
        m_pc = spc.get();
        m_mc = smc.get();
        reset();
        saturate(src);
        rule_set* result = alloc(rule_set, m_ctx);
        declare_predicates(src, *result);
        if (m_predicates.empty()) {
            // nothing could be sliced.
            dealloc(result);
            return nullptr;
        }
        TRACE("dl", display(tout););        
        update_rules(src, *result);
        TRACE("dl", result->display(tout););
        if (m_mc) {
            obj_map<func_decl, bit_vector>::iterator it = m_sliceable.begin(), end = m_sliceable.end();
            for (; it != end; ++it) {
                m_mc->add_sliceable(it->m_key, it->m_value);
            }
        }
        m_ctx.add_proof_converter(spc.get());
        m_ctx.add_model_converter(smc.get());
        return result;
    }    

};

