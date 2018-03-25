/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    dl_mk_quantifier_instantiation.cpp

Abstract:

    Convert Quantified Horn clauses into non-quantified clauses using
    instantiation.

Author:

    Ken McMillan 
    Andrey Rybalchenko
    Nikolaj Bjorner (nbjorner) 2013-04-02

Revision History:

    Based on approach suggested in the SAS 2013 paper 
    "On Solving Universally Quantified Horn Clauses"    

--*/

#include "muz/transforms/dl_mk_quantifier_instantiation.h"
#include "muz/base/dl_context.h"
#include "ast/pattern/pattern_inference.h"
#include "ast/rewriter/rewriter_def.h"
#include "ast/ast_util.h"


namespace datalog {

    mk_quantifier_instantiation::mk_quantifier_instantiation(
        context & ctx, unsigned priority):
        plugin(priority),
        m(ctx.get_manager()),
        m_ctx(ctx),
        m_var2cnst(m),
        m_cnst2var(m) {        
    }

    mk_quantifier_instantiation::~mk_quantifier_instantiation() {        
    }

    void mk_quantifier_instantiation::extract_quantifiers(rule& r, expr_ref_vector& conjs, quantifier_ref_vector& qs) {
        conjs.reset();
        qs.reset();
        unsigned tsz = r.get_tail_size();
        for (unsigned j = 0; j < tsz; ++j) {
            conjs.push_back(r.get_tail(j));            
        }
        flatten_and(conjs);
        for (unsigned j = 0; j < conjs.size(); ++j) {
            expr* e = conjs[j].get();
            quantifier* q;
            if (rule_manager::is_forall(m, e, q)) {
                qs.push_back(q);
                conjs[j] = conjs.back();
                conjs.pop_back();
                --j;
            }
        }
    }

    void mk_quantifier_instantiation::instantiate_quantifier(quantifier* q, expr_ref_vector & conjs) {
        expr_ref qe(m);
        qe = q;
        m_var2cnst(qe);        
        q = to_quantifier(qe);
        if (q->get_num_patterns() == 0) {
            proof_ref new_pr(m);
            pattern_inference_params params;
            pattern_inference_rw infer(m, params);
            infer(q, qe, new_pr);
            q = to_quantifier(qe);
        }
        unsigned num_patterns = q->get_num_patterns();
        for (unsigned i = 0; i < num_patterns; ++i) {
            expr * pat = q->get_pattern(i);
            SASSERT(m.is_pattern(pat));
            instantiate_quantifier(q, to_app(pat), conjs);
        }
    }


    void mk_quantifier_instantiation::instantiate_quantifier(quantifier* q, app* pat, expr_ref_vector & conjs) {
        m_binding.reset();
        m_binding.resize(q->get_num_decls());
        term_pairs todo;
        match(0, pat, 0, todo, q, conjs);
    }

    void mk_quantifier_instantiation::match(unsigned i, app* pat, unsigned j, term_pairs& todo, quantifier* q, expr_ref_vector& conjs) {
        TRACE("dl", tout << "match" << mk_pp(pat, m) << "\n";);
        while (j < todo.size()) {
            expr* p = todo[j].first;
            expr* t = todo[j].second;
            if (is_var(p)) {
                unsigned idx = to_var(p)->get_idx();
                if (!m_binding[idx]) {
                    m_binding[idx] = t;
                    match(i, pat, j + 1, todo, q, conjs);
                    m_binding[idx] = 0;
                    return;
                }
                ++j;
                continue;
            }
            if (!is_app(p)) {
                return;
            }
            app* a1 = to_app(p);
            unsigned id = t->get_id();
            unsigned next_id = id;
            unsigned sz = todo.size();
            do {
                expr* t2 = m_terms[next_id];
                if (is_app(t2)) {
                    app* a2 = to_app(t2);
                    if (a1->get_decl() == a2->get_decl() &&
                        a1->get_num_args() == a2->get_num_args()) {
                        for (unsigned k = 0; k < a1->get_num_args(); ++k) {
                            todo.push_back(std::make_pair(a1->get_arg(k), a2->get_arg(k)));
                        }
                        match(i, pat, j + 1, todo, q, conjs);
                        todo.resize(sz);
                    }                    
                }
                next_id = m_uf.next(next_id);
            }
            while (next_id != id);
            return;
        }

        if (i == pat->get_num_args()) {
            yield_binding(q, conjs);
            return;
        }
        expr* arg = pat->get_arg(i);
        ptr_vector<expr>* terms = nullptr;
    
        if (m_funs.find(to_app(arg)->get_decl(), terms)) {
            for (unsigned k = 0; k < terms->size(); ++k) {
                todo.push_back(std::make_pair(arg, (*terms)[k]));
                match(i + 1, pat, j, todo, q, conjs);
                todo.pop_back();
            }
        }
    }

    void mk_quantifier_instantiation::yield_binding(quantifier* q, expr_ref_vector& conjs) {
        DEBUG_CODE(
            for (unsigned i = 0; i < m_binding.size(); ++i) {
                SASSERT(m_binding[i]);
            });
        m_binding.reverse();
        expr_ref res(m);
        instantiate(m, q, m_binding.c_ptr(), res);
        m_binding.reverse();
        m_cnst2var(res);
        conjs.push_back(res);
        TRACE("dl", tout << mk_pp(q, m) << "\n==>\n" << mk_pp(res, m) << "\n";);
    }

    void mk_quantifier_instantiation::collect_egraph(expr* e) {
        expr* e1, *e2;
        m_todo.push_back(e);
        expr_fast_mark1 visited;
        while (!m_todo.empty()) {
            e = m_todo.back();
            m_todo.pop_back();
            if (visited.is_marked(e)) {
                continue;
            }
            unsigned n = e->get_id();
            if (n >= m_terms.size()) {
                m_terms.resize(n+1);
            }
            m_terms[n] = e;
            visited.mark(e);
            if (m.is_eq(e, e1, e2) || m.is_iff(e, e1, e2)) {
                m_uf.merge(e1->get_id(), e2->get_id());
            }
            if (is_app(e)) {
                app* ap = to_app(e);
                ptr_vector<expr>* terms = nullptr;
                if (!m_funs.find(ap->get_decl(), terms)) {
                    terms = alloc(ptr_vector<expr>);
                    m_funs.insert(ap->get_decl(), terms);
                }
                terms->push_back(e);
                m_todo.append(ap->get_num_args(), ap->get_args());
            }
        }
    }

    void mk_quantifier_instantiation::instantiate_rule(rule& r, expr_ref_vector& conjs, quantifier_ref_vector& qs, rule_set& rules) {
        rule_manager& rm = m_ctx.get_rule_manager();
        expr_ref fml(m), cnst(m);
        var_ref var(m);
        ptr_vector<sort> sorts;
        r.get_vars(m, sorts);
        m_uf.reset();
        m_terms.reset();
        m_var2cnst.reset();
        m_cnst2var.reset();
        fml = m.mk_and(conjs.size(), conjs.c_ptr());

        for (unsigned i = 0; i < sorts.size(); ++i) {
            var = m.mk_var(i, sorts[i]);
            cnst = m.mk_fresh_const("C", sorts[i]);
            m_var2cnst.insert(var, cnst);
            m_cnst2var.insert(cnst, var);
        }

        fml = m.mk_and(conjs.size(), conjs.c_ptr());
        m_var2cnst(fml);
        collect_egraph(fml);

        for (unsigned i = 0; i < qs.size(); ++i) {
            instantiate_quantifier(qs[i].get(), conjs);
        }
        obj_map<func_decl, ptr_vector<expr>*>::iterator it = m_funs.begin(), end = m_funs.end();
        for (; it != end; ++it) {
            dealloc(it->m_value);
        }
        m_funs.reset();

        fml = m.mk_and(conjs.size(), conjs.c_ptr());
        fml = m.mk_implies(fml, r.get_head());
        TRACE("dl", r.display(m_ctx, tout); tout << mk_pp(fml, m) << "\n";);
        
        rule_set added_rules(m_ctx);
        proof_ref pr(m); 
        rm.mk_rule(fml, pr, added_rules, r.name());
        if (r.get_proof()) {
            // use def-axiom to encode that new rule is a weakening of the original.
            proof* p1 = r.get_proof();
            for (unsigned i = 0; i < added_rules.get_num_rules(); ++i) {
                rule* r2 = added_rules.get_rule(i);
                rm.to_formula(*r2, fml);
                pr = m.mk_modus_ponens(m.mk_def_axiom(m.mk_implies(m.get_fact(p1), fml)), p1);
                r2->set_proof(m, pr);
            }
        }
        rules.add_rules(added_rules);
    }
        
    rule_set * mk_quantifier_instantiation::operator()(rule_set const & source) {
        if (!m_ctx.instantiate_quantifiers()) {
            return nullptr;
        }
        bool has_quantifiers = false;
        unsigned sz = source.get_num_rules();
        rule_manager& rm = m_ctx.get_rule_manager();
        for (unsigned i = 0; !has_quantifiers && i < sz; ++i) {
            rule& r = *source.get_rule(i);
            has_quantifiers = has_quantifiers || rm.has_quantifiers(r);   
            if (r.has_negation()) {
                return nullptr;
            }
        }
        if (!has_quantifiers) {
            return nullptr;
        }

        expr_ref_vector conjs(m);
        quantifier_ref_vector qs(m);
        rule_set * result = alloc(rule_set, m_ctx);

        bool instantiated = false;

        for (unsigned i = 0; i < sz; ++i) {       
            rule * r = source.get_rule(i);
            extract_quantifiers(*r, conjs, qs);
            if (qs.empty()) {
                result->add_rule(r);
            }
            else {
                instantiate_rule(*r, conjs, qs, *result);
                instantiated = true;
            }
        }

        // model convertion: identity function.

        if (instantiated) {
            result->inherit_predicates(source);
        }
        else {
            dealloc(result);
            result = nullptr;
        }
        return result;
    }


};


