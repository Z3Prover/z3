/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    rule_properties.cpp

Abstract:

    Collect properties of rules.

Author:

    Nikolaj Bjorner (nbjorner) 9-25-2014

Notes:
    

--*/

#include"expr_functors.h"
#include"rule_properties.h"
#include"dl_rule_set.h"
#include"for_each_expr.h"
#include"dl_context.h"

using namespace datalog;
rule_properties::rule_properties(ast_manager & m, rule_manager& rm, context& ctx, i_expr_pred& p): 
    m(m), rm(rm), m_ctx(ctx), m_is_predicate(p), m_dt(m), m_dl(m), m_bv(m), m_generate_proof(false) {}

rule_properties::~rule_properties() {}

void rule_properties::collect(rule_set const& rules) {
    reset();
    rule_set::iterator it = rules.begin(), end = rules.end();
    expr_sparse_mark visited;
    for (; it != end; ++it) {
        rule* r = *it;
        m_rule = r;
        unsigned ut_size = r->get_uninterpreted_tail_size();
        unsigned t_size  = r->get_tail_size();  
        if (r->has_negation()) {
            m_negative_rules.push_back(r);            
        }
        for (unsigned i = ut_size; i < t_size; ++i) {
            for_each_expr_core<rule_properties,expr_sparse_mark, true, false>(*this, visited, r->get_tail(i));
        }
        if (m_generate_proof && !r->get_proof()) {
            rm.mk_rule_asserted_proof(*r);
        }
        for (unsigned i = 0; m_inf_sort.empty() && i < r->get_decl()->get_arity(); ++i) {
            sort* d = r->get_decl()->get_domain(i);
            if (!m.is_bool(d) && !m_dl.is_finite_sort(d) && !m_bv.is_bv_sort(d)) {
                m_inf_sort.push_back(m_rule);
            }
        }
    }     
}

void rule_properties::check_quantifier_free() {
    if (!m_quantifiers.empty()) {
        rule* r = m_quantifiers.begin()->m_value;
        std::stringstream stm;
        stm << "cannot process quantifier in rule ";
        r->display(m_ctx, stm);
        throw default_exception(stm.str());
    }
}

void rule_properties::check_for_negated_predicates() {
    if (!m_negative_rules.empty()) {
        rule* r = m_negative_rules[0];
        std::stringstream stm;
        stm << "Rule contains negative predicate ";
        r->display(m_ctx, stm);
        throw default_exception(stm.str());        
    }
}


void rule_properties::check_uninterpreted_free() {    
    if (!m_uninterp_funs.empty()) {
        func_decl* f = m_uninterp_funs.begin()->m_key;
        rule* r = m_uninterp_funs.begin()->m_value;
        std::stringstream stm;
        stm << "Uninterpreted '" 
            << f->get_name() 
            << "' in ";
        r->display(m_ctx, stm);
        throw default_exception(stm.str());
    }
}

void rule_properties::check_infinite_sorts() {
    if (!m_inf_sort.empty()) {
        std::stringstream stm;
        rule* r = m_inf_sort.back();
        stm << "Rule contains infinite sorts in rule ";
        r->display(m_ctx, stm);
        throw default_exception(stm.str());
    }
}

void rule_properties::check_nested_free() {
    if (!m_interp_pred.empty()) {
        std::stringstream stm;
        rule* r = m_interp_pred[0];
        stm << "Rule contains nested predicates ";
        r->display(m_ctx, stm);
        throw default_exception(stm.str());
    }
}

void rule_properties::check_existential_tail() {
    ast_mark visited;
    ptr_vector<expr> todo, tocheck;
    for (unsigned i = 0; i < m_interp_pred.size(); ++i) {
        rule& r = *m_interp_pred[i];
        unsigned ut_size = r.get_uninterpreted_tail_size();
        unsigned t_size  = r.get_tail_size();   
        for (unsigned i = ut_size; i < t_size; ++i) {
            todo.push_back(r.get_tail(i));
        }
    }
    context::contains_pred contains_p(m_ctx);
    check_pred check_pred(contains_p, m);
    
    while (!todo.empty()) {
        expr* e = todo.back(), *e1, *e2;
        todo.pop_back();
        if (visited.is_marked(e)) {
            continue;
        }
        visited.mark(e, true);
        if (m_is_predicate(e)) {
        }
        else if (m.is_and(e) || m.is_or(e)) {
            todo.append(to_app(e)->get_num_args(), to_app(e)->get_args());
        }
        else if (m.is_implies(e, e1, e2)) {
            tocheck.push_back(e1);
            todo.push_back(e2);
        }
        else if (is_quantifier(e)) {
            todo.push_back(to_quantifier(e)->get_expr());
        }
        else if ((m.is_eq(e, e1, e2) || m.is_iff(e, e1, e2)) && 
                 m.is_true(e1)) {
            todo.push_back(e2);
        }
        else if ((m.is_eq(e, e1, e2) || m.is_iff(e, e1, e2)) &&
                 m.is_true(e2)) {
            todo.push_back(e1);
        }
        else {
            tocheck.push_back(e);
        }
    }
    for (unsigned i = 0; i < tocheck.size(); ++i) {
        expr* e = tocheck[i];
        if (check_pred(e)) {
            std::ostringstream out;
            out << "recursive predicate " << mk_ismt2_pp(e, m) << " occurs nested in the body of a rule";
            throw default_exception(out.str());            
        }
    }
}


void rule_properties::insert(ptr_vector<rule>& rules, rule* r) {
    if (rules.empty() || rules.back() != r) {
        rules.push_back(r);
    }
}

void rule_properties::operator()(var* n) { 
}

void rule_properties::operator()(quantifier* n) {
    m_quantifiers.insert(n, m_rule);
}
void rule_properties::operator()(app* n) {
    if (m_is_predicate(n)) {
        insert(m_interp_pred, m_rule);
    }    
    else if (is_uninterp(n) && !m_dl.is_rule_sort(n->get_decl()->get_range())) {
        m_uninterp_funs.insert(n->get_decl(), m_rule);
    }
    else if (m_dt.is_accessor(n)) {
        sort* s = m.get_sort(n->get_arg(0));
        SASSERT(m_dt.is_datatype(s));
        if (m_dt.get_datatype_constructors(s)->size() > 1) {
            m_uninterp_funs.insert(n->get_decl(), m_rule);
        }
    }
    else {
    }

}

void rule_properties::reset() {
    m_quantifiers.reset();
    m_uninterp_funs.reset();
    m_interp_pred.reset();
    m_negative_rules.reset();
    m_inf_sort.reset();
}

