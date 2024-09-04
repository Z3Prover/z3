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

#include "ast/expr_functors.h"
#include "ast/for_each_expr.h"
#include "ast/rewriter/th_rewriter.h"
#include "muz/base/rule_properties.h"
#include "muz/base/dl_rule_set.h"
#include "muz/base/dl_context.h"

using namespace datalog;
rule_properties::rule_properties(ast_manager & m, rule_manager& rm, context& ctx, i_expr_pred& p): 
    m(m), rm(rm), m_ctx(ctx), m_is_predicate(p), 
    m_dt(m), m_dl(m), m_a(m), m_bv(m), m_ar(m), m_rec(m), 
    m_generate_proof(false), m_collected(false), m_is_monotone(true) {}

void rule_properties::collect(rule_set const& rules) {
    reset();
    m_collected = true;
    expr_sparse_mark visited;
    visit_rules(visited, rules);
}

void rule_properties::visit_rules(expr_sparse_mark& visited, rule_set const& rules) {
    for (rule* r : rules) {
        m_rule = r;
        unsigned ut_size = r->get_uninterpreted_tail_size();
        unsigned t_size  = r->get_tail_size();  
        if (r->has_negation()) {
            m_is_monotone = false;
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
            check_sort(d);
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

static const std::string qkind_str(quantifier_kind qkind) {
    switch (qkind) {
    case forall_k: return "FORALL";
    case exists_k: return "EXISTS";
    case lambda_k: return "LAMBDA";
    default: UNREACHABLE(); return "";
    }
}

void rule_properties::check_quantifier_free(quantifier_kind qkind) {
    for (auto &kv : m_quantifiers) {
        if (kv.get_key().get_kind() == qkind) {
            rule *r = kv.get_value();
            std::stringstream stm;
            stm << "cannot process " << qkind_str(qkind) << " quantifier in rule ";
            r->display(m_ctx, stm);
            throw default_exception(stm.str());
        } 
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

void rule_properties::check_background_free() {
    if (m_ctx.get_num_assertions() > 0)
        throw default_exception("engine does not support background assertions");
}


void rule_properties::check_existential_tail() {
    ast_mark visited;
    ptr_vector<expr> todo, tocheck;
    for (rule* r : m_interp_pred) {
        unsigned ut_size = r->get_uninterpreted_tail_size();
        unsigned t_size  = r->get_tail_size();   
        for (unsigned i = ut_size; i < t_size; ++i) {
            todo.push_back(r->get_tail(i));
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
            tocheck.push_back(to_quantifier(e)->get_expr());
        }
        else if (m.is_eq(e, e1, e2) && m.is_true(e1)) {
            todo.push_back(e2);
        }
        else if (m.is_eq(e, e1, e2) && m.is_true(e2)) {
            todo.push_back(e1);
        }
        else {
            tocheck.push_back(e);
        }
    }
    for (expr* e : tocheck) {
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
    check_sort(n->get_sort());
}

void rule_properties::operator()(quantifier* n) {
    m_quantifiers.insert(n, m_rule);
}

bool rule_properties::check_accessor(app* n) {
    sort* s = n->get_arg(0)->get_sort();
    SASSERT(m_dt.is_datatype(s));
    if (m_dt.get_datatype_constructors(s)->size() <= 1)
        return true;
    
    func_decl* f = n->get_decl();
    func_decl* c = m_dt.get_accessor_constructor(f);
    unsigned ut_size = m_rule->get_uninterpreted_tail_size();
    unsigned t_size  = m_rule->get_tail_size();
    ptr_vector<func_decl> ctors;

    // add recognizer constructor to ctors
    auto add_recognizer = [&](expr* r) {
        if (!m_dt.is_recognizer(r))
            return;
        if (n->get_arg(0) != to_app(r)->get_arg(0))
            return;
        auto* c2 = m_dt.get_recognizer_constructor(to_app(r)->get_decl());
        if (c == c2)
            return;
        ctors.push_back(c2);
    };
    auto add_not_recognizer = [&](expr* r) {
        if (m.is_not(r, r))
            add_recognizer(r);
    };

    // t is a recognizer for n
    auto is_recognizer_base = [&](expr* t) {
        return m_dt.is_recognizer(t) &&
            to_app(t)->get_arg(0) == n->get_arg(0) &&
            m_dt.get_recognizer_constructor(to_app(t)->get_decl()) == c;
    };
    auto is_recognizer = [&](expr* t) {
        if (m.is_and(t))
            for (expr* arg : *to_app(t))
                if (is_recognizer_base(arg))
                    return true;
        return is_recognizer_base(t);
    };

    for (unsigned i = ut_size; i < t_size; ++i) {
        auto* tail = m_rule->get_tail(i);
        if (is_recognizer(tail))
            return true;
        add_not_recognizer(tail);
    }

    // create parent use list for every sub-expression in the rule
    obj_map<expr, ptr_vector<expr>> use_list;
    for (unsigned i = ut_size; i < t_size; ++i) {
        app* t = m_rule->get_tail(i);
        use_list.insert_if_not_there(t, ptr_vector<expr>()).push_back(nullptr); // add marker for top-level expression.
        for (expr* sub : subterms::all(expr_ref(t, m)))
            if (is_app(sub)) 
                for (expr* arg : *to_app(sub))
                    use_list.insert_if_not_there(arg, ptr_vector<expr>()).push_back(sub);
    }

    // walk parents of n depth first to check that each path is guarded by a recognizer.
    vector<std::tuple<expr *, unsigned int, bool>> todo;
    todo.push_back({n, ctors.size(), false});
    while(!todo.empty()) {
        auto [e, ctors_size, visited] = todo.back();
        if (visited) {
            todo.pop_back();
            while (ctors.size() > ctors_size) ctors.pop_back();
            continue;
        }
        std::get<2>(todo.back()) = true; // set visited

        if (!use_list.contains(e))
            return false;
        for (expr* parent : use_list[e]) {
            if (!parent) { // top-level expression
                // check if n is an unguarded "else" branch
                ptr_vector<func_decl> diff;
                for (auto* dtc : *m_dt.get_datatype_constructors(s))
                    if (!ctors.contains(dtc))
                        diff.push_back(dtc);
                // the only unguarded constructor for s is c:
                // all the others are guarded and we are in an "else" branch so the accessor is safe
                if (diff.size() == 1 && diff[0] == c)
                    continue;
                return false; // the accessor is not safe
            }
            if (is_recognizer(parent))
                continue;

            expr *cnd, *thn, *els;
            if (m.is_ite(parent, cnd, thn, els)) {
                if (thn == e) {
                    if (is_recognizer(cnd) && els != e)
                        continue; // e is guarded
                }
                add_recognizer(cnd);
            }
            if (m.is_and(parent))
                for (expr* arg : *to_app(parent))
                    add_not_recognizer(arg);
            if (m.is_or(parent))
                for (expr* arg : *to_app(parent)) {
                    add_recognizer(arg);
                    // if one branch is not(recognizer) then the accessor is safe
                    if (m.is_not(arg, arg) && is_recognizer(arg))
                        goto _continue;
                }
            todo.push_back({parent, ctors.size(), false});
        _continue:;
        }
    }

    return true;
}

void rule_properties::operator()(app* n) {
    func_decl_ref f_out(m);
    expr* n1 = nullptr, *n2 = nullptr;
    func_decl* f = n->get_decl();
    rational r;
    if (m_is_predicate(n)) {
        insert(m_interp_pred, m_rule);
    }    
    else if (is_uninterp(n) && !m_dl.is_rule_sort(f->get_range())) {
        m_uninterp_funs.insert(f, m_rule);
    }
    else if (m_dt.is_accessor(n)) {
        if (!check_accessor(n))
            m_uninterp_funs.insert(f, m_rule);            
        
    }
    else if (m_a.is_considered_uninterpreted(f, n->get_num_args(), n->get_args(), f_out)) {
        m_uninterp_funs.insert(f, m_rule);
    }
    else if ((m_a.is_mod(n, n1, n2) || m_a.is_div(n, n1, n2) ||
              m_a.is_idiv(n, n1, n2) || m_a.is_rem(n, n1, n2))
             && (!evaluates_to_numeral(n2, r) || r.is_zero())) {
        m_uninterp_funs.insert(f, m_rule);
    }
    else if (m_rec.is_defined(f)) {
        m_uninterp_funs.insert(f, m_rule);
    }
    check_sort(n->get_sort());
}

bool rule_properties::evaluates_to_numeral(expr * n, rational& val) {    
    if (m_a.is_numeral(n, val))
        return true;
    th_rewriter rw(m);
    expr_ref tmp(n, m);
    rw(tmp);
    return m_a.is_numeral(tmp, val);
}


void rule_properties::check_sort(sort* s) {
    sort_size sz = s->get_num_elements();
    if (m_ar.is_array(s) || (!sz.is_finite() && !m_dl.is_rule_sort(s))) {
        m_inf_sort.push_back(m_rule);
    }
}

void rule_properties::reset() {
    m_quantifiers.reset();
    m_uninterp_funs.reset();
    m_interp_pred.reset();
    m_negative_rules.reset();
    m_inf_sort.reset();
    m_collected = false;
    m_generate_proof = false;
}

