/*++
Copyright (c) 2010 Microsoft Corporation

Module Name:

    quasi_macros.cpp

Abstract:

    <abstract>

Author:

    Christoph Wintersteiger (t-cwinte) 2010-04-23

Revision History:

--*/
#include "ast/macros/quasi_macros.h"
#include "ast/for_each_expr.h"
#include "ast/ast_pp.h"
#include "util/uint_set.h"
#include "ast/rewriter/var_subst.h"

quasi_macros::quasi_macros(ast_manager & m, macro_manager & mm) :
  m_manager(m), 
  m_macro_manager(mm),
  m_rewriter(m),
  m_new_vars(m),
  m_new_eqs(m),
  m_new_qsorts(m) {
}

quasi_macros::~quasi_macros() {
}

void quasi_macros::find_occurrences(expr * e) {
    unsigned j;
    m_todo.reset();
    m_todo.push_back(e);

    // we remember whether we have seen an expr once, or more than once;
    // when we see it the second time, we don't have to visit it another time,
    // as we are only interested in finding unique function applications.
    m_visited_once.reset();
    m_visited_more.reset();

    while (!m_todo.empty()) {
        expr * cur = m_todo.back();
        m_todo.pop_back();

        if (m_visited_more.is_marked(cur))
            continue;

        if (m_visited_once.is_marked(cur))
            m_visited_more.mark(cur, true);

        m_visited_once.mark(cur, true);

        switch (cur->get_kind()) {
            case AST_VAR: break;
            case AST_QUANTIFIER: m_todo.push_back(to_quantifier(cur)->get_expr()); break;
            case AST_APP:
                if (is_non_ground_uninterp(cur)) {
                    func_decl * f = to_app(cur)->get_decl();
                    m_occurrences.insert_if_not_there(f, 0);
                    occurrences_map::iterator it = m_occurrences.find_iterator(f);
                    it->m_value++;
                }
                j = to_app(cur)->get_num_args();
                while (j)
                    m_todo.push_back(to_app(cur)->get_arg(--j));
                break;
            default: UNREACHABLE();
        }
    }
};

bool quasi_macros::is_non_ground_uninterp(expr const * e) const {
    return is_non_ground(e) && is_uninterp(e);
}

bool quasi_macros::is_unique(func_decl * f) const {
    return m_occurrences.find(f) == 1;
}

struct var_dep_proc {
    bit_vector m_bitset;
public:
    var_dep_proc(quantifier * q) { m_bitset.resize(q->get_num_decls(), false); }
    void operator()(var * n) { m_bitset.set(n->get_idx(), true); }
    void operator()(quantifier * n) {}
    void operator()(app * n) {}
    bool all_used() {
        for (unsigned i = 0; i < m_bitset.size() ; i++)
            if (!m_bitset.get(i))
                return false;
        return true;
    }
};

bool quasi_macros::fully_depends_on(app * a, quantifier * q) const {
    // CMW: This checks whether all variables in q are used _somewhere_ deep down in the children of a

    /* var_dep_proc proc(q);
    for_each_expr(proc, a);
    return proc.all_used(); */

    // CMW: This code instead checks that all variables appear at least once as a
    // direct argument of a, i.e., a->get_arg(i) == v for some i
    bit_vector bitset;
    bitset.resize(q->get_num_decls(), false);
    for (unsigned i = 0 ; i < a->get_num_args() ; i++) {
        if (is_var(a->get_arg(i)))
            bitset.set(to_var(a->get_arg(i))->get_idx(), true);
    }

    for (unsigned i = 0; i < bitset.size() ; i++) {
        if (!bitset.get(i))
            return false;
    }

    return true;
}

bool quasi_macros::depends_on(expr * e, func_decl * f) const {
    ptr_vector<expr> todo;
    expr_mark visited;
    todo.push_back(e);
    while(!todo.empty()) {
        expr * cur = todo.back();
        todo.pop_back();

        if (visited.is_marked(cur))
            continue;

        if (is_app(cur)) {
            app * a = to_app(cur);
            if (a->get_decl() == f)
                return true;

            unsigned j = a->get_num_args();
            while (j>0)
                todo.push_back(a->get_arg(--j));
        }

        visited.mark(cur, true);
    }
    return false;
}

bool quasi_macros::is_quasi_macro(expr * e, app_ref & a, expr_ref & t) const {
    // Our definition of a quasi-macro:
    // Forall X. f[X] = T[X], where f[X] is a term starting with symbol f, f is uninterpreted,
    // f[X] contains all universally quantified variables, and f does not occur in T[X].
    TRACE("quasi_macros", tout << "Checking for quasi macro: " << mk_pp(e, m_manager) << std::endl;);

    if (is_forall(e)) {
        quantifier * q = to_quantifier(e);
        expr * qe = q->get_expr();
        if ((m_manager.is_eq(qe))) {
            expr * lhs = to_app(qe)->get_arg(0);
            expr * rhs = to_app(qe)->get_arg(1);

            if (is_non_ground_uninterp(lhs) && is_unique(to_app(lhs)->get_decl()) &&
                !depends_on(rhs, to_app(lhs)->get_decl()) && fully_depends_on(to_app(lhs), q)) {
                a = to_app(lhs);
                t = rhs;
                return true;
            } else if (is_non_ground_uninterp(rhs) && is_unique(to_app(rhs)->get_decl()) &&
                !depends_on(lhs, to_app(rhs)->get_decl()) && fully_depends_on(to_app(rhs), q)) {
                a = to_app(rhs);
                t = lhs;
                return true;
            }
        } else if (m_manager.is_not(qe) && is_non_ground_uninterp(to_app(qe)->get_arg(0)) &&
                   is_unique(to_app(to_app(qe)->get_arg(0))->get_decl())) { // this is like f(...) = false
            a = to_app(to_app(qe)->get_arg(0));
            t = m_manager.mk_false();
            return true;
        } else if (is_non_ground_uninterp(qe) && is_unique(to_app(qe)->get_decl())) { // this is like f(...) = true
            a = to_app(qe);
            t = m_manager.mk_true();
            return true;
        }
    }

    return false;
}

void quasi_macros::quasi_macro_to_macro(quantifier * q, app * a, expr * t, quantifier_ref & macro) {
    m_new_var_names.reset();
    m_new_vars.reset();
    m_new_qsorts.reset();
    m_new_eqs.reset();

    func_decl * f = a->get_decl();

    // CMW: we rely on the fact that all variables in q appear at least once as
    // a direct argument of `a'.

    bit_vector v_seen;
    v_seen.resize(q->get_num_decls(), false);
    for (unsigned i = 0 ; i < a->get_num_args() ; i++) {
        if (!is_var(a->get_arg(i)) ||
            v_seen.get(to_var(a->get_arg(i))->get_idx())) {
            unsigned inx = m_new_var_names.size();
            m_new_name.str("");
            m_new_name << "X" << inx;
            m_new_var_names.push_back(symbol(m_new_name.str().c_str()));
            m_new_qsorts.push_back(f->get_domain()[i]);

            m_new_vars.push_back(m_manager.mk_var(inx + q->get_num_decls(), f->get_domain()[i]));
            m_new_eqs.push_back(m_manager.mk_eq(m_new_vars.back(), a->get_arg(i)));
        } else {
            var * v = to_var(a->get_arg(i));
            m_new_vars.push_back(v);
            v_seen.set(v->get_idx(), true);
        }
    }

    // Reverse the new variable names and sorts. [CMW: There is a smarter way to do this.]
    vector<symbol> new_var_names_rev;
    sort_ref_vector new_qsorts_rev(m_manager);
    unsigned i = m_new_var_names.size();
    while (i > 0) {
        i--;
        new_var_names_rev.push_back(m_new_var_names.get(i));
        new_qsorts_rev.push_back(m_new_qsorts.get(i));
    }

    // We want to keep all the old variables [already reversed]
    for (unsigned i = 0 ; i < q->get_num_decls() ; i++) {
        new_var_names_rev.push_back(q->get_decl_name(i));
        new_qsorts_rev.push_back(q->get_decl_sort(i));
    }

    // Macro  :=  Forall m_new_vars . appl = ITE( m_new_eqs, t, f_else)

    app_ref appl(m_manager);
    expr_ref eq(m_manager);
    appl = m_manager.mk_app(f, m_new_vars.size(), m_new_vars.c_ptr());

    func_decl * fd = m_manager.mk_fresh_func_decl(f->get_name(), symbol("else"),
                                                  f->get_arity(), f->get_domain(),
                                                  f->get_range());
    expr * f_else = m_manager.mk_app(fd, m_new_vars.size(), m_new_vars.c_ptr());

    expr_ref ite(m_manager);
    ite = m_manager.mk_ite(m_manager.mk_and(m_new_eqs.size(), m_new_eqs.c_ptr()), t, f_else);

    eq = m_manager.mk_eq(appl, ite);

    macro = m_manager.mk_quantifier(forall_k, new_var_names_rev.size(),
                                    new_qsorts_rev.c_ptr(), new_var_names_rev.c_ptr(), eq);
}

bool quasi_macros::find_macros(unsigned n, expr * const * exprs) {
    TRACE("quasi_macros", tout << "Finding quasi-macros in: " << std::endl;
                          for (unsigned i = 0 ; i < n ; i++)
                              tout << i << ": " << mk_pp(exprs[i], m_manager) << std::endl; );
    bool res = false;
    m_occurrences.reset();


    // Find out how many non-ground appearences for each uninterpreted function there are
    for (unsigned i = 0 ; i < n ; i++)
        find_occurrences(exprs[i]);

    TRACE("quasi_macros",
        tout << "Occurrences: " << std::endl;
        for (auto & kd : m_occurrences)
            tout << kd.m_key->get_name() << ": " << kd.m_value << std::endl; );

    // Find all macros
    for (unsigned i = 0 ; i < n ; i++) {
        app_ref a(m_manager);
        expr_ref t(m_manager);
        if (is_quasi_macro(exprs[i], a, t)) {
            quantifier_ref macro(m_manager);
            quasi_macro_to_macro(to_quantifier(exprs[i]), a, t, macro);
            TRACE("quasi_macros", tout << "Found quasi macro: " << mk_pp(exprs[i], m_manager) << std::endl;
                                  tout << "Macro: " << mk_pp(macro, m_manager) << std::endl; );
            proof * pr = nullptr;
            if (m_manager.proofs_enabled())
                pr = m_manager.mk_def_axiom(macro);
            expr_dependency * dep = nullptr;
            if (m_macro_manager.insert(a->get_decl(), macro, pr, dep))
                res = true;
        }
    }

    return res;
}

bool quasi_macros::find_macros(unsigned n, justified_expr const * exprs) {
    TRACE("quasi_macros", tout << "Finding quasi-macros in: " << std::endl;
                          for (unsigned i = 0 ; i < n ; i++) 
                              tout << i << ": " << mk_pp(exprs[i].get_fml(), m_manager) << std::endl; );
    bool res = false;
    m_occurrences.reset();
    

    // Find out how many non-ground appearences for each uninterpreted function there are    
    for ( unsigned i = 0 ; i < n ; i++ )
        find_occurrences(exprs[i].get_fml());

    TRACE("quasi_macros", tout << "Occurrences: " << std::endl;
    for (occurrences_map::iterator it = m_occurrences.begin(); 
         it != m_occurrences.end(); 
         it++)
        tout << it->m_key->get_name() << ": " << it->m_value << std::endl; );
   
    // Find all macros
    for ( unsigned i = 0 ; i < n ; i++ ) {
        app_ref a(m_manager);
        expr_ref t(m_manager);
        if (is_quasi_macro(exprs[i].get_fml(), a, t)) {
            quantifier_ref macro(m_manager);
            quasi_macro_to_macro(to_quantifier(exprs[i].get_fml()), a, t, macro);
            TRACE("quasi_macros", tout << "Found quasi macro: " << mk_pp(exprs[i].get_fml(), m_manager) << std::endl;
                                  tout << "Macro: " << mk_pp(macro, m_manager) << std::endl; );
            proof * pr = nullptr;
            if (m_manager.proofs_enabled())
                pr = m_manager.mk_def_axiom(macro);
            if (m_macro_manager.insert(a->get_decl(), macro, pr))
                res = true;
        }
    }

    return res;
}

void quasi_macros::apply_macros(unsigned n, expr * const * exprs, proof * const * prs, expr_dependency * const* deps, expr_ref_vector & new_exprs, proof_ref_vector & new_prs, expr_dependency_ref_vector& new_deps) {     
    for ( unsigned i = 0 ; i < n ; i++ ) {
        expr_ref r(m_manager), rs(m_manager);
        proof_ref pr(m_manager), ps(m_manager);
        expr_dependency_ref dep(m_manager);
        proof * p = m_manager.proofs_enabled() ? prs[i] : nullptr;
        
        m_macro_manager.expand_macros(exprs[i], p, deps[i], r, pr, dep);
        m_rewriter(r);
        new_exprs.push_back(r);
        new_prs.push_back(ps);    
        new_deps.push_back(dep);
    }
}

bool quasi_macros::operator()(unsigned n, expr * const * exprs, proof * const * prs, expr_dependency * const * deps, expr_ref_vector & new_exprs, proof_ref_vector & new_prs, expr_dependency_ref_vector & new_deps) {
    if (find_macros(n, exprs)) {
        apply_macros(n, exprs, prs, deps, new_exprs, new_prs, new_deps);
        return true;
    } 
    else {
        // just copy them over
        for ( unsigned i = 0 ; i < n ; i++ ) {
            new_exprs.push_back(exprs[i]);
            if (m_manager.proofs_enabled())
                new_prs.push_back(prs[i]);
        }
        return false;
    }
}

void quasi_macros::apply_macros(unsigned n, justified_expr const* fmls, vector<justified_expr>& new_fmls) {     
    for ( unsigned i = 0 ; i < n ; i++ ) {
        expr_ref r(m_manager), rs(m_manager);
        proof_ref pr(m_manager), ps(m_manager);
        proof * p = m_manager.proofs_enabled() ? fmls[i].get_proof() : nullptr;
        expr_dependency_ref dep(m_manager);
        m_macro_manager.expand_macros(fmls[i].get_fml(), p, nullptr, r, pr, dep);
        m_rewriter(r);
        new_fmls.push_back(justified_expr(m_manager, r, pr));
    }
}

bool quasi_macros::operator()(unsigned n, justified_expr const* fmls, vector<justified_expr>& new_fmls) {
    if (find_macros(n, fmls)) {
        apply_macros(n, fmls, new_fmls);
        return true;
    } else {
        // just copy them over
        for ( unsigned i = 0 ; i < n ; i++ ) {
            new_fmls.push_back(fmls[i]);
        }
        return false;
    }    
}
