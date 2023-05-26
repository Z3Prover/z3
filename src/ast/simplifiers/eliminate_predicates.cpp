/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    eliminate_predicates.cpp

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-17.

Notes:

The simplifier 
- detects macros of the form p(x) = q(x)
  - other more general macro detection is TBD. 
    For example {~p, a} {~p, b} {p, ~a, ~b} {p, C} {~p, D} defines p as a conjunction
    and we can obbtain {a, C}, {b, C} {~a, ~b, D } similar to propositional case.
    Instead the case is handled by predicate elimination when p only occurs positively 
    outside of {~p, a} {~p, b} {p, ~a, ~b} 
    The SAT based definition detection scheme creates clauses 
    {a}, {b}, {~a,~b}, C, D and checks for an unsat core.
    The core {a}, {b}, {~a, ~b} maps back to a definition for p
    Then {p, C}, {~p, D} clauses are replaced based on the definition.
    Claim: {C, D} is a consequence when we have created resolvents {C,X}, {D,Y}, where X => p => Y => X
    (a task for a "Kitten"?)
  - Handle various permutations of variables that are arguments to p?
  - other SMT-based macro detection could be made here as well.
    The (legacy) macro finder is not very flexible and could be replaced
    by a module building on this one. 


- eliminates predicates p(x) that occur at most once in each clause and the
  number of occurrences is small.

Two sets of disabled functions are tracked:

forbidden from macros vs forbidden from elimination
  - forbidden from macros: uninterpreted functions in recursive definitions
                           predicates before m_qhead
                           arguments to as-array
  - forbidden from elimination:
    - forbidden from macros,
    - occurs more than once in some clause, or in nested occurrence.

--*/


#include "util/uint_set.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_util.h"
#include "ast/for_each_ast.h"
#include "ast/recfun_decl_plugin.h"
#include "ast/bv_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/occurs.h"
#include "ast/array_decl_plugin.h"
#include "ast/rewriter/var_subst.h"
#include "ast/rewriter/rewriter_def.h"
#include "ast/simplifiers/eliminate_predicates.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/rewriter/macro_replacer.h"


std::ostream& eliminate_predicates::clause::display(std::ostream& out) const {
    ast_manager& m = m_dep.get_manager();
    for (sort* s : m_bound)
        out << mk_pp(s, m) << " ";
    for (auto const& [atom, sign] : m_literals)
        out << (sign ? "~" : "") << mk_bounded_pp(atom, m) << " ";
    return out;
}

eliminate_predicates::eliminate_predicates(ast_manager& m, dependent_expr_state& fmls):
    dependent_expr_simplifier(m, fmls), m_der(m), m_rewriter(m) {}


void eliminate_predicates::add_use_list(clause& cl) {
    ast_mark seen;
    for (auto const& [atom, sign] : cl.m_literals) {        
        if (!is_uninterp(atom)) {
            m_to_exclude.push_back(atom);
            continue;
        }
        
        func_decl* p = to_app(atom)->get_decl();
        m_use_list.get(p, sign).push_back(&cl);
        
        if (!m_predicate_decls.is_marked(p)) {
            m_predicates.push_back(p);
            m_predicate_decls.mark(p, true);
        }
        if (seen.is_marked(p)) 
            m_to_exclude.push_back(atom);
        else {
            seen.mark(p, true);
            m_to_exclude.append(to_app(atom)->get_num_args(), to_app(atom)->get_args());
        }
    }
}

/**
* Check that all arguments are distinct variables that are bound.
*/

bool eliminate_predicates::can_be_macro_head(expr* _head, unsigned num_bound) {
    if (!is_app(_head))
        return false;
    app* head = to_app(_head);
    func_decl* f = head->get_decl();
    if (m_fmls.frozen(f))
        return false;
    if (m_is_macro.is_marked(f))
        return false;
    if (f->is_associative())
        return false;
    if (!is_uninterp(f))
        return false;
    uint_set indices;
    for (expr* arg : *head) {
        if (!is_var(arg))
            return false;
        unsigned idx = to_var(arg)->get_idx();
        if (indices.contains(idx))
            return false;
        if (idx >= num_bound)
            return false;
        indices.insert(idx);
    }
    return true;
}

/**
 * a quasi macro head is of the form 
 * f(x,x)   where x is the only bound variable
 * f(x,y,x+y+3,1) where x, y are the only bound variables
 */

bool eliminate_predicates::can_be_quasi_macro_head(expr* _head, unsigned num_bound) {
    if (!is_app(_head))
        return false;
    app* head = to_app(_head);
    func_decl* f = head->get_decl();
    if (m_fmls.frozen(f))
        return false;
    if (m_is_macro.is_marked(f))
        return false;
    if (f->is_associative())
        return false;
    if (!is_uninterp(f))
        return false;
    uint_set indices;
    for (expr* arg : *head) {
        if (occurs(f, arg))
            return false;
        if (!is_macro_safe(arg))
            return false;
        if (!is_var(arg))
            continue;
        unsigned idx = to_var(arg)->get_idx();
        if (indices.contains(idx))
            continue;
        if (idx >= num_bound)
            return false;
        indices.insert(idx);
    }
    return indices.num_elems() == num_bound;
}


//
// (= (f x y (+ x y)) s), where x y are all bound variables.    
// then replace (f x y z) by (if (= z (+ x y)) s (f' x y z))
//

void eliminate_predicates::insert_quasi_macro(app* head, expr* body, clause& cl) {
    expr_ref _body(body, m);
    uint_set indices;
    expr_ref_vector args(m), eqs(m);
    var_ref new_var(m);
    app_ref lhs(m), rhs(m);
    func_decl_ref f1(m);
    sort_ref_vector sorts(m);
    svector<symbol> names;

    unsigned num_decls = cl.m_bound.size();
    func_decl* f = head->get_decl();
    
    for (expr* arg : *head) {
        sorts.push_back(arg->get_sort());
        names.push_back(symbol(std::string("x") + std::to_string(args.size())));
        if (is_var(arg)) {
            unsigned idx = to_var(arg)->get_idx();
            if (!indices.contains(idx)) {
                indices.insert(idx);
                args.push_back(arg);
                continue;
            }
        }
        new_var = m.mk_var(eqs.size() + num_decls, arg->get_sort());
        args.push_back(new_var);
        eqs.push_back(m.mk_eq(arg, new_var));
    }    
    
    // forall vars . f(args) = if eqs then body else f'(args)
    f1 = m.mk_fresh_func_decl(f->get_name(), symbol::null, sorts.size(), sorts.data(), f->get_range());

    lhs = m.mk_app(f, args);
    rhs = m.mk_ite(mk_and(eqs), body, m.mk_app(f1, args));
    insert_macro(lhs, rhs, cl);
}



expr_ref eliminate_predicates::bind_free_variables_in_def(clause& cl, app* head, expr* def) {
    unsigned num_bound = cl.m_bound.size();
    if (head->get_num_args() == num_bound)
        return expr_ref(def, m);

    // head(x) <=> forall yx', x = x' => def(yx')
    svector<symbol> names;
    expr_ref_vector ors(m);
    expr_ref result(m);
    ors.push_back(def);

    for (unsigned i = 0; i < num_bound; ++i)
        names.push_back(symbol(i));
    for (expr* arg : *head) {
        unsigned idx = to_var(arg)->get_idx();
        ors.push_back(m.mk_not(m.mk_eq(arg, m.mk_var(idx + num_bound, arg->get_sort()))));
    }
    result = mk_or(ors);
    result = m.mk_forall(num_bound, cl.m_bound.data(), names.data(), result);
    rewrite(result);
    return result;
}
/**
* cheap/simplistic heuristic to find definitions that are based on binary clauses
* (or (head x) (not (def x))
* (or (not (head x)) (def x))
*/
bool eliminate_predicates::try_find_binary_definition(func_decl* p, app_ref& head, expr_ref& def, expr_dependency_ref& dep) {
    if (m_fmls.frozen(p))
        return false;
    expr_mark binary_pos, binary_neg;
    obj_map<expr, expr_dependency*> deps;
    auto is_def_predicate = [&](clause& cl, expr* atom) {
        return is_app(atom) && to_app(atom)->get_decl() == p && can_be_macro_head(to_app(atom), cl.m_bound.size());
    };
    auto add_def = [&](clause& cl, expr* atom1, bool sign1, expr* atom2, bool sign2) {
        if (is_def_predicate(cl, atom1) && !sign1) {
            if (sign2)
                binary_neg.mark(atom2);
            else
                binary_pos.mark(atom2);
            if (cl.m_dep)
                deps.insert(atom1, cl.m_dep);
        }
    };

    for (auto* cl : m_use_list.get(p, false)) {
        if (cl->m_alive && cl->size() == 2) {
            auto const& [atom1, sign1] = cl->m_literals[0];
            auto const& [atom2, sign2] = cl->m_literals[1];
            add_def(*cl, atom1, sign1, atom2, sign2);
            add_def(*cl, atom2, sign2, atom1, sign1);
        }
    }

    auto is_def = [&](unsigned i, unsigned j, clause& cl) {
        auto const& [atom1, sign1] = cl.m_literals[i];
        auto const& [atom2, sign2] = cl.m_literals[j];
        expr_dependency* d = nullptr;
        if (is_def_predicate(cl, atom1) && sign1) {
            if (sign2 && binary_pos.is_marked(atom2) && is_macro_safe(atom2) && !occurs(p, atom2)) {
                head = to_app(atom1);
                def = bind_free_variables_in_def(cl, head, m.mk_not(atom2));
                dep = cl.m_dep;
                if (deps.find(atom1, d))
                    dep = m.mk_join(dep, d);                    
                return true;
            }
            if (!sign2 && binary_neg.is_marked(atom2) && is_macro_safe(atom2) && !occurs(p, atom2)) {
                head = to_app(atom1);
                def = bind_free_variables_in_def(cl, head, atom2);
                dep = cl.m_dep;
                if (deps.find(atom1, d))
                    dep = m.mk_join(dep, d);
                return true;
            }
        }
        return false;
    };

    for (auto* cl : m_use_list.get(p, true)) {
        if (cl->m_alive && cl->size() == 2) {
            if (is_def(0, 1, *cl))
                return true;
            if (is_def(1, 0, *cl))
                return true;
        }
    }
    return false;
}

bool eliminate_predicates::is_macro_safe(expr* e) {
    for (expr* arg : subterms::all(expr_ref(e, m))) 
        if (is_app(arg) && m_is_macro.is_marked(to_app(arg)->get_decl()))
            return false;    
    return true;
}

void eliminate_predicates::insert_macro(app* head, expr* def, clause& cl) {
    insert_macro(head, def, cl.m_dep);
    TRACE("elim_predicates", tout << "remove " << cl << "\n");
    cl.m_alive = false;
}

void eliminate_predicates::insert_macro(app* head, expr* def, expr_dependency* dep) {
    unsigned num = head->get_num_args();
    ptr_buffer<expr> vars, subst_args;
    subst_args.resize(num, nullptr);
    vars.resize(num, nullptr);
    for (unsigned i = 0; i < num; i++) {
        var* v = to_var(head->get_arg(i));
        var* w = m.mk_var(i, v->get_sort());
        unsigned idx = v->get_idx();
        VERIFY(idx < num);
        SASSERT(subst_args[idx] == 0);        
        subst_args[idx] = w;
        vars[i] = w;
    }
    var_subst sub(m, false);
    app_ref _head(m);
    expr_ref _def(m);
    expr_dependency_ref _dep(dep, m);
    _def = sub(def, subst_args.size(), subst_args.data());
    _head = m.mk_app(head->get_decl(), vars);
    
    auto* info = alloc(macro_def, _head, _def, _dep);
    m_macros.insert(head->get_decl(), info);
    m_fmls.model_trail().push(head->get_decl(), _def, _dep, {}); // augment with definition for head
    m_is_macro.mark(head->get_decl(), true);    
    TRACE("elim_predicates", tout << "insert " << _head << " " << _def << "\n");
    ++m_stats.m_num_macros;
}

void eliminate_predicates::try_resolve_definition(func_decl* p) {
    app_ref head(m);
    expr_ref def(m);
    expr_dependency_ref dep(m);
    if (try_find_binary_definition(p, head, def, dep)) 
        insert_macro(head, def, dep);    
}

/**
* Port of macros handled by macro_finder/macro_util
*/
void eliminate_predicates::try_find_macro(clause& cl) {
    if (!cl.m_alive)
        return;
    expr* x, * y;
    auto can_be_def = [&](expr* _x, expr* y) {
        if (!is_app(_x))
            return false;
        app* x = to_app(_x);
        return 
            can_be_macro_head(x, cl.m_bound.size()) &&
            is_macro_safe(y) &&
            x->get_num_args() == cl.m_bound.size() &&
            !occurs(x->get_decl(), y);
    };
    // (= (f x) t)
    if (cl.is_unit() && !cl.sign(0) && m.is_eq(cl.atom(0), x, y)) {
        if (can_be_def(x, y)) {
            insert_macro(to_app(x), y, cl);
            return;
        }
        if (can_be_def(y, x)) {
            insert_macro(to_app(y), x, cl);
            return;
        }
    }
    // not (= (p x) t) -> (p x) = (not t)
    if (cl.is_unit() && cl.sign(0) && m.is_iff(cl.atom(0), x, y)) {
        if (can_be_def(x, y)) {
            insert_macro(to_app(x), m.mk_not(y), cl);
            return;
        }
        if (can_be_def(y, x)) {
            insert_macro(to_app(y), m.mk_not(x), cl);
            return;
        }
    }

    // pseudo-macros: 
    // (iff (= (f x) t) cond)
    // rewrites to (f x) = (if cond t else (k x))
    // add clause (not (= (k x) t))
    // 
    // we will call them _conditioned_ macros

    auto can_be_conditioned = [&](expr* f, expr* t, expr* cond) {
        return 
            can_be_def(f, t) &&
            !occurs(to_app(f)->get_decl(), cond) &&
            is_macro_safe(cond);
    };

    auto make_conditioned = [&](app* f, expr* t, expr* cond) {
        func_decl* df = f->get_decl();
        app_ref def(m), k(m), fml(m);
        func_decl_ref fn(m);
        fn = m.mk_fresh_func_decl(df->get_arity(), df->get_domain(), df->get_range());
        m_fmls.model_trail().hide(fn); // hide definition of fn
        k = m.mk_app(fn, f->get_num_args(), f->get_args());        
        def = m.mk_ite(cond, t, k);
        insert_macro(f, def, cl);
        fml = m.mk_not(m.mk_eq(k, t));
        clause* new_cl = init_clause(fml, cl.m_dep, UINT_MAX);
        add_use_list(*new_cl);
        m_clauses.push_back(new_cl);        
    };

    if (cl.is_unit() && !cl.sign(0) && m.is_iff(cl.atom(0), x, y)) {
        expr* z, * u;
        if (m.is_eq(x, z, u) && can_be_conditioned(z, u, y)) {
            make_conditioned(to_app(z), u, y);
            return;
        }
        if (m.is_eq(x, u, z) && can_be_conditioned(z, u, y)) {
            make_conditioned(to_app(z), u, y);
            return;
        }
        if (m.is_eq(y, z, u) && can_be_conditioned(z, u, x)) {
            make_conditioned(to_app(z), u, x);
            return;
        }
        if (m.is_eq(y, u, z) && can_be_conditioned(z, u, x)) {
            make_conditioned(to_app(z), u, x);
            return;
        }
    }

    //
    // other macros handled by macro_finder:
    //
    // arithmetic/bit-vectors
    // (= (+ (f x) s) t) 
    // becomes (= (f x) (- t s))
    //
    // (= (+ (* -1 (f x)) x) t)
    // becomes (= (f x) (- (- t s)))

    bv_util bv(m);
    arith_util a(m);
    auto is_add = [&](expr * e) {
        rational n;
        return a.is_add(e) || bv.is_bv_add(e);
    };

    auto sub = [&](expr* t, expr* s) {
        if (a.is_int_real(t))
            return expr_ref(a.mk_sub(t, s), m);
        else
            return expr_ref(bv.mk_bv_sub(t, s), m);
    };

    auto subtract = [&](expr* t, app* s, unsigned i) {
        expr_ref result(t, m);
        unsigned j = 0;
        for (expr* arg : *s) {
            ++j;
            if (i != j)
                result = sub(result, arg);
        }
        return result;
    };

    auto uminus = [&](expr* t) {
        if (a.is_int_real(t))
            return expr_ref(a.mk_uminus(t), m);
        else
            return expr_ref(bv.mk_bv_neg(t), m);
    };

    auto is_inverse = [&](expr*& t) {
        expr* x, * y;
        rational n;
        if (a.is_mul(t, x, y) && a.is_numeral(x, n) && n == -1) {
            t = y;
            return true;
        }
        if (bv.is_bv_mul(t, x, y) && bv.is_numeral(x, n) && n + 1 == rational::power_of_two(bv.get_bv_size(t))) {
            t = y;
            return true;
        }
        return false;
    };

    auto find_arith_macro = [&](expr* x, expr* y) {
        if (!is_add(x))
            return false;

        if (!is_macro_safe(y))
            return false;

        unsigned i = 0;
        for (expr* arg : *to_app(x)) {
            ++i;
            bool inv = is_inverse(arg);
            if (!can_be_macro_head(arg, cl.m_bound.size()))
                continue;            
            app* head = to_app(arg);
            func_decl* f = head->get_decl();
            if (head->get_num_args() != cl.m_bound.size())
                continue;
            if (occurs(f, y))
                continue;
            unsigned j = 0;
            for (expr* arg2 : *head) {
                ++j;
                if (i == j)
                    continue;
                if (occurs(f, arg2))
                    goto next;
                if (!is_macro_safe(arg2))
                    goto next;
            }
            {
                // arg = y - x - arg;
                expr_ref y1 = subtract(y, to_app(x), i);
                if (inv) 
                    y1 = uminus(y1);                
                insert_macro(to_app(arg), y1, cl);
                return true;
            }
        next:
            ;
        }
        return false;
    };

    if (cl.is_unit() && !cl.sign(0) && m.is_eq(cl.atom(0), x, y)) {
        if (find_arith_macro(x, y))
            return;
        if (find_arith_macro(y, x))
            return;
    }


    //
    // macro_finder also has:
    // (>= (+ (f x) s) t)
    // becomes (= (f x) (- t s (k x))
    // add (>= (k x) 0)
    // why is this a real improvement?
    //
    
    //
    // quasi-macros
    // (= (f x y (+ x y)) s), where x y are all bound variables.    
    // then replace (f x y z) by (if (= z (+ x y)) s (f' x y z))
    //
    auto can_be_qdef = [&](expr* _x, expr* y) {
        if (!is_app(_x))
            return false;
        app* x = to_app(_x);
        return 
            can_be_quasi_macro_head(x, cl.m_bound.size()) && 
            is_macro_safe(y) &&
            !occurs(x->get_decl(), y);
    };

    if (cl.is_unit() && m.is_eq(cl.atom(0), x, y) && !cl.m_bound.empty()) {
        if (!cl.sign(0) && can_be_qdef(x, y)) {
            insert_quasi_macro(to_app(x), y, cl);
            return;
        }
        else if (!cl.sign(0) && can_be_qdef(y, x)) {
            insert_quasi_macro(to_app(y), x, cl);        
            return;
        }
        else if (cl.sign(0) && m.is_bool(y) && can_be_qdef(x, y)) {
            insert_quasi_macro(to_app(x), m.mk_not(y), cl);
            return;
        }
        else if (cl.sign(0) && m.is_bool(y) && can_be_qdef(y, x)) {
            insert_quasi_macro(to_app(y), m.mk_not(x), cl);
            return;
        }
    }
    if (cl.is_unit() && !cl.m_bound.empty()) {
        expr* body = cl.sign(0) ? m.mk_false() : m.mk_true();
        expr* x = cl.atom(0);
        if (can_be_qdef(x, body)) {
            insert_quasi_macro(to_app(x), body, cl);
            return;            
        }
    }
}


void eliminate_predicates::find_definitions() {
    for (auto* p : m_predicates)
        try_resolve_definition(p);
    for (auto* cl : m_clauses)
        try_find_macro(*cl);
}

void eliminate_predicates::rewrite(expr_ref& t) {
    proof_ref pr(m);
    m_der(t, t, pr);
    m_rewriter(t);
}

void eliminate_predicates::reduce_definitions() {
    if (m_macros.empty())
        return;
    
    macro_replacer macro_expander(m);
    for (auto const& [k, v] : m_macros) 
        macro_expander.insert(v->m_head, v->m_def, v->m_dep);
    
    for (unsigned i : indices()) {
        auto [f, p, d] = m_fmls[i]();
        expr_ref fml(f, m), new_fml(m);
        expr_dependency_ref dep(d, m);
        while (true) {
            macro_expander(fml, dep, new_fml, dep);
            if (new_fml == fml)
                break;
            rewrite(new_fml);
            fml = new_fml;
        }
        m_fmls.update(i, dependent_expr(m, fml, nullptr, dep));
    }
    reset();
    init_clauses();
}

void eliminate_predicates::try_resolve(func_decl* p) {
    if (m_disable_elimination.is_marked(p))
        return;
    if (m_fmls.frozen(p))
        return;
    
    unsigned num_pos = 0, num_neg = 0;
    for (auto* cl : m_use_list.get(p, false))
        if (cl->m_alive)
            ++num_pos;
    for (auto* cl : m_use_list.get(p, true))
        if (cl->m_alive)
            ++num_neg;

    TRACE("elim_predicates", tout << "try resolve " << p->get_name() << " " << num_pos << " " << num_neg << "\n");
    
    if (num_pos >= 4 && num_neg >= 2)
        return;
    if (num_neg >= 4 && num_pos >= 2)
        return;
    if (num_neg >= 3 && num_pos >= 3)
        return;

    for (auto* pos : m_use_list.get(p, false)) {
        for (auto* neg : m_use_list.get(p, true)) {
            clause* cl = resolve(p, *pos, *neg);
            if (!cl)
                continue;
            m_clauses.push_back(cl);
            add_use_list(*cl);
            process_to_exclude(m_disable_elimination);
            IF_VERBOSE(11, verbose_stream() << "resolve " << p->get_name() << "\n" << *pos << "\n" << *neg << "\n------\n" << *cl << "\n\n");
        }
    }

    update_model(p);

    for (auto* pos : m_use_list.get(p, false))
        pos->m_alive = false;
    for (auto* neg : m_use_list.get(p, true))
        neg->m_alive = false;

    ++m_stats.m_num_eliminated;
}

//
//  update model for p
// 
// Example, ground case:
// {p, a} {p, b} {-p, c}, {-p, d}
// p <=> !(a & b)
// p <=> c & d 
// 
// Example non-ground cases
// {p(t)} {p(s)} {~p(u)}
// p(x) <=> (x = t or x = s) 
// p(x) <=> x != u
// 
// {p(t), a, b}
// p(x) <=> (x = t & !(a or b))
//
// {~p(t), a, b}
// ~p(x) <=> (x = t & !(a or b))
// p(x) <=> x = t => a or b
// 

void eliminate_predicates::update_model(func_decl* p) {
    expr_ref_vector fmls(m);
    expr_ref def(m);
    expr_dependency_ref dep(m);
    unsigned numpos = 0, numneg = 0;
    vector<dependent_expr> deleted;
    for (auto* pos : m_use_list.get(p, false)) 
        if (pos->m_alive)
            ++numpos;
    for (auto* neg : m_use_list.get(p, true))
        if (neg->m_alive)
            ++numneg;

    if (numpos < numneg) {
        for (auto* pos : m_use_list.get(p, false))
            if (pos->m_alive) {
                fmls.push_back(create_residue_formula(p, *pos));
                dep = m.mk_join(dep, pos->m_dep);
            }
        def = mk_or(fmls);
    }
    else {
        for (auto* neg : m_use_list.get(p, true))
            if (neg->m_alive) {
                fmls.push_back(mk_not(m, create_residue_formula(p, *neg)));
                dep = m.mk_join(dep, neg->m_dep);
            }
        def = mk_and(fmls);
    }

    rewrite(def);
    TRACE("elim_predicates", tout << "insert " << p->get_name() << " " << def << "\n");
    m_fmls.model_trail().push(p, def, dep, deleted);
}

/**
* Convert a clause that contains p(t) into a definition for p
*   forall y . (or p(t) C)
* Into
*   exists y . x = t[y] & !(or C)
*/

expr_ref eliminate_predicates::create_residue_formula(func_decl* p, clause& cl) {
    unsigned num_args = p->get_arity();
    unsigned num_bound = cl.m_bound.size();
    expr_ref_vector ors(m), ands(m);
    expr_ref fml(m);
    app_ref patom(m);
    for (auto const& [atom, sign] : cl.m_literals) {
        if (is_app(atom) && to_app(atom)->get_decl() == p) {
            SASSERT(!patom);
            patom = to_app(atom);
            continue;
        }
        fml = sign ? m.mk_not(atom) : atom.get();
        ors.push_back(fml);
    }
    if (!ors.empty()) {
        fml = mk_not(m, mk_or(ors));
        ands.push_back(fml);
    }
    for (unsigned i = 0; i < num_args; ++i) {
        SASSERT(patom->get_arg(i)->get_sort() == p->get_domain(i));
        ands.push_back(m.mk_eq(patom->get_arg(i), m.mk_var(num_bound + i, p->get_domain(i))));
    }
    fml = m.mk_and(ands);
    if (num_bound > 0) {
        svector<symbol> names;
        for (unsigned i = 0; i < num_bound; ++i)
            names.push_back(symbol(i));
        fml = m.mk_exists(num_bound, cl.m_bound.data(), names.data(), fml, 1);
    }
    return fml;
}

/**
* Resolve p in clauses pos, neg where p occurs only once.
*/
eliminate_predicates::clause* eliminate_predicates::resolve(func_decl* p, clause& pos, clause& neg) {
    var_shifter sh(m);
    expr_dependency_ref dep(m);
    dep = m.mk_join(pos.m_dep, neg.m_dep);
    expr_ref new_lit(m);
    expr_ref_vector lits(m);
    expr* plit = nullptr, * nlit = nullptr;
    
    for (auto const& [lit, sign] : pos.m_literals)
        if (is_app(lit) && to_app(lit)->get_decl() == p)
            plit = lit;
        else
            lits.push_back(sign ? m.mk_not(lit) : lit.get());
    for (auto const & [lit, sign] : neg.m_literals) {
        if (is_app(lit) && to_app(lit)->get_decl() == p)
            nlit = lit;
        else {
            sh(lit, pos.m_bound.size(), new_lit);
            lits.push_back(sign ? m.mk_not(new_lit) : new_lit.get());
        }
    }
    sh(nlit, pos.m_bound.size(), new_lit);
    for (unsigned i = 0; i < p->get_arity(); ++i) {
        expr* a = to_app(plit)->get_arg(i);
        expr* b = to_app(new_lit)->get_arg(i);
        if (a != b)
            lits.push_back(m.mk_not(m.mk_eq(a, b)));
    }

    expr_ref cl = mk_or(lits);
    ptr_vector<sort> bound;
    bound.append(neg.m_bound);
    bound.append(pos.m_bound);
    if (!bound.empty()) {
        svector<symbol> names;
        for (unsigned i = 0; i < bound.size(); ++i)
            names.push_back(symbol(i));
        cl = m.mk_forall(bound.size(), bound.data(), names.data(), cl, 1);
    }
    rewrite(cl);
    if (m.is_true(cl))
        return nullptr;
    return init_clause(cl, dep, UINT_MAX);    
}

void eliminate_predicates::try_resolve() {
    for (auto* f : m_predicates)
        try_resolve(f);
}

/**
* Process the terms m_to_exclude, walk all subterms.
* Uninterpreted function declarations in these terms are added to 'exclude_set'
*/
void eliminate_predicates::process_to_exclude(ast_mark& exclude_set) {
    ast_mark visited;
    struct proc {        
        ast_mark&   to_exclude;
        proc(ast_mark& f) : 
            to_exclude(f) {}
        void operator()(func_decl* f) {
            if (is_uninterp(f))
                to_exclude.mark(f, true);
        }
        void operator()(ast* s) {}
    };
    proc proc(exclude_set);

    for (expr* e : m_to_exclude)
        for_each_ast(proc, visited, e);
    m_to_exclude.reset();
}


eliminate_predicates::clause* eliminate_predicates::init_clause(unsigned i) {
    auto [f, p, d] = m_fmls[i]();
    return init_clause(f, d, i);
}

/**
* Create a clause from a formula.
*/
eliminate_predicates::clause* eliminate_predicates::init_clause(expr* f, expr_dependency* d, unsigned i) {
    clause* cl = alloc(clause, m, d);
    cl->m_fml = f;
    cl->m_fml_index = i;
    while (is_forall(f)) {
        cl->m_bound.append(to_quantifier(f)->get_num_decls(), to_quantifier(f)->get_decl_sorts());
        f = to_quantifier(f)->get_expr();
    }
    expr_ref_vector ors(m);
    flatten_or(f, ors);
    for (expr* lit : ors) {
        bool sign = m.is_not(lit, lit);
        cl->m_literals.push_back({ expr_ref(lit, m), sign });
    }       

    // extend macro detection to exploit bijective functions?
    // f(+ x 1) = g(x) -> f(x) = g(- x 1)
    // init_injective(*cl);
    // init_surjective(*cl);
    return cl;
}

/**
* functions in the prefix of qhead are fully disabled
* Create clauses from the suffix, and process subeterms of clauses to be disabled from 
* eliminations.
*/
void eliminate_predicates::init_clauses() {

    m_fmls.freeze_suffix();

    for (unsigned i : indices()) {
        clause* cl = init_clause(i);
        add_use_list(*cl);
        m_clauses.push_back(cl);
    }
    process_to_exclude(m_disable_elimination);
}

/**
 * Ad hoc recognize surjectivity axioms
 * - exists y . f(y) = x
 */
void eliminate_predicates::init_surjective(clause const& cl) {
    if (!cl.is_unit())
        return;
    if (cl.sign(0))
        return;
    if (!is_exists(cl.atom(0)))
        return;
}

/**
 * Ad hoc recognize injectivity axioms
 * - f(x) = f(y) => x = y
 */
void eliminate_predicates::init_injective(clause const& cl) {
    if (cl.size() != 2)
        return;
    if (cl.m_bound.size() != 2)
        return;
    if (cl.sign(0) == cl.sign(1))
        return;
    expr* a = cl.atom(0), *b = cl.atom(1);
    if (!cl.sign(0) && cl.sign(1))
        std::swap(a, b);
    expr* x, *y, *fx, *fy;
    if (!m.is_eq(a, fx, fy))
        return;
    if (!m.is_eq(b, x, y))
        return;
    
    auto is_fx = [&](expr* _fx, func_decl*& f, unsigned& idx) {
        if (!is_app(_fx))
            return false;
        app* fx = to_app(_fx);
        if (fx->get_num_args() != 1)
            return false;
        if (!is_var(fx->get_arg(0)))
            return false;
        f = fx->get_decl();
        idx = to_var(fx->get_arg(0))->get_idx();
        return true;
    };
    func_decl* f1, *f2;
    unsigned idx1, idx2;
    if (!is_fx(fx, f1, idx1))
        return;
    if (!is_fx(fy, f2, idx2))
        return;
    if (idx1 == idx2 || f1 != f2)
        return;

    auto check_var = [&](expr* x, unsigned& idx) {
        if (!is_var(x))
            return false;
        idx = to_var(x)->get_idx();
        return true;
    };
    if (!check_var(x, idx1) || !check_var(y, idx2))
        return;
    if (idx1 == idx2)
        return;
    m_is_injective.mark(f1, true);
}

/**
* Convert clauses to m_fmls
*/
void eliminate_predicates::decompile() {
    for (clause* cl : m_clauses) {
        if (m_fmls.inconsistent())
            break;
        if (cl->m_fml_index != UINT_MAX) {
            if (cl->m_alive)
                continue;
            dependent_expr de(m, m.mk_true(), nullptr, nullptr);
            m_fmls.update(cl->m_fml_index, de);
        }
        else if (cl->m_alive) {
            expr_ref new_cl = cl->m_fml;
            dependent_expr de(m, new_cl, nullptr, cl->m_dep);
            m_fmls.add(de);
        }        
    }
}

void eliminate_predicates::reset() {
    m_predicates.reset();
    m_predicate_decls.reset();
    m_to_exclude.reset();
    m_disable_elimination.reset();
    m_is_macro.reset();
    m_is_injective.reset();
    m_is_surjective.reset();
    for (auto const& [k, v] : m_macros)
        dealloc(v);
    m_macros.reset();
    m_clauses.reset();
    m_use_list.reset();
}


void eliminate_predicates::reduce() {
    reset();
    init_clauses();
    find_definitions();
    reduce_definitions();
    try_resolve();
    decompile();
    reset();
}
