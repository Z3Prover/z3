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


#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/ast_util.h"
#include "ast/for_each_ast.h"
#include "ast/recfun_decl_plugin.h"
#include "ast/occurs.h"
#include "ast/array_decl_plugin.h"
#include "ast/rewriter/var_subst.h"
#include "ast/rewriter/rewriter_def.h"
#include "ast/simplifiers/eliminate_predicates.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/macros/macro_util.h"


/**
* Rewriting formulas using macro definitions.
*/
struct eliminate_predicates::macro_expander_cfg : public default_rewriter_cfg {
    ast_manager& m;
    eliminate_predicates& ep;
    expr_dependency_ref& m_used_macro_dependencies;
    expr_ref_vector m_trail;

    macro_expander_cfg(ast_manager& m, eliminate_predicates& ep, expr_dependency_ref& deps) :
        m(m),
        ep(ep),
        m_used_macro_dependencies(deps),
        m_trail(m)
    {}

    bool rewrite_patterns() const { return false; }
    bool flat_assoc(func_decl* f) const { return false; }
    br_status reduce_app(func_decl* f, unsigned num, expr* const* args, expr_ref& result, proof_ref& result_pr) {
        result_pr = nullptr;
        return BR_FAILED;
    }

    /**
    * adapted from macro_manager.cpp
    */
    bool reduce_quantifier(quantifier* old_q,
        expr* new_body,
        expr* const* new_patterns,
        expr* const* new_no_patterns,
        expr_ref& result,
        proof_ref& result_pr) {

        bool erase_patterns = false;
        for (unsigned i = 0; !erase_patterns && i < old_q->get_num_patterns(); i++) 
            if (old_q->get_pattern(i) != new_patterns[i])
                erase_patterns = true;
        
        for (unsigned i = 0; !erase_patterns && i < old_q->get_num_no_patterns(); i++) 
            if (old_q->get_no_pattern(i) != new_no_patterns[i])
                erase_patterns = true;
        
        if (erase_patterns) 
            result = m.update_quantifier(old_q, 0, nullptr, 0, nullptr, new_body);
        
        if (erase_patterns && m.proofs_enabled()) 
            result_pr = m.mk_rewrite(old_q, result);
        
        return erase_patterns;
    }

    bool get_subst(expr* _n, expr*& r, proof*& p) {
        if (!is_app(_n))
            return false;
        p = nullptr;
        app* n = to_app(_n);
        quantifier* q = nullptr;
        func_decl* d = n->get_decl(), * d2 = nullptr;
        app_ref head(m);
        expr_ref def(m);
        expr_dependency_ref dep(m);
        if (ep.has_macro(d, head, def, dep)) {
            unsigned num = head->get_num_args();
            ptr_buffer<expr> subst_args;
            subst_args.resize(num, 0);
            // TODO: we can exploit that variables occur in "non-standard" order
            // that is in order (:var 0) (:var 1) (:var 2)
            // then substitution just takes n->get_args() instead of this renaming.
            for (unsigned i = 0; i < num; i++) {
                var* v = to_var(head->get_arg(i));
                VERIFY(v->get_idx() < num);
                unsigned nidx = num - v->get_idx() - 1;
                SASSERT(subst_args[nidx] == 0);
                subst_args[nidx] = n->get_arg(i);
            }
            var_subst s(m);
            expr_ref rr = s(def, num, subst_args.data());
            r = rr;
            m_trail.push_back(rr);
            m_used_macro_dependencies = m.mk_join(m_used_macro_dependencies, dep);
            return true;
        }
        
        return false;
    }
};

struct eliminate_predicates::macro_expander_rw : public rewriter_tpl<eliminate_predicates::macro_expander_cfg> {
    eliminate_predicates::macro_expander_cfg m_cfg;

    macro_expander_rw(ast_manager& m, eliminate_predicates& ep, expr_dependency_ref& deps) :
        rewriter_tpl<eliminate_predicates::macro_expander_cfg>(m, false, m_cfg),
        m_cfg(m, ep, deps)
    {}
};


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
* cheap/simplistic heuristic to find definitions that are based on binary clauses
* (or (head x) (not (def x))
* (or (not (head x)) (def x))
*/
bool eliminate_predicates::try_find_binary_definition(func_decl* p, app_ref& head, expr_ref& def, expr_dependency_ref& dep) {
    if (m_disable_macro.is_marked(p))
        return false;
    expr_mark binary_pos, binary_neg;
    macro_util mutil(m);
    obj_map<expr, expr_dependency*> deps;
    auto is_def_predicate = [&](expr* atom) {
        return is_app(atom) && to_app(atom)->get_decl() == p && mutil.is_macro_head(atom, p->get_arity());
    };
    auto add_def = [&](clause& cl, expr* atom1, bool sign1, expr* atom2, bool sign2) {
        if (is_def_predicate(atom1) && !sign1) {
            if (sign2)
                binary_neg.mark(atom2);
            else
                binary_pos.mark(atom2);
            if (cl.m_dep)
                deps.insert(atom1, cl.m_dep);
        }
    };

    for (auto* cl : m_use_list.get(p, false)) {
        if (cl->m_alive && cl->m_literals.size() == 2) {
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
        if (is_def_predicate(atom1) && sign1) {
            if (sign2 && binary_pos.is_marked(atom2) && is_macro_safe(atom2) && !occurs(p, atom2)) {
                head = to_app(atom1);
                def = m.mk_not(atom2);
                dep = cl.m_dep;
                if (deps.find(atom1, d))
                    dep = m.mk_join(dep, d);                    
                return true;
            }
            if (!sign2 && binary_neg.is_marked(atom2) && is_macro_safe(atom2) && !occurs(p, atom2)) {
                head = to_app(atom1);
                def = atom2;
                dep = cl.m_dep;
                if (deps.find(atom1, d))
                    dep = m.mk_join(dep, d);
                return true;
            }
        }
        return false;
    };

    for (auto* cl : m_use_list.get(p, true)) {
        if (cl->m_alive && cl->m_literals.size() == 2) {
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

void eliminate_predicates::insert_macro(app_ref& head, expr_ref& def, expr_dependency_ref& dep) {
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
    def = sub(def, subst_args.size(), subst_args.data());
    head = m.mk_app(head->get_decl(), vars);
    auto* info = alloc(macro_def, head, def, dep);
    m_macros.insert(head->get_decl(), info);
    m_fmls.model_trail().push(head->get_decl(), def, {});
    m_is_macro.mark(head->get_decl(), true);
    TRACE("elim_predicates", tout << "insert " << head << " " << def << "\n");
    ++m_stats.m_num_macros;
}

void eliminate_predicates::try_resolve_definition(func_decl* p) {
    app_ref head(m);
    expr_ref def(m);
    expr_dependency_ref dep(m);
    if (try_find_binary_definition(p, head, def, dep)) 
        insert_macro(head, def, dep);    
}

bool eliminate_predicates::has_macro(func_decl* p, app_ref& head, expr_ref& def, expr_dependency_ref& dep) {
    macro_def* md = nullptr;
    if (m_macros.find(p, md)) {
        head = md->m_head;
        def = md->m_def;
        dep = md->m_dep;
        return true;
    }
    return false;
}

void eliminate_predicates::find_definitions() {
    for (auto* p : m_predicates)
        try_resolve_definition(p);
}

void eliminate_predicates::rewrite(expr_ref& t) {
    proof_ref pr(m);
    m_der(t, t, pr);
    m_rewriter(t);
}

void eliminate_predicates::reduce_definitions() {
    if (m_macros.empty())
        return;
    
    for (unsigned i = m_qhead; i < m_fmls.size(); ++i) {
        auto [f, d] = m_fmls[i]();
        expr_ref fml(f, m), new_fml(m);
        expr_dependency_ref dep(m);
        while (true) {
            macro_expander_rw macro_expander(m, *this, dep);
            macro_expander(fml, new_fml);
            if (new_fml == fml)
                break;
            rewrite(new_fml);
            fml = new_fml;
        }
        if (fml != f) {
            dep = m.mk_join(d, dep);
            m_fmls.update(i, dependent_expr(m, fml, dep));
        }
    }
    reset();
    init_clauses();
}

void eliminate_predicates::try_resolve(func_decl* p) {
    if (m_disable_elimination.is_marked(p))
        return;
    if (m_disable_macro.is_marked(p))
        return;
    
    unsigned num_pos = 0, num_neg = 0;
    for (auto* cl : m_use_list.get(p, false))
        if (cl->m_alive)
            ++num_pos;
    for (auto* cl : m_use_list.get(p, true))
        if (cl->m_alive)
            ++num_neg;

    TRACE("elim_predicates", tout << "try resolve " << p->get_name() << " " << num_pos << " " << num_neg << "\n");
    IF_VERBOSE(0, verbose_stream() << "try resolve " << p->get_name() << " " << num_pos << " " << num_neg << "\n");
    // TODO - probe for a definition
    // generally, probe for binary clause equivalences in binary implication graph
    
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
            if (pos->m_alive)
                fmls.push_back(create_residue_formula(p, *pos));
        def = mk_or(fmls);
    }
    else {
        for (auto* neg : m_use_list.get(p, true))
            if (neg->m_alive)
                fmls.push_back(mk_not(m, create_residue_formula(p, *neg)));
        def = mk_and(fmls);
    }

    IF_VERBOSE(0, verbose_stream() << p->get_name() << " " << def << "\n");
    rewrite(def);
    m_fmls.model_trail().push(p, def, deleted);
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
    IF_VERBOSE(0, verbose_stream() << fml << "\n");
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
* Uninterpreted function declarations from as-array terms are added to 'm_disable_macro'
*/
void eliminate_predicates::process_to_exclude(ast_mark& exclude_set) {
    ast_mark visited;
    array_util a(m);

    struct proc {        
        array_util& a;
        ast_mark&   to_exclude;
        ast_mark&   to_disable;
        proc(array_util& a, ast_mark& f, ast_mark& d) : 
            a(a), to_exclude(f), to_disable(d) {}
        void operator()(func_decl* f) {
            if (is_uninterp(f))
                to_exclude.mark(f, true);
        }
        void operator()(app* e) {
            func_decl* f;
            if (a.is_as_array(e, f) && is_uninterp(f))
                to_disable.mark(f, true);
        }
        void operator()(ast* s) {}
    };
    proc proc(a, exclude_set, m_disable_macro);

    for (expr* e : m_to_exclude)
        for_each_ast(proc, visited, e);
    m_to_exclude.reset();
}


eliminate_predicates::clause* eliminate_predicates::init_clause(unsigned i) {
    auto [f, d] = m_fmls[i]();
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
    return cl;
}

/**
* functions in the prefix of qhead are fully disabled
* Create clauses from the suffix, and process subeterms of clauses to be disabled from 
* eliminations.
*/
void eliminate_predicates::init_clauses() {
    for (unsigned i = 0; i < m_qhead; ++i)
        m_to_exclude.push_back(m_fmls[i].fml());
    recfun::util rec(m);
    if (rec.has_rec_defs()) 
        for (auto& d : rec.get_rec_funs())
            m_to_exclude.push_back(rec.get_def(d).get_rhs());
    
    process_to_exclude(m_disable_macro);

    for (unsigned i = m_qhead; i < m_fmls.size(); ++i) {
        clause* cl = init_clause(i);
        add_use_list(*cl);
        m_clauses.push_back(cl);
    }
    process_to_exclude(m_disable_elimination);
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
            dependent_expr de(m, m.mk_true(), nullptr);
            m_fmls.update(cl->m_fml_index, de);
        }
        else if (cl->m_alive) {
            expr_ref new_cl = cl->m_fml;
            dependent_expr de(m, new_cl, cl->m_dep);
            m_fmls.add(de);
        }        
    }
}

void eliminate_predicates::reset() {
    m_predicates.reset();
    m_predicate_decls.reset();
    m_to_exclude.reset();
    m_disable_macro.reset();
    m_disable_elimination.reset();
    m_is_macro.reset();
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
