/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    elim_unconstrained.cpp

Abstract:

   Incremental, modular and more efficient version of elim_unconstr_tactic and 
   reduce_invertible_tactic.

   reduce_invertible_tactic should be subsumed by elim_unconstr_tactic
   elim_unconstr_tactic has some built-in limitations that are not easy to fix with small changes:
   - it is inefficient for examples like x <= y, y <= z, z <= u, ...
     All variables x, y, z, .. can eventually be eliminated, but the tactic requires a global 
     analysis between each elimination. We address this by using reference counts and maintaining
     a heap of reference counts.
   - it does not accomodate side constraints. The more general invertibility reduction methods, such 
     as those introduced for bit-vectors use side constraints.
   - it is not modular: we detach the expression invertion routines to self-contained code.

   Maintain a representation of terms as a set of nodes.
   Each node has:

   - reference count = number of parents that are live
   - orig - original term, the orig->get_id() is the index to the node
   - term - current term representing the node after rewriting
   - parents - list of parents where orig occurs.

  Subterms have reference counts
  Elegible variables are inserted into a heap ordered by reference counts.
  Variables that have reference count 1 are examined for invertibility.

Author:

    Nikolaj Bjorner (nbjorner) 2022-11-11.

Notes:

proof production is work in progress.
reconstruct_term should assign proof objects with nodes by applying
monotonicity or reflexivity rules. 

--*/



#include "ast/ast_ll_pp.h"
#include "ast/ast_pp.h"
#include "ast/recfun_decl_plugin.h"
#include "ast/simplifiers/elim_unconstrained.h"

elim_unconstrained::elim_unconstrained(ast_manager& m, dependent_expr_state& fmls) :
    dependent_expr_simplifier(m, fmls), m_inverter(m), m_lt(*this), m_heap(1024, m_lt), m_trail(m), m_args(m) {
    std::function<bool(expr*)> is_var = [&](expr* e) {
        return is_uninterp_const(e) && !m_fmls.frozen(e) && is_node(e) && get_node(e).m_refcount <= 1;
    };
    m_inverter.set_is_var(is_var);
}

bool elim_unconstrained::is_var_lt(int v1, int v2) const {
    node const& n1 = get_node(v1);
    node const& n2 = get_node(v2);
    return n1.m_refcount < n2.m_refcount;
}

void elim_unconstrained::eliminate() {
    while (!m_heap.empty()) {
        expr_ref r(m);
        int v = m_heap.erase_min();
        node& n = get_node(v);
        if (n.m_refcount == 0)
            continue;
        if (n.m_refcount > 1) 
            return;

        if (n.m_parents.empty()) {
            n.m_refcount = 0;
            continue;
        }
        expr* e = get_parent(v);
        IF_VERBOSE(11, for (expr* p : n.m_parents) verbose_stream() << "parent " << mk_bounded_pp(p, m) << " @ " << get_node(p).m_refcount << "\n";);
        if (!e || !is_app(e) || !is_ground(e)) {
            n.m_refcount = 0;
            continue;
        }
        if (m_heap.contains(root(e))) {
            IF_VERBOSE(11, verbose_stream() << "already in heap " << mk_bounded_pp(e, m) << "\n");
            continue;
        }
        app* t = to_app(e);
        TRACE("elim_unconstrained", tout << "eliminating " << mk_pp(t, m) << "\n";);
        unsigned sz = m_args.size();
        for (expr* arg : *to_app(t))
            m_args.push_back(reconstruct_term(get_node(arg)));
        bool inverted = m_inverter(t->get_decl(), t->get_num_args(), m_args.data() + sz, r);
        proof_ref pr(m);
        if (inverted && m_enable_proofs) {
            expr * s    = m.mk_app(t->get_decl(), t->get_num_args(), m_args.data() + sz);
            expr * eq   = m.mk_eq(s, r);
            proof * pr1 = m.mk_def_intro(eq);
            proof * pr  = m.mk_apply_def(s, r, pr1);
            m_trail.push_back(pr);
        }
        expr_ref rr(m.mk_app(t->get_decl(), t->get_num_args(), m_args.data() + sz), m);
        n.m_refcount = 0;
        m_args.shrink(sz);
        if (!inverted) {
            IF_VERBOSE(11, verbose_stream() << "not inverted " << mk_bounded_pp(e, m) << "\n");
            continue;
        }

        IF_VERBOSE(11, verbose_stream() << "replace " << mk_pp(t, m) << " / " << rr << " -> " << r << "\n");
        
        TRACE("elim_unconstrained", tout << mk_pp(t, m) << " / " << rr << " -> " << r << "\n");
        SASSERT(r->get_sort() == t->get_sort());
        m_stats.m_num_eliminated++;
        m_trail.push_back(r);
        SASSERT(r);
        gc(e);
        invalidate_parents(e);
        freeze_rec(r);
        
        m_root.setx(r->get_id(), e->get_id(), UINT_MAX);
        get_node(e).m_term = r;
        get_node(e).m_proof = pr;
        get_node(e).m_refcount++;
        get_node(e).m_dirty = false;
        IF_VERBOSE(11, verbose_stream() << "set " << &get_node(e) << " " << root(e) << " " << mk_bounded_pp(e, m) << " := " << mk_bounded_pp(r, m) << "\n");
        SASSERT(!m_heap.contains(root(e)));
        if (is_uninterp_const(r))
            m_heap.insert(root(e));
        else
            m_created_compound = true;

        IF_VERBOSE(11, verbose_stream() << mk_bounded_pp(get_node(v).m_orig, m) << " " << mk_bounded_pp(t, m) << " -> " << r << " " << get_node(e).m_refcount << "\n";);

    }
}

expr* elim_unconstrained::get_parent(unsigned n) const {
    for (expr* p : get_node(n).m_parents)
        if (get_node(p).m_refcount > 0 && get_node(p).m_term == get_node(p).m_orig)
            return p;
    return nullptr;
}

void elim_unconstrained::invalidate_parents(expr* e) {
    ptr_vector<expr> todo;
    do {
        node& n = get_node(e);
        if (!n.m_dirty) {
            n.m_dirty = true;
            for (expr* e : n.m_parents)
                todo.push_back(e);            
        }
        e = nullptr;
        if (!todo.empty()) {
            e = todo.back();
            todo.pop_back();
        }
    }
    while (e);    
}


/**
 * initialize node structure
 */
void elim_unconstrained::init_nodes() {

    m_enable_proofs = false;
    m_trail.reset();
    m_fmls.freeze_suffix();

    expr_ref_vector terms(m);
    for (unsigned i : indices()) {
        auto [f, p, d] = m_fmls[i]();
        terms.push_back(f);
        if (p)
            m_enable_proofs = true;
    }

    m_trail.append(terms);
    m_heap.reset();
    m_root.reset();
    m_nodes.reset();

    // initialize nodes for terms in the original goal
    init_terms(terms);

    // top-level terms have reference count > 0
    for (expr* e : terms)
        inc_ref(e);

    m_inverter.set_produce_proofs(m_enable_proofs);
        
}

/**
* Create nodes for all terms in the goal
*/
void elim_unconstrained::init_terms(expr_ref_vector const& terms) {
    unsigned max_id = 0;
    for (expr* e : subterms::all(terms))
        max_id = std::max(max_id, e->get_id());

    m_nodes.reserve(max_id + 1);
    m_heap.reserve(max_id + 1);
    m_root.reserve(max_id + 1, UINT_MAX);

    for (expr* e : subterms_postorder::all(terms)) {
        m_root.setx(e->get_id(), e->get_id(), UINT_MAX);
        node& n = get_node(e);
        if (n.m_term)
            continue;        
        n.m_orig = e;
        n.m_term = e;
        n.m_refcount = 0;
        
        if (is_uninterp_const(e))
            m_heap.insert(root(e));
        if (is_quantifier(e)) {
            expr* body = to_quantifier(e)->get_expr();
            get_node(body).m_parents.push_back(e);
            inc_ref(body);
        }
        else if (is_app(e)) {
            for (expr* arg : *to_app(e)) {
                get_node(arg).m_parents.push_back(e);
                inc_ref(arg);
            }
        }
    }
}

void elim_unconstrained::freeze_rec(expr* r) {
    expr_ref_vector children(m);
    if (is_quantifier(r))
        children.push_back(to_quantifier(r)->get_expr());
    else if (is_app(r))
        children.append(to_app(r)->get_num_args(), to_app(r)->get_args());
    else
        return;
    if (children.empty())
        return;
    for (expr* t : subterms::all(children))
        freeze(t);
}

void elim_unconstrained::freeze(expr* t) {
    if (!is_uninterp_const(t))
        return;
    if (m_nodes.size() <= t->get_id())
        return;
    if (m_nodes.size() <= root(t))
        return;
    node& n = get_node(t);
    if (!n.m_term)
        return;    
    if (m_heap.contains(root(t))) {
        n.m_refcount = UINT_MAX / 2;
        m_heap.increased(root(t));
    }
}

void elim_unconstrained::gc(expr* t) {
    ptr_vector<expr> todo;
    todo.push_back(t);
    while (!todo.empty()) {
        t = todo.back();
        todo.pop_back();
        
        node& n = get_node(t);  
        if (n.m_refcount == 0)
            continue;
        if (n.m_term && !is_node(n.m_term))
            continue;

        dec_ref(t);
        if (n.m_refcount != 0)
            continue;
        if (n.m_term)
            t = n.m_term;
        if (is_app(t)) {
            for (expr* arg : *to_app(t))
                todo.push_back(arg);
        }
        else if (is_quantifier(t)) 
            todo.push_back(to_quantifier(t)->get_expr());        
    }
}


expr_ref elim_unconstrained::reconstruct_term(node& n0) {
    expr* t = n0.m_term;
    if (!n0.m_dirty)
        return expr_ref(t, m);
    if (!is_node(t))
        return expr_ref(t, m);
    ptr_vector<expr> todo;
    todo.push_back(t);
    while (!todo.empty()) {
        t = todo.back();
        if (!is_node(t)) {
            UNREACHABLE();
        }
        node& n = get_node(t);
        unsigned sz0 = todo.size();
        if (is_app(t)) {     
            if (n.m_term != t) {
                todo.pop_back();
                continue;
            }
            for (expr* arg : *to_app(t)) 
                if (get_node(arg).m_dirty || !get_node(arg).m_term)
                    todo.push_back(arg);
            if (todo.size() != sz0)
                continue;

            unsigned sz = m_args.size();
            for (expr* arg : *to_app(t)) 
                m_args.push_back(get_node(arg).m_term);            
            n.m_term = m.mk_app(to_app(t)->get_decl(), to_app(t)->get_num_args(), m_args.data() + sz);
            m_args.shrink(sz);
        }
        else if (is_quantifier(t)) {
            expr* body = to_quantifier(t)->get_expr();
            node& n2 = get_node(body);
            if (n2.m_dirty || !n2.m_term) {
                todo.push_back(body);
                continue;
            }
            n.m_term = m.update_quantifier(to_quantifier(t), n2.m_term);            
        }
        m_trail.push_back(n.m_term);
        m_root.setx(n.m_term->get_id(), n.m_term->get_id(), UINT_MAX);
        todo.pop_back();
        n.m_dirty = false;
    }
    return expr_ref(n0.m_term, m);
}

/**
 * walk nodes starting from lowest depth and reconstruct their normalized forms.
 */
void elim_unconstrained::reconstruct_terms() {
    expr_ref_vector terms(m);
    for (unsigned i : indices())
        terms.push_back(m_fmls[i].fml());    

    for (expr* e : subterms_postorder::all(terms)) {
        node& n = get_node(e);
        expr* t = n.m_term;
        if (t != n.m_orig)
            continue;
        if (is_app(t)) {
            bool change = false;
            m_args.reset();
            for (expr* arg : *to_app(t)) {
                node& n2 = get_node(arg);
                m_args.push_back(n2.m_term);
                change |= n2.m_term != n2.m_orig;
            }
            if (change) {
                n.m_term = m.mk_app(to_app(t)->get_decl(), m_args);
                m_trail.push_back(n.m_term);
            }            
        }
        else if (is_quantifier(t)) {
            node& n2 = get_node(to_quantifier(t)->get_expr());
            if (n2.m_term != n2.m_orig) {
                n.m_term = m.update_quantifier(to_quantifier(t), n2.m_term);
                m_trail.push_back(n.m_term);
            }
        }
    }
}


void elim_unconstrained::assert_normalized(vector<dependent_expr>& old_fmls) {

    for (unsigned i : indices()) {
        auto [f, p, d] = m_fmls[i]();
        node& n = get_node(f);
        expr* g = n.m_term;
        if (f == g)
            continue;
        old_fmls.push_back(m_fmls[i]);
        IF_VERBOSE(11, verbose_stream() << mk_bounded_pp(f, m, 3) << " -> " << mk_bounded_pp(g, m, 3) << "\n");
        TRACE("elim_unconstrained", tout << mk_bounded_pp(f, m) << " -> " << mk_bounded_pp(g, m) << "\n");
        m_fmls.update(i, dependent_expr(m, g, nullptr, d));
    }
}

void elim_unconstrained::update_model_trail(generic_model_converter& mc, vector<dependent_expr> const& old_fmls) {
    auto& trail = m_fmls.model_trail();

    // fresh declarations are added first since 
    // model reconstruction proceeds in reverse order of stack.
    for (auto const& entry : mc.entries()) {
        switch (entry.m_instruction) {
        case generic_model_converter::instruction::HIDE:
            trail.hide(entry.m_f);
            break;
        case generic_model_converter::instruction::ADD:
            // trail.push(entry.m_f, entry.m_def, nullptr, old_fmls);
            break;
        }
    }
    scoped_ptr<expr_replacer> rp = mk_default_expr_replacer(m, false);
    scoped_ptr<expr_substitution> sub = alloc(expr_substitution, m, true, false);
    rp->set_substitution(sub.get());
    expr_ref new_def(m);
    for (unsigned i = mc.entries().size(); i-- > 0; ) {
        auto const& entry = mc.entries()[i];
        switch (entry.m_instruction) {
        case generic_model_converter::instruction::HIDE:
            break;
        case generic_model_converter::instruction::ADD:
            new_def = entry.m_def;
            (*rp)(new_def);           
            sub->insert(m.mk_const(entry.m_f), new_def, nullptr, nullptr);
            break;
        }
    }
    trail.push(sub.detach(), old_fmls);
}

void elim_unconstrained::reduce() {
    generic_model_converter_ref mc = alloc(generic_model_converter, m, "elim-unconstrained");
    m_inverter.set_model_converter(mc.get());
    m_created_compound = true;
    for (unsigned rounds = 0; m_created_compound && rounds < 3; ++rounds) {
        m_created_compound = false;
        init_nodes();
        eliminate();
        reconstruct_terms();
        vector<dependent_expr> old_fmls;
        assert_normalized(old_fmls);
        update_model_trail(*mc, old_fmls);
        mc->reset();
    }
}
