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

Maintain term nodes.
Each term node has a root. The root of the root is itself.
The root of a term node can be updated.
The parents of terms with same roots are combined.
The depth of a parent is always greater than the depth of a child.
The effective term of a node is reconstructed by taking the root and canonizing the children based on roots.
The reference count of a term is the number of parents it has.

node:  term -> node
dirty: node -> bool
root:  node -> node
top:   node -> bool
term:  node -> term

invariant:
- root(root(n)) = root(n)
- term(node(t)) = t

parents: node -> node* 
parents(root(node)) = union of parents of n : root(n) = root(node).
is_child(n, p) = term(root(n)) in args(term(root(p)))

set_root: node -> node -> void
set_root(n, r) = 
   r = root(r)
   n = root(n)
   if r = n then return
   parents(r) = parents(r) union parents(n)
   root(n) := r,
   top(r) := top(r) or top(n)
   set all parents of class(r) to dirty, recursively

reconstruct_term: node -> term
reconstruct_term(n) =
  r = root(n)
  if dirty(r) then
    args = [reconstruct_term(c) | c in args(term(r))]
    term(r) := term(r).f(args)
    dirty(r) := false
  return term(r)

live : term -> bool
live(t) = 
   n = node(t)
   is_root(n) & (top(n) or p in parents(n) : live(p))

Only live nodes require updates.

eliminate:
  while heap is not empty:
     v = heap.erase_min()
     n = node(v)
     if n.parents.size() > 1 then
        return
     if !is_root(n) or !live(n) or n.parents.size() != 1 then 
        continue
     p = n.parents[0]
     if !is_child(n, p) or !is_root(p) then 
        continue
     t = p.term
     args = [reconstruct_term(node(arg)) | arg in t]
     r = inverter(t.f, args)
     if r then        
        set_root(n, r)



--*/



#include "ast/ast_ll_pp.h"
#include "ast/ast_pp.h"
#include "ast/recfun_decl_plugin.h"
#include "ast/simplifiers/elim_unconstrained.h"

elim_unconstrained::elim_unconstrained(ast_manager& m, dependent_expr_state& fmls) :
    dependent_expr_simplifier(m, fmls), m_inverter(m), m_lt(*this), m_heap(1024, m_lt), m_trail(m), m_args(m) {
    std::function<bool(expr*)> is_var = [&](expr* e) {
        return is_uninterp_const(e) && !m_fmls.frozen(e) && get_node(e).is_root() && get_node(e).num_parents() <= 1;
    };
    m_inverter.set_is_var(is_var);
}

elim_unconstrained::~elim_unconstrained() {
    reset_nodes();
}

bool elim_unconstrained::is_var_lt(int v1, int v2) const {   
    auto p1 = get_node(v1).num_parents();
    auto p2 = get_node(v2).num_parents();
    return  p1 < p2;
}

void elim_unconstrained::eliminate() {
    while (!m_heap.empty()) {
        expr_ref r(m);
        int v = m_heap.erase_min();
        node& n = get_node(v);
        if (!n.is_root() || n.is_top())
            continue;
        unsigned num_parents = n.num_parents();
        if (num_parents == 0)
            continue;
        if (num_parents > 1)
            return;

        node& p = n.parent();
        if (!is_child(n, p) || !p.is_root())
            continue;
        expr* e = p.term();
        if (!e || !is_app(e) || !is_ground(e)) 
            continue;

        SASSERT(!m_heap.contains(p.term()->get_id()));
        
        app* t = to_app(e);
        TRACE("elim_unconstrained", tout << "eliminating " << mk_bounded_pp(t, m) << "\n";);
        unsigned sz = m_args.size();
        for (expr* arg : *to_app(t))
            m_args.push_back(reconstruct_term(root(arg)));
        expr_ref rr(m.mk_app(t->get_decl(), t->get_num_args(), m_args.data() + sz), m);
        bool inverted = m_inverter(t->get_decl(), t->get_num_args(), m_args.data() + sz, r);
        proof_ref pr(m);
        if (inverted && m_enable_proofs) {
            expr * s    = m.mk_app(t->get_decl(), t->get_num_args(), m_args.data() + sz);
            expr * eq   = m.mk_eq(s, r);
            proof * pr1 = m.mk_def_intro(eq);
            proof * pr  = m.mk_apply_def(s, r, pr1);
            m_trail.push_back(pr);
        }
        m_args.shrink(sz);
        if (!inverted)
            continue;

        IF_VERBOSE(4, verbose_stream() << "replace " << mk_bounded_pp(t, m) << " / " << mk_bounded_pp(rr, m) << " -> " << mk_bounded_pp(r, m) << "\n");

        
        TRACE("elim_unconstrained", tout << mk_bounded_pp(t, m) << " / " << mk_bounded_pp(rr, m) << " -> " << mk_bounded_pp(r, m) << "\n");
        SASSERT(r->get_sort() == t->get_sort());
        m_stats.m_num_eliminated++;
        node& rn = root(r);
        set_root(p, rn);
        expr* rt = rn.term();
        SASSERT(!m_heap.contains(rt->get_id()));
        m_heap.reserve(rt->get_id() + 1);
        if (is_uninterp_const(rt)) 
            m_heap.insert(rt->get_id());
        else
            m_created_compound = true;
    }
}

void elim_unconstrained::set_root(node& n, node& r) {
    SASSERT(n.is_root());
    SASSERT(r.is_root());
    if (&n == &r)
        return;
    r.add_parents(n.parents());    
    n.set_root(r);
    for (auto p : n.parents())
        invalidate_parents(*p);
}

void elim_unconstrained::invalidate_parents(node& n) {
    ptr_buffer<node> todo;
    node* np = &n;
    do {
        node& n = *np;
        if (!n.is_dirty()) {
            n.set_dirty();
            for (auto* p : n.parents())
                todo.push_back(p);            
        }
        np = nullptr;
        if (!todo.empty()) {
            np = todo.back();
            todo.pop_back();
        }
    }
    while (np);    
}

bool elim_unconstrained::is_child(node const& ch, node const& p) {
    SASSERT(ch.is_root());
    return is_app(p.term()) && any_of(*to_app(p.term()), [&](expr* arg) { return &root(arg) == &ch; });
}

elim_unconstrained::node& elim_unconstrained::get_node(expr* t) {
    unsigned id = t->get_id();
    if (m_nodes.size() <= id)
        m_nodes.resize(id + 1, nullptr);
    node* n = m_nodes[id];
    if (!n) {
        n = alloc(node, m, t);               
        m_nodes[id] = n;
        if (is_app(t)) {
            for (auto arg : *to_app(t)) {
                node& ch = get_node(arg);
                SASSERT(ch.is_root());
                ch.add_parent(*n);
                if (is_uninterp_const(arg) && m_heap.contains(arg->get_id()))
                    m_heap.increased(arg->get_id());
            }
        }
        else if (is_quantifier(t)) {            
            node& ch = get_node(to_quantifier(t)->get_expr());
            SASSERT(ch.is_root());
            ch.add_parent(*n);
        }
    }
    return *n;
}

void elim_unconstrained::reset_nodes() {
    for (node* n : m_nodes)
        dealloc(n);
    m_nodes.reset();
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

    m_heap.reset();
    reset_nodes();

    // initialize nodes for terms in the original goal
    unsigned max_id = 0;
    for (expr* e : subterms::all(terms))
        max_id = std::max(max_id, e->get_id());

    m_nodes.reserve(max_id + 1);
    m_heap.reserve(max_id + 1);

    for (expr* e : subterms_postorder::all(terms)) {
        SASSERT(get_node(e).is_root());
        
        if (is_uninterp_const(e)) {
            get_node(e); // ensure the node exists
            m_heap.insert(e->get_id());
        }
    }

    // mark top level terms
    for (expr* e : terms)
        get_node(e).set_top();      

    m_inverter.set_produce_proofs(m_enable_proofs);
        
}

expr* elim_unconstrained::reconstruct_term(node& n) {
    SASSERT(n.is_root());
    if (!n.is_dirty())
        return n.term();
    ptr_buffer<node> todo;
    todo.push_back(&n);
    expr_ref new_t(m);
    while (!todo.empty()) {
        node* np = todo.back();
        if (!np->is_dirty()) {
            todo.pop_back();
            continue;
        }
        SASSERT(np->is_root());
        auto t = np->term();
        unsigned sz0 = todo.size();
        if (is_app(t)) {
            for (expr* arg : *to_app(t)) {
                node& r = root(arg);
                if (r.is_dirty())
                    todo.push_back(&r);
            }
            if (todo.size() != sz0)
                continue;

            unsigned sz = m_args.size();
            for (expr* arg : *to_app(t))
                m_args.push_back(root(arg).term());
            new_t = m.mk_app(to_app(t)->get_decl(), to_app(t)->get_num_args(), m_args.data() + sz);
            m_args.shrink(sz);
        }
        else if (is_quantifier(t)) {
            expr* body = to_quantifier(t)->get_expr();
            node& n2 = root(body);
            if (n2.is_dirty()) {
                todo.push_back(&n2);
                continue;
            }
            new_t = m.update_quantifier(to_quantifier(t), n2.term());
        }
        else
            new_t = t;
        node& new_n = get_node(new_t);
        set_root(*np, new_n);
        np->set_clean();
        todo.pop_back();
    }
    return n.root().term();
}

/**
 * walk nodes starting from lowest depth and reconstruct their normalized forms.
 */
void elim_unconstrained::reconstruct_terms() {
    ptr_vector<node> nodes;
    for (node* n : m_nodes)
        if (n && n->is_root())
            nodes.push_back(n);

    std::stable_sort(nodes.begin(), nodes.end(), [&](node* a, node* b) { return get_depth(a->term()) < get_depth(b->term()); });

    for (node* n : nodes) 
        reconstruct_term(*n);    
}


void elim_unconstrained::assert_normalized(vector<dependent_expr>& old_fmls) {

    for (unsigned i : indices()) {
        auto [f, p, d] = m_fmls[i]();
        node& n = root(f);
        expr* g = n.term();
        if (f == g)
            continue;
        old_fmls.push_back(m_fmls[i]);
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
            //            new_def = entry.m_def;
            // (*rp)(new_def);
            new_def = m.mk_const(entry.m_f);
            sub->insert(new_def, new_def, nullptr, nullptr);
            break;
        }
    }
    trail.push(sub.detach(), old_fmls, true);
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
