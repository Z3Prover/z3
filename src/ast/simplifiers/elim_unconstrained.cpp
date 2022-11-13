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

--*/



#include "ast/ast_ll_pp.h"
#include "ast/ast_pp.h"
#include "ast/recfun_decl_plugin.h"
#include "ast/simplifiers/elim_unconstrained.h"

elim_unconstrained::elim_unconstrained(ast_manager& m, dependent_expr_state& fmls) :
    dependent_expr_simplifier(m, fmls), m_inverter(m), m_lt(*this), m_heap(1024, m_lt), m_trail(m) {

    std::function<bool(expr*)> is_var = [&](expr* e) {
        return is_uninterp_const(e) && !m_frozen.is_marked(e) && get_node(e).m_refcount == 1;
    };

    m_inverter.set_is_var(is_var);
}


void elim_unconstrained::eliminate() {

    while (!m_heap.empty()) {
        expr_ref r(m), side_cond(m);
        int v = m_heap.erase_min();
        node& n = get_node(v);
        IF_VERBOSE(11, verbose_stream() << mk_pp(n.m_orig, m) << " @ " << n.m_refcount << "\n");
        if (n.m_refcount == 0)
            continue;
        if (n.m_refcount > 1)
            return;

        if (n.m_parents.empty())
            continue;
        expr* e = get_parent(v);
        for (expr* p : n.m_parents)
            IF_VERBOSE(11, verbose_stream() << "parent " << mk_pp(p, m) << "\n");
        if (!is_app(e))
            continue;
        if (!is_ground(e))
            continue;
        app* t = to_app(e);
        m_args.reset();
        for (expr* arg : *to_app(t))
            m_args.push_back(get_node(arg).m_term);
        if (!m_inverter(t->get_decl(), m_args.size(), m_args.data(), r, side_cond))
            continue;

        m_stats.m_num_eliminated++;
        n.m_refcount = 0;
        SASSERT(r);
        m_trail.push_back(r);
        gc(e);

        get_node(e).m_term = r;
        get_node(e).m_refcount++;
        IF_VERBOSE(11, verbose_stream() << mk_pp(e, m) << "\n");
        SASSERT(!m_heap.contains(e->get_id()));
        if (is_uninterp_const(r)) 
            m_heap.insert(e->get_id());                    

        IF_VERBOSE(11, verbose_stream() << mk_pp(n.m_orig, m) << " " << mk_pp(t, m) << " -> " << r << " " << get_node(e).m_refcount << "\n");

        SASSERT(!side_cond && "not implemented to add side conditions\n");
    }
}

expr* elim_unconstrained::get_parent(unsigned n) const {
    for (expr* p : get_node(n).m_parents)
        if (get_node(p).m_refcount > 0 && get_node(p).m_term == get_node(p).m_orig)
            return p;
    IF_VERBOSE(0, verbose_stream() << "term " << mk_pp(get_node(n).m_term, m) << "\n");
    for (expr* p : get_node(n).m_parents)
        IF_VERBOSE(0, verbose_stream() << "parent " << mk_pp(p, m) << "\n");
    UNREACHABLE();
    return nullptr;
}
/**
 * initialize node structure
 */
void elim_unconstrained::init_nodes() {
    expr_ref_vector terms(m);
    for (unsigned i = 0; i < m_fmls.size(); ++i)
        terms.push_back(m_fmls[i].fml());
    m_trail.append(terms);
    m_heap.reset();
    m_frozen.reset();

    // initialize nodes for terms in the original goal
    init_terms(terms);

    // top-level terms have reference count > 0
    for (expr* e : terms)
        inc_ref(e);

    // freeze subterms before the already processed head
    terms.reset();
    for (unsigned i = 0; i < m_qhead; ++i)
        terms.push_back(m_fmls[i].fml());
    for (expr* e : subterms::all(terms))
        m_frozen.mark(e, true);    

    // freeze subterms that occur with recursive function definitions
    recfun::util rec(m);
    if (rec.has_rec_defs()) {
        for (func_decl* f : rec.get_rec_funs()) {
            expr* rhs = rec.get_def(f).get_rhs();
            for (expr* t : subterms::all(expr_ref(rhs, m)))
                m_frozen.mark(t);
        }
    }
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

    for (expr* e : subterms_postorder::all(terms)) {
        node& n = get_node(e);
        if (n.m_term)
            continue;
        n.m_orig = e;
        n.m_term = e;
        n.m_refcount = 0;
        if (is_uninterp_const(e))
            m_heap.insert(e->get_id());
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

void elim_unconstrained::gc(expr* t) {
    ptr_vector<expr> todo;
    todo.push_back(t);
    while (!todo.empty()) {
        t = todo.back();
        todo.pop_back();
        node& n = get_node(t);  
        if (n.m_refcount == 0)
            continue;
        dec_ref(t);
        if (n.m_refcount != 0)
            continue;
        if (is_app(t)) {
            for (expr* arg : *to_app(t))
                todo.push_back(arg);
        }
        else if (is_quantifier(t)) 
            todo.push_back(to_quantifier(t)->get_expr());        
    }
}

/**
 * walk nodes starting from lowest depth and reconstruct their normalized forms.
 */
void elim_unconstrained::reconstruct_terms() {
    expr_ref_vector terms(m);
    for (unsigned i = m_qhead; i < m_fmls.size(); ++i)
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
    for (unsigned i = m_qhead; i < m_fmls.size(); ++i) {
        auto [f, d] = m_fmls[i]();
        node& n = get_node(f);
        expr* g = n.m_term;
        if (f == g)
            continue;
        old_fmls.push_back(m_fmls[i]);
        m_fmls.update(i, dependent_expr(m, g, d));
        IF_VERBOSE(11, verbose_stream() << mk_bounded_pp(f, m, 3) << " -> " << mk_bounded_pp(g, m, 3) << "\n");
        TRACE("elim_unconstrained", tout << mk_bounded_pp(f, m) << " -> " << mk_bounded_pp(g, m) << "\n");
    }
}

void elim_unconstrained::update_model_trail(generic_model_converter& mc, vector<dependent_expr> const& old_fmls) {
    auto& trail = m_fmls.model_trail();
    scoped_ptr<expr_replacer> rp = mk_default_expr_replacer(m, false);
    scoped_ptr<expr_substitution> sub = alloc(expr_substitution, m, true, false);
    rp->set_substitution(sub.get());
    expr_ref new_def(m);
    for (auto const& entry : mc.entries()) {
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

    for (auto const& entry : mc.entries()) {
        switch (entry.m_instruction) {
        case generic_model_converter::instruction::HIDE:
            trail.push(entry.m_f);
            break;
        case generic_model_converter::instruction::ADD:
            break;
        }
    }
}

void elim_unconstrained::reduce() {
    generic_model_converter_ref mc = alloc(generic_model_converter, m, "elim-unconstrained");
    m_inverter.set_model_converter(mc.get());
    init_nodes();
    eliminate();
    reconstruct_terms();
    vector<dependent_expr> old_fmls;
    assert_normalized(old_fmls);
    update_model_trail(*mc, old_fmls);
    advance_qhead(m_fmls.size());
}
