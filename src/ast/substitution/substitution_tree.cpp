/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    substitution_tree.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-04.

Revision History:

--*/
#include "ast/substitution/substitution_tree.h"
#include "ast/ast_pp.h"
#include "ast/ast_smt2_pp.h"

/**
   \brief Return the next available register.
*/
unsigned substitution_tree::next_reg() {
    while(true) {
        unsigned curr = m_next_reg;
        if (curr > m_max_reg)
            m_max_reg = curr;
        m_next_reg++;
        if (curr >= m_used_regs.size() || !m_used_regs.get(curr))
            return curr;
    }
}

inline void substitution_tree::push(svector<subst> & sv, subst const & s) {
    sv.push_back(s);
    m_manager.inc_ref(s.first);
    m_manager.inc_ref(s.second);
}

inline expr * substitution_tree::get_reg_value(unsigned ridx) {
    return m_registers.get(ridx, 0);
}

inline void substitution_tree::set_reg_value(unsigned ridx, expr * e) {
    m_registers.setx(ridx, e, 0);
}

inline void substitution_tree::erase_reg_from_todo(unsigned ridx) {
    SASSERT(m_registers[ridx]);
    m_registers[ridx] = 0;
    SASSERT(m_todo.contains(ridx));
    m_todo.erase(ridx);
}

/**
   \brief Linearize the expressions in the registers stored in m_todo.
   Store the result in \c result.

   Example:
     m_todo = { 3, 4 }
     m_registers[3] = (f (g a))
     m_registers[4] = b
     next_regs are 5 6 7
     
     result:
     #3 -> (f #5); #4 -> b; #5 -> (g #6); #6 -> a
*/
void substitution_tree::linearize(svector<subst> & result) {
    ptr_buffer<expr> new_args;
    for (unsigned i = 0; i < m_todo.size(); i++) {
        unsigned ireg_idx = m_todo[i];
        expr * n          = get_reg_value(ireg_idx);
        var * ireg        = m_manager.mk_var(ireg_idx, m_manager.get_sort(n));
        if (is_var(n))
            push(result, subst(ireg, n));
        else {
            SASSERT(is_app(n));
            app * new_app;
            unsigned num = to_app(n)->get_num_args();
            if (num == 0)
                new_app = to_app(n);
            else {
                for (unsigned j = 0; j < num; j++) {
                    unsigned oreg     = next_reg();
                    set_reg_value(oreg, to_app(n)->get_arg(j));
                    m_todo.push_back(oreg);
                    sort * s          = m_manager.get_sort(get_reg_value(oreg));
                    new_args.push_back(m_manager.mk_var(oreg, s));
                }
                new_app = m_manager.mk_app(to_app(n)->get_decl(), new_args.size(), new_args.c_ptr());
                new_args.reset();
            }
            push(result, subst(ireg, new_app));
        }
    }
}

/**
   \brief Process the pair in := (f t_1 ... t_n) and out := (f r_1 ... r_n),
   where r_i's are variables (register ids), and t_i's are arbitrary expressions.
   The r_i's are added to the m_todo list, and m_registers[r_i] is assigned to t_i.

   If save_set_registers == true, then r_i's are stored in m_to_reset.
*/
void substitution_tree::process_args(app * in, app * out) {
    CTRACE("subst_tree_bug", in->get_num_args() != out->get_num_args(), tout << mk_ismt2_pp(in, m_manager) << "\n" 
           << mk_ismt2_pp(out, m_manager) << "\n";);
    unsigned num = out->get_num_args();
    for (unsigned i = 0; i < num; i++) {
        expr * in_arg  = in->get_arg(i);
        expr * out_arg = out->get_arg(i);
        SASSERT(is_var(out_arg));
        unsigned oreg  = to_var(out_arg)->get_idx();
        set_reg_value(oreg, in_arg);
        m_todo.push_back(oreg);
    }
}

/**
   \brief Reset registers in m_todo at [old_size, m_todo.size())
*/
void substitution_tree::reset_registers(unsigned old_size) {
    SASSERT(m_todo.size() >= old_size);
    unsigned_vector::iterator it2  = m_todo.begin() + old_size;
    unsigned_vector::iterator end2 = m_todo.end();
    for (; it2 != end2; ++it2)
        m_registers[*it2] = 0;
    m_todo.shrink(old_size);
}

/**
   \brief Return a measure on how compatible sv and the expressions to be processed are.
*/
unsigned substitution_tree::get_compatibility_measure(svector<subst> const & sv) {
    unsigned old_size = m_todo.size();
    unsigned measure  = 0;
    svector<subst>::const_iterator it  = sv.begin();
    svector<subst>::const_iterator end = sv.end();
    for (; it != end; ++it) {
        subst const & s = *it;
        unsigned ireg = s.first->get_idx();
        expr * out    = s.second;
        expr * in     = get_reg_value(ireg);

        if (is_var(out)) {
            if (out == in)
                measure += 1;
        }
        else {
            SASSERT(is_app(out));
            if (in && is_app(in) && to_app(out)->get_decl() == to_app(in)->get_decl()) {
                measure += 2;
                process_args(to_app(in), to_app(out));
            }
        }
    }
    reset_registers(old_size);
    return measure;
}

/**
   \brief Find the child of r that is most compatible with the expressions stored
   in the registers in m_todo.

   Return 0 if none of the children has any compatible substitution entry.
*/
substitution_tree::node * substitution_tree::find_best_child(node * r) {
    SASSERT(!r->m_leaf);
#ifdef Z3DEBUG
    unsigned todo_size   = m_todo.size();
#endif
    node * best_child    = nullptr;
    unsigned max_measure = 0;
    node * curr_child    = r->m_first_child;
    while (curr_child) {
        unsigned measure = get_compatibility_measure(curr_child->m_subst);
        if (measure > max_measure) {
            best_child  = curr_child;
            max_measure = measure;
        }
        curr_child = curr_child->m_next_sibling;
    }
    SASSERT(todo_size == m_todo.size());
    return best_child;
}

/**
   \brief Reset datastructures used to insert/erase elements from the substitution tree.
*/
void substitution_tree::reset_compiler() {
    m_todo.reset();
    m_used_regs.reset();
    m_next_reg = 1; // register 0 is reserved for input.
    DEBUG_CODE({
        ptr_vector<expr>::iterator it  = m_registers.begin();
        ptr_vector<expr>::iterator end = m_registers.end();
        for (; it != end; ++it) {
            SASSERT(*it == 0);
        }
    });
}

/**
   \brief Create a node with the linearization for all registers in todo.
   Attach new_expr to it.
*/
substitution_tree::node * substitution_tree::mk_node_for(expr * new_expr) {
    node * n = alloc(node, true);
    linearize(n->m_subst);
    n->m_expr = new_expr;
    m_manager.inc_ref(new_expr);
    return n;
}

/**
   \brief Mark register ridx as used.
*/
void substitution_tree::mark_used_reg(unsigned ridx) {
    if (ridx >= m_used_regs.size()) 
        m_used_regs.resize(ridx+1);
    m_used_regs.set(ridx);
}

/**
   \brief Mark (m_used_regs) all registers used in \c sv.
*/
void substitution_tree::mark_used_regs(svector<subst> const & sv) {
    svector<subst>::const_iterator it  = sv.begin();
    svector<subst>::const_iterator end = sv.end();
    for (; it != end; ++it) {
        subst const & s = *it;
        mark_used_reg(s.first->get_idx());
        if (is_app(s.second)) {
            unsigned num_args = to_app(s.second)->get_num_args();
            for (unsigned i = 0; i < num_args; i++) {
                expr * arg = to_app(s.second)->get_arg(i);
                SASSERT(is_var(arg));
                mark_used_reg(to_var(arg)->get_idx());
            }
        }
    }
}

/**
   \brief Insert a new expression in the substitution tree.
*/
void substitution_tree::insert(expr * new_expr) {
    if (is_app(new_expr)) {
        insert(to_app(new_expr));
    }
    else {
        SASSERT(is_var(new_expr));
        sort * s    = to_var(new_expr)->get_sort();
        unsigned id = s->get_decl_id();
        if (id >= m_vars.size())
            m_vars.resize(id+1);
        if (m_vars[id] == 0)
            m_vars[id] = alloc(var_ref_vector, m_manager);
        var_ref_vector * v = m_vars[id];
        if (!v->contains(to_var(new_expr)))
            v->push_back(to_var(new_expr));
    }
}

/**
   \brief Insert a new application in the substitution tree.
*/
void substitution_tree::insert(app * new_expr) {
    reset_compiler();
    set_reg_value(0, new_expr);
    m_todo.push_back(0);

    func_decl * d = new_expr->get_decl();
    unsigned id   = d->get_decl_id();
    
    if (id >= m_roots.size()) 
        m_roots.resize(id+1);

    if (!m_roots[id]) {
        // there is no tree for the function symbol heading new_expr
        m_roots[id] = mk_node_for(new_expr);
        reset_registers(0);
        m_size++;
        return;
    }

    node * r = m_roots[id];
    
    while (true) {
        m_compatible.reset();
        m_incompatible.reset();
        svector<subst> & sv = r->m_subst;
        // separate sv in the set of compatible & incompatible instructions
        svector<subst>::iterator it  = sv.begin();
        svector<subst>::iterator end = sv.end();
        for (; it != end; ++it) {
            subst & s = *it;
            unsigned ireg = s.first->get_idx();
            expr * out = s.second;
            expr * in  = get_reg_value(ireg);
            SASSERT(is_var(out) || is_app(out));
            if (is_var(out)) {
                if (out == in) {
                    erase_reg_from_todo(ireg);
                    m_compatible.push_back(s);
                }
                else {
                    m_incompatible.push_back(s);
                }
            }
            else {
                if (in && is_app(in) && to_app(out)->get_decl() == to_app(in)->get_decl()) {
                    erase_reg_from_todo(ireg);
                    m_compatible.push_back(s);
                    process_args(to_app(in), to_app(out));
                }
                else {
                    m_incompatible.push_back(s);
                }
            }
        }

        // process m_compatible & m_incompatible
        if (m_incompatible.empty()) {
            if (m_todo.empty()) {
                // nothing else to process
                // new_expr is already in the substitution tree
                SASSERT(r->m_leaf && r->m_expr == new_expr);
                reset_registers(0);
                return;
            }
            else {
                mark_used_regs(r->m_subst);
                node * best_child = find_best_child(r);
                if (best_child == nullptr) {
                    // there is no compatible child
                    node * n          = mk_node_for(new_expr);
                    n->m_next_sibling = r->m_first_child;
                    r->m_first_child  = n;
                    reset_registers(0);
                    m_size++;
                    return;
                }
                else {
                    // continue with best_child
                    r = best_child;
                }
            }
        }
        else {
            SASSERT(!m_compatible.empty());
            SASSERT(!m_incompatible.empty());

            mark_used_regs(m_compatible);

            r->m_subst.swap(m_compatible);
            
            node * n      = mk_node_for(new_expr);

            node * incomp = alloc(node, r->m_leaf);
            incomp->m_subst.swap(m_incompatible);
            if (r->m_leaf) {
                incomp->m_expr = r->m_expr;
                r->m_leaf      = false;
            }
            else 
                incomp->m_first_child  = r->m_first_child;
            incomp->m_next_sibling = n; 

            SASSERT(!r->m_leaf);
            r->m_first_child = incomp;
            reset_registers(0);
            m_size++;
            return;
        }
    }
}

/**
   \brief Return true if sv is fully compatible with the expressions in the registers in m_todo.
*/
bool substitution_tree::is_fully_compatible(svector<subst> const & sv) {
    unsigned old_size = m_todo.size();
    svector<subst>::const_iterator it  = sv.begin();
    svector<subst>::const_iterator end = sv.end();
    for (; it != end; ++it) {
        subst const & s = *it;
        unsigned ireg = s.first->get_idx();
        expr * out    = s.second;
        expr * in     = get_reg_value(ireg);
        if (is_var(out)) {
            if (out != in) {
                reset_registers(old_size);
                return false;
            }
        }
        else {
            if (!in || !is_app(in) || to_app(in)->get_decl() != to_app(out)->get_decl()) {
                reset_registers(old_size);
                return false;
            }
            process_args(to_app(in), to_app(out));
        }
    }
    reset_registers(old_size);
    return true;
}

/**
   \brief Return a child of r that is fully compatible with the expressions in the registers in m_todo.
*/
bool substitution_tree::find_fully_compatible_child(node * r, node * & prev, node * & child) {
    SASSERT(!r->m_leaf);
    prev  = nullptr;
    child = r->m_first_child;
    while (child) {
        if (is_fully_compatible(child->m_subst))
            return true;
        prev  = child;
        child = child->m_next_sibling;
    }
    return false;
}

inline bool substitution_tree::at_least_3_children(node * r) {
    return !r->m_leaf && r->m_first_child->m_next_sibling && r->m_first_child->m_next_sibling->m_next_sibling;
}

/**
   \brief Remove expression from the substitution tree.
   Do nothing, if n is not in the tree.
*/
void substitution_tree::erase(expr * e) {
    if (is_app(e))
        erase(to_app(e));
    else {
        SASSERT(is_var(e));
        sort * s = to_var(e)->get_sort();
        unsigned id = s->get_decl_id();
        if (id >= m_vars.size() || m_vars[id] == 0)
            return;
        var_ref_vector * v = m_vars[id];
        v->erase(to_var(e));
    }
}

/**
   \brief Remove application from the substitution tree.
   Do nothing, if n is not in the tree.
*/
void substitution_tree::erase(app * e) {
    func_decl * d = e->get_decl();
    unsigned id   = d->get_decl_id();
    if (id >= m_roots.size() || !m_roots[id])
        return;

    reset_compiler();
    set_reg_value(0, e);
    m_todo.push_back(0);
    
    node * r = m_roots[id];
    node * parent = nullptr;
    node * prev   = nullptr;

    while (true) {
        svector<subst> & sv = r->m_subst;
        svector<subst>::iterator it  = sv.begin();
        svector<subst>::iterator end = sv.end();
        for (; it != end; ++it) {
            subst & s     = *it;
            unsigned ireg = s.first->get_idx();
            expr * out    = s.second;
            expr * in     = get_reg_value(ireg);
            SASSERT(is_var(out) || is_app(out));
            if (is_var(out)) {
                if (out != in) {
                    reset_registers(0);
                    return; // node is not in the substitution tree
                }
                erase_reg_from_todo(ireg);
            }
            else {
                if (!in || !is_app(in) || to_app(out)->get_decl() != to_app(in)->get_decl()) {
                    reset_registers(0);
                    return; // node is not in the substitution tree
                }
                erase_reg_from_todo(ireg);
                process_args(to_app(in), to_app(out));
            }
        }

        if (m_todo.empty()) {
            reset_registers(0);
            SASSERT(r->m_expr == e);
            if (parent == nullptr) {
                delete_node(r);
                m_roots[id] = 0;
            }
            else if (at_least_3_children(parent)) {
                if (prev == nullptr)
                    parent->m_first_child = r->m_next_sibling;
                else 
                    prev->m_next_sibling  = r->m_next_sibling;
                delete_node(r);
            }
            else {
                SASSERT(parent->m_first_child && parent->m_first_child->m_next_sibling && !parent->m_first_child->m_next_sibling->m_next_sibling);
                node * other_child = prev ? prev : r->m_next_sibling;
                SASSERT(other_child);
                parent->m_subst.append(other_child->m_subst);
                parent->m_leaf = other_child->m_leaf;
                if (other_child->m_leaf)
                    parent->m_expr = other_child->m_expr;
                else 
                    parent->m_first_child = other_child->m_first_child;
                delete_node(r);
                dealloc(other_child); // Remark: I didn't use delete_node since its resources were sent to parent.
            }
            m_size --;
            return;
        }
        else {
            parent = r;
            if (!find_fully_compatible_child(r, prev, r)) {
                // node is not in the substitution tree
                reset_registers(0);
                return;
            }
            // continue with fully compatible child
        }
    }
}

void substitution_tree::delete_node(node * n) {
    ptr_buffer<node> todo;
    SASSERT(todo.empty());
    todo.push_back(n);
    while (!todo.empty()) {
        node * n = todo.back();
        todo.pop_back();
        svector<subst>::iterator it2  = n->m_subst.begin();
        svector<subst>::iterator end2 = n->m_subst.end();
        for (; it2 != end2; ++it2) {
            m_manager.dec_ref(it2->first);
            m_manager.dec_ref(it2->second);
        }
        if (n->m_leaf) 
            m_manager.dec_ref(n->m_expr);
        else {
            node * c = n->m_first_child;
            while (c) {
                todo.push_back(c);
                c = c->m_next_sibling;
            }
        }
        dealloc(n);
    }
}

void substitution_tree::reset() {
    ptr_vector<node>::iterator it  = m_roots.begin();
    ptr_vector<node>::iterator end = m_roots.end();
    for (; it != end; ++it) {
        if (*it)
            delete_node(*it);
    }
    m_roots.reset();
    std::for_each(m_vars.begin(), m_vars.end(), delete_proc<var_ref_vector>());
    m_vars.reset();
    m_size = 0;
}

void substitution_tree::display(std::ostream & out, subst const & s) const {
    out << "r!" << s.first->get_idx() << " -> ";
    if (is_app(s.second)) {
        unsigned num = to_app(s.second)->get_num_args();
        if (num == 0)
            out << to_app(s.second)->get_decl()->get_name();
        else {
            out << "(" << to_app(s.second)->get_decl()->get_name();
            for (unsigned i = 0; i < num; i++)
                out << " r!" << to_var(to_app(s.second)->get_arg(i))->get_idx();
            out << ")";
        }
    }
    else {
        out << mk_pp(s.second, m_manager);
    }
}

void substitution_tree::display(std::ostream & out, svector<subst> const & sv) const {
    svector<subst>::const_iterator it  = sv.begin();
    svector<subst>::const_iterator end = sv.end();
    for (bool first = true; it != end; ++it, first = false) {
        subst const & s = *it;
        if (!first) 
            out << "; ";
        display(out, s);
    }
}

void substitution_tree::display(std::ostream & out, node * n, unsigned delta) const {
    for (unsigned i = 0; i < delta; i++) 
        out << "  ";
    display(out, n->m_subst);
    if (n->m_leaf) {
        params_ref p;
        p.set_bool("single_line", true);
        out << "  ==> ";
        out << mk_pp(n->m_expr, m_manager, p);
        out << "\n";
    }
    else {
        out << "\n";
        node * c = n->m_first_child;
        while (c) {
            display(out, c, delta+1);
            c = c->m_next_sibling;
        }
    }
}

bool substitution_tree::backtrack() {
    while (!m_bstack.empty()) {
        TRACE("st", tout << "backtracking...\n";);
        m_subst->pop_scope();

        node * n = m_bstack.back();
        if (n->m_next_sibling) {
            m_bstack.back() = n->m_next_sibling;
            return true;
        }
        m_bstack.pop_back();
    }
    return false;
}

inline expr_offset substitution_tree::find(expr_offset p) {
    TRACE("substitution_tree_bug", tout << "find...\n";);
    while (is_var(p.get_expr())) {
        TRACE("substitution_tree_bug", tout << mk_pp(p.get_expr(), m_manager) << " " << p.get_offset() << "\n";);
        if (!m_subst->find(to_var(p.get_expr()), p.get_offset(), p))
            return p;
    }
    return p;
}

template<substitution_tree::st_visit_mode Mode>
bool substitution_tree::bind_var(var * v, unsigned offset, expr_offset const & p) {
    TRACE("st", tout << "bind_var: " << mk_pp(v, m_manager) << " " << offset << "\n" << 
          mk_pp(p.get_expr(), m_manager) << " " << p.get_offset() << "\n";);
    if (Mode == STV_INST && offset == m_st_offset) {
        SASSERT(!is_var(p.get_expr()) || p.get_offset() != m_reg_offset);
        if (is_var(p.get_expr()) && p.get_offset() == m_in_offset) {
            m_subst->insert(p, expr_offset(v, offset));
            return true;
        }
        return false;
    }
    if (Mode == STV_GEN && offset == m_in_offset) {
        SASSERT(!is_var(p.get_expr()) || p.get_offset() != m_reg_offset);
        if (is_var(p.get_expr()) && p.get_offset() == m_st_offset) {
            m_subst->insert(p, expr_offset(v, offset));
            return true;
        }
        return false;
    }
    m_subst->insert(v, offset, p);
    TRACE("st_bug", tout << "substitution updated\n"; m_subst->display(tout););
    return true;
}

template<substitution_tree::st_visit_mode Mode>
bool substitution_tree::unify_match(expr_offset p1, expr_offset p2) {
    svector<entry> & todo = m_visit_todo;
    todo.reset();
    todo.push_back(entry(p1, p2));
    while (!todo.empty()) {
        entry const & e = todo.back();
        p1 = find(e.first);
        p2 = find(e.second);
        todo.pop_back();
        if (p1 != p2) {
            expr * n1 = p1.get_expr();
            expr * n2 = p2.get_expr();
            SASSERT(!is_quantifier(n1));
            SASSERT(!is_quantifier(n2));
            bool v1 = is_var(n1);
            bool v2 = is_var(n2);
            TRACE("st", 
                  tout << "n1: " << mk_pp(n1, m_manager) << " " << p1.get_offset() << "\n";
                  tout << "n2: " << mk_pp(n2, m_manager) << " " << p2.get_offset() << "\n";);
            if (v1 && v2) {
                if (p2.get_offset() == m_reg_offset)
                    std::swap(p1, p2);
                if (!bind_var<Mode>(to_var(p1.get_expr()), p1.get_offset(), p2))
                    return false;
            }
            else if (v1) { 
                if (!bind_var<Mode>(to_var(n1), p1.get_offset(), p2))
                    return false;
            }
            else if (v2) {
                if (!bind_var<Mode>(to_var(n2), p2.get_offset(), p1))
                    return false;
            }
            else {
                app * a1 = to_app(n1);
                app * a2 = to_app(n2);
                unsigned off1 = p1.get_offset();
                unsigned off2 = p2.get_offset();
                if (a1->get_decl() != a2->get_decl() || a1->get_num_args() != a2->get_num_args())
                    return false;
                unsigned j = a1->get_num_args();
                while (j > 0) {
                    --j;
                    entry new_e(expr_offset(a1->get_arg(j), off1),
                                expr_offset(a2->get_arg(j), off2));
                    todo.push_back(new_e);
                }
            }
        }
    }
    return true;
}

template<substitution_tree::st_visit_mode Mode>
bool substitution_tree::visit_vars(expr * e, st_visitor & st) {
    if (m_vars.empty())
        return true; // continue
    sort * s      = m_manager.get_sort(e);
    unsigned s_id = s->get_decl_id();
    if (s_id < m_vars.size()) {
        var_ref_vector * v = m_vars[s_id];
        if (v && !v->empty()) {
            unsigned sz = v->size();
            for (unsigned i = 0; i < sz; i++) {
                var * curr = v->get(i);
                m_subst->push_scope();
                if (unify_match<Mode>(expr_offset(curr, m_st_offset), expr_offset(e, m_in_offset))) {
                    if (Mode != STV_UNIF || m_subst->acyclic()) {
                        if (!st(curr)) {
                            m_subst->pop_scope();
                            return false; // stop
                        }
                    }
                }
                m_subst->pop_scope();
            }
        }
    }
    return true; // continue
}

template<substitution_tree::st_visit_mode Mode>
bool substitution_tree::visit(svector<subst> const & sv) {
    svector<subst>::const_iterator it  = sv.begin();
    svector<subst>::const_iterator end = sv.end();
    for (; it != end; ++it) {
        subst const & s = *it;
        TRACE("st", tout << "processing subst:\n"; display(tout, s); tout << "\n";);
        var *  rin  = s.first;
        expr * out  = s.second; 
        expr_offset p1(rin, m_reg_offset);
        expr_offset p2(out, is_var(out) ? m_st_offset : m_reg_offset);
        if (!unify_match<Mode>(p1, p2)) 
            return false;
    }
    return true;
}

template<substitution_tree::st_visit_mode Mode>
bool substitution_tree::visit(expr * e, st_visitor & st, node * r) {
    m_bstack.reset();
    m_bstack.push_back(r);
    m_subst->push_scope();
    m_subst->insert(static_cast<unsigned>(0), m_reg_offset, expr_offset(e, m_in_offset));

    while (true) {
        node * n = m_bstack.back();
        TRACE("st", tout << "push scope...\n";);
        m_subst->push_scope();
        TRACE("st", tout << "processing node:\n"; display(tout, n->m_subst); tout << "\n";);
        if (visit<Mode>(n->m_subst)) {
            if (n->m_leaf) {
                // if searching for unifiers and the substitution is cyclic, then backtrack.
                if (Mode == STV_UNIF && !m_subst->acyclic()) {
                    if (!backtrack())
                        break;
                }
                else {
                    TRACE("st_bug", tout << "found match:\n"; m_subst->display(tout); tout << "m_subst: " << m_subst << "\n";);
                    if (!st(n->m_expr)) {
                        clear_stack();
                        return false;
                    }
                    if (!backtrack())
                        break;
                }
            }
            else {
                m_bstack.push_back(n->m_first_child);
            }
        }
        else if (!backtrack())
            break;
    }
    clear_stack();
    return true;
}

void substitution_tree::clear_stack() {
    while (!m_bstack.empty()) {
        m_subst->pop_scope();
        m_bstack.pop_back();
    }
    m_subst->pop_scope();
}

template<substitution_tree::st_visit_mode Mode>
void substitution_tree::visit(expr * e, st_visitor & st, unsigned in_offset, unsigned st_offset, unsigned reg_offset) {
    m_in_offset  = in_offset;
    m_st_offset  = st_offset;
    m_reg_offset = reg_offset;

    m_subst = &(st.get_substitution());
    m_subst->reserve_vars(get_approx_num_regs());

    if (visit_vars<Mode>(e, st)) {
        if (is_app(e)) {
            func_decl * d  = to_app(e)->get_decl();
            unsigned id    = d->get_decl_id();
            node * r       = m_roots.get(id, 0);
            if (r)  
                visit<Mode>(e, st, r);
        }
        else {
            SASSERT(is_var(e));
            ptr_vector<node>::iterator it  = m_roots.begin();
            ptr_vector<node>::iterator end = m_roots.end();
            for (; it != end; ++it) {
                node * r = *it;
                if (r != nullptr) {
                    var * v = r->m_subst[0].first;
                    if (v->get_sort() == to_var(e)->get_sort())
                        if (!visit<Mode>(e, st, r))
                            break;
                }
            }
        }
    }
}

void substitution_tree::unify(expr * e, st_visitor & v, unsigned in_offset, unsigned st_offset, unsigned reg_offset) {
    visit<STV_UNIF>(e, v, in_offset, st_offset, reg_offset);
}

void substitution_tree::inst(expr * e, st_visitor & v, unsigned in_offset, unsigned st_offset, unsigned reg_offset) {
    visit<STV_INST>(e, v, in_offset, st_offset, reg_offset);
}

void substitution_tree::gen(expr * e, st_visitor & v, unsigned in_offset, unsigned st_offset, unsigned reg_offset) {
    visit<STV_GEN>(e, v, in_offset, st_offset, reg_offset);
}

void substitution_tree::display(std::ostream & out) const {
    out << "substitution tree:\n";
    ptr_vector<node>::const_iterator it  = m_roots.begin();
    ptr_vector<node>::const_iterator end = m_roots.end();
    for (; it != end; ++it)
        if (*it)
            display(out, *it, 0);
    bool found_var = false;
    ptr_vector<var_ref_vector>::const_iterator it2  = m_vars.begin();
    ptr_vector<var_ref_vector>::const_iterator end2 = m_vars.end();
    for (; it2 != end2; ++it2) {
        var_ref_vector * v = *it2;
        if (v == nullptr)
            continue; // m_vars may contain null pointers. See substitution_tree::insert.
        unsigned num = v->size();
        for (unsigned i = 0; i < num; i++) {
            if (!found_var) {
                found_var = true;
                out << "vars: ";
            }
            out << mk_pp(v->get(i), m_manager) << " ";
        }
    }
    if (found_var)
        out << "\n";
}


substitution_tree::substitution_tree(ast_manager & m):
    m_manager(m),
    m_max_reg(0),
    m_size(0) {
}

substitution_tree::~substitution_tree() {
    reset();
}
