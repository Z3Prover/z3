/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    func_interp.cpp

Abstract:
    See func_interp.h

Author:

    Leonardo de Moura (leonardo) 2010-12-30.

Revision History:

--*/
#include"func_interp.h"
#include"var_subst.h"
#include"obj_hashtable.h"
#include"ast_pp.h"
#include"ast_smt2_pp.h"

func_entry::func_entry(ast_manager & m, unsigned arity, expr * const * args, expr * result):
    m_args_are_values(true),
    m_result(result) {
    SASSERT(is_ground(result));
    m.inc_ref(result);
    for (unsigned i = 0; i < arity; i++) {
        expr * arg = args[i];
        SASSERT(is_ground(arg));
        if (!m.is_value(arg))
            m_args_are_values = false;
        m.inc_ref(arg);
        m_args[i] = arg;
    }
}

func_entry * func_entry::mk(ast_manager & m, unsigned arity, expr * const * args, expr * result) {
    small_object_allocator & allocator = m.get_allocator();
    unsigned sz = get_obj_size(arity);
    void * mem  = allocator.allocate(sz);
    return new (mem) func_entry(m, arity, args, result);
}

void func_entry::set_result(ast_manager & m, expr * r) {
    m.inc_ref(r);
    m.dec_ref(m_result);
    m_result = r;
}

bool func_entry::eq_args(ast_manager & m, unsigned arity, expr * const * args) const {
    unsigned i = 0;
    for (; i < arity; i++) {
        if (!m.are_equal(m_args[i], args[i]))
            return false;
    }
    return true;
}

void func_entry::deallocate(ast_manager & m, unsigned arity) {
    for (unsigned i = 0; i < arity; i++) {
        m.dec_ref(m_args[i]);
    }
    m.dec_ref(m_result);
    small_object_allocator & allocator = m.get_allocator();
    unsigned sz = get_obj_size(arity);
    allocator.deallocate(sz, this);
}

func_interp::func_interp(ast_manager & m, unsigned arity):
    m_manager(m),
    m_arity(arity),
    m_else(0),
    m_args_are_values(true),
    m_interp(0) {
}

func_interp::~func_interp() {
    ptr_vector<func_entry>::iterator it  = m_entries.begin();
    ptr_vector<func_entry>::iterator end = m_entries.end();
    for (; it != end; ++it) {
        func_entry * curr = *it;
        curr->deallocate(m_manager, m_arity);
    }
    m_manager.dec_ref(m_else);
    m_manager.dec_ref(m_interp);
}

func_interp * func_interp::copy() const {
    func_interp * new_fi = alloc(func_interp, m_manager, m_arity);

    ptr_vector<func_entry>::const_iterator it  = m_entries.begin();
    ptr_vector<func_entry>::const_iterator end = m_entries.end();
    for (; it != end; ++it) {
        func_entry * curr = *it;
        new_fi->insert_new_entry(curr->get_args(), curr->get_result());
    }
    new_fi->set_else(m_else);
    return new_fi;
}

void func_interp::reset_interp_cache() {
    m_manager.dec_ref(m_interp);
    m_interp = 0;
}
    
void func_interp::set_else(expr * e) {
    reset_interp_cache();
    m_manager.inc_ref(e);
    m_manager.dec_ref(m_else);
    m_else = e;
}

/**
   \brief Return true if the interpretation represents the constant function.
*/
bool func_interp::is_constant() const {
    if (is_partial())
        return false;
    if (!is_ground(m_else))
        return false;
    ptr_vector<func_entry>::const_iterator it  = m_entries.begin();
    ptr_vector<func_entry>::const_iterator end = m_entries.end();
    for (; it != end; ++it) {
        func_entry * curr = *it;
        if (curr->get_result() != m_else)
            return false;
    }
    return true;
}

/**
   \brief Return a func_entry e such that m().are_equal(e.m_args[i], args[i]) for all i in [0, m_arity).
   If such entry does not exist then return 0, and store set
   args_are_values to true if for all entries e e.args_are_values() is true.
*/
func_entry * func_interp::get_entry(expr * const * args) const {
    ptr_vector<func_entry>::const_iterator it  = m_entries.begin();
    ptr_vector<func_entry>::const_iterator end = m_entries.end();
    for (; it != end; ++it) {
        func_entry * curr = *it;
        if (curr->eq_args(m(), m_arity, args))
            return curr;
    }
    return 0;
}

void func_interp::insert_entry(expr * const * args, expr * r) {
    reset_interp_cache();
    func_entry * entry = get_entry(args); 
    if (entry != 0) {
        entry->set_result(m_manager, r);
        return;
    }
    insert_new_entry(args, r);
}

void func_interp::insert_new_entry(expr * const * args, expr * r) {
    reset_interp_cache();
    CTRACE("func_interp_bug", get_entry(args) != 0,
           tout << "Old: " << mk_ismt2_pp(get_entry(args)->m_result, m_manager) << "\n";
           tout << "Args:";
           for (unsigned i = 0; i < m_arity; i++) {
               tout << mk_ismt2_pp(get_entry(args)->get_arg(i), m_manager) << "\n";
           }
           tout << "New: " << mk_ismt2_pp(r, m_manager) << "\n";
           tout << "Args:";
           for (unsigned i = 0; i < m_arity; i++) {
               tout << mk_ismt2_pp(args[i], m_manager) << "\n";
           }
           );
    SASSERT(get_entry(args) == 0);
    func_entry * new_entry = func_entry::mk(m_manager, m_arity, args, r);
    if (!new_entry->args_are_values())
        m_args_are_values = false;
    m_entries.push_back(new_entry);
}

bool func_interp::eval_else(expr * const * args, expr_ref & result) const {
    if (m_else == 0)
        return false;
    var_subst s(m_manager, false);
    SASSERT(!s.std_order()); // (VAR 0) <- args[0], (VAR 1) <- args[1], ...
    s(m_else, m_arity, args, result);
    return true;
}

/**
   \brief Return the result with the maximal number of occurrencies in m_entries.
*/
expr * func_interp::get_max_occ_result() const {
    if (m_entries.empty())
        return 0;
    obj_map<expr, unsigned> num_occs;
    expr *   r_max = 0;
    unsigned max   = 0;
    ptr_vector<func_entry>::const_iterator it  = m_entries.begin();
    ptr_vector<func_entry>::const_iterator end = m_entries.end();
    for (; it != end; ++it) {
        func_entry * curr = *it;
        expr * r = curr->get_result();
        unsigned occs = 0; 
        num_occs.find(r, occs);
        occs++;
        num_occs.insert(r, occs);
        if (occs > max) {
            max   = occs;
            r_max = r;
        }
    }
    return r_max;
}

/**
   \brief Remove entries e such that e.get_result() == m_else.
*/
void func_interp::compress() {
    if (m_else == 0 || m_entries.empty())
        return; // nothing to be done
    if (!is_ground(m_else))
        return; // forall entries e in m_entries e.get_result() is ground
    unsigned i = 0;
    unsigned j = 0;
    unsigned sz = m_entries.size();
    m_args_are_values = true;
    for (; i < sz; i++) {
        func_entry * curr = m_entries[i];
        if (curr->get_result() != m_else) {
            m_entries[j] = curr;
            j++;
            if (!curr->args_are_values())
                m_args_are_values = false;
        }
        else {
            curr->deallocate(m_manager, m_arity);
        }
    }
    if (j < sz) {
        reset_interp_cache();
        m_entries.shrink(j);
    }
}

expr * func_interp::get_interp_core() const {
    if (m_else == 0)
        return 0;
    expr * r = m_else;
    ptr_buffer<expr> vars;
    ptr_vector<func_entry>::const_iterator it  = m_entries.begin();
    ptr_vector<func_entry>::const_iterator end = m_entries.end();
    for (; it != end; ++it) {
        func_entry * curr = *it;
        if (vars.empty()) {
            for (unsigned i = 0; i < m_arity; i++) {
                vars.push_back(m_manager.mk_var(i, m_manager.get_sort(curr->get_arg(i))));
            }
        }
        ptr_buffer<expr> eqs;
        for (unsigned i = 0; i < m_arity; i++) {
            eqs.push_back(m_manager.mk_eq(vars[i], curr->get_arg(i)));
        }
        SASSERT(eqs.size() == m_arity);
        expr * cond;
        if (m_arity == 1)
            cond = eqs.get(0);
        else
            cond = m_manager.mk_and(eqs.size(), eqs.c_ptr());
        r = m_manager.mk_ite(cond, curr->get_result(), r);
    }
    return r;
}

expr * func_interp::get_interp() const {
    if (m_interp != 0)
        return m_interp;
    expr * r = get_interp_core();
    if (r != 0) {
        const_cast<func_interp*>(this)->m_interp = r;
        m_manager.inc_ref(m_interp);
    }
    return r;
}

func_interp * func_interp::translate(ast_translation & translator) const {    
    func_interp * new_fi = alloc(func_interp, translator.to(), m_arity);

    ptr_vector<func_entry>::const_iterator it  = m_entries.begin();
    ptr_vector<func_entry>::const_iterator end = m_entries.end();
    for (; it != end; ++it) {
        func_entry * curr = *it;        
        ptr_buffer<expr> new_args;
        for (unsigned i=0; i<m_arity; i++)
            new_args.push_back(translator(curr->get_arg(i)));
        new_fi->insert_new_entry(new_args.c_ptr(), translator(curr->get_result()));
    }
    new_fi->set_else(translator(m_else));
    return new_fi;
}
