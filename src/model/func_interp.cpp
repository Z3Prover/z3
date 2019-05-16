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
#include "util/obj_hashtable.h"
#include "ast/rewriter/var_subst.h"
#include "ast/ast_pp.h"
#include "ast/ast_smt2_pp.h"
#include "ast/ast_util.h"
#include "model/func_interp.h"
#include "ast/array_decl_plugin.h"

func_entry::func_entry(ast_manager & m, unsigned arity, expr * const * args, expr * result):
    m_args_are_values(true),
    m_result(result) {
    //SASSERT(is_ground(result));
    m.inc_ref(result);
    for (unsigned i = 0; i < arity; i++) {
        expr * arg = args[i];
        //SASSERT(is_ground(arg));
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
    m_else(nullptr),
    m_args_are_values(true),
    m_interp(nullptr) {
}

func_interp::~func_interp() {
    for (func_entry* curr : m_entries) {
        curr->deallocate(m_manager, m_arity);
    }
    m_manager.dec_ref(m_else);
    m_manager.dec_ref(m_interp);
}

func_interp * func_interp::copy() const {
    func_interp * new_fi = alloc(func_interp, m_manager, m_arity);

    for (func_entry * curr : m_entries) {
        new_fi->insert_new_entry(curr->get_args(), curr->get_result());
    }
    new_fi->set_else(m_else);
    return new_fi;
}

void func_interp::reset_interp_cache() {
    m_manager.dec_ref(m_interp);
    m_interp = nullptr;
}

bool func_interp::is_fi_entry_expr(expr * e, ptr_vector<expr> & args) {
    args.reset();
    expr* c, *t, *f, *a0, *a1;
    if (!m().is_ite(e, c, t, f)) {
        return false;
    }

    if (!is_ground(t) ||
        (m_arity == 0) ||
        (m_arity == 1 && !m().is_eq(c, a0, a1)) ||
        (m_arity > 1 && (!m().is_and(c) || to_app(c)->get_num_args() != m_arity)))
        return false;

    args.resize(m_arity);
    for (unsigned i = 0; i < m_arity; i++) {
        expr * ci = (m_arity == 1 && i == 0) ? c : to_app(c)->get_arg(i);

        if (!m().is_eq(ci, a0, a1)) 
            return false;

        if (is_var(a0) && to_var(a0)->get_idx() == i)
            args[i] = a1;
        else if (is_var(a1) && to_var(a1)->get_idx() == i)
            args[i] = a0;
        else
            return false;
    }

    return true;
}

void func_interp::set_else(expr * e) {
    if (e == m_else)
        return;

    reset_interp_cache();

    TRACE("func_interp", tout << "set_else: " << expr_ref(e, m()) << "\n";);

    ptr_vector<expr> args;
    while (e && is_fi_entry_expr(e, args)) {
        insert_entry(args.c_ptr(), to_app(e)->get_arg(1));
        e = to_app(e)->get_arg(2);
    }

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
    for (func_entry* curr : m_entries) {
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
    for (func_entry* curr : m_entries) {
        if (curr->eq_args(m(), m_arity, args))
            return curr;
    }
    return nullptr;
}

void func_interp::insert_entry(expr * const * args, expr * r) {
    reset_interp_cache();
    func_entry * entry = get_entry(args);
    if (entry != nullptr) {
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
           tout << "Old: " << mk_ismt2_pp(get_entry(args)->get_result(), m_manager) << "\n";
           );
    SASSERT(get_entry(args) == nullptr);
    func_entry * new_entry = func_entry::mk(m_manager, m_arity, args, r);
    if (!new_entry->args_are_values())
        m_args_are_values = false;
    m_entries.push_back(new_entry);
}

bool func_interp::eval_else(expr * const * args, expr_ref & result) const {
    if (m_else == nullptr)
        return false;
    var_subst s(m_manager, false);
    SASSERT(!s.std_order()); // (VAR 0) <- args[0], (VAR 1) <- args[1], ...
    result = s(m_else, m_arity, args);
    return true;
}

/**
   \brief Return the result with the maximal number of occurrencies in m_entries.
*/
expr * func_interp::get_max_occ_result() const {
    if (m_entries.empty())
        return nullptr;
    obj_map<expr, unsigned> num_occs;
    expr *   r_max = nullptr;
    unsigned max   = 0;
    for (func_entry * curr : m_entries) {
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
    if (m_else == nullptr || m_entries.empty())
        return; // nothing to be done
    if (!is_ground(m_else))
        return; // forall entries e in m_entries e.get_result() is ground
    unsigned j = 0;
    m_args_are_values = true;
    for (func_entry * curr : m_entries) {
        if (curr->get_result() != m_else) {
            m_entries[j++] = curr;
            if (!curr->args_are_values())
                m_args_are_values = false;
        }
        else {
            curr->deallocate(m_manager, m_arity);
        }
    }
    if (j < m_entries.size()) {
        reset_interp_cache();
        m_entries.shrink(j);
    }
    // other compression, if else is a default branch.
    // or function encode identity.
    if (m_manager.is_false(m_else)) {
        expr_ref new_else(get_interp(), m_manager);
        for (func_entry * curr : m_entries) {
            curr->deallocate(m_manager, m_arity);
        }
        m_entries.reset();
        reset_interp_cache();
        m_manager.inc_ref(new_else);
        m_manager.dec_ref(m_else);
        m_else = new_else;
    }
    else if (!m_entries.empty() && is_identity()) {
        for (func_entry * curr : m_entries) {
            curr->deallocate(m_manager, m_arity);
        }
        m_entries.reset();
        reset_interp_cache();
        expr_ref new_else(m_manager.mk_var(0, m_manager.get_sort(m_else)), m_manager);
        m_manager.inc_ref(new_else);
        m_manager.dec_ref(m_else);
        m_else = new_else;
    }
}

/**
 * \brief check if function is identity
 */
bool func_interp::is_identity() const {
    if (m_arity != 1) return false;
    if (m_else == nullptr) return false;

    // all entries map a value to itself
    for (func_entry * curr : m_entries) {
        if (curr->get_arg(0) != curr->get_result()) return false;
        if (curr->get_result() == m_else) return false;
    }    
    if (is_var(m_else)) return true;
    if (!m_manager.is_value(m_else)) return false;    
    sort_size const& sz = m_manager.get_sort(m_else)->get_num_elements();
    if (!sz.is_finite()) return false;

    //
    // the else entry is a value not covered by other entries
    // it, together with the entries covers the entire domain.
    //
    return (sz.size() == m_entries.size() + 1);
}

expr_ref func_interp::get_array_interp(sort_ref_vector const& domain) const {
    if (m_else == nullptr) 
        return expr_ref(m_manager);
    if (!is_ground(m_else)) {
        return expr_ref(m_manager);
    }
    array_util autil(m_manager);
    sort_ref A(autil.mk_array_sort(domain.size(), domain.c_ptr(), m_manager.get_sort(m_else)), m_manager);
    expr_ref r(autil.mk_const_array(A, m_else), m_manager);
    expr_ref_vector args(m_manager);
    for (func_entry * curr : m_entries) {
        expr * res = curr->get_result();

        if (m_else == res) {
            continue;
        }
        args.reset();
        args.push_back(r);        
        for (unsigned i = 0; i < m_arity; i++) {
            expr* arg = curr->get_arg(i);
            if (!is_ground(arg)) {
                return expr_ref(m_manager);
            }
            args.push_back(arg);
        }
        args.push_back(res);
        r = autil.mk_store(args.size(), args.c_ptr());
    }
    return r;    
}

expr * func_interp::get_interp_core() const {
    if (m_else == nullptr)
        return nullptr;
    expr * r = m_else;
    ptr_buffer<expr> vars;
    for (func_entry * curr : m_entries) {
        if (m_else == curr->get_result()) {
            continue;
        }
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
        expr * cond = mk_and(m_manager, eqs.size(), eqs.c_ptr());
        expr * th = curr->get_result();
        if (m_manager.is_true(th)) {
            r = m_manager.mk_or(cond, r);
        }
        else if (m_manager.is_false(th)) {
            r = m_manager.mk_and(m_manager.mk_not(cond), r);
        }
        else {
            r = m_manager.mk_ite(cond, th, r);
        }
    }
    return r;
}

expr * func_interp::get_interp() const {
    if (m_interp != nullptr)
        return m_interp;
    expr * r = get_interp_core();
    if (r != nullptr) {
        const_cast<func_interp*>(this)->m_interp = r;
        m_manager.inc_ref(m_interp);
    }
    return r;
}

func_interp * func_interp::translate(ast_translation & translator) const {
    func_interp * new_fi = alloc(func_interp, translator.to(), m_arity);

    for (func_entry * curr : m_entries) {
        ptr_buffer<expr> new_args;
        for (unsigned i = 0; i < m_arity; i++)
            new_args.push_back(translator(curr->get_arg(i)));
        new_fi->insert_new_entry(new_args.c_ptr(), translator(curr->get_result()));
    }
    new_fi->set_else(translator(m_else));
    return new_fi;
}
