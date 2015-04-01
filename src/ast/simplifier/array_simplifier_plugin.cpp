/*++
Copyright (c) 2008 Microsoft Corporation

Module Name:

    array_simplifier_plugin.cpp

Abstract:

    <abstract>

Author:

    Nikolaj Bjorner (nbjorner) 2008-05-05

Revision History:

Notes TODO:

    Examine quadratic cost of simplification vs. model-based procedure.

    Parameterize cache replacement strategy.
    Some parameters are hard-wired.

--*/

#include "array_simplifier_plugin.h"
#include "ast_ll_pp.h"
#include "ast_pp.h"


array_simplifier_plugin::array_simplifier_plugin(
    ast_manager & m, 
    basic_simplifier_plugin& s, 
    simplifier& simp,
    array_simplifier_params const& p) : 
    simplifier_plugin(symbol("array"),m),
    m_util(m),
    m_simp(s),
    m_simplifier(simp),
    m_params(p),
    m_store_cache_size(0)
{}


array_simplifier_plugin::~array_simplifier_plugin() {

    select_cache::iterator it = m_select_cache.begin();
    select_cache::iterator end = m_select_cache.end();
    for ( ; it != end; ++it) {
        m_manager.dec_array_ref(it->m_key->size(), it->m_key->c_ptr());
        m_manager.dec_ref(it->m_value);
        dealloc(it->m_key);
    }

    store_cache::iterator it2 = m_store_cache.begin();
    store_cache::iterator end2 = m_store_cache.end();
    for (; it2 != end2; ++it2) {
        m_manager.dec_ref(it->m_value);
        dealloc(it->m_key);
    }
}


bool array_simplifier_plugin::reduce(func_decl * f, unsigned num_args, expr * const * args, expr_ref & result) {
    if (!m_params.m_array_simplify)
        return false;
    set_reduce_invoked();
    if (m_presimp)
        return false;
#if Z3DEBUG
    for (unsigned i = 0; i < num_args && i < f->get_arity(); ++i) {
        SASSERT(m_manager.get_sort(args[i]) == f->get_domain(i));
    }
#endif
    TRACE("array_simplifier", {
            tout << mk_pp(f, m_manager) << " ";
            for (unsigned i = 0; i < num_args; ++i) {
                tout << mk_pp(args[i], m_manager) << " ";
            }
            tout << "\n";
        }
        );
    SASSERT(f->get_family_id() == m_fid);
    switch(f->get_decl_kind()) {
    case OP_SELECT: 
        mk_select(num_args, args, result);
        break;
    case OP_STORE:
        mk_store(f, num_args, args, result);
        break;
    case OP_SET_UNION: {
        sort* s = f->get_range();
        expr_ref empty(m_manager);
        mk_empty_set(s, empty);
        switch(num_args) {
        case 0:
            result = empty;
            break;
        case 1:
            result = args[0];
            break;
        default: {
            result = args[0];
            func_decl* f_or = m_manager.mk_or_decl();
            for (unsigned i = 1; i < num_args; ++i) {
                mk_map(f_or, result, args[i], result);
            }
            break;
        }
        }
        break;
    }
    case OP_SET_INTERSECT: {
        expr_ref full(m_manager);
        mk_full_set(f->get_range(), full);
        switch(num_args) {
        case 0:
            result = full;
            break;
        case 1:
            result = args[0];
            break;
        default: {
            result = args[0];
            func_decl* f_and = m_manager.mk_and_decl();
            for (unsigned i = 1; i < num_args; ++i) {
                mk_map(f_and, result, args[i], result);
            }
            break;
        }
        }
        TRACE("array_simplifier", tout << "sort " << mk_pp(result.get(), m_manager) << "\n";);
        break;
    }
    case OP_SET_SUBSET: {
        SASSERT(num_args == 2);
        expr_ref diff(m_manager), emp(m_manager);
        mk_set_difference(num_args, args, diff);
        mk_empty_set(m_manager.get_sort(args[0]), emp);
        m_simp.mk_eq(diff.get(), emp.get(), result);
        break;
    }
    case OP_SET_COMPLEMENT: {
        SASSERT(num_args == 1);
        func_decl* f_not = m_manager.mk_not_decl();
        mk_map(f_not, args[0], result);
        break;
    }
    case OP_SET_DIFFERENCE: {
        SASSERT(num_args == 2);
        expr_ref r1(m_manager);
        mk_map(m_manager.mk_not_decl(), args[1], r1);
        mk_map(m_manager.mk_and_decl(), args[0], r1, result);
        break;
    }
    case OP_ARRAY_MAP: {
        SASSERT(f->get_num_parameters() == 1);
        SASSERT(f->get_parameter(0).is_ast());
        SASSERT(is_func_decl(f->get_parameter(0).get_ast()));
        //
        // map_d (store a j v) = (store (map_f a) v (d v)) 
        //
        if (num_args == 1 && is_store(args[0])) {
            app* store_expr = to_app(args[0]);
            unsigned num_args = store_expr->get_num_args();
            SASSERT(num_args >= 3);
            parameter p = f->get_parameter(0);
            func_decl* d = to_func_decl(p.get_ast());
            expr* a = store_expr->get_arg(0);
            expr* v = store_expr->get_arg(num_args-1);
            // expr*const* args = store_expr->get_args()+1;            
            expr_ref r1(m_manager), r2(m_manager);
            ptr_vector<expr> new_args;

            reduce(f, 1, &a, r1);
            m_simplifier.mk_app(d, 1, &v, r2);
            new_args.push_back(r1);
            for (unsigned i = 1; i + 1 < num_args; ++i) {
                new_args.push_back(store_expr->get_arg(i));
            }
            new_args.push_back(r2);
            mk_store(store_expr->get_decl(), num_args, new_args.c_ptr(), result);
            break;
        }
 
       //
        // map_d (store a j v) (store b j w) = (store (map_f a b) j (d v w)) 
        //
        if (num_args > 1 && same_store(num_args, args)) {
            app* store_expr1 = to_app(args[0]);
            unsigned num_indices = store_expr1->get_num_args();
            SASSERT(num_indices >= 3);
            parameter p = f->get_parameter(0);
            func_decl* d = to_func_decl(p.get_ast());
            ptr_vector<expr> arrays;
            ptr_vector<expr> values;
            for (unsigned i = 0; i < num_args; ++i) {
                arrays.push_back(to_app(args[i])->get_arg(0));
                values.push_back(to_app(args[i])->get_arg(num_indices-1));
            }
            
            expr_ref r1(m_manager), r2(m_manager);
            reduce(f, arrays.size(), arrays.c_ptr(), r1);
            m_simplifier.mk_app(d, values.size(), values.c_ptr(), r2);
            ptr_vector<expr> new_args;
            new_args.push_back(r1);
            for (unsigned i = 1; i + 1 < num_indices; ++i) {
                new_args.push_back(store_expr1->get_arg(i));
            }
            new_args.push_back(r2);
            mk_store(store_expr1->get_decl(), new_args.size(), new_args.c_ptr(), result);
            break;
        }
        //
        // map_d (const v) = (const (d v))
        //
        if (num_args == 1 && is_const_array(args[0])) {
            app* const_expr = to_app(args[0]);
            SASSERT(const_expr->get_num_args() == 1);
            parameter p = f->get_parameter(0);
            func_decl* d = to_func_decl(p.get_ast());
            expr* v = const_expr->get_arg(0);
            expr_ref r1(m_manager);
            
            m_simplifier.mk_app(d, 1, &v, r1);
            expr* arg = r1.get();
            parameter param(f->get_range());
            result = m_manager.mk_app(m_fid, OP_CONST_ARRAY, 1, &param, 1, &arg);
            break;
        }
        //
        // map_d (const v) (const w) = (const (d v w))
        //
        if (num_args > 1 && all_const_array(num_args, args)) {
            parameter p = f->get_parameter(0);
            func_decl* d = to_func_decl(p.get_ast());
            ptr_vector<expr> values;
            for (unsigned i = 0; i < num_args; ++i) {
                values.push_back(to_app(args[i])->get_arg(0));
            }
            expr_ref r1(m_manager);
            
            m_simplifier.mk_app(d, values.size(), values.c_ptr(), r1);
            expr* arg = r1.get();
            parameter param(f->get_range());
            result = m_manager.mk_app(m_fid, OP_CONST_ARRAY, 1, &param, 1, &arg);
            break;
        }
        result = m_manager.mk_app(f, num_args, args);
        
        break;
    }
    default:
        result = m_manager.mk_app(f, num_args, args);
        break;
    }
    TRACE("array_simplifier", 
          tout << mk_pp(result.get(), m_manager) << "\n";);

    return true;
}

bool array_simplifier_plugin::same_store(unsigned num_args, expr* const* args) const {
    if (num_args == 0) {
        return true;
    }
    if (!is_store(args[0])) {
        return false;
    }
    SASSERT(to_app(args[0])->get_num_args() >= 3);
    unsigned num_indices = to_app(args[0])->get_num_args() - 2;
    for (unsigned i = 1; i < num_args; ++i) {
        if (!is_store(args[i])) {
            return false;
        }
        for (unsigned j = 1; j < num_indices + 1; ++j) {
            if (to_app(args[0])->get_arg(j) != to_app(args[i])->get_arg(j)) {
                return false;
            }
        }
    }
    return true;
}

bool array_simplifier_plugin::all_const_array(unsigned num_args, expr* const* args) const {
    bool is_const = true;
    for (unsigned i = 0; is_const && i < num_args; ++i) {
        is_const = is_const_array(args[i]);
    }
    return is_const;
}

bool array_simplifier_plugin::all_values(unsigned num_args, expr* const* args) const {
    for (unsigned i = 0; i < num_args; ++i) {
        if (!m_manager.is_unique_value(args[i])) {
            return false;
        }
    }
    return true;
}

bool array_simplifier_plugin::lex_lt(unsigned num_args, expr* const* args1, expr* const* args2) {
    for (unsigned i = 0; i < num_args; ++i) {
    TRACE("array_simplifier", 
          tout << mk_pp(args1[i], m_manager) << "\n";
          tout << mk_pp(args2[i], m_manager) << "\n";
          tout << args1[i]->get_id() << " " << args2[i]->get_id() << "\n";
          );

        if (args1[i]->get_id() < args2[i]->get_id()) return true;
        if (args1[i]->get_id() > args2[i]->get_id()) return false;
    }
    return false;
}


void array_simplifier_plugin::get_stores(expr* n, unsigned& arity, expr*& m, ptr_vector<expr*const>& stores) {
    while (is_store(n)) {
        app* a = to_app(n);
        SASSERT(a->get_num_args() > 2);
        arity = a->get_num_args()-2;
        n = a->get_arg(0);
        stores.push_back(a->get_args()+1);
    }
    m = n;
}

lbool array_simplifier_plugin::eq_default(expr* def, unsigned arity, unsigned num_st, expr*const* const* st) {
    bool all_diseq = m_manager.is_unique_value(def) && num_st > 0;
    bool all_eq = true;
    for (unsigned i = 0; i < num_st; ++i) {
        all_eq  &= (st[i][arity] == def);
        all_diseq &= m_manager.is_unique_value(st[i][arity]) && (st[i][arity] != def);
        TRACE("array_simplifier", tout << m_manager.is_unique_value(st[i][arity]) << " " << mk_pp(st[i][arity], m_manager) << "\n";);
    }
    if (all_eq) {
        return l_true;
    }
    if (all_diseq) {
        return l_false;
    }   
    return l_undef;
}


bool array_simplifier_plugin::insert_table(expr* def, unsigned arity, unsigned num_st, expr*const* const* st, arg_table& table) {
    for (unsigned i = 0; i < num_st; ++i ) {
        for (unsigned j = 0; j < arity; ++j) {
            if (!m_manager.is_unique_value(st[i][j])) {
                return false;
            }
        }
        TRACE("array_simplifier", tout << "inserting: ";
              for (unsigned j = 0; j < arity; ++j) {
                  tout << mk_pp(st[i][j], m_manager) << " ";              
              }
            tout << " |-> " << mk_pp(def, m_manager) << "\n";
            );
        args_entry e(arity, st[i]);
        table.insert_if_not_there(e);
    }
    return true;
}


lbool array_simplifier_plugin::eq_stores(expr* def, unsigned arity, unsigned num_st1, expr*const* const* st1, unsigned num_st2, expr*const* const* st2) {
    if (num_st1 == 0) {
        return eq_default(def, arity, num_st2, st2);
    }
    if (num_st2 == 0) {
        return eq_default(def, arity, num_st1, st1);
    }
    arg_table table1, table2;
    if (!insert_table(def, arity, num_st1, st1, table1)) {
        return l_undef;
    }
    if (!insert_table(def, arity, num_st2, st2, table2)) {
        return l_undef;
    }

    arg_table::iterator it = table1.begin();
    arg_table::iterator end = table1.end();
    for (; it != end; ++it) {
        args_entry const & e1 = *it;
        args_entry e2;
        expr* v1 = e1.m_args[arity];
        if (table2.find(e1, e2)) {
            expr* v2 = e2.m_args[arity];
            if (v1 == v2) {
                table2.erase(e1);
                continue;
            }
            if (m_manager.is_unique_value(v1) && m_manager.is_unique_value(v2)) {
                return l_false;
            }
            return l_undef;
        }
        else if (m_manager.is_unique_value(v1) && m_manager.is_unique_value(def) && v1 != def) {
            return l_false;
        }
    }
    it = table2.begin();
    end = table2.end();
    for (; it != end; ++it) {
        args_entry const & e = *it;
        expr* v = e.m_args[arity];
        if (m_manager.is_unique_value(v) && m_manager.is_unique_value(def) && v != def) {
            return l_false;
        }
    }
    if (!table2.empty() || !table1.empty()) {
        return l_undef;
    }
    return l_true;    
}


bool array_simplifier_plugin::reduce_eq(expr * lhs, expr * rhs, expr_ref & result) {
    set_reduce_invoked();
    expr* c1, *c2;
    ptr_vector<expr*const> st1, st2;
    unsigned arity1 = 0;
    unsigned arity2 = 0;
    get_stores(lhs, arity1, c1, st1);
    get_stores(rhs, arity2, c2, st2);
    if (arity1 == arity2 && is_const_array(c1) && is_const_array(c2)) {
        c1 = to_app(c1)->get_arg(0);
        c2 = to_app(c2)->get_arg(0);
        if (c1 == c2) {
            lbool eq = eq_stores(c1, arity2, st1.size(), st1.c_ptr(), st2.size(), st2.c_ptr());
            TRACE("array_simplifier", 
                  tout << mk_pp(lhs, m_manager) << " = " 
                  << mk_pp(rhs, m_manager) << " := " << eq << "\n";
                  tout << "arity: " << arity1 << "\n";);
            switch(eq) {
            case l_false: 
                result = m_manager.mk_false(); 
                return true;
            case l_true: 
                result = m_manager.mk_true(); 
                return true;
            default: 
                return false;
            }
        }
        else if (m_manager.is_unique_value(c1) && m_manager.is_unique_value(c2)) {
            result = m_manager.mk_false();
            return true;
        }
    }
    return false;
}
    
bool array_simplifier_plugin::reduce_distinct(unsigned num_args, expr * const * args, expr_ref & result) {
    set_reduce_invoked();
    return false;
}
    

array_simplifier_plugin::const_select_result
array_simplifier_plugin::mk_select_const(expr* m, app* index, expr_ref& result) {
    store_info* info = 0;
    expr* r = 0, *a = 0;
    if (!is_store(m)) {
        return NOT_CACHED;
    }
    if (!m_store_cache.find(m, info)) {
        return NOT_CACHED;
    }       
    if (info->m_map.find(index, r)) {
        result = r;
        return FOUND_VALUE;
    }
    a = info->m_default.get();

    // 
    // Unfold and cache the store while searching for value of index.
    //     
    while (is_store(a) && m_manager.is_unique_value(to_app(a)->get_arg(1))) {
        app* b = to_app(a);
        app* c = to_app(b->get_arg(1));
        
        if (!info->m_map.contains(c)) {
            info->m_map.insert(c, b->get_arg(2));
            m_manager.inc_ref(b->get_arg(2));
            ++m_store_cache_size;
        }
        a = b->get_arg(0);
        info->m_default = a;
        
        if (c == index) {
            result = b->get_arg(2);
            return FOUND_VALUE;
        }
    }
    result = info->m_default.get();
    return FOUND_DEFAULT;
}

void array_simplifier_plugin::cache_store(unsigned num_stores, expr* store_term) 
{
    if (num_stores <= m_const_store_threshold) {
        return;
    }
    prune_store_cache();
    if (!m_store_cache.contains(store_term)) {
        store_info * info = alloc(store_info, m_manager, store_term);
        m_manager.inc_ref(store_term);
        m_store_cache.insert(store_term, info);
        TRACE("cache_store", tout << m_store_cache.size() << "\n";);
        ++m_store_cache_size;
    }
}

void array_simplifier_plugin::cache_select(unsigned num_args, expr * const * args, expr * result) {
    ptr_vector<expr> * entry = alloc(ptr_vector<expr>);
    entry->append(num_args, const_cast<expr**>(args));
    const select_cache::key_data & kd = m_select_cache.insert_if_not_there(entry, result);
    if (kd.m_key != entry) {
        dealloc(entry);
        return;
    }
    m_manager.inc_array_ref(num_args, args);
    m_manager.inc_ref(result);
    TRACE("cache_select", tout << m_select_cache.size() << "\n";);
}



void array_simplifier_plugin::prune_select_cache() {
    if (m_select_cache.size() > m_select_cache_max_size) {
        flush_select_cache();
    }
}

void array_simplifier_plugin::prune_store_cache() {
    if (m_store_cache_size > m_store_cache_max_size) {
        flush_store_cache();
    }
}

void array_simplifier_plugin::flush_select_cache() {
    select_cache::iterator it  = m_select_cache.begin();
    select_cache::iterator end = m_select_cache.end();
    for (; it != end; ++it) {
        ptr_vector<expr> * e = (*it).m_key;
        m_manager.dec_array_ref(e->size(), e->begin());
        m_manager.dec_ref((*it).m_value);
        dealloc(e);
    }
    m_select_cache.reset();
}

void array_simplifier_plugin::flush_store_cache() {
    store_cache::iterator it = m_store_cache.begin();
    store_cache::iterator end = m_store_cache.end();
    for (; it != end; ++it) {
        m_manager.dec_ref((*it).m_key);
        const_map::iterator mit = (*it).m_value->m_map.begin();
        const_map::iterator mend = (*it).m_value->m_map.end();
        for (; mit != mend; ++mit) {
            m_manager.dec_ref((*mit).m_value);
        }
        dealloc((*it).m_value);
    }
    m_store_cache.reset();
    m_store_cache_size = 0;
}


void array_simplifier_plugin::flush_caches() {
    flush_select_cache();
    flush_store_cache();
}

void array_simplifier_plugin::mk_set_difference(unsigned num_args, expr * const * args, expr_ref & result) {
    SASSERT(num_args == 2);
    result = m_manager.mk_app(m_fid, OP_SET_DIFFERENCE, 0, 0, num_args, args);
}

void array_simplifier_plugin::mk_empty_set(sort* ty, expr_ref & result) {
    parameter param(ty);
    expr* args[1] = { m_manager.mk_false() };
    result = m_manager.mk_app(m_fid, OP_CONST_ARRAY, 1, &param, 1, args);
}

void array_simplifier_plugin::mk_full_set(sort* ty, expr_ref & result) {
    parameter param(ty);
    expr* args[1] = { m_manager.mk_true() };
    result = m_manager.mk_app(m_fid, OP_CONST_ARRAY, 1, &param, 1, args);
}


bool array_simplifier_plugin::same_args(unsigned num_args, expr * const * args1, expr * const * args2) {
    for (unsigned i = 0; i < num_args; ++i) {
        if (args1[i] != args2[i]) {
            return false;
        }
    }
    return true;
}

void array_simplifier_plugin::mk_store(func_decl* f, unsigned num_args, expr * const * args, expr_ref & result) {

    SASSERT(num_args >= 3);

    expr* arg0 = args[0];
    expr* argn = args[num_args-1];

    //
    // store(store(a,i,v),i,w) = store(a,i,w)
    // 
    if (is_store(arg0) &&
        same_args(num_args-2, args+1, to_app(arg0)->get_args()+1)) {
        expr_ref_buffer new_args(m_manager);
        new_args.push_back(to_app(arg0)->get_arg(0));
        for (unsigned i = 1; i < num_args; ++i) {
            new_args.push_back(args[i]);
        }
        reduce(f, num_args, new_args.c_ptr(), result);
        TRACE("array_simplifier", tout << mk_pp(result.get(), m_manager) << "\n";);
        return;
    }

    //
    // store(const(v),i,v) = const(v)
    //
    if (is_const_array(arg0) &&
        to_app(arg0)->get_arg(0) == args[num_args-1]) {
        result = arg0;
        TRACE("array_simplifier", tout << mk_pp(result.get(), m_manager) << "\n";);
        return;
    }

    // 
    // store(a, i, select(a, i)) = a
    //
    if (is_select(argn) && 
        (to_app(argn)->get_num_args() == num_args - 1) &&
        same_args(num_args-1, args, to_app(argn)->get_args())) {
        TRACE("dummy_store", tout << "dummy store simplified mk_store(\n";
              for (unsigned i = 0; i < num_args; i++) ast_ll_pp(tout, m_manager, args[i]);
              tout << ") =====>\n";
              ast_ll_pp(tout, m_manager, arg0););
        result = arg0;
        TRACE("array_simplifier", tout << mk_pp(result.get(), m_manager) << "\n";);
        return;
    }

    // 
    // store(store(a,i,v),j,w) -> store(store(a,j,w),i,v)
    // if i, j are values, i->get_id() < j->get_id()
    // 
    if (m_params.m_array_canonize_simplify &&
        is_store(arg0) && 
        all_values(num_args-2, args+1) &&
        all_values(num_args-2, to_app(arg0)->get_args()+1) &&
        lex_lt(num_args-2, args+1, to_app(arg0)->get_args()+1)) {
        expr* const* args2 = to_app(arg0)->get_args();
        expr_ref_buffer new_args(m_manager);
        new_args.push_back(args2[0]);
        for (unsigned i = 1; i < num_args; ++i) {
            new_args.push_back(args[i]);
        }
        reduce(f, num_args, new_args.c_ptr(), result);
        new_args.reset();
        new_args.push_back(result);
        for (unsigned i = 1; i < num_args; ++i) {
            new_args.push_back(args2[i]);
        }
        result = m_manager.mk_app(m_fid, OP_STORE, num_args, new_args.c_ptr());
        TRACE("array_simplifier", tout << mk_pp(result.get(), m_manager) << "\n";);
        return;
    }
        

    result = m_manager.mk_app(m_fid, OP_STORE, num_args, args);
    TRACE("array_simplifier", tout << "default: " << mk_pp(result.get(), m_manager) << "\n";);

}

void array_simplifier_plugin::mk_select_as_array(unsigned num_args, expr * const * args, expr_ref & result) {
    SASSERT(is_as_array(args[0]));
    func_decl * f = get_as_array_func_decl(to_app(args[0]));
    result = m_manager.mk_app(f, num_args - 1, args+1);
}

void array_simplifier_plugin::mk_select_as_array_tree(unsigned num_args, expr * const * args, expr_ref & result) {
    SASSERT(is_as_array_tree(args[0]));
    SASSERT(m_manager.is_ite(args[0]));
    ptr_buffer<app, 32> todo;
    obj_map<app, app *> cache;
    app_ref_buffer trail(m_manager);
    todo.push_back(to_app(args[0]));
    while (!todo.empty()) {
        app * curr = todo.back();
        SASSERT(m_manager.is_ite(curr));
        expr * branches[2] = {0, 0};
        bool visited = true;
        for (unsigned i = 0; i < 2; i++) {
            expr * arg = curr->get_arg(i+1);
            if (is_as_array(arg)) {
                branches[i] = m_manager.mk_app(get_as_array_func_decl(to_app(arg)), num_args - 1, args+1);
            }
            else {
                SASSERT(m_manager.is_ite(arg));
                app * new_arg = 0;
                if (!cache.find(to_app(arg), new_arg)) {
                    todo.push_back(to_app(arg));
                    visited = false;
                }
                else {
                    branches[i] = new_arg;
                }
            }
        }
        if (visited) {
            todo.pop_back();
            app * new_curr = m_manager.mk_ite(curr->get_arg(0), branches[0], branches[1]);
            trail.push_back(new_curr);
            cache.insert(curr, new_curr);
        }
    }
    SASSERT(cache.contains(to_app(args[0])));
    app * r = 0;
    cache.find(to_app(args[0]), r);
    result = r;
}

void array_simplifier_plugin::mk_select(unsigned num_args, expr * const * args, expr_ref & result) {
    expr * r = 0;
    
    if (is_as_array(args[0])) {
        mk_select_as_array(num_args, args, result);
        return;
    }

    if (is_as_array_tree(args[0])) {
        mk_select_as_array_tree(num_args, args, result);
        return;
    }

    bool is_const_select = num_args == 2 && m_manager.is_unique_value(args[1]);
    app* const_index = is_const_select?to_app(args[1]):0;
    unsigned num_const_stores = 0;
    expr_ref tmp(m_manager);
    expr* args2[2];
    if (is_const_select) {
        switch(mk_select_const(args[0], const_index, tmp)) {
        case NOT_CACHED:
            break;
        case FOUND_VALUE:
            TRACE("mk_select", tout << "found value\n"; ast_ll_pp(tout, m_manager, tmp.get()); );
            result = tmp.get();
            // value of select is stored under result.
            return;
        case FOUND_DEFAULT:
            args2[0] = tmp.get();
            args2[1] = args[1];
            args = args2;
            is_const_select = false;
            break;
        }
    }

    SASSERT(num_args > 0);
    ptr_vector<expr> & entry = m_tmp2;
    entry.reset();
    entry.append(num_args, args);
    expr * entry0 = entry[0];
    SASSERT(m_todo.empty());
    m_todo.push_back(entry0);
    while (!m_todo.empty()) {
        expr * m = m_todo.back();
        TRACE("array_simplifier", tout << mk_bounded_pp(m, m_manager) << "\n";);
        if (is_store(m)) {
            expr * nested_array = to_app(m)->get_arg(0);
            expr * else_branch  = 0;
            entry[0] = nested_array;
            if (is_const_select) {
                if (m_manager.is_unique_value(to_app(m)->get_arg(1))) {
                    app* const_index2 = to_app(to_app(m)->get_arg(1));
                    //
                    // we found the value, all other stores are different.
                    // there is no need to recurse.
                    //
                    if (const_index == const_index2) {
                        result = to_app(m)->get_arg(2);
                        cache_store(num_const_stores, args[0]);
                        m_todo.reset();
                        return;
                    }
                    ++num_const_stores;
                }
                else {
                    is_const_select = false;
                }
            }
            if (m_select_cache.find(&entry, else_branch)) {
                expr_ref_buffer eqs(m_manager);
                for (unsigned i = 1; i < num_args ; ++i) {
                    expr * a = args[i];
                    expr * b = to_app(m)->get_arg(i);
                    expr_ref eq(m_manager);
                    m_simp.mk_eq(a, b, eq);
                    eqs.push_back(eq.get());
                }
                expr_ref cond(m_manager);
                m_simp.mk_and(eqs.size(), eqs.c_ptr(), cond);
                expr * then_branch = to_app(m)->get_arg(num_args);
                if (m_manager.is_true(cond.get())) {
                    result = then_branch;
                }
                else if (m_manager.is_false(cond.get())) {
                    result = else_branch;
                }
                else {
                    m_simp.mk_ite(cond.get(), then_branch, else_branch, result);
                }
                entry[0] = m;
                cache_select(entry.size(), entry.c_ptr(), result.get());
                m_todo.pop_back();
            }
            else {
                m_todo.push_back(nested_array);
            }
        }
        else if (is_const_array(m)) {
            entry[0] = m;
            cache_select(entry.size(), entry.c_ptr(), to_app(m)->get_arg(0));
            m_todo.pop_back();
        }
        else {
            entry[0] = m;
            TRACE("array_simplifier", {
                    for (unsigned i = 0; i < entry.size(); ++i) {
                        tout << mk_bounded_pp(entry[i], m_manager) << ": " 
                             << mk_bounded_pp(m_manager.get_sort(entry[i]), m_manager) << "\n";
                    }}
                    );
            r = m_manager.mk_app(m_fid, OP_SELECT, 0, 0, entry.size(), entry.c_ptr());
            cache_select(entry.size(), entry.c_ptr(), r);
            m_todo.pop_back();
        }
    }
    cache_store(num_const_stores, args[0]);
    entry[0] = entry0;
#ifdef Z3DEBUG
    bool f =
#endif
    m_select_cache.find(&entry, r);
    SASSERT(f);
    result = r;
    prune_select_cache();
    prune_store_cache();
    TRACE("mk_select", 
          for (unsigned i = 0; i < num_args; i++) { 
              ast_ll_pp(tout, m_manager, args[i]); tout << "\n"; 
          };
          tout << "is_store: " << is_store(args[0]) << "\n";
          ast_ll_pp(tout, m_manager, r););
}


void array_simplifier_plugin::mk_map(func_decl* f, expr* a, expr* b, expr_ref& result) {
    expr* exprs[2] = { a, b };
    parameter param(f);
    result = m_manager.mk_app(m_fid, OP_ARRAY_MAP, 1, &param, 2, exprs );
}

void array_simplifier_plugin::mk_map(func_decl* f, expr* a, expr_ref& result) {
    parameter param(f);
    result = m_manager.mk_app(m_fid, OP_ARRAY_MAP, 1, &param, 1, &a );
}


