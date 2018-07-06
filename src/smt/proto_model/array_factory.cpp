/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    array_factory.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-10-28.

Revision History:

--*/

#include "ast/array_decl_plugin.h"
#include "ast/ast_pp.h"
#include "model/func_interp.h"
#include "smt/proto_model/array_factory.h"
#include "smt/proto_model/proto_model.h"

func_decl * mk_aux_decl_for_array_sort(ast_manager & m, sort * s) {
    ptr_buffer<sort> domain;
    sort * range = get_array_range(s);
    unsigned arity = get_array_arity(s);
    for (unsigned i = 0; i < arity; i++) {
        domain.push_back(get_array_domain(s, i));
    }
    return m.mk_fresh_func_decl(symbol::null, symbol::null, arity, domain.c_ptr(), range);
}

array_factory::array_factory(ast_manager & m, proto_model & md):
    struct_factory(m, m.mk_family_id("array"), md) {
}

/**
   \brieft Return as-array[f] where f is a fresh function symbol with the right domain and range for the array sort s.
   Store in fi the function interpretation for f.
*/
expr * array_factory::mk_array_interp(sort * s, func_interp * & fi) {
    func_decl * f    = mk_aux_decl_for_array_sort(m_manager, s);
    fi = alloc(func_interp, m_manager, get_array_arity(s));
    m_model.register_decl(f, fi);
    parameter p[1] = { parameter(f) };
    expr * val = m_manager.mk_app(get_family_id(), OP_AS_ARRAY, 1, p);
    register_value(val);
    return val;
}

void array_factory::get_some_args_for(sort * s, ptr_buffer<expr> & args) {
    unsigned arity = get_array_arity(s);
    for (unsigned i = 0; i < arity; i++) {
        sort * d = get_array_domain(s, i);
        expr * a = m_model.get_some_value(d);
        args.push_back(a);
    }
}

expr * array_factory::get_some_value(sort * s) {
    TRACE("array_factory", tout << mk_pp(s, m_manager) << "\n";);
    value_set * set = nullptr;
    if (m_sort2value_set.find(s, set) && !set->empty())
        return *(set->begin());
    func_interp * fi;
    expr * val = mk_array_interp(s, fi);
#if 0
    ptr_buffer<expr> args;
    get_some_args_for(s, args);
    fi->insert_entry(args.c_ptr(), m_model.get_some_value(get_array_range(s)));
#else
    fi->set_else(m_model.get_some_value(get_array_range(s)));
#endif
    return val;
}

bool array_factory::mk_two_diff_values_for(sort * s) {
    DEBUG_CODE({
        value_set * set = 0;
        SASSERT(!m_sort2value_set.find(s, set) || set->size() == 0);
    });
    expr_ref r1(m_manager);
    expr_ref r2(m_manager);
    sort * range = get_array_range(s);
    if (!m_model.get_some_values(range, r1, r2))
        return false; // failed... the range is probably unit.
    ptr_buffer<expr> args;
    get_some_args_for(s, args);
    func_interp * fi1;
    func_interp * fi2;
    mk_array_interp(s, fi1);    
    mk_array_interp(s, fi2);
    fi1->insert_entry(args.c_ptr(), r1);
    fi2->insert_entry(args.c_ptr(), r2);
    DEBUG_CODE({
        value_set * set = 0;
        SASSERT(m_sort2value_set.find(s, set) && set->size() == 2);
    });
    return true;
}

bool array_factory::get_some_values(sort * s, expr_ref & v1, expr_ref & v2) {
    value_set * set = nullptr;
    if (!m_sort2value_set.find(s, set) || set->size() == 0) {
        if (!mk_two_diff_values_for(s))
            return false;
    }
    m_sort2value_set.find(s, set);
    SASSERT(set != 0);
    SASSERT(set->size() > 0);
    
    if (set->size() == 1) {
        v1 = *(set->begin());
        v2 = get_fresh_value(s);
        return v2.get() != nullptr;
    }
    else {
        SASSERT(set->size() >= 2);
        value_set::iterator it = set->begin();
        v1 = *it;
        ++it;
        v2 = *it;
        return true;
    }
}

//
// TODO: I have to check if the following procedure is really correct.
// I'm supporting partial arrays where the "else" can be set later by the model_finder or model classes.
// Projection functions may be also used.
//
// If projections are not used, then the following code should work if the "else" of a partial array
// is set with the result of some entry.
//
expr * array_factory::get_fresh_value(sort * s) {
    value_set * set = get_value_set(s);
    if (set->empty()) {
        // easy case 
        return get_some_value(s);
    }
    sort * range    = get_array_range(s);
    expr * range_val = m_model.get_fresh_value(range);
    if (range_val != nullptr) {
        // easy case
        func_interp * fi;
        expr * val = mk_array_interp(s, fi);
#if 0
        ptr_buffer<expr> args;
        get_some_args_for(s, args);
        fi->insert_entry(args.c_ptr(), range_val);
#else
        fi->set_else(range_val);
#endif
        return val;
    }
    else {
        TRACE("array_factory_bug", tout << "array fresh value: using fresh index, range: " << mk_pp(range, m_manager) << "\n";);
        expr_ref v1(m_manager);
        expr_ref v2(m_manager);
        if (m_model.get_some_values(range, v1, v2)) {
            // Claim: A is fresh if A[i1] = v1 and A[i2] = v2 where i1 and i2 are fresh values,
            // and v1 and v2 are distinct.
            //
            // Proof: let assume there is an Array A' such that A' = A.
            // Then A[i1] == A'[i1] and A[i2] == A'[i2]. Since, i1 and i2 are fresh,
            // A' does not have an entry for i1 or i2, So A'[i1] == A'[i2] == A'.m_else.
            // Thus, A[i1] == A[i2] which is a contradiction since v1 != v2 and A[i1] = v1 and A[i2] = v2. 
            TRACE("array_factory_bug", tout << "v1: " << mk_pp(v1, m_manager) << " v2: " << mk_pp(v2, m_manager) << "\n";);
            ptr_buffer<expr> args1;
            ptr_buffer<expr> args2;
            bool found = false;
            unsigned arity = get_array_arity(s);
            for (unsigned i = 0; i < arity; i++) {
                sort * d    = get_array_domain(s, i);
                if (!found) {
                    expr * arg1 = m_model.get_fresh_value(d);
                    expr * arg2 = m_model.get_fresh_value(d);
                    if (arg1 != nullptr && arg2 != nullptr) {
                        found = true;
                        args1.push_back(arg1);
                        args2.push_back(arg2);
                        continue;
                    }
                }
                expr * arg = m_model.get_some_value(d);
                args1.push_back(arg);
                args2.push_back(arg);
            }
            if (found) {
                func_interp * fi;
                expr * val = mk_array_interp(s, fi);
                fi->insert_entry(args1.c_ptr(), v1);
                fi->insert_entry(args2.c_ptr(), v2);
                return val;
            }
        }
    }
    
    // TODO: use more expensive procedures to create a fresh array value.
    // Example: track the values used in the domain.
    
    // Remark: in the current implementation, this function
    // will never fail, since if a type is finite, then
    // type_pred will be applied and get_fresh_value will not
    // need to be used.
    
    // failed to create a fresh array value
    TRACE("array_factory_bug", tout << "failed to build fresh array value\n";);
    return nullptr;
}

