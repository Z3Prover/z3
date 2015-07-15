/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    api_datatype.cpp

Abstract:
    API for datatype theory

Author:

    Leonardo de Moura (leonardo) 2012-02-29.

Revision History:

--*/
#include<iostream>
#include"z3.h"
#include"api_log_macros.h"
#include"api_context.h"
#include"api_util.h"
#include"datatype_decl_plugin.h"

extern "C" {

    Z3_sort Z3_API Z3_mk_tuple_sort(Z3_context c, 
                                    Z3_symbol name,
                                    unsigned num_fields, 
                                    Z3_symbol const field_names[],
                                    Z3_sort const field_sorts[],
                                    Z3_func_decl * mk_tuple_decl,
                                    Z3_func_decl proj_decls[]) {
        Z3_TRY;
        LOG_Z3_mk_tuple_sort(c, name, num_fields, field_names, field_sorts, mk_tuple_decl, proj_decls);
        RESET_ERROR_CODE(); 
        mk_c(c)->reset_last_result();
        ast_manager& m = mk_c(c)->m();
        datatype_util& dt_util = mk_c(c)->dtutil();

        sort_ref_vector tuples(m);
        sort* tuple;
        std::string recognizer_s("is_");
        recognizer_s += to_symbol(name).str();
        symbol recognizer(recognizer_s.c_str());
        
        ptr_vector<accessor_decl> acc;
        for (unsigned i = 0; i < num_fields; ++i) {
            acc.push_back(mk_accessor_decl(to_symbol(field_names[i]), type_ref(to_sort(field_sorts[i]))));
        }

        constructor_decl* constrs[1] = { mk_constructor_decl(to_symbol(name), recognizer, acc.size(), acc.c_ptr()) };
        
        {
            datatype_decl * dt = mk_datatype_decl(to_symbol(name), 1, constrs);
            bool is_ok = mk_c(c)->get_dt_plugin()->mk_datatypes(1, &dt, tuples);
            del_datatype_decl(dt);

            if (!is_ok) {
                SET_ERROR_CODE(Z3_INVALID_ARG);
                RETURN_Z3(0);
            }
        }

        // create tuple type
        SASSERT(tuples.size() == 1);        
        tuple = tuples[0].get();
        mk_c(c)->save_multiple_ast_trail(tuple);

        // create constructor
        SASSERT(dt_util.is_datatype(tuple));
        SASSERT(!dt_util.is_recursive(tuple));
        ptr_vector<func_decl> const * decls = dt_util.get_datatype_constructors(tuple);
        func_decl* decl = (*decls)[0];
        mk_c(c)->save_multiple_ast_trail(decl);        
        *mk_tuple_decl = of_func_decl(decl);
        
        // Create projections
        ptr_vector<func_decl> const * accs = dt_util.get_constructor_accessors(decl);
        if (!accs) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            RETURN_Z3(0);
        }
        ptr_vector<func_decl> const & _accs = *accs;
        SASSERT(_accs.size() == num_fields);
        for (unsigned i = 0; i < _accs.size(); i++) {
            mk_c(c)->save_multiple_ast_trail(_accs[i]);
            proj_decls[i] = of_func_decl(_accs[i]);
        }
        RETURN_Z3_mk_tuple_sort(of_sort(tuple));
        Z3_CATCH_RETURN(0);
    }
    
    Z3_sort Z3_API Z3_mk_enumeration_sort(Z3_context c, 
                                          Z3_symbol name,
                                          unsigned n,
                                          Z3_symbol const enum_names[],
                                          Z3_func_decl enum_consts[],
                                          Z3_func_decl enum_testers[]) {
        Z3_TRY;
        LOG_Z3_mk_enumeration_sort(c, name, n, enum_names, enum_consts, enum_testers);
        RESET_ERROR_CODE();
        mk_c(c)->reset_last_result();
        ast_manager& m = mk_c(c)->m();
        datatype_util& dt_util = mk_c(c)->dtutil();

        sort_ref_vector sorts(m);
        sort* e;
        
        ptr_vector<constructor_decl> constrs;
        for (unsigned i = 0; i < n; ++i) {
            symbol e_name(to_symbol(enum_names[i]));
            std::string recognizer_s("is_");
            recognizer_s += e_name.str();
            symbol recognizer(recognizer_s.c_str());

            constrs.push_back(mk_constructor_decl(e_name, recognizer, 0, 0));
        }


        {
            datatype_decl * dt = mk_datatype_decl(to_symbol(name), n, constrs.c_ptr());
            bool is_ok = mk_c(c)->get_dt_plugin()->mk_datatypes(1, &dt, sorts);
            del_datatype_decl(dt);

            if (!is_ok) {
                SET_ERROR_CODE(Z3_INVALID_ARG);
                RETURN_Z3(0);
            }
        }
            
        // create enum type.
        SASSERT(sorts.size() == 1);        
        e = sorts[0].get();
        mk_c(c)->save_multiple_ast_trail(e);

        // create constructor
        SASSERT(dt_util.is_datatype(e));
        SASSERT(!dt_util.is_recursive(e));
        ptr_vector<func_decl> const * decls = dt_util.get_datatype_constructors(e);
        SASSERT(decls && decls->size() == n);
        for (unsigned i = 0; i < n; ++i) {
            func_decl* decl = (*decls)[i];
            mk_c(c)->save_multiple_ast_trail(decl);    
            enum_consts[i] = of_func_decl(decl);
            decl = dt_util.get_constructor_recognizer(decl);
            mk_c(c)->save_multiple_ast_trail(decl);    
            enum_testers[i] = of_func_decl(decl);
        }

        RETURN_Z3_mk_enumeration_sort(of_sort(e));
        Z3_CATCH_RETURN(0);
    }

    Z3_sort Z3_API Z3_mk_list_sort(Z3_context c,
                                   Z3_symbol name,
                                   Z3_sort   elem_sort,
                                   Z3_func_decl* nil_decl,
                                   Z3_func_decl* is_nil_decl,
                                   Z3_func_decl* cons_decl,
                                   Z3_func_decl* is_cons_decl,
                                   Z3_func_decl* head_decl,
                                   Z3_func_decl* tail_decl
                                   ) {
        Z3_TRY;
        LOG_Z3_mk_list_sort(c, name, elem_sort, nil_decl, is_nil_decl, cons_decl, is_cons_decl, head_decl, tail_decl);
        RESET_ERROR_CODE();
        ast_manager& m = mk_c(c)->m();
        mk_c(c)->reset_last_result();
        datatype_util data_util(m);
        accessor_decl* head_tail[2] = { 
            mk_accessor_decl(symbol("head"), type_ref(to_sort(elem_sort))),
            mk_accessor_decl(symbol("tail"), type_ref(0))
        };
        constructor_decl* constrs[2] = { 
            mk_constructor_decl(symbol("nil"), symbol("is_nil"), 0, 0),
            // Leo: SMT 2.0 document uses 'insert' instead of cons
            mk_constructor_decl(symbol("cons"), symbol("is_cons"), 2, head_tail)
        };

        sort_ref_vector sorts(m);
        {
            datatype_decl * decl = mk_datatype_decl(to_symbol(name), 2, constrs);
            bool is_ok = mk_c(c)->get_dt_plugin()->mk_datatypes(1, &decl, sorts);
            del_datatype_decl(decl);

            if (!is_ok) {
                SET_ERROR_CODE(Z3_INVALID_ARG);
                RETURN_Z3(0);
            }
        }
        sort * s = sorts.get(0);

        mk_c(c)->save_multiple_ast_trail(s);
        ptr_vector<func_decl> const& cnstrs = *data_util.get_datatype_constructors(s);
        SASSERT(cnstrs.size() == 2);
        func_decl* f;
        if (nil_decl) {
            f = cnstrs[0];
            mk_c(c)->save_multiple_ast_trail(f);            
            *nil_decl = of_func_decl(f);
        }
        if (is_nil_decl) {
            f = data_util.get_constructor_recognizer(cnstrs[0]);
            mk_c(c)->save_multiple_ast_trail(f);            
            *is_nil_decl = of_func_decl(f);
        }
        if (cons_decl) {
            f = cnstrs[1];
            mk_c(c)->save_multiple_ast_trail(f);                        
            *cons_decl = of_func_decl(f);
        }
        if (is_cons_decl) {
            f = data_util.get_constructor_recognizer(cnstrs[1]);
            mk_c(c)->save_multiple_ast_trail(f);                        
            *is_cons_decl = of_func_decl(f);
        }
        if (head_decl) {
            ptr_vector<func_decl> const* acc = data_util.get_constructor_accessors(cnstrs[1]);
            SASSERT(acc);
            SASSERT(acc->size() == 2);
            f = (*acc)[0];
            mk_c(c)->save_multiple_ast_trail(f);                        
            *head_decl = of_func_decl(f);
        }
        if (tail_decl) {
            ptr_vector<func_decl> const* acc = data_util.get_constructor_accessors(cnstrs[1]);
            SASSERT(acc);
            SASSERT(acc->size() == 2);
            f = (*acc)[1];
            mk_c(c)->save_multiple_ast_trail(f);                        
            *tail_decl = of_func_decl(f);
        }
        RETURN_Z3_mk_list_sort(of_sort(s));
        Z3_CATCH_RETURN(0);
    }

    struct constructor {
        symbol           m_name;
        symbol           m_tester;
        svector<symbol>  m_field_names;
        sort_ref_vector  m_sorts;
        unsigned_vector  m_sort_refs;
        func_decl_ref    m_constructor;
        constructor(ast_manager& m) : m_sorts(m), m_constructor(m) {}
    };

    Z3_constructor Z3_API Z3_mk_constructor(Z3_context c,
                                            Z3_symbol name,
                                            Z3_symbol tester,
                                            unsigned num_fields,
                                            Z3_symbol const field_names[],
                                            Z3_sort const sorts[],
                                            unsigned sort_refs[]
                                            ) {
        Z3_TRY;
        LOG_Z3_mk_constructor(c, name, tester, num_fields, field_names, sorts, sort_refs);
        RESET_ERROR_CODE();  
        ast_manager& m = mk_c(c)->m();
        constructor* cnstr = alloc(constructor, m);
        cnstr->m_name = to_symbol(name);
        cnstr->m_tester = to_symbol(tester);
        for (unsigned i = 0; i < num_fields; ++i) {
            cnstr->m_field_names.push_back(to_symbol(field_names[i]));
            cnstr->m_sorts.push_back(to_sort(sorts[i]));
            cnstr->m_sort_refs.push_back(sort_refs[i]);
        }
        RETURN_Z3(reinterpret_cast<Z3_constructor>(cnstr));
        Z3_CATCH_RETURN(0);
    }


    void Z3_API Z3_query_constructor(Z3_context c,
                                     Z3_constructor constr,
                                     unsigned num_fields,
                                     Z3_func_decl* constructor_decl,
                                     Z3_func_decl* tester,
                                     Z3_func_decl accessors[]) {
        Z3_TRY;
        LOG_Z3_query_constructor(c, constr, num_fields, constructor_decl, tester, accessors);
        RESET_ERROR_CODE();
        mk_c(c)->reset_last_result();
        if (!constr) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            return;
        }
        ast_manager& m = mk_c(c)->m();
        datatype_util data_util(m);
        func_decl* f = reinterpret_cast<constructor*>(constr)->m_constructor.get();

        if (!f) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            return;
        }    
        if (constructor_decl) {
            mk_c(c)->save_multiple_ast_trail(f);
            *constructor_decl = of_func_decl(f);
        }
        if (tester) {
            func_decl* f2 = data_util.get_constructor_recognizer(f);
            mk_c(c)->save_multiple_ast_trail(f2);
            *tester = of_func_decl(f2);
        }
        
        ptr_vector<func_decl> const* accs = data_util.get_constructor_accessors(f);
        if (!accs && num_fields > 0) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            return;            
        }
        for (unsigned i = 0; i < num_fields; ++i) {
            func_decl* f2 = (*accs)[i];
            mk_c(c)->save_multiple_ast_trail(f2);            
            accessors[i] = of_func_decl(f2);
        }
        RETURN_Z3_query_constructor;
        Z3_CATCH;
    }

    void Z3_API Z3_del_constructor(Z3_context c, Z3_constructor constr) {
        Z3_TRY;
        LOG_Z3_del_constructor(c, constr);
        RESET_ERROR_CODE();
        dealloc(reinterpret_cast<constructor*>(constr));
        Z3_CATCH;
    }

    static datatype_decl* mk_datatype_decl(Z3_context c, 
                                           Z3_symbol name,
                                           unsigned num_constructors,
                                           Z3_constructor constructors[]) {
        ptr_vector<constructor_decl> constrs;
        for (unsigned i = 0; i < num_constructors; ++i) {
            constructor* cn = reinterpret_cast<constructor*>(constructors[i]);
            ptr_vector<accessor_decl> acc;
            for (unsigned j = 0; j < cn->m_sorts.size(); ++j) {
                if (cn->m_sorts[j].get()) {
                    acc.push_back(mk_accessor_decl(cn->m_field_names[j], type_ref(cn->m_sorts[j].get())));
                }
                else {
                    acc.push_back(mk_accessor_decl(cn->m_field_names[j], type_ref(cn->m_sort_refs[j])));
                }
            }
            constrs.push_back(mk_constructor_decl(cn->m_name, cn->m_tester, acc.size(), acc.c_ptr()));
        }
        return mk_datatype_decl(to_symbol(name), num_constructors, constrs.c_ptr());        
    }

    Z3_sort Z3_API Z3_mk_datatype(Z3_context c,
                                  Z3_symbol name,
                                  unsigned num_constructors,
                                  Z3_constructor constructors[]) {
        Z3_TRY;
        LOG_Z3_mk_datatype(c, name, num_constructors, constructors);
        RESET_ERROR_CODE();
        ast_manager& m = mk_c(c)->m();        
        datatype_util data_util(m);
        
        sort_ref_vector sorts(m);
        {
            datatype_decl * data = mk_datatype_decl(c, name, num_constructors, constructors);
            bool is_ok = mk_c(c)->get_dt_plugin()->mk_datatypes(1, &data, sorts);
            del_datatype_decl(data);

            if (!is_ok) {
                SET_ERROR_CODE(Z3_INVALID_ARG);
                RETURN_Z3(0);
            }
        }
        sort * s = sorts.get(0);

        mk_c(c)->save_ast_trail(s);
        ptr_vector<func_decl> const* cnstrs = data_util.get_datatype_constructors(s);
        
        for (unsigned i = 0; i < num_constructors; ++i) {
            constructor* cn = reinterpret_cast<constructor*>(constructors[i]);
            cn->m_constructor = (*cnstrs)[i];
        }
        RETURN_Z3_mk_datatype(of_sort(s));
        Z3_CATCH_RETURN(0);
    }

    typedef ptr_vector<constructor> constructor_list;

    Z3_constructor_list Z3_API Z3_mk_constructor_list(Z3_context c,
                                                      unsigned num_constructors,
                                                      Z3_constructor const constructors[]) {
        Z3_TRY;
        LOG_Z3_mk_constructor_list(c, num_constructors, constructors);
        RESET_ERROR_CODE();
        constructor_list* result = alloc(ptr_vector<constructor>);
        for (unsigned i = 0; i < num_constructors; ++i) {
            result->push_back(reinterpret_cast<constructor*>(constructors[i]));
        }
        RETURN_Z3(reinterpret_cast<Z3_constructor_list>(result));
        Z3_CATCH_RETURN(0);
    }

    void Z3_API Z3_del_constructor_list(Z3_context c, Z3_constructor_list clist) {
        Z3_TRY;
        LOG_Z3_del_constructor_list(c, clist);
        RESET_ERROR_CODE();
        dealloc(reinterpret_cast<constructor_list*>(clist));
        Z3_CATCH;
    }

    void Z3_API Z3_mk_datatypes(Z3_context c,
                                unsigned num_sorts,
                                Z3_symbol const sort_names[],
                                Z3_sort sorts[],
                                Z3_constructor_list constructor_lists[]) {
        Z3_TRY;
        LOG_Z3_mk_datatypes(c, num_sorts, sort_names, sorts, constructor_lists);
        RESET_ERROR_CODE();
        ast_manager& m = mk_c(c)->m();        
        mk_c(c)->reset_last_result();
        datatype_util data_util(m);

        ptr_vector<datatype_decl> datas;
        for (unsigned i = 0; i < num_sorts; ++i) {
            constructor_list* cl = reinterpret_cast<constructor_list*>(constructor_lists[i]);
            datas.push_back(mk_datatype_decl(c,sort_names[i], cl->size(), reinterpret_cast<Z3_constructor*>(cl->c_ptr())));
        }
        sort_ref_vector _sorts(m);
        bool ok = mk_c(c)->get_dt_plugin()->mk_datatypes(datas.size(), datas.c_ptr(), _sorts);
        del_datatype_decls(datas.size(), datas.c_ptr());
        
        if (!ok) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            return;
        }

        SASSERT(_sorts.size() == num_sorts);
        for (unsigned i = 0; i < _sorts.size(); ++i) {
            sort* s = _sorts[i].get();
            mk_c(c)->save_multiple_ast_trail(s);
            sorts[i] = of_sort(s);
            constructor_list* cl = reinterpret_cast<constructor_list*>(constructor_lists[i]);
            ptr_vector<func_decl> const* cnstrs = data_util.get_datatype_constructors(s);
            for (unsigned j = 0; j < cl->size(); ++j) {
                constructor* cn = (*cl)[j];                
                cn->m_constructor = (*cnstrs)[j];                
            }
        }
        RETURN_Z3_mk_datatypes;
        Z3_CATCH;
    }

    unsigned Z3_API Z3_get_datatype_sort_num_constructors(Z3_context c, Z3_sort t) {
        Z3_TRY;
        LOG_Z3_get_datatype_sort_num_constructors(c, t);
        RESET_ERROR_CODE();
        CHECK_VALID_AST(t, 0);
        sort * _t = to_sort(t);
        datatype_util& dt_util = mk_c(c)->dtutil();
        
        if (!dt_util.is_datatype(_t)) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            return 0;            
        }
        ptr_vector<func_decl> const * decls = dt_util.get_datatype_constructors(_t);
        if (!decls) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            return 0;                        
        }
        return decls->size();
        Z3_CATCH_RETURN(0);
    }

    Z3_func_decl get_datatype_sort_constructor_core(Z3_context c, Z3_sort t, unsigned idx) {
        RESET_ERROR_CODE();
        CHECK_VALID_AST(t, 0);   
        sort * _t = to_sort(t);
        datatype_util& dt_util = mk_c(c)->dtutil();
        if (!dt_util.is_datatype(_t)) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            return 0;
        }
        ptr_vector<func_decl> const * decls = dt_util.get_datatype_constructors(_t);
        if (!decls || idx >= decls->size()) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            return 0;
        }
        func_decl* decl = (*decls)[idx];
        mk_c(c)->save_ast_trail(decl);
        return of_func_decl(decl);
    }

    Z3_func_decl Z3_API Z3_get_datatype_sort_constructor(Z3_context c, Z3_sort t, unsigned idx) {
        Z3_TRY;
        LOG_Z3_get_datatype_sort_constructor(c, t, idx);
        RESET_ERROR_CODE();
        Z3_func_decl r = get_datatype_sort_constructor_core(c, t, idx);
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }

    Z3_func_decl Z3_API Z3_get_datatype_sort_recognizer(Z3_context c, Z3_sort t, unsigned idx) {
        Z3_TRY;
        LOG_Z3_get_datatype_sort_recognizer(c, t, idx);
        RESET_ERROR_CODE();   
        sort * _t = to_sort(t);
        datatype_util& dt_util = mk_c(c)->dtutil();
        
        if (!dt_util.is_datatype(_t)) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            RETURN_Z3(0);
        }
        ptr_vector<func_decl> const * decls = dt_util.get_datatype_constructors(_t);
        if (!decls || idx >= decls->size()) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            RETURN_Z3(0);
        }
        func_decl* decl = (*decls)[idx];
        decl = dt_util.get_constructor_recognizer(decl);
        mk_c(c)->save_ast_trail(decl);
        RETURN_Z3(of_func_decl(decl));
        Z3_CATCH_RETURN(0);
    }

    Z3_func_decl Z3_API Z3_get_datatype_sort_constructor_accessor(Z3_context c, Z3_sort t, unsigned idx_c, unsigned idx_a) {
        Z3_TRY;
        LOG_Z3_get_datatype_sort_constructor_accessor(c, t, idx_c, idx_a);
        RESET_ERROR_CODE();  
        sort * _t = to_sort(t);
        datatype_util& dt_util = mk_c(c)->dtutil();
        
        if (!dt_util.is_datatype(_t)) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            RETURN_Z3(0);            
        }
        ptr_vector<func_decl> const * decls = dt_util.get_datatype_constructors(_t);
        if (!decls || idx_c >= decls->size()) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            return 0;
        }
        func_decl* decl = (*decls)[idx_c];
        if (decl->get_arity() <= idx_a) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            RETURN_Z3(0);                        
        }
        ptr_vector<func_decl> const * accs = dt_util.get_constructor_accessors(decl);
        SASSERT(accs && accs->size() == decl->get_arity());
        if (!accs || accs->size() <= idx_a) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            RETURN_Z3(0);                        
        }
        decl = (*accs)[idx_a];
        mk_c(c)->save_ast_trail(decl);
        RETURN_Z3(of_func_decl(decl)); 
        Z3_CATCH_RETURN(0);
    }

    Z3_func_decl Z3_API Z3_get_tuple_sort_mk_decl(Z3_context c, Z3_sort t) {
        Z3_TRY;
        LOG_Z3_get_tuple_sort_mk_decl(c, t);
        RESET_ERROR_CODE();  
        sort * tuple = to_sort(t);
        datatype_util& dt_util = mk_c(c)->dtutil();
        if (!dt_util.is_datatype(tuple) || dt_util.is_recursive(tuple) || dt_util.get_datatype_num_constructors(tuple) != 1) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            RETURN_Z3(0);
        }
        Z3_func_decl r = get_datatype_sort_constructor_core(c, t, 0);
        RETURN_Z3(r);
        Z3_CATCH_RETURN(0);
    }
    
    unsigned Z3_API Z3_get_tuple_sort_num_fields(Z3_context c, Z3_sort t) {
        Z3_TRY;
        LOG_Z3_get_tuple_sort_num_fields(c, t);
        RESET_ERROR_CODE();   
        sort * tuple = to_sort(t);
        datatype_util& dt_util = mk_c(c)->dtutil();
        if (!dt_util.is_datatype(tuple) || dt_util.is_recursive(tuple) || dt_util.get_datatype_num_constructors(tuple) != 1) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            return 0;            
        }
        ptr_vector<func_decl> const * decls = dt_util.get_datatype_constructors(tuple);
        if (!decls || decls->size() != 1) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            return 0;                        
        }
        ptr_vector<func_decl> const * accs = dt_util.get_constructor_accessors((*decls)[0]);
        if (!accs) {
            return 0;                        
        }
        return accs->size();
        Z3_CATCH_RETURN(0);
    }
    
    Z3_func_decl Z3_API Z3_get_tuple_sort_field_decl(Z3_context c, Z3_sort t, unsigned i) {
        Z3_TRY;
        LOG_Z3_get_tuple_sort_field_decl(c, t, i);
        RESET_ERROR_CODE();  
        sort * tuple = to_sort(t);
        datatype_util& dt_util = mk_c(c)->dtutil();
        if (!dt_util.is_datatype(tuple) || dt_util.is_recursive(tuple) || dt_util.get_datatype_num_constructors(tuple) != 1) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            RETURN_Z3(0);
        }
        ptr_vector<func_decl> const * decls = dt_util.get_datatype_constructors(tuple);
        if (!decls || decls->size() != 1) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            RETURN_Z3(0);
        }
        ptr_vector<func_decl> const * accs = dt_util.get_constructor_accessors((*decls)[0]);
        if (!accs) {
            SET_ERROR_CODE(Z3_INVALID_ARG);
            RETURN_Z3(0);
        }
        if (accs->size() <= i) {
            SET_ERROR_CODE(Z3_IOB);
            RETURN_Z3(0);
        }
        func_decl* acc = (*accs)[i];
        mk_c(c)->save_ast_trail(acc);
        RETURN_Z3(of_func_decl(acc));
        Z3_CATCH_RETURN(0);
    }

    Z3_ast Z3_datatype_update_field(
        Z3_context c,  Z3_func_decl f, Z3_ast t, Z3_ast v) {        
        Z3_TRY;
        LOG_Z3_datatype_update_field(c, f, t, v);
        RESET_ERROR_CODE();
        ast_manager & m = mk_c(c)->m();
        func_decl* _f      = to_func_decl(f);
        expr* _t = to_expr(t);
        expr* _v = to_expr(v);  
        expr* args[2] = { _t, _v };
        sort* domain[2] = { m.get_sort(_t), m.get_sort(_v) };
        parameter param(_f);
        func_decl * d = m.mk_func_decl(mk_c(c)->get_array_fid(), OP_DT_UPDATE_FIELD, 1, &param, 2, domain);
        app* r = m.mk_app(d, 2, args);
        mk_c(c)->save_ast_trail(r);
        check_sorts(c, r);
        RETURN_Z3(of_ast(r));
        Z3_CATCH_RETURN(0);
    }


};
