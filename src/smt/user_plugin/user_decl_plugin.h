/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    user_decl_plugin.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-05-22.

Revision History:

--*/
#ifndef USER_DECL_PLUGIN_H_
#define USER_DECL_PLUGIN_H_

#include"ast.h"
#include"obj_hashtable.h"

class user_decl_plugin : public decl_plugin {
    ptr_vector<sort>         m_kind2sort;
    ptr_vector<func_decl>    m_kind2func;
    obj_hashtable<func_decl> m_values;
    svector<builtin_name>    m_op_names;
    svector<builtin_name>    m_sort_names;
public:
    user_decl_plugin();
    
    virtual ~user_decl_plugin() {}
    virtual void finalize();

    virtual decl_plugin * mk_fresh();

    sort * mk_sort(symbol const & name);
    
    func_decl * mk_func_decl(symbol const & name, unsigned arity, sort * const * domain, sort * range);
    
    func_decl * mk_value_decl(symbol const & name, sort * s);
    
    virtual sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters);
    
    virtual func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters, 
                                     unsigned arity, sort * const * domain, sort * range);
    
    virtual bool is_value(app*) const;

    virtual bool is_unique_value(app * a) const { return is_value(a); }

    bool is_value(func_decl *) const;
    
    virtual void get_op_names(svector<builtin_name> & op_names, symbol const & logic);
    
    virtual void get_sort_names(svector<builtin_name> & sort_names, symbol const & logic);
};

#endif /* USER_DECL_PLUGIN_H_ */

