/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    datatype_decl_plugin.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-01-09.

Revision History:

--*/
#ifndef DATATYPE_DECL_PLUGIN_H_
#define DATATYPE_DECL_PLUGIN_H_

#include"ast.h"
#include"tptr.h"
#include"buffer.h"
#include"obj_hashtable.h"

enum datatype_sort_kind {
    DATATYPE_SORT
};

enum datatype_op_kind {
    OP_DT_CONSTRUCTOR,
    OP_DT_RECOGNISER,
    OP_DT_ACCESSOR,
    OP_DT_UPDATE_FIELD,
    LAST_DT_OP
};

/**
   \brief Auxiliary class used to declare inductive datatypes.
   It may be a sort or an integer. If it is an integer,
   then it represents a reference to a recursive type.

   For example, consider the datatypes
   Datatype
     Tree     = tree(value:Real, children:TreeList)
     TreeList = cons_t(first_t:Tree, rest_t:Tree)
              | nil_t
   End
  
   The recursive occurrences of Tree and TreeList will have idx 0 and
   1 respectively.

   This is a transient value, it is only used to declare a set of
   recursive datatypes.
*/
class type_ref {
    void * m_data;
public:
    type_ref():m_data(TAG(void *, static_cast<void*>(0), 1)) {}
    type_ref(int idx):m_data(BOXINT(void *, idx)) {}
    type_ref(sort * s):m_data(TAG(void *, s, 1)) {}
    
    bool is_idx() const { return GET_TAG(m_data) == 0; }
    bool is_sort() const { return GET_TAG(m_data) == 1; }
    sort * get_sort() const { return UNTAG(sort *, m_data); }
    int get_idx() const { return UNBOXINT(m_data); }
};

class accessor_decl;
class constructor_decl;
class datatype_decl;
class datatype_util;

accessor_decl * mk_accessor_decl(symbol const & n, type_ref const & t);
void del_accessor_decl(accessor_decl * d);
void del_accessor_decls(unsigned num, accessor_decl * const * as);
// Remark: the constructor becomes the owner of the accessor_decls
constructor_decl * mk_constructor_decl(symbol const & n, symbol const & r, unsigned num_accessors, accessor_decl * const * acs);
void del_constructor_decl(constructor_decl * d);
void del_constructor_decls(unsigned num, constructor_decl * const * cs);
// Remark: the datatype becomes the owner of the constructor_decls
datatype_decl * mk_datatype_decl(symbol const & n, unsigned num_constructors, constructor_decl * const * cs);
void del_datatype_decl(datatype_decl * d);
void del_datatype_decls(unsigned num, datatype_decl * const * ds);

class datatype_decl_plugin : public decl_plugin {
    mutable scoped_ptr<datatype_util> m_util;
    datatype_util & get_util() const;
public:
    datatype_decl_plugin() {}

    virtual ~datatype_decl_plugin();
    virtual void finalize();

    virtual decl_plugin * mk_fresh() { return alloc(datatype_decl_plugin); }

    
    /**
       Contract for sort: 
         parameters[0]            - (int) n - number of recursive types.
         parameters[1]            - (int) i - index 0..n-1 of which type is defined.
      
         for j in 0..n-1
         parameters[2 + 2*j]      - (symbol) name of the type
         parameters[2 + 2*j + 1]  - (int) o - offset where the constructors are defined.
      
         for each offset o at parameters[2 + 2*j + 1] for some j in 0..n-1
         parameters[o]            - (int) m - number of constructors
         parameters[o+1]          - (int) k_1 - offset for constructor definition
         ...
         parameters[o+m]          - (int) k_m - offset ofr constructor definition
      
         for each offset k_i at parameters[o+s] for some s in 0..m-1
         parameters[k_i]          - (symbol) name of the constructor
         parameters[k_i+1]        - (symbol) name of the recognizer
         parameters[k_i+2]        - (int) m' - number of accessors
         parameters[k_i+3+2*r]    - (symbol) name of the r accessor
         parameters[k_i+3+2*r+1]  - (int or type_ast) type of the accessor. If integer, then the value must be in [0..n-1], and it 
                                    represents an reference to the recursive type.
       
       The idea with the additional offsets is that
       access to relevant constructors and types can be performed using
       a few address calculations.
    */
    virtual sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters);
    
    /**
       Contract for constructors
         parameters[0] - (ast) datatype ast.
         parmaeters[1] - (int) constructor idx.
       Contract for accessors
         parameters[0] - (ast) datatype ast.
         parameters[1] - (int) constructor idx.
         parameters[2] - (int) accessor idx.
       Contract for tester
         parameters[0] - (ast) datatype ast.
         parameters[1] - (int) constructor idx.
    */
    virtual func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters, 
                                     unsigned arity, sort * const * domain, sort * range);
    
    bool mk_datatypes(unsigned num_datatypes, datatype_decl * const * datatypes, sort_ref_vector & new_sorts);

    virtual expr * get_some_value(sort * s);

    virtual bool is_fully_interp(sort const * s) const;

    virtual bool is_value(app* e) const;

    virtual bool is_unique_value(app * e) const { return is_value(e); }

    virtual void get_op_names(svector<builtin_name> & op_names, symbol const & logic);

private:
    bool is_value_visit(expr * arg, ptr_buffer<app> & todo) const;

    func_decl * mk_update_field(
        unsigned num_parameters, parameter const * parameters, 
        unsigned arity, sort * const * domain, sort * range);
};

class datatype_util {
    ast_manager & m_manager;
    family_id     m_family_id;

    func_decl * get_constructor(sort * ty, unsigned c_id) const;

    obj_map<sort, ptr_vector<func_decl> *>      m_datatype2constructors;
    obj_map<sort, func_decl *>                  m_datatype2nonrec_constructor;
    obj_map<func_decl, ptr_vector<func_decl> *> m_constructor2accessors;
    obj_map<func_decl, func_decl *>             m_constructor2recognizer;
    obj_map<func_decl, func_decl *>             m_recognizer2constructor;
    obj_map<func_decl, func_decl *>             m_accessor2constructor;
    obj_map<sort, bool>                         m_is_recursive;
    ast_ref_vector                              m_asts;
    ptr_vector<ptr_vector<func_decl> >          m_vectors;
    
    func_decl * get_non_rec_constructor_core(sort * ty, ptr_vector<sort> & forbidden_set);
    func_decl * get_constructor(sort * ty, unsigned c_id);

public:
    datatype_util(ast_manager & m);
    ~datatype_util();
    ast_manager & get_manager() const { return m_manager; }
    bool is_datatype(sort * s) const { return is_sort_of(s, m_family_id, DATATYPE_SORT); }
    bool is_recursive(sort * ty);
    bool is_constructor(func_decl * f) const { return is_decl_of(f, m_family_id, OP_DT_CONSTRUCTOR); }
    bool is_recognizer(func_decl * f) const { return is_decl_of(f, m_family_id, OP_DT_RECOGNISER); }
    bool is_accessor(func_decl * f) const { return is_decl_of(f, m_family_id, OP_DT_ACCESSOR); }
    bool is_update_field(func_decl * f) const { return is_decl_of(f, m_family_id, OP_DT_UPDATE_FIELD); }
    bool is_constructor(app * f) const { return is_app_of(f, m_family_id, OP_DT_CONSTRUCTOR); }
    bool is_recognizer(app * f) const { return is_app_of(f, m_family_id, OP_DT_RECOGNISER); }
    bool is_accessor(app * f) const { return is_app_of(f, m_family_id, OP_DT_ACCESSOR); }
    bool is_update_field(app * f) const { return is_app_of(f, m_family_id, OP_DT_UPDATE_FIELD); }
    ptr_vector<func_decl> const * get_datatype_constructors(sort * ty);
    unsigned get_datatype_num_constructors(sort * ty) { 
        SASSERT(is_datatype(ty));
        unsigned tid = ty->get_parameter(1).get_int();
        unsigned o = ty->get_parameter(3 + 2 * tid).get_int();
        return ty->get_parameter(o).get_int(); 
    }
    unsigned get_constructor_idx(func_decl * f) const { SASSERT(is_constructor(f)); return f->get_parameter(1).get_int(); }
    unsigned get_recognizer_constructor_idx(func_decl * f) const { SASSERT(is_recognizer(f)); return f->get_parameter(1).get_int(); }
    func_decl * get_non_rec_constructor(sort * ty);
    func_decl * get_constructor_recognizer(func_decl * constructor);
    ptr_vector<func_decl> const * get_constructor_accessors(func_decl * constructor);
    func_decl * get_accessor_constructor(func_decl * accessor);
    func_decl * get_recognizer_constructor(func_decl * recognizer);
    family_id get_family_id() const { return m_family_id; }
    bool are_siblings(sort * s1, sort * s2);
    bool is_func_decl(datatype_op_kind k, unsigned num_params, parameter const* params, func_decl* f);
    bool is_constructor_of(unsigned num_params, parameter const* params, func_decl* f);
    void reset();
    void display_datatype(sort *s, std::ostream& strm);

};

#endif /* DATATYPE_DECL_PLUGIN_H_ */

