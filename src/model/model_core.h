/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    model_core.h

Abstract:

    Base class for models.

Author:

    Leonardo de Moura (leonardo) 2011-04-30.

Revision History:

--*/
#ifndef MODEL_CORE_H_
#define MODEL_CORE_H_

#include "ast/ast.h"
#include "util/obj_hashtable.h"
#include "model/func_interp.h"

class model_core {
protected:
    typedef obj_map<func_decl, expr *>       decl2expr;
    typedef obj_map<func_decl, func_interp*> decl2finterp;
    ast_manager &                 m_manager;
    unsigned                      m_ref_count;
    decl2expr                     m_interp;      //!< interpretation for uninterpreted constants
    decl2finterp                  m_finterp;     //!< interpretation for uninterpreted functions
    ptr_vector<func_decl>         m_decls;       //!< domain of m_interp
    ptr_vector<func_decl>         m_const_decls; 
    ptr_vector<func_decl>         m_func_decls;  
    
public:
    model_core(ast_manager & m):m_manager(m), m_ref_count(0) { }
    virtual ~model_core();

    ast_manager & get_manager() const { return m_manager; }

    unsigned get_num_decls() const { return m_decls.size(); }
    func_decl * get_decl(unsigned i) const { return m_decls[i]; }
    bool has_interpretation(func_decl * d) const { return m_interp.contains(d) || m_finterp.contains(d); }
    expr * get_const_interp(func_decl * d) const { expr * v; return m_interp.find(d, v) ? v : nullptr; }
    func_interp * get_func_interp(func_decl * d) const { func_interp * fi; return m_finterp.find(d, fi) ? fi : nullptr; }

    bool eval(func_decl * f, expr_ref & r) const;

    unsigned get_num_constants() const { return m_const_decls.size(); }
    unsigned get_num_functions() const { return m_func_decls.size(); }
    func_decl * get_constant(unsigned i) const { return m_const_decls[i]; }
    func_decl * get_function(unsigned i) const { return m_func_decls[i]; }

    virtual ptr_vector<expr> const & get_universe(sort * s) const = 0;
    virtual unsigned get_num_uninterpreted_sorts() const = 0;
    virtual sort * get_uninterpreted_sort(unsigned idx) const = 0;

    void register_decl(func_decl * d, expr * v);
    void register_decl(func_decl * f, func_interp * fi);
    void unregister_decl(func_decl * d);

    virtual expr * get_some_value(sort * s) = 0;

    //
    // Reference counting
    //
    void inc_ref() { ++m_ref_count; }
    void dec_ref() { 
        --m_ref_count;
        if (m_ref_count == 0) {
            dealloc(this);
        }
    }

};

#endif
