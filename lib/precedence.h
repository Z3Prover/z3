/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    precedence.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-08.

Revision History:

--*/
#ifndef _PRECEDENCE_H_
#define _PRECEDENCE_H_

#include"ast.h"
#include"order_params.h"

/**
   \brief Abstract functor used to implement an order on function symbols.
*/
class precedence {
public:
    virtual ~precedence() {}
    virtual int compare(func_decl * f, func_decl * g) = 0;
    bool operator()(func_decl * f, func_decl * g) { return compare(f, g) < 0; }
};

/**
   \brief Compose different precedence functors using lexicographical order.
*/
class lex_precedence : public precedence {
    ptr_vector<precedence> m_precedences;
public:
    lex_precedence(unsigned n, precedence ** ps);
    virtual ~lex_precedence();
    virtual int compare(func_decl * f, func_decl * g);
};

/**
   \brief Invert functor
 */
class inv_precedence : public precedence {
    precedence * m_precedence;
public:
    inv_precedence(precedence * p);
    virtual ~inv_precedence();
    virtual int compare(func_decl * f, func_decl * g);
};

/**
   \brief An arbitrary total order based on the func_decl ids.
*/
class arbitrary_precedence : public precedence {
public:
    virtual int compare(func_decl * f, func_decl * g);
};

/**
   \brief Precedence based on the arity. 

   \remark This is not a total order, so it must be combined
   with other precedence functors (e.g., arbitrary_precedence).
*/
class arity_precedence : public precedence {
public:
    virtual int compare(func_decl * f, func_decl * g);
};

/**
   \brief Interpreted function symbols are smaller.
 */
class interpreted_precedence : public precedence {
public:
    virtual int compare(func_decl * f, func_decl * g);
};

/**
   \brief A precedence given as a sequence of func_decls.
   This functor is used to encapsulate automatically/externally generated
   precedences.
*/
class ext_precedence : public precedence {
    unsigned          m_undefined;  // position for func_decl's not specified by the user.
    int_vector        m_cached;     // mapping: decl -> int 
    decl_ref_vector   m_cached_domain;
    
    int get_func_pos(func_decl * f);
public:
    ext_precedence(ast_manager & m, unsigned num_decls, func_decl ** decls);
    virtual ~ext_precedence();
    virtual int compare(func_decl * f, func_decl * g);
};

/**
   \brief Abstract class for user precedences based on
   function or sort symbols.
*/
class abstract_user_precedence : public precedence {
protected:
    symbol_table<int> m_symbol2pos;
    unsigned          m_undefined;  // position for symbols not specified by the user.
    int_vector        m_cached;     // mapping: decl -> int 
    decl_ref_vector   m_cached_domain;

    int get_decl_pos(decl * d);
public:
    abstract_user_precedence(ast_manager & m, unsigned num_syms, symbol * syms);
    virtual ~abstract_user_precedence();
};

/**
   \brief A user defined precedence given as a sequence of symbols.

   \remark User provided precedences are usually not total.
*/
class user_precedence : public abstract_user_precedence {
public:
    user_precedence(ast_manager & m, unsigned num_syms, symbol * syms):abstract_user_precedence(m, num_syms, syms) {}
    virtual int compare(func_decl * f, func_decl * g);
};

/**
   \brief A user defined precedence given as a sequence of sort symbols.
   The functions are ordered based on their range sort.
*/
class user_sort_precedence : public abstract_user_precedence {
public:
    user_sort_precedence(ast_manager & m, unsigned num_syms, symbol * syms):abstract_user_precedence(m, num_syms, syms) {}
    virtual int compare(func_decl * f, func_decl * g);
};

precedence * mk_precedence(ast_manager & m, order_params const & params);

#endif /* _PRECEDENCE_H_ */

