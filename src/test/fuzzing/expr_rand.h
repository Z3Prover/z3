/*++
Copyright (c) 2008 Microsoft Corporation

Module Name:

    expr_rand.h

Abstract:

    Generator of random ASTs.

Author:

    Nikolaj Bjorner 2008-04-10.

Revision History:

--*/
#ifndef _EXPR_RAND_H_
#define _EXPR_RAND_H_

#include"ast.h"
#include"obj_hashtable.h"

class expr_rand {
    ast_manager& m_manager;
    unsigned     m_num_vars;
    unsigned     m_num_apps;
    unsigned     m_num_nodes;
    unsigned     m_max_steps;
    random_gen   m_random;

    typedef obj_map<sort, expr_ref_vector*> map_t;

    func_decl_ref_vector m_funcs;
    map_t                m_nodes;
    
public:
    expr_rand(ast_manager& m);
    ~expr_rand();
    void add_var(sort*);
    void add_func_decl(func_decl*);
    void add_expr(expr* t);
    void get_next(sort* s, expr_ref& e);
    void initialize_bv(unsigned num_vars);
    void initialize_arith(unsigned num_vars);
    void initialize_array(unsigned num_vars, sort* dom, sort* rng);
    void initialize_basic(unsigned amplification);
    void seed(unsigned n) { m_random = random_gen(n); }
                       
private:
    void walk();
    void walk(unsigned n);
    
    func_decl* choose_func_decl();
    expr*      choose_expr(sort*);

};


#endif
