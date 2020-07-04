/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    expr_stat.h

Abstract:

    Expression statistics (symbol count, var count, depth, ...)
    
    All functions in these module assume expressions do not contain
    nested quantifiers.
    
Author:

    Leonardo de Moura (leonardo) 2008-02-05.

Revision History:

--*/
#pragma once

class expr;

struct expr_stat {
    unsigned m_sym_count; // symbol count
    unsigned m_depth;     // depth
    unsigned m_const_count; // constant count
    unsigned m_max_var_idx;  
    bool     m_ground;
    expr_stat():m_sym_count(0), m_depth(0), m_const_count(0), m_max_var_idx(0), m_ground(true) {}
};

/**
   \brief Collect statistics regarding the given expression. 

   \warning This function traverses the dag as a tree.
*/
void get_expr_stat(expr * n, expr_stat & r);

/**
   \brief Return the number of symbols in \c n.

   \warning This function traverses the dag as a tree.
*/
unsigned get_symbol_count(expr * n);

