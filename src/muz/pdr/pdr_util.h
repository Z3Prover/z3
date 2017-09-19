/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    pdr_util.h

Abstract:

    Utility functions for PDR.

Author:

    Krystof Hoder (t-khoder) 2011-8-19.

Revision History:

--*/

#ifndef PDR_UTIL_H_
#define PDR_UTIL_H_

#include "ast/ast.h"
#include "ast/ast_pp.h"
#include "ast/ast_util.h"
#include "util/obj_hashtable.h"
#include "util/ref_vector.h"
#include "util/trace.h"
#include "util/vector.h"
#include "ast/arith_decl_plugin.h"
#include "ast/array_decl_plugin.h"
#include "ast/bv_decl_plugin.h"


class model;
class model_core;

namespace pdr {

    /**
     * Return the ceiling of base 2 logarithm of a number, 
     * or zero if the nmber is zero.
     */
    unsigned ceil_log2(unsigned u);

    typedef ptr_vector<app> app_vector;
    typedef ptr_vector<func_decl> decl_vector;
    typedef obj_hashtable<func_decl> func_decl_set;
    
    std::string pp_cube(const ptr_vector<expr>& model, ast_manager& manager);
    std::string pp_cube(const expr_ref_vector& model, ast_manager& manager);
    std::string pp_cube(const ptr_vector<app>& model, ast_manager& manager);
    std::string pp_cube(const app_ref_vector& model, ast_manager& manager);
    std::string pp_cube(unsigned sz, app * const * lits, ast_manager& manager);
    std::string pp_cube(unsigned sz, expr * const * lits, ast_manager& manager);
    

    /**
       \brief replace variables that are used in many disequalities by
       an equality using the model. 
       
       Assumption: the model satisfies the conjunctions.       
     */
    void reduce_disequalities(model& model, unsigned threshold, expr_ref& fml);

    /**
       \brief normalize coefficients in polynomials so that least coefficient is 1.
     */
    void normalize_arithmetic(expr_ref& t);


    /**
       \brief determine if formulas belong to difference logic or UTVPI fragment.
     */
    bool is_difference_logic(ast_manager& m, unsigned num_fmls, expr* const* fmls);

    bool is_utvpi_logic(ast_manager& m, unsigned num_fmls, expr* const* fmls);

}

#endif
