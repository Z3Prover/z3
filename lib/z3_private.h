/*++
Copyright (c) 2007 Microsoft Corporation

Module Name:

    z3_private.h

Abstract:

    Z3 API.

Author:

    Nikolaj Bjorner (nbjorner)
    Leonardo de Moura (leonardo) 2007-06-8

Notes:
    
--*/

#include<iostream>
#include"rational.h"
#include"z3_macros.h"

#ifndef _Z3_PRIVATE__H_
#define _Z3_PRIVATE__H_


#ifndef CAMLIDL
#ifdef __cplusplus
extern "C" {
#endif // __cplusplus
#else
[pointer_default(ref)] interface Z3 {
#endif // CAMLIDL  

    Z3_bool Z3_API Z3_get_numeral_rational(__in Z3_context c, __in Z3_ast a, rational& r);

    /**
       \brief \mlh exec_smtlib2_string c str \endmlh
       Parse the given string using the SMT-LIB2 parser and execute its commands.
              
       It returns a formula comprising of the conjunction of assertions in the scope
       (up to push/pop) at the end of the string.
       The returned formula is also asserted to the logical context on return.
     */
    Z3_ast Z3_API Z3_exec_smtlib2_string(__in Z3_context c, 
                                         __in Z3_string str,
                                         __in unsigned num_sorts,
                                         __in_ecount(num_sorts) Z3_symbol sort_names[],
                                         __in_ecount(num_sorts) Z3_sort sorts[],
                                         __in unsigned num_decls,
                                         __in_ecount(num_decls) Z3_symbol decl_names[],
                                         __in_ecount(num_decls) Z3_func_decl decls[]  
                                         );
    
    /**
       \brief Similar to #Z3_exec_smtlib2_string, but reads the commands from a file.
    */
    Z3_ast Z3_API Z3_exec_smtlib2_file(__in Z3_context c, 
                                       __in Z3_string file_name,
                                          __in unsigned num_sorts,
                                          __in_ecount(num_sorts) Z3_symbol sort_names[],
                                          __in_ecount(num_sorts) Z3_sort sorts[],
                                          __in unsigned num_decls,
                                          __in_ecount(num_decls) Z3_symbol decl_names[],
                                          __in_ecount(num_decls) Z3_func_decl decls[]  
                                       );


#ifndef CAMLIDL
#ifdef __cplusplus
};
#endif // __cplusplus
#else
}
#endif // CAMLIDL

#endif

