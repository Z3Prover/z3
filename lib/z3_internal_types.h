/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    z3_internal_types.h

Abstract:

    Z3 internal API type declarations.

Author:

    Leonardo de Moura (leonardo) 2012-10-18

Notes:
    
--*/
#ifndef _Z3_INTERNAL_TYPES_H_
#define _Z3_INTERNAL_TYPES_H_

DEFINE_TYPE(Z3_polynomial_manager);
DEFINE_TYPE(Z3_polynomial);
DEFINE_TYPE(Z3_monomial);

/*
  Definitions for update_api.py
  
  def_Type('POLYNOMIAL_MANAGER',           'Z3_polynomial_manager',           'PolynomialManagerObj')
  def_Type('POLYNOMIAL',                   'Z3_polynomial',                   'PolynomialObj')
  def_Type('MONOMIAL',                     'Z3_monomial',                     'MonomialObj')
*/

#endif
