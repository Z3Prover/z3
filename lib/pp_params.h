/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    pp_params.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-01-20.

Revision History:

--*/
#ifndef _PP_PARAMS_H_
#define _PP_PARAMS_H_

#include"ini_file.h"

struct pp_params {
    unsigned  m_pp_max_indent; // max. indentation
    unsigned  m_pp_max_num_lines; // max. num. lines
    unsigned  m_pp_max_width;  // max. width
    unsigned  m_pp_max_ribbon; // max. ribbon: width - indentation
    unsigned  m_pp_max_depth;
    unsigned  m_pp_min_alias_size; 
    bool      m_pp_decimal; // display reals using decimals
    unsigned  m_pp_decimal_precision; // max. number of decimal places
    bool      m_pp_bv_lits;
    bool      m_pp_bv_neg; // use bvneg to display bit-vector literals which the most significant bit is 1
    bool      m_pp_flat_assoc;
    bool      m_pp_fixed_indent; 
    bool      m_pp_single_line; // ignore line breaks if true
    bool      m_pp_bounded; // ignore characters exceeding max width.
    bool      m_pp_simplify_implies; // simplify nested implications during pretty printing

    pp_params();
    void register_params(ini_params & p);
};

#endif /* _PP_PARAMS_H_ */

