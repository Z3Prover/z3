/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    pp_params.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-01-20.

Revision History:

--*/

#include"pp_params.h"

pp_params::pp_params():
    m_pp_max_indent(UINT_MAX),
    m_pp_max_num_lines(UINT_MAX),
    m_pp_max_width(80),
    m_pp_max_ribbon(80),
    m_pp_max_depth(5),
    m_pp_min_alias_size(10),
    m_pp_decimal(false),
    m_pp_decimal_precision(10),
    m_pp_bv_lits(true),
    m_pp_bv_neg(false),
    m_pp_flat_assoc(true),
    m_pp_fixed_indent(false),
    m_pp_single_line(false),
    m_pp_bounded(false),
    m_pp_simplify_implies(false) {
}

void pp_params::register_params(ini_params & p) {
    p.register_unsigned_param("PP_MAX_INDENT", m_pp_max_indent, "max. indentation in pretty printer", true);
    p.register_unsigned_param("PP_MAX_NUM_LINES", m_pp_max_num_lines, "max. number of lines to be displayed in pretty printer", true);
    p.register_unsigned_param("PP_MAX_WIDTH", m_pp_max_width, "max. width in pretty printer", true);
    p.register_unsigned_param("PP_MAX_RIBBON", m_pp_max_ribbon, "max. ribbon (width - indentation) in pretty printer", true);
    p.register_unsigned_param("PP_MAX_DEPTH", m_pp_max_depth, "max. term depth (when pretty printing SMT2 terms/formulas)", true);
    p.register_unsigned_param("PP_MIN_ALIAS_SIZE", m_pp_min_alias_size, "min. size for creating an alias for a shared term (when pretty printing SMT2 terms/formulas)", true);
    p.register_bool_param("PP_DECIMAL", m_pp_decimal, "pretty print real numbers using decimal notation (the output may be truncated). Z3 adds a '?' if the value is not precise", true);
    p.register_unsigned_param("PP_DECIMAL_PRECISION", m_pp_decimal_precision, "maximum number of decimal places to be used when PP_DECIMAL=true", true);
    p.register_bool_param("PP_BV_LITERALS", m_pp_bv_lits, "use Bit-Vector literals (e.g, #x0F and #b0101) during pretty printing", true);
    p.register_bool_param("PP_BV_NEG", m_pp_bv_neg, "use bvneg when displaying Bit-Vector literals where the most significant bit is 1", true);
    p.register_bool_param("PP_FLAT_ASSOC", m_pp_flat_assoc, "flat associative operators (when pretty printing SMT2 terms/formulas)", true);
    p.register_bool_param("PP_FIXED_INDENT", m_pp_fixed_indent, "use a fixed indentation for applications", true);
    p.register_bool_param("PP_SINGLE_LINE", m_pp_single_line, "ignore line breaks when true", true);
    p.register_bool_param("PP_BOUNDED", m_pp_bounded, "ignore characters exceeding max widht", true);
    p.register_bool_param("PP_SIMPLIFY_IMPLIES", m_pp_simplify_implies, "simplify nested implications for pretty printing", true);
}

