/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    ast_smt2_pp.cpp

Abstract:

    Pretty printer of AST formulas using SMT2 format.
    This printer is more expensive than the one in ast_smt_pp.h,
    but is supposed to generated a "prettier" and SMT2 compliant output.

Author:

    Leonardo de Moura (leonardo)

Revision History:


--*/
#ifndef AST_SMT2_PP_H_
#define AST_SMT2_PP_H_

#include"format.h"
#include"params.h"
#include"arith_decl_plugin.h"
#include"bv_decl_plugin.h"
#include"array_decl_plugin.h"
#include"fpa_decl_plugin.h"
#include"dl_decl_plugin.h"
#include"smt2_util.h"

class smt2_pp_environment {
protected:
    format_ns::format * mk_neg(format_ns::format * f) const;
    format_ns::format * mk_float(rational const & val) const;
    bool is_indexed_fdecl(func_decl * f) const;
    format_ns::format * pp_fdecl_params(format_ns::format * fname, func_decl * f);
    bool is_sort_param(func_decl * f) const;
    format_ns::format * pp_as(format_ns::format * fname, sort * s);
    format_ns::format * pp_signature(format_ns::format * f_name, func_decl * f);
public:
    virtual ~smt2_pp_environment() {}
    virtual ast_manager & get_manager() const = 0;
    virtual arith_util & get_autil() = 0;
    virtual bv_util & get_bvutil() = 0;
    virtual array_util & get_arutil() = 0;
    virtual fpa_util & get_futil() = 0;
    virtual datalog::dl_decl_util& get_dlutil() = 0;
    virtual bool uses(symbol const & s) const = 0; 
    virtual format_ns::format * pp_fdecl(func_decl * f, unsigned & len);
    virtual format_ns::format * pp_bv_literal(app * t, bool use_bv_lits, bool bv_neg);
    virtual format_ns::format * pp_arith_literal(app * t, bool decimal, unsigned prec);
    virtual format_ns::format * pp_float_literal(app * t, bool use_bv_lits, bool use_float_real_lits);
    virtual format_ns::format * pp_datalog_literal(app * t);
    virtual format_ns::format * pp_sort(sort * s);
    virtual format_ns::format * pp_fdecl_ref(func_decl * f);
    format_ns::format * pp_fdecl_name(symbol const & fname, unsigned & len) const;
    format_ns::format * pp_fdecl_name(func_decl * f, unsigned & len) const;
};

/**
   \brief Simple environment that ignores name clashes.
   Useful for debugging code.
 */
class smt2_pp_environment_dbg : public smt2_pp_environment {
    ast_manager & m_manager;
    arith_util    m_autil;
    bv_util       m_bvutil;
    array_util    m_arutil;
    fpa_util      m_futil;
    datalog::dl_decl_util m_dlutil;
public:
    smt2_pp_environment_dbg(ast_manager & m):m_manager(m), m_autil(m), m_bvutil(m), m_arutil(m), m_futil(m), m_dlutil(m) {}
    virtual ast_manager & get_manager() const { return m_manager; }
    virtual arith_util & get_autil() { return m_autil; }
    virtual bv_util & get_bvutil() { return m_bvutil; }
    virtual array_util & get_arutil() { return m_arutil; }
    virtual fpa_util & get_futil() { return m_futil; }
    virtual datalog::dl_decl_util& get_dlutil() { return m_dlutil; }
    virtual bool uses(symbol const & s) const { return false; }
};

void mk_smt2_format(expr * n, smt2_pp_environment & env, params_ref const & p, 
                    unsigned num_vars, char const * var_prefix,
                    format_ns::format_ref & r, sbuffer<symbol> & var_names);
void mk_smt2_format(sort * s, smt2_pp_environment & env, params_ref const & p, format_ns::format_ref & r);
void mk_smt2_format(func_decl * f, smt2_pp_environment & env, params_ref const & p, format_ns::format_ref & r);

std::ostream & ast_smt2_pp(std::ostream & out, expr * n, smt2_pp_environment & env, params_ref const & p = params_ref(), unsigned indent = 0, 
                           unsigned num_vars = 0, char const * var_prefix = 0);
std::ostream & ast_smt2_pp(std::ostream & out, sort * s, smt2_pp_environment & env, params_ref const & p = params_ref(), unsigned indent = 0);
std::ostream & ast_smt2_pp(std::ostream & out, func_decl * f, smt2_pp_environment & env, params_ref const & p = params_ref(), unsigned indent = 0);

/**
   \brief Internal wrapper (for debugging purposes only)
*/
struct mk_ismt2_pp {
    ast *              m_ast;
    ast_manager &      m_manager;
    params_ref         m_empty;
    params_ref const & m_params;
    unsigned           m_indent;
    unsigned           m_num_vars;
    char const *       m_var_prefix;
    mk_ismt2_pp(ast * t, ast_manager & m, params_ref const & p, unsigned indent = 0, unsigned num_vars = 0, char const * var_prefix = 0);
    mk_ismt2_pp(ast * t, ast_manager & m, unsigned indent = 0, unsigned num_vars = 0, char const * var_prefix = 0);
};

std::ostream& operator<<(std::ostream& out, mk_ismt2_pp const & p);

std::ostream& operator<<(std::ostream& out, expr_ref const& e);
std::ostream& operator<<(std::ostream& out, app_ref const& e);

std::ostream& operator<<(std::ostream& out, expr_ref_vector const& e);
std::ostream& operator<<(std::ostream& out, app_ref_vector const& e);

#endif
