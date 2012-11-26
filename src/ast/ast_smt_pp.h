/*++
Copyright (c) 2008 Microsoft Corporation

Module Name:

    ast_smt_pp.h

Abstract:

    Pretty printer of AST formulas as SMT benchmarks.

Author:

    Nikolaj Bjorner 2008-04-09.

Revision History:

--*/
#ifndef _AST_SMT_PP_H_
#define _AST_SMT_PP_H_

#include"ast.h"
#include<string>
#include"map.h"

class smt_renaming {
    typedef map<symbol, symbol, symbol_hash_proc, symbol_eq_proc> symbol2symbol;
    symbol2symbol  m_translate;
    symbol2symbol  m_rev_translate;

    symbol fix_symbol(symbol s, int k);
    bool is_legal(char c);
    bool is_special(char const* s);
    bool is_numerical(char const* s);
    bool all_is_legal(char const* s);
public:
    smt_renaming();
    symbol get_symbol(symbol s0);
    symbol operator()(symbol const & s) { return get_symbol(s); }
};

class ast_smt_pp {
public:
    class is_declared { 
    public:
        virtual bool operator()(func_decl* d) const { return false; }
        virtual bool operator()(sort* s) const { return false; }
    };
private:
    ast_manager& m_manager;
    expr_ref_vector m_assumptions;
    expr_ref_vector m_assumptions_star;
    symbol      m_benchmark_name;
    symbol      m_source_info;
    symbol      m_status;
    symbol      m_category;
    symbol      m_logic;
    std::string m_attributes;
    family_id   m_dt_fid;
    is_declared m_is_declared_default;
    is_declared* m_is_declared;
    bool         m_simplify_implies;
public:
    ast_smt_pp(ast_manager& m);

    void set_benchmark_name(const char* bn) { if (bn) m_benchmark_name = bn; }
    void set_source_info(const char* si) { if (si) m_source_info = si; }
    void set_status(const char* s) { if (s) m_status = s; }
    void set_category(const char* c) { if (c) m_category = c; }
    void set_logic(const char* l) { if (l) m_logic = l; }
    void add_attributes(const char* s) { if (s) m_attributes += s; }
    void add_assumption(expr* n) { m_assumptions.push_back(n); }
    void add_assumption_star(expr* n) { m_assumptions_star.push_back(n); }
    void set_simplify_implies(bool f) { m_simplify_implies = f; }

    void set_is_declared(is_declared* id) { m_is_declared = id; }

    void display(std::ostream& strm, expr* n);
    void display_smt2(std::ostream& strm, expr* n);
    void display_expr(std::ostream& strm, expr* n);
    void display_expr_smt2(std::ostream& strm, expr* n, unsigned indent = 0, unsigned num_var_names = 0, char const* const* var_names = 0);
    void display_ast_smt2(std::ostream& strm, ast* n, unsigned indent = 0, unsigned num_var_names = 0, char const* const* var_names = 0);

};

struct mk_smt_pp {
    ast*   m_ast;
    ast_manager& m_manager;
    unsigned m_indent;
    unsigned m_num_var_names;
    char const* const* m_var_names;
    mk_smt_pp(ast* e, ast_manager & m, unsigned indent = 0, unsigned num_var_names = 0, char const* const* var_names = 0) :
        m_ast(e), m_manager(m), m_indent(indent), m_num_var_names(num_var_names), m_var_names(var_names) {}
};

inline std::ostream& operator<<(std::ostream& out, const mk_smt_pp & p) {
    ast_smt_pp pp(p.m_manager);
    pp.display_ast_smt2(out, p.m_ast, p.m_indent, p.m_num_var_names, p.m_var_names);
    return out;
}



#endif
