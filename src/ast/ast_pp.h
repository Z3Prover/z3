/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    ast_pp.h

Abstract:

    Pretty printer

Author:

    Leonardo de Moura 2008-01-20.

Revision History:

    2012-11-17 - ast_smt2_pp is the official pretty printer in Z3

--*/
#ifndef AST_PP_H_
#define AST_PP_H_

#include "ast/ast_smt2_pp.h"

struct mk_pp : public mk_ismt2_pp {
    mk_pp(ast * t, ast_manager & m, params_ref const & p, unsigned indent = 0, unsigned num_vars = 0, char const * var_prefix = nullptr):
        mk_ismt2_pp(t, m, p, indent, num_vars, var_prefix) {
    }
    mk_pp(ast * t, ast_manager & m, unsigned indent = 0, unsigned num_vars = 0, char const * var_prefix = nullptr):
        mk_ismt2_pp(t, m, indent, num_vars, var_prefix) {
    }
};

//<! print vector of ASTs
class mk_pp_vec {
    ast_manager &   m;
    ast_ref_vector  vec;
public:
    mk_pp_vec(unsigned len, ast ** vec0, ast_manager & m) : m(m), vec(m) {
        for (unsigned i=0; i<len; ++i) vec.push_back(vec0[i]);
    }
    void display(std::ostream & out) const {
        bool first = true;
        for (ast* e : vec) {
            if (first) { first = false; } else { out << " "; }
            out << mk_pp(e, m);
        }
    }
};

inline std::ostream& operator<<(std::ostream & out, mk_pp_vec const & pp) {
    pp.display(out);
    return out;
}

#endif

