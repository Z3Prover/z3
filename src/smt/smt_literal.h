/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_literal.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-18.

Revision History:

--*/
#pragma once

#include "ast/ast.h"
#include "smt/smt_types.h"
#include "util/approx_set.h"
#include "util/sat_literal.h"

namespace smt {

    typedef sat::literal literal;
    
    inline literal to_literal(int x) { return sat::to_literal(x); }

    const literal null_literal;
    const literal true_literal(true_bool_var, false); 
    const literal false_literal(true_bool_var, true);

    typedef svector<literal> literal_vector;
    typedef sbuffer<literal> literal_buffer;

    std::ostream& display(std::ostream & out, literal lit, ast_manager & m, expr * const * bool_var2expr_map);
    
    std::ostream& display_smt2(std::ostream & out, literal lit, ast_manager & m, expr * const * bool_var2expr_map);
    
    std::ostream& display_compact(std::ostream & out, literal lit, expr * const * bool_var2expr_map);

    std::ostream& display_compact(std::ostream & out, unsigned num_lits, literal const * lits, expr * const * bool_var2expr_map);

    std::ostream& display_verbose(std::ostream & out, ast_manager& m, unsigned num_lits, literal const * lits, expr * const * bool_var2expr_map, char const* sep = "\n");

    template<typename T>
    void neg_literals(unsigned num_lits, literal const * lits, T & result) {
        for (unsigned i = 0; i < num_lits; ++i) 
            result.push_back(~lits[i]);
    }


    bool backward_subsumption(unsigned num_lits1, literal const * lits1, unsigned num_lits2, literal const * lits2);
};


