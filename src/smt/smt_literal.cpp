/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_literal.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-02-18.

Revision History:

--*/
#include "smt/smt_literal.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"

namespace smt {

    std::ostream& display(std::ostream & out, literal lit, ast_manager & m, expr * const * bool_var2expr_map) {
        if (lit == true_literal)
            out << "true";
        else if (lit == false_literal)
            out << "false";
        else if (lit == null_literal)
            out << "null";
        else if (lit.sign())
            out << "(not " << mk_bounded_pp(bool_var2expr_map[lit.var()], m, 3) << ")";
        else
            out << mk_bounded_pp(bool_var2expr_map[lit.var()], m, 3);
        return out;
    }

    std::ostream& display_smt2(std::ostream & out, literal lit, ast_manager & m, expr * const * bool_var2expr_map) {
        if (lit == true_literal)
            out << "true";
        else if (lit == false_literal)
            out << "false";
        else if (lit == null_literal)
            out << "null";
        else if (lit.sign())
            out << "(not " << mk_pp(bool_var2expr_map[lit.var()], m, 3) << ")";
        else
            out << mk_pp(bool_var2expr_map[lit.var()], m, 3);
        return out;
    }

    std::ostream& display_compact(std::ostream & out, literal lit, expr * const * bool_var2expr_map) {
        if (lit == true_literal)
            out << "true";
        else if (lit == false_literal)
            out << "false";
        else if (lit.sign())
            out << "(not #" << bool_var2expr_map[lit.var()]->get_id() << ")";
        else
            out << "#" << bool_var2expr_map[lit.var()]->get_id();
        return out;
    }

    std::ostream & operator<<(std::ostream & out, literal l) {
        if (l == true_literal)
            out << "true";
        else if (l == false_literal)
            out << "false";
        else if (l.sign())
            out << "-" << l.var();
        else
            out << l.var();
        return out;
    }

    std::ostream & operator<<(std::ostream & out, const literal_vector & v) {
        ::display(out, v.begin(), v.end());
        return out;
    }

    std::ostream& display_compact(std::ostream & out, unsigned num_lits, literal const * lits, expr * const * bool_var2expr_map) {
        for (unsigned i = 0; i < num_lits; i++) {
            if (i > 0)
                out << " ";
            display_compact(out, lits[i], bool_var2expr_map);
        }
        return out;
    }

    std::ostream& display_verbose(std::ostream & out, ast_manager& m, unsigned num_lits, literal const * lits, expr * const * bool_var2expr_map, char const* sep) {
        for (unsigned i = 0; i < num_lits; i++) {
            if (i > 0)
                out << sep;
            display(out, lits[i], m, bool_var2expr_map);
        }
        return out;
    }

    /**
       \brief Return true if lits1 subsumes lits2.
       That is every literal in lits1 is in lits2
    */
    bool backward_subsumption(unsigned num_lits1, literal const * lits1, unsigned num_lits2, literal const * lits2) {
        unsigned i = 0;
        for (; i < num_lits1; i++) {
            literal l1 = lits1[i];
            unsigned j = 0;
            for (; j < num_lits2; j++)
                if (l1 == lits2[j])
                    break;
            if (j == num_lits2)
                break;
        }
        return i == num_lits1;
    }


};

