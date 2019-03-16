/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    display_dimacs.h

Abstract:

    Display expressions in DIMACS format.
    
Author:

    Nikolaj Bjorner (nbjorner0 2019-01-24

Revision History:

--*/

#include "ast.h"
#include "display_dimacs.h"

std::ostream& display_dimacs(std::ostream& out, expr_ref_vector const& fmls) {
    ast_manager& m = fmls.m();
    unsigned_vector expr2var;
    ptr_vector<expr> exprs;
    unsigned num_vars = 0;
    unsigned num_cls  = fmls.size();
    bool is_from_dimacs = true;
    for (expr * f : fmls) {
        unsigned num_lits;
        expr * const * lits;
        if (m.is_or(f)) {
            num_lits = to_app(f)->get_num_args();
            lits     = to_app(f)->get_args();
        }
        else {
            num_lits = 1;
            lits     = &f;
        }
        for (unsigned j = 0; j < num_lits; j++) {
            expr * l = lits[j];
            if (m.is_not(l))
                l = to_app(l)->get_arg(0);
            if (!is_uninterp_const(l)) {
                is_from_dimacs = false;
                break;
            }
            symbol const& s = to_app(l)->get_decl()->get_name();
            if (s.is_numerical() && s.get_num() > 0) {
                if (expr2var.get(l->get_id(), UINT_MAX) == UINT_MAX) {
                    ++num_vars;
                    expr2var.setx(l->get_id(), s.get_num(), UINT_MAX);
                    exprs.setx(l->get_id(), l, nullptr);
                }
                continue;
            }
            is_from_dimacs = false;
            break;            
        }
        if (!is_from_dimacs) {
            num_vars = 0;
            expr2var.reset();
            exprs.reset();
            break;
        }
    }
    
    if (!is_from_dimacs) {
        for (expr * f : fmls) {
            unsigned num_lits;
            expr * const * lits;
            if (m.is_or(f)) {
                num_lits = to_app(f)->get_num_args();
                lits     = to_app(f)->get_args();
            }
            else {
                num_lits = 1;
                lits     = &f;
            }
            for (unsigned j = 0; j < num_lits; j++) {
                expr * l = lits[j];
                if (m.is_not(l))
                    l = to_app(l)->get_arg(0);
                if (expr2var.get(l->get_id(), UINT_MAX) == UINT_MAX) {
                    num_vars++;
                    expr2var.setx(l->get_id(), num_vars, UINT_MAX);
                    exprs.setx(l->get_id(), l, nullptr);
                }
            }
        }
    }
    out << "p cnf " << num_vars << " " << num_cls << "\n";
    for (expr* f : fmls) {
        unsigned num_lits;
        expr * const * lits;
        if (m.is_or(f)) {
            num_lits = to_app(f)->get_num_args();
            lits     = to_app(f)->get_args();
        }
        else {
            num_lits = 1;
            lits     = &f;
        }
        for (unsigned j = 0; j < num_lits; j++) {
            expr * l = lits[j];
            if (m.is_not(l)) {
                out << "-";
                l = to_app(l)->get_arg(0);
            }
            SASSERT(exprs[l->get_id()]);
            out << expr2var[l->get_id()] << " ";
        }
        out << "0\n";
    }
    if (!is_from_dimacs) {
        for (expr* e : exprs) {
            if (e && is_app(e)) {
                symbol const& n = to_app(e)->get_decl()->get_name();
                out << "c " << expr2var[e->get_id()] << " " << n << "\n";            
            }
        }
    }
    return out;
}
