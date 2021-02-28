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

struct dimacs_pp {
    ast_manager& m;
    unsigned_vector expr2var;
    ptr_vector<expr> exprs;
    unsigned num_vars { 0 };

    dimacs_pp(ast_manager& m): m(m) {}

    void reset() {
        num_vars = 0;
        expr2var.reset();
        exprs.reset();
    }
    
    bool init_from_dimacs(expr* f) {
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
            if (!is_uninterp_const(l)) 
                return false;
            symbol const& s = to_app(l)->get_decl()->get_name();
            if (s.is_numerical() && s.get_num() > 0) {
                if (expr2var.get(l->get_id(), UINT_MAX) == UINT_MAX) {
                    ++num_vars;
                    expr2var.setx(l->get_id(), s.get_num(), UINT_MAX);
                    exprs.setx(l->get_id(), l, nullptr);
                }
                continue;
            }
            return false;
        }
        return true;
    }    

    void init_formula(expr* f) {
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

    void pp_formula(std::ostream& out, expr* f) {
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

    void pp_defs(std::ostream& out) {
        for (expr* e : exprs) 
            if (e && is_app(e)) {
                symbol const& n = to_app(e)->get_decl()->get_name();
                out << "c " << expr2var[e->get_id()] << " " << n << "\n";            
            }
    }

};

std::ostream& display_dimacs(std::ostream& out, expr_ref_vector const& fmls, bool include_names) {
    ast_manager& m = fmls.m();
    dimacs_pp pp(m);
    unsigned num_cls  = fmls.size();
    bool is_from_dimacs = true;
    for (expr * f : fmls) {
        is_from_dimacs = pp.init_from_dimacs(f);
        if (!is_from_dimacs)
            break;
    }

    if (!is_from_dimacs) {
        pp.reset();
        for (expr * f : fmls) {
            pp.init_formula(f);
        }
    }
    out << "p cnf " << pp.num_vars << " " << num_cls << "\n";
    for (expr* f : fmls) 
        pp.pp_formula(out, f);
    if (include_names && !is_from_dimacs) 
        pp.pp_defs(out);
    return out;
}

std::ostream& display_wcnf(std::ostream& out, expr_ref_vector const& fmls, svector<std::pair<expr*,unsigned>> const& soft) {
    ast_manager& m = fmls.m();
    dimacs_pp pp(m);
    for (expr* f : fmls)
        pp.init_formula(f);
    for (auto s : soft)
        pp.init_formula(s.first);
    out << "p wcnf " << pp.num_vars << " " << fmls.size() + soft.size() << "\n";
    unsigned sum_soft = 1;
    for (auto s : soft)
        sum_soft += s.second;
    for (expr* f : fmls) {
        out << sum_soft << " ";
        pp.pp_formula(out, f);
    }
    for (auto s : soft) {
        out << s.second << " ";
        pp.pp_formula(out, s.first);
    }
    pp.pp_defs(out);
    return out;
}
