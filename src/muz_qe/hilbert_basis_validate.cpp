/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    hilbert_basis_validate.cpp

Abstract:

    Basic Hilbert Basis validation.

    hilbert_basis computes a Hilbert basis for linear
    homogeneous inequalities over naturals.

Author:

    Nikolaj Bjorner (nbjorner) 2013-02-15.

Revision History:

--*/

#include "hilbert_basis_validate.h"
#include "arith_decl_plugin.h"
#include "ast_pp.h"
#include <sstream>


hilbert_basis_validate::hilbert_basis_validate(ast_manager& m): 
    m(m) {
}

void hilbert_basis_validate::validate_solution(hilbert_basis& hb, vector<rational> const& v, bool is_initial) {
    unsigned sz = hb.get_num_ineqs();
    rational bound;
    for (unsigned i = 0; i < sz; ++i) {
        bool is_eq;
        vector<rational> w;
        hb.get_ge(i, w, bound, is_eq);
        rational sum(0);
        for (unsigned j = 0; j < v.size(); ++j) {
            sum += w[j]*v[j];
        }
        if (bound > sum || 
            (is_eq && bound != sum)) {
            // validation failed.
            std::cout << "validation failed for inequality\n";
            for (unsigned j = 0; j < v.size(); ++j) {
                std::cout << v[j] << " ";
            }
            std::cout << "\n";
            for (unsigned j = 0; j < w.size(); ++j) {
                std::cout << w[j] << " ";
            }
            std::cout << (is_eq?" = ":" >= ") << bound << "\n";
            std::cout << "is initial: " << (is_initial?"true":"false") << "\n";
            std::cout << "sum: " << sum << "\n";
        }        
    }
}

expr_ref hilbert_basis_validate::mk_validate(hilbert_basis& hb) {
    arith_util a(m);
    unsigned sz = hb.get_basis_size();
    vector<rational> v;
    bool is_initial;

    // check that claimed solution really satisfies inequalities:        
    for (unsigned i = 0; i < sz; ++i) {
        hb.get_basis_solution(i, v, is_initial);
        validate_solution(hb, v, is_initial);
    }

    // check that solutions satisfying inequalities are in solution.
    // build a formula that says solutions to linear inequalities
    // coincide with linear combinations of basis.
    vector<expr_ref_vector> offsets, increments;
    expr_ref_vector xs(m), vars(m);
    expr_ref var(m);
    svector<symbol> names;
    sort_ref_vector sorts(m);

#define mk_mul(_r,_x) (_r.is_one()?((expr*)_x):((expr*)a.mk_mul(a.mk_numeral(_r,true),_x)))
    

    for (unsigned i = 0; i < sz; ++i) {
        hb.get_basis_solution(i, v, is_initial);

        for (unsigned j = 0; xs.size() < v.size(); ++j) {
            xs.push_back(m.mk_fresh_const("x", a.mk_int()));
        }

        if (is_initial) {
            expr_ref_vector tmp(m);
            for (unsigned j = 0; j < v.size(); ++j) {
                tmp.push_back(a.mk_numeral(v[j], true));
            }
            offsets.push_back(tmp);
        }
        else {
            var = m.mk_var(vars.size(), a.mk_int());
            expr_ref_vector tmp(m);
            for (unsigned j = 0; j < v.size(); ++j) {
                tmp.push_back(mk_mul(v[j], var));
            }
            std::stringstream name;
            name << "u" << i;
            increments.push_back(tmp);
            vars.push_back(var);
            names.push_back(symbol(name.str().c_str()));
            sorts.push_back(a.mk_int());
        }
    }

    expr_ref_vector bounds(m);
    for (unsigned i = 0; i < vars.size(); ++i) {
        bounds.push_back(a.mk_ge(vars[i].get(), a.mk_numeral(rational(0), true)));
    }
    expr_ref_vector fmls(m);
    expr_ref fml(m), fml1(m), fml2(m);
    for (unsigned i = 0; i < offsets.size(); ++i) {
        expr_ref_vector eqs(m);
        eqs.append(bounds);
        for (unsigned j = 0; j < xs.size(); ++j) {
            expr_ref_vector sum(m);
            sum.push_back(offsets[i][j].get());
            for (unsigned k = 0; k < increments.size(); ++k) {
                sum.push_back(increments[k][j].get());
            }
            eqs.push_back(m.mk_eq(xs[j].get(), a.mk_add(sum.size(), sum.c_ptr())));
        }
        fml = m.mk_and(eqs.size(), eqs.c_ptr());
        if (!names.empty()) {
            fml = m.mk_exists(names.size(), sorts.c_ptr(), names.c_ptr(), fml);
        }
        fmls.push_back(fml);
    }
    fml1 = m.mk_or(fmls.size(), fmls.c_ptr());
    fmls.reset();
    
    sz = hb.get_num_ineqs();
    for (unsigned i = 0; i < sz; ++i) {
        bool is_eq;
        vector<rational> w;
        rational bound;
        hb.get_ge(i, w, bound, is_eq);
        expr_ref_vector sum(m);
        for (unsigned j = 0; j < w.size(); ++j) {
            if (!w[j].is_zero()) {
                sum.push_back(mk_mul(w[j], xs[j].get()));
            }
        }
        expr_ref lhs(m), rhs(m);
        lhs = a.mk_add(sum.size(), sum.c_ptr());
        rhs = a.mk_numeral(bound, true);
        if (is_eq) {
            fmls.push_back(a.mk_eq(lhs, rhs));
        }
        else {
            fmls.push_back(a.mk_ge(lhs, rhs));
        }
    }
    fml2 = m.mk_and(fmls.size(), fmls.c_ptr());
    fml = m.mk_eq(fml1, fml2);
    
    bounds.reset();
    for (unsigned i = 0; i < xs.size(); ++i) {
        if (!hb.get_is_int(i)) {
            bounds.push_back(a.mk_ge(xs[i].get(), a.mk_numeral(rational(0), true)));
        }
    }
    if (!bounds.empty()) {
        fml = m.mk_implies(m.mk_and(bounds.size(), bounds.c_ptr()), fml);
    }
    return fml;

}

