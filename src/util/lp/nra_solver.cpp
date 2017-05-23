/*
  Copyright (c) 2017 Microsoft Corporation
  Author: Lev Nachmanson
*/

#pragma once
#include "util/lp/nra_solver.h"

namespace lp {

    struct nra_solver::imp {
        lean::lar_solver& s;
        imp(lean::lar_solver& s): s(s) {}

        lean::final_check_status check_feasible() {
            return lean::final_check_status::GIVEUP;
        }
    };

    nra_solver::nra_solver(lean::lar_solver& s) {
        m_imp = alloc(imp, s);
    }

    nra_solver::~nra_solver() {
        dealloc(m_imp);
    }

    lean::final_check_status nra_solver::check_feasible() {
        return m_imp->check_feasible();
    }
}
