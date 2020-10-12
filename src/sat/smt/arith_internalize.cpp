/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    arith_internalize.cpp

Abstract:

    Theory plugin for arithmetic

Author:

    Nikolaj Bjorner (nbjorner) 2020-09-08

--*/
#pragma once

#include "sat/smt/euf_solver.h"
#include "sat/smt/arith_solver.h"

namespace arith {

    bool solver::visit(expr* e) { return false; }
    bool solver::visited(expr* e) { return false; }
    bool solver::post_visit(expr* e, bool sign, bool root) { return false; }
    void solver::ensure_var(euf::enode* n) {}
    sat::literal solver::internalize(expr* e, bool sign, bool root, bool learned) { return sat::null_literal; }
    void solver::internalize(expr* e, bool redundant) {}
    euf::theory_var solver::mk_var(euf::enode* n) { return euf::null_theory_var; }
    bool solver::is_shared(theory_var v) const { return false; }   
    void solver::pop_core(unsigned n) {}
        
}
