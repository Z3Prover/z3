/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    xor_solver.h

Abstract:

    XOR solver.
    Interface outline.

--*/


#include "sat/smt/xor_solver.h"
#include "sat/sat_simplifier_params.hpp"
#include "sat/sat_xor_finder.h"

namespace xr {

    solver::solver(euf::solver& ctx):
        th_solver(ctx.get_manager(), symbol("xor-solver"), ctx.get_manager().get_family_id("xor-solver"))
    {}

    euf::th_solver* solver::clone(euf::solver& ctx) {
        // and relevant copy internal state
        return alloc(solver, ctx);
    }

    void solver::asserted(sat::literal l) {

    }

    bool solver::unit_propagate() {
        return false;
    }
    
    void solver::get_antecedents(sat::literal l, sat::ext_justification_idx idx,
                                 sat::literal_vector & r, bool probing) {
        
    }
    
    sat::check_result solver::check() {
        return sat::check_result::CR_DONE;
    }
    
    void solver::push() {
    }
    
    void solver::pop(unsigned n) {
    }

    // inprocessing
    // pre_simplify: decompile all xor constraints to allow other in-processing.
    // simplify: recompile clauses to xor constraints
    // literals that get added to xor constraints are tagged with the theory.
    void solver::pre_simplify() {
        
    }

    void solver::simplify() {
        
    }

    std::ostream& solver::display(std::ostream& out) const {
        return out;
    }
    
    std::ostream& solver::display_justification(std::ostream& out, sat::ext_justification_idx idx) const  {
        return out;
    }
    
    std::ostream& solver::display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const {
        return out;
    }
    
}

