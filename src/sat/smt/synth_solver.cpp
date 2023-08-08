/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    synth_solver.h

Author:

    Petra Hozzova 2023-08-08
    Nikolaj Bjorner (nbjorner) 2020-08-17

--*/


#include "sat/smt/synth_solver.h"
#include "sat/smt/euf_solver.h"

namespace synth {

    solver::solver(euf::solver& ctx):
        th_euf_solver(ctx, symbol("synth"), ctx.get_manager().mk_family_id("synth")) {}
        
    solver::~solver() {}


    // recognize synthesis objective as part of search objective.
    // register it for calls to check.
    void solver::asserted(sat::literal lit) {

    }

    // block current model using realizer by E-graph (and arithmetic)
    // 
    sat::check_result solver::check() {

        return sat::check_result::CR_DONE;
    }

    // nothing particular to do
    void solver::push_core() {

    }

    // nothing particular to do
    void solver::pop_core(unsigned n) {
    }

    // nothing particular to do
    bool solver::unit_propagate() {
        return false;
    }

    // retrieve explanation for assertions made by synth solver. It only asserts unit literals so nothing to retrieve
    void solver::get_antecedents(sat::literal l, sat::ext_justification_idx idx, sat::literal_vector & r, bool probing) {
    }

    // where we collect statistics (number of invocations?)
    void solver::collect_statistics(statistics& st) const {}

    // recognize synthesis objectives here.
    sat::literal solver::internalize(expr* e, bool sign, bool root) {
        NOT_IMPLEMENTED_YET();
        return sat::null_literal;
    }

    // recognize synthesis objectives here and above
    void solver::internalize(expr* e) {}

    // display current state (eg. current set of realizers)
    std::ostream& solver::display(std::ostream& out) const {
        return out;
    }

    // justified by "synth".
    std::ostream& solver::display_justification(std::ostream& out, sat::ext_justification_idx idx) const {
        return out << "synth";
    }
    
    std::ostream& solver::display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const {
        return out << "synth";
    }

    // create a clone of the solver.
    euf::th_solver* solver::clone(euf::solver& ctx) {
        NOT_IMPLEMENTED_YET();
        return nullptr;
    }

}
