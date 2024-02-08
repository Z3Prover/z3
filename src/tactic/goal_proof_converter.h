/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    goal_proof_converter.h

Abstract:

    Proof converter for goals

Author:

    Nikolaj Bjorner (nbjorner) 2012-11-23

--*/

#pragma once

#include "ast/converters/proof_converter.h"
class goal;

/**
   \brief create a proof converter that takes a set of subgoals and converts their proofs to a proof of 
   the goal they were derived from.
 */
proof_converter * concat(proof_converter *pc1, unsigned n, goal* const* goals);

class subgoal_proof_converter : public proof_converter {
    proof_converter_ref m_pc;
    goal_ref_buffer     m_goals;
public:
    subgoal_proof_converter(proof_converter* pc, unsigned n, goal * const* goals):
        m_pc(pc)
    {
        for (unsigned i = 0; i < n; ++i) m_goals.push_back(goals[i]);
    }

    proof_ref operator()(ast_manager & m, unsigned num_source, proof * const * source) override {
        // ignore the proofs from the arguments, instead obtain the proofs from the subgoals.
        SASSERT(num_source == 0);
        proof_converter_ref_buffer pc_buffer;          
        for (goal_ref g : m_goals) {
            pc_buffer.push_back(g->pc());

        }
        return apply(m, m_pc, pc_buffer);
    }

    proof_converter* translate(ast_translation& tr) override {
        proof_converter_ref pc1 = m_pc->translate(tr);
        goal_ref_buffer goals;
        for (goal_ref g : m_goals) goals.push_back(g->translate(tr));
        return alloc(subgoal_proof_converter, pc1.get(), goals.size(), goals.data());
    }

    void display(std::ostream& out) override {}
    
};

inline proof_converter * concat(proof_converter *pc, unsigned n, goal* const* goals) {
    return alloc(subgoal_proof_converter, pc, n, goals);
}
