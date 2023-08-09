/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    synth_solver.h

Author:

    Petra Hozzova 2023-08-08
    Nikolaj Bjorner (nbjorner) 2020-08-17

--*/

#pragma once

#include "muz/spacer/spacer_util.h"
#include "sat/smt/sat_th.h"
#include "solver/solver.h"


namespace synth {

    class solver : public euf::th_euf_solver {

    public:
        solver(euf::solver& ctx);
        
        ~solver() override;

        
        void asserted(sat::literal lit) override;

        sat::check_result check() override;
        void push_core() override;
        void pop_core(unsigned n) override;
        bool unit_propagate() override;
        void get_antecedents(sat::literal l, sat::ext_justification_idx idx, sat::literal_vector & r, bool probing) override;
        void collect_statistics(statistics& st) const override;
        sat::literal internalize(expr* e, bool sign, bool root) override;
        void internalize(expr* e) override;
        std::ostream& display(std::ostream& out) const override;
        std::ostream& display_justification(std::ostream& out, sat::ext_justification_idx idx) const override;
        std::ostream& display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const override;
        euf::th_solver* clone(euf::solver& ctx) override;

    private:
	bool synthesize(app* e);
	void add_uncomputable(app* e);
	bool contains_uncomputable(expr* e);

    	ptr_vector<app> m_synth;
	spacer::func_decl_set m_uncomputable;

    };

};
