/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    ba_xor.h

Abstract:
 
    Interface for Xor constraints.

Author:

    Nikolaj Bjorner (nbjorner) 2017-01-30

--*/

#pragma once 

#include "sat/sat_types.h"
#include "sat/smt/ba_constraint.h"


namespace ba {

    class xr : public constraint {
        literal        m_lits[0];        
    public:
        static size_t get_obj_size(unsigned num_lits) { return sat::constraint_base::obj_size(sizeof(xr) + num_lits * sizeof(literal)); }
        xr(unsigned id, literal_vector const& lits);
        literal operator[](unsigned i) const { return m_lits[i]; }
        literal const* begin() const { return m_lits; }
        literal const* end() const { return begin() + m_size; }
        void negate() override { m_lits[0].neg(); }
        void swap(unsigned i, unsigned j) override { std::swap(m_lits[i], m_lits[j]); }
        bool is_watching(literal l) const override;
        literal_vector literals() const override { return literal_vector(size(), begin()); }
        literal get_lit(unsigned i) const override { return m_lits[i]; }
        void set_lit(unsigned i, literal l) override { m_lits[i] = l; }
        bool well_formed() const override;
        void clear_watch(solver_interface& s) override;
        bool init_watch(solver_interface& s) override;
        std::ostream& display(std::ostream& out) const override;
        std::ostream& display(std::ostream& out, solver_interface const& s, bool values) const override;

        bool parity(solver_interface const& s, unsigned offset) const;
        bool validate_unit_propagation(solver_interface const& s, literal alit) const override;
        lbool eval(sat::model const& m) const override;
        lbool eval(solver_interface const& s) const override;
        void init_use_list(sat::ext_use_list& ul) const override;
        bool is_blocked(sat::simplifier& s, literal lit) const override { return false;  }
    };
}
