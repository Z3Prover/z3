/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    ba_card.h

Abstract:
 
    Interface for Cardinality constraints.

Author:

    Nikolaj Bjorner (nbjorner) 2017-01-30

--*/

#pragma once 

#include "sat/sat_types.h"
#include "sat/smt/ba_constraint.h"


namespace ba {

    // base class for pb and cardinality constraints
    class pb_base : public constraint {
    protected:
        unsigned       m_k;
    public:
        pb_base(ba::tag_t t, unsigned id, literal l, unsigned sz, size_t osz, unsigned k) :
            constraint(t, id, l, sz, osz), m_k(k) {
            VERIFY(k < 4000000000);
        }
        virtual void set_k(unsigned k) { VERIFY(k < 4000000000);  m_k = k; }
        virtual unsigned get_coeff(unsigned i) const { UNREACHABLE(); return 0; }
        unsigned k() const { return m_k; }
        bool well_formed() const override;
    };

    class card : public pb_base {
        literal        m_lits[0];
    public:
        static size_t get_obj_size(unsigned num_lits) { return sat::constraint_base::obj_size(sizeof(card) + num_lits * sizeof(literal)); }
        card(unsigned id, literal lit, literal_vector const& lits, unsigned k);
        literal operator[](unsigned i) const { return m_lits[i]; }
        literal& operator[](unsigned i) { return m_lits[i]; }
        literal const* begin() const { return m_lits; }
        literal const* end() const { return static_cast<literal const*>(m_lits) + m_size; }
        void negate() override;
        void swap(unsigned i, unsigned j) override { std::swap(m_lits[i], m_lits[j]); }
        literal_vector literals() const override { return literal_vector(m_size, m_lits); }
        bool is_watching(literal l) const override;
        literal get_lit(unsigned i) const override { return m_lits[i]; }
        void set_lit(unsigned i, literal l) override { m_lits[i] = l; }
        unsigned get_coeff(unsigned i) const override { return 1; }
        double get_reward(ba::solver_interface const& s, sat::literal_occs_fun& occs) const override;
        std::ostream& display(std::ostream& out) const override;
        std::ostream& display(std::ostream& out, solver_interface const& s, bool values) const override;
        void clear_watch(solver_interface& s) override;
        bool init_watch(solver_interface& s) override;        
        bool is_extended_binary(literal_vector& r) const override;
        bool validate_unit_propagation(solver_interface const& s, literal alit) const override;
        lbool eval(sat::model const& m) const override;
        lbool eval(solver_interface const& s) const override;

    };
}
