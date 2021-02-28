/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    pb_pb.h

Abstract:
 
    Interface for PB constraints.

Author:

    Nikolaj Bjorner (nbjorner) 2017-01-30

--*/

#pragma once 

#include "sat/sat_types.h"
#include "sat/smt/pb_card.h"


namespace pb {

    class pbc : public constraint {
        unsigned       m_slack;
        unsigned       m_num_watch;
        unsigned       m_max_sum;
        wliteral       m_wlits[0];
    public:
        static size_t get_obj_size(unsigned num_lits) { return sat::constraint_base::obj_size(sizeof(pbc) + num_lits * sizeof(wliteral)); }
        pbc(unsigned id, literal lit, svector<wliteral> const& wlits, unsigned k);
        literal lit() const { return m_lit; }
        wliteral operator[](unsigned i) const { return m_wlits[i]; }
        wliteral& operator[](unsigned i) { return m_wlits[i]; }
        wliteral const* begin() const { return m_wlits; }
        wliteral const* end() const { return begin() + m_size; }

        unsigned slack() const { return m_slack; }
        void set_slack(unsigned s) { m_slack = s; }
        unsigned num_watch() const { return m_num_watch; }
        unsigned max_sum() const { return m_max_sum; }
        void update_max_sum();
        void set_num_watch(unsigned s) { m_num_watch = s; }
        bool is_cardinality() const;
        void negate() override;
        void set_k(unsigned k) override { m_k = k; VERIFY(k < 4000000000); update_max_sum(); }
        void swap(unsigned i, unsigned j) override { std::swap(m_wlits[i], m_wlits[j]); }
        literal_vector literals() const override { literal_vector lits; for (auto wl : *this) lits.push_back(wl.second); return lits; }
        bool is_watching(literal l) const override;
        literal get_lit(unsigned i) const override { return m_wlits[i].second; }
        void set_lit(unsigned i, literal l) override { m_wlits[i].second = l; }
        unsigned get_coeff(unsigned i) const override { return m_wlits[i].first; }
        double get_reward(solver_interface const& s, sat::literal_occs_fun& occs) const override;
        void clear_watch(solver_interface& s) override;
        std::ostream& display(std::ostream& out) const override;
        std::ostream& display(std::ostream& out, solver_interface const& s, bool values) const override;
        bool init_watch(solver_interface& s) override;
        bool validate_unit_propagation(solver_interface const& s, literal alit) const override;
        lbool eval(sat::model const& m) const override;
        lbool eval(solver_interface const& s) const override;
        void init_use_list(sat::ext_use_list& ul) const override;
        bool is_blocked(sat::simplifier& s, literal lit) const override;
    };

}
