/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    xor_solver.h

Abstract:

    XOR solver.
    Interface outline.

--*/

#pragma once

#include "sat/smt/euf_solver.h"

namespace xr {

    class constraint {
        unsigned        m_size;
        bool            m_detached;
        size_t          m_obj_size;
        bool            m_rhs;
        sat::bool_var   m_vars[0];
        
    public:
        static size_t get_obj_size(unsigned num_lits) { return sat::constraint_base::obj_size(sizeof(constraint) + num_lits * sizeof(sat::bool_var)); }
        
        constraint(const svector<sat::bool_var>& ids, bool expected_result) : m_size(ids.size()), m_detached(false), m_obj_size(get_obj_size(ids.size())), m_rhs(expected_result) {
            unsigned i = 0;
            for (auto v : ids)
                m_vars[i++] = v;
        }
        sat::ext_constraint_idx cindex() const { return sat::constraint_base::mem2base(this); }
        void deallocate(small_object_allocator& a) { a.deallocate(m_obj_size, sat::constraint_base::mem2base_ptr(this)); }
        sat::bool_var operator[](unsigned i) const { return m_vars[i]; }
        bool is_detached() const { return m_detached; }
        unsigned get_size() const { return m_size; }
        bool get_rhs() const { return m_rhs; }
        sat::bool_var const* begin() const { return m_vars; }
        sat::bool_var const* end() const { return m_vars + m_size; }
        std::ostream& display(std::ostream& out) const {
            bool first = true;
            for (auto v : *this)
                out << (first ? "" : " ^ ") << v, first = false;
            return out << " = " << m_rhs;
        }
    };
    
    class solver : public euf::th_solver {
        friend class xor_matrix_finder;


        euf::solver* m_ctx = nullptr;
        sat::sat_internalizer& si;

        ptr_vector<constraint> m_constraints;

    public:
        solver(euf::solver& ctx);
        solver(ast_manager& m, sat::sat_internalizer& si, euf::theory_id id);
        th_solver* clone(euf::solver& ctx) override;

        sat::literal internalize(expr* e, bool sign, bool root)  override { UNREACHABLE(); return sat::null_literal; }

        void internalize(expr* e) override { UNREACHABLE(); }


        void asserted(sat::literal l) override;
        bool unit_propagate() override;
        void get_antecedents(sat::literal l, sat::ext_justification_idx idx, sat::literal_vector & r, bool probing) override;

        void pre_simplify() override;
        void simplify() override;

        sat::check_result check() override;
        void push() override;
        void pop(unsigned n) override;

        std::ostream& display(std::ostream& out) const override;
        std::ostream& display_justification(std::ostream& out, sat::ext_justification_idx idx) const override;
        std::ostream& display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const override;

    };

}
