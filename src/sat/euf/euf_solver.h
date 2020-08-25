/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    euf_solver.h

Abstract:

    Solver plugin for EUF

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-25

--*/
#pragma once

#include "sat/sat_extension.h"
#include "ast/euf/euf_egraph.h"
#include "sat/tactic/atom2bool_var.h"
#include "sat/tactic/goal2sat.h"

namespace euf_sat {
    typedef sat::literal literal;
    typedef sat::ext_constraint_idx ext_constraint_idx;
    typedef sat::ext_justification_idx ext_justification_idx;
    typedef sat::literal_vector literal_vector;
    typedef sat::bool_var bool_var;

    struct frame {
        expr* m_e;
        unsigned m_idx;
        frame(expr* e) : m_e(e), m_idx(0) {}
    };

    class solver : public sat::extension {
        ast_manager& m;
        atom2bool_var&        m_expr2var;
        euf::egraph           m_egraph;
        sat::solver*          m_solver;

        euf::enode*           m_true;
        euf::enode*           m_false;
        svector<euf::enode_bool_pair> m_var2node;
        ptr_vector<unsigned>  m_explain;
        euf::enode_vector     m_args;
        svector<frame>        m_stack;

        sat::solver& s() { return *m_solver; }
        unsigned * base_ptr() { return reinterpret_cast<unsigned*>(this); }
        euf::enode* visit(sat_internalizer& si, expr* e);
        void attach_bool_var(sat_internalizer& si, euf::enode* n);
        void attach_bool_var(sat::bool_var v, bool sign, euf::enode* n);

    public:
        solver(ast_manager& m, atom2bool_var& expr2var):
            m(m),
            m_expr2var(expr2var),
            m_egraph(m),
            m_solver(nullptr)
        {}

        void set_solver(sat::solver* s) override { m_solver = s; }
        void set_lookahead(sat::lookahead* s) override { }
        double get_reward(literal l, ext_constraint_idx idx, sat::literal_occs_fun& occs) const override { return 0; }
        bool is_extended_binary(ext_justification_idx idx, literal_vector & r) override { return false; }

        bool propagate(literal l, ext_constraint_idx idx) override;
        void get_antecedents(literal l, ext_justification_idx idx, literal_vector & r) override;
        void asserted(literal l) override;
        sat::check_result check() override;
        void push() override;
        void pop(unsigned n) override;
        void pre_simplify() override;
        void simplify() override;
        // have a way to replace l by r in all constraints
        void clauses_modifed() override;
        lbool get_phase(bool_var v) override;
        std::ostream& display(std::ostream& out) const override;
        std::ostream& display_justification(std::ostream& out, ext_justification_idx idx) const override;
        std::ostream& display_constraint(std::ostream& out, ext_constraint_idx idx) const override;
        void collect_statistics(statistics& st) const override;
        extension* copy(sat::solver* s) override;       
        extension* copy(sat::lookahead* s, bool learned) override;       
        void find_mutexes(literal_vector& lits, vector<literal_vector> & mutexes) override;
        void gc() override;
        void pop_reinit() override;
        bool validate() override;
        void init_use_list(sat::ext_use_list& ul) override;
        bool is_blocked(literal l, ext_constraint_idx) override;
        bool check_model(sat::model const& m) const override;
        unsigned max_var(unsigned w) const override;

        void internalize(sat_internalizer& si, expr* e);

    };
};
