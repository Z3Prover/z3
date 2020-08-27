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

#include "util/scoped_ptr_vector.h"
#include "sat/sat_extension.h"
#include "ast/euf/euf_egraph.h"
#include "ast/ast_translation.h"
#include "sat/smt/atom2bool_var.h"
#include "sat/smt/sat_th.h"
#include "tactic/model_converter.h"

namespace euf {
    typedef sat::literal literal;
    typedef sat::ext_constraint_idx ext_constraint_idx;
    typedef sat::ext_justification_idx ext_justification_idx;
    typedef sat::literal_vector literal_vector;
    typedef sat::bool_var bool_var;

    class euf_base : public sat::index_base {
        unsigned m_id;
    public:
        euf_base(sat::extension* e, unsigned id) :
            index_base(e), m_id(id)
        {}
        unsigned id() const { return m_id; }
        static euf_base* from_idx(size_t z) { return reinterpret_cast<euf_base*>(z); }
    };

    class solver : public sat::extension, public sat::th_internalizer {
        ast_manager& m;
        atom2bool_var&        m_expr2var;
        euf::egraph           m_egraph;
        sat::solver*          m_solver;
        sat::lookahead*       m_lookahead;
        ast_translation*      m_translate;
        atom2bool_var*        m_translate_expr2var;

        euf::enode*           m_true;
        euf::enode*           m_false;
        svector<euf::enode_bool_pair> m_var2node;
        ptr_vector<unsigned>  m_explain;
        euf::enode_vector     m_args;
        svector<sat::frame>   m_stack;
        unsigned              m_num_scopes { 0 };
        unsigned_vector       m_bool_var_trail;
        unsigned_vector       m_bool_var_lim;
        scoped_ptr_vector<sat::extension> m_extensions;
        ptr_vector<sat::extension>        m_id2extension;
        ptr_vector<sat::th_internalizer>  m_id2internalize;
        scoped_ptr_vector<sat::th_internalizer>        m_internalizers;
        scoped_ptr_vector<sat::th_model_builder>       m_model_builders;
        ptr_vector<sat::th_model_builder>              m_id2model_builder;
        euf_base              m_conflict_idx, m_eq_idx, m_lit_idx;

        sat::solver& s() { return *m_solver; }
        unsigned * base_ptr() { return reinterpret_cast<unsigned*>(this); }
        euf::enode* visit(sat::sat_internalizer& si, expr* e);
        void attach_bool_var(sat::sat_internalizer& si, euf::enode* n);
        void attach_bool_var(sat::bool_var v, bool sign, euf::enode* n);
        solver* copy_core();
        sat::extension* get_extension(sat::bool_var v);
        sat::extension* get_extension(expr* e);
        void add_extension(family_id fid, sat::extension* e);
        sat::th_internalizer* get_internalizer(expr* e);

        sat::th_model_builder* get_model_builder(expr* e);

        void propagate();
        void get_antecedents(literal l, euf_base& j, literal_vector& r);

        void dependencies2values(sat::th_dependencies& deps, expr_ref_vector& values);
        void collect_dependencies(sat::th_dependencies& deps);        
        void sort_dependencies(sat::th_dependencies& deps);

    public:
        solver(ast_manager& m, atom2bool_var& expr2var):
            m(m),
            m_expr2var(expr2var),
            m_egraph(m),
            m_solver(nullptr),
            m_lookahead(nullptr),
            m_translate(nullptr),
            m_translate_expr2var(nullptr),
            m_true(nullptr),
            m_false(nullptr),
            m_conflict_idx(this, 0),
            m_eq_idx(this, 1),
            m_lit_idx(this, 2)
        {}
        ~solver() override {}

        void set_solver(sat::solver* s) override { m_solver = s; }
        void set_lookahead(sat::lookahead* s) override { m_lookahead = s; }
        struct scoped_set_translate {
            solver& s;
            scoped_set_translate(solver& s, ast_translation& t, atom2bool_var& a2b):s(s) { s.m_translate = &t; s.m_translate_expr2var = &a2b; }
            ~scoped_set_translate() { s.m_translate = nullptr; s. m_translate_expr2var = nullptr; }
        };
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

        bool extract_pb(std::function<void(unsigned sz, literal const* c, unsigned k)>& card,
                        std::function<void(unsigned sz, literal const* c, unsigned const* coeffs, unsigned k)>& pb) override;


        sat::literal internalize(sat::sat_internalizer& si, expr* e, bool sign, bool root) override;
        model_converter* get_model();

        

    };
};
