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
#include "ast/ast_translation.h"
#include "ast/euf/euf_egraph.h"
#include "smt/params/smt_params.h"
#include "tactic/model_converter.h"
#include "sat/sat_extension.h"
#include "sat/smt/atom2bool_var.h"
#include "sat/smt/sat_th.h"
#include "sat/smt/euf_ackerman.h"

namespace euf {
    typedef sat::literal literal;
    typedef sat::ext_constraint_idx ext_constraint_idx;
    typedef sat::ext_justification_idx ext_justification_idx;
    typedef sat::literal_vector literal_vector;
    typedef sat::bool_var bool_var;

    class constraint {
        unsigned m_id;
    public:
        constraint(unsigned id) :
        m_id(id)
        {}
        unsigned id() const { return m_id; }
        static constraint* from_idx(size_t z) { return reinterpret_cast<constraint*>(z); }
        size_t to_index() const { return sat::constraint_base::mem2base(this); }
    };

    class solver : public sat::extension, public sat::th_internalizer, public sat::th_decompile {
        typedef top_sort<euf::enode> deps_t;
        friend class ackerman;
        struct stats {
            unsigned m_num_dynack;
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
        };

        ast_manager&          m;
        atom2bool_var&        m_expr2var;
        sat::sat_internalizer& si;
        smt_params            m_config;
        euf::egraph           m_egraph;
        stats                 m_stats;
        sat::solver*          m_solver { nullptr };
        sat::lookahead*       m_lookahead { nullptr };
        ast_manager*           m_to_m { nullptr };
        atom2bool_var*         m_to_expr2var { nullptr };
        sat::sat_internalizer* m_to_si{ nullptr };
        scoped_ptr<ackerman>   m_ackerman;

        svector<euf::enode_bool_pair>                   m_var2node;
        ptr_vector<unsigned>                            m_explain;
        euf::enode_vector                               m_args;
        svector<sat::frame>                             m_stack;
        unsigned                                        m_num_scopes { 0 };
        unsigned_vector                                 m_bool_var_trail;
        unsigned_vector                                 m_bool_var_lim;
        scoped_ptr_vector<sat::th_solver>               m_solvers;
        ptr_vector<sat::th_solver>                      m_id2solver;

        constraint* m_conflict { nullptr };
        constraint* m_eq       { nullptr };
        constraint* m_lit      { nullptr };

        sat::solver& s() { return *m_solver; }
        unsigned * base_ptr() { return reinterpret_cast<unsigned*>(this); }

        // internalization
        euf::enode* visit(expr* e);
        void attach_bool_var(euf::enode* n);
        void attach_bool_var(sat::bool_var v, bool sign, euf::enode* n);
        euf::enode* mk_true();
        euf::enode* mk_false();

        // extensions
        sat::th_solver* get_solver(func_decl* f) { return fid2solver(f->get_family_id()); }
        sat::th_solver* get_solver(expr* e);
        sat::th_solver* get_solver(sat::bool_var v);
        sat::th_solver* fid2solver(family_id fid);
        void add_solver(family_id fid, sat::th_solver* th);
        void init_ackerman();

        // model building
        bool include_func_interp(func_decl* f);
        void register_macros(model& mdl);
        void dependencies2values(deps_t& deps, expr_ref_vector& values, model_ref const& mdl);
        void collect_dependencies(deps_t& deps);        
        void values2model(deps_t const& deps, expr_ref_vector const& values, model_ref& mdl);

        // solving
        void propagate();
        void get_antecedents(literal l, constraint& j, literal_vector& r);

        constraint& mk_constraint(constraint*& c, unsigned id);
        constraint& conflict_constraint() { return mk_constraint(m_conflict, 0); }
        constraint& eq_constraint() { return mk_constraint(m_eq, 1); }
        constraint& lit_constraint() { return mk_constraint(m_lit, 2); }

    public:
       solver(ast_manager& m, atom2bool_var& expr2var, sat::sat_internalizer& si, params_ref const& p = params_ref()):
            m(m),
            m_expr2var(expr2var),
            si(si),
            m_egraph(m),
            m_solver(nullptr),
            m_lookahead(nullptr),
            m_to_m(&m),
            m_to_expr2var(&expr2var),
            m_to_si(&si)
        {
            updt_params(p);
        }

       ~solver() override {
           if (m_conflict) dealloc(sat::constraint_base::mem2base_ptr(m_conflict));
           if (m_eq) dealloc(sat::constraint_base::mem2base_ptr(m_eq));
           if (m_lit) dealloc(sat::constraint_base::mem2base_ptr(m_lit));
       }

        void updt_params(params_ref const& p);
        void set_solver(sat::solver* s) override { m_solver = s; }
        void set_lookahead(sat::lookahead* s) override { m_lookahead = s; }
        struct scoped_set_translate {
            solver& s;
            scoped_set_translate(solver& s, ast_manager& m, atom2bool_var& a2b, sat::sat_internalizer& si) :
                s(s) { 
                s.m_to_m = &m; 
                s.m_to_expr2var = &a2b; 
                s.m_to_si = &si; 
            }
            ~scoped_set_translate() { s.m_to_m = &s.m; s.m_to_expr2var = &s.m_expr2var; s.m_to_si = &s.si;  }
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

        bool to_formulas(std::function<expr_ref(sat::literal)>& l2e, expr_ref_vector& fmls) override;
        sat::literal internalize(expr* e, bool sign, bool root) override;
        void update_model(model_ref& mdl);
       
    };
};
