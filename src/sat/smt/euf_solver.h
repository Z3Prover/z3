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
#include "util/trail.h"
#include "ast/ast_translation.h"
#include "ast/euf/euf_egraph.h"
#include "tactic/model_converter.h"
#include "sat/sat_extension.h"
#include "sat/smt/atom2bool_var.h"
#include "sat/smt/sat_th.h"
#include "sat/smt/euf_ackerman.h"
#include "smt/params/smt_params.h"

namespace euf {
    typedef sat::literal literal;
    typedef sat::ext_constraint_idx ext_constraint_idx;
    typedef sat::ext_justification_idx ext_justification_idx;
    typedef sat::literal_vector literal_vector;
    typedef sat::bool_var bool_var;

    class constraint {
    public:
        enum class kind_t { conflict, eq, lit};
    private:
        kind_t m_kind;
    public:
        constraint(kind_t k) : m_kind(k) {}
        kind_t kind() const { return m_kind; }
        static constraint& from_idx(size_t z) { 
            return *reinterpret_cast<constraint*>(sat::constraint_base::idx2mem(z)); 
        }
        size_t to_index() const { return sat::constraint_base::mem2base(this); }
    };

    class solver : public sat::extension, public th_internalizer, public th_decompile {
        typedef top_sort<euf::enode> deps_t;
        friend class ackerman;
        // friend class sat::ba_solver;
        struct stats {
            unsigned m_num_dynack;
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
        };
        struct scope {
            unsigned m_var_lim;
            unsigned m_trail_lim;
        };
        typedef ptr_vector<trail<solver> > trail_stack;

        ast_manager&          m;
        atom2bool_var&        m_expr2var;
        sat::sat_internalizer& si;
        smt_params            m_config;
        bool                  m_drat { false };
        euf::egraph           m_egraph;
        stats                 m_stats;
        region                m_region;
        func_decl_ref_vector  m_unhandled_functions;
        trail_stack           m_trail;

        sat::solver*           m_solver { nullptr };
        sat::lookahead*        m_lookahead { nullptr };
        ast_manager*           m_to_m;
        atom2bool_var*         m_to_expr2var;
        sat::sat_internalizer* m_to_si;
        scoped_ptr<euf::ackerman>   m_ackerman;

        ptr_vector<euf::enode>                          m_var2node;
        ptr_vector<unsigned>                            m_explain;
        unsigned                                        m_num_scopes { 0 };
        unsigned_vector                                 m_var_trail;
        svector<scope>                                  m_scopes;
        scoped_ptr_vector<th_solver>                    m_solvers;
        ptr_vector<th_solver>                           m_id2solver;

        constraint* m_conflict { nullptr };
        constraint* m_eq       { nullptr };
        constraint* m_lit      { nullptr };

        sat::solver& s() { return *m_solver; }
        unsigned * base_ptr() { return reinterpret_cast<unsigned*>(this); }

        // internalization

        bool visit(expr* e) override;
        bool visited(expr* e) override;
        bool post_visit(expr* e, bool sign, bool root) override;
        void attach_node(euf::enode* n);
        void attach_lit(sat::literal lit, euf::enode* n);
        void add_distinct_axiom(app* e, euf::enode* const* args);
        void add_not_distinct_axiom(app* e, euf::enode* const* args);
        void axiomatize_basic(enode* n);
        bool internalize_root(app* e, bool sign);
        euf::enode* mk_true();
        euf::enode* mk_false();
        

        // extensions
        th_solver* get_solver(func_decl* f);
        th_solver* get_solver(expr* e);
        th_solver* get_solver(sat::bool_var v);
        void add_solver(family_id fid, th_solver* th);
        void unhandled_function(func_decl* f);
        void init_ackerman();

        // model building
        bool include_func_interp(func_decl* f);
        void register_macros(model& mdl);
        void dependencies2values(deps_t& deps, expr_ref_vector& values, model_ref const& mdl);
        void collect_dependencies(deps_t& deps);        
        void values2model(deps_t const& deps, expr_ref_vector const& values, model_ref& mdl);

        // solving
        void propagate();
        void propagate_literals();
        void propagate_th_eqs();
        void get_antecedents(literal l, constraint& j, literal_vector& r);
        void force_push();
        void log_antecedents(std::ostream& out, literal l, literal_vector const& r);
        void log_antecedents(literal l, literal_vector const& r);
        void log_node(enode* n);
        void log_bool_var(sat::bool_var v, enode* n);

        constraint& mk_constraint(constraint*& c, constraint::kind_t k);
        constraint& conflict_constraint() { return mk_constraint(m_conflict, constraint::kind_t::conflict); }
        constraint& eq_constraint() { return mk_constraint(m_eq, constraint::kind_t::eq); }
        constraint& lit_constraint() { return mk_constraint(m_lit, constraint::kind_t::lit); }

    public:
       solver(ast_manager& m, atom2bool_var& expr2var, sat::sat_internalizer& si, params_ref const& p = params_ref()):
            m(m),
            m_expr2var(expr2var),
            si(si),
            m_egraph(m),
            m_unhandled_functions(m),
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

       struct scoped_set_translate {
           solver& s;
           scoped_set_translate(solver& s, ast_manager& m, atom2bool_var& a2b, sat::sat_internalizer& si) :
               s(s) {
               s.m_to_m = &m;
               s.m_to_expr2var = &a2b;
               s.m_to_si = &si;
           }
           ~scoped_set_translate() {
               s.m_to_m = &s.m;
               s.m_to_expr2var = &s.m_expr2var;
               s.m_to_si = &s.si;
           }
       };

        sat::sat_internalizer& get_si() { return si; }
        ast_manager& get_manager() { return m; }
        enode* get_enode(expr* e) { return m_egraph.find(e); }
        sat::literal get_literal(expr* e) { return literal(m_expr2var.to_bool_var(e), false); }
        smt_params const& get_config() { return m_config; }
        region& get_region() { return m_region; }
        template <typename C>
        void push(C const& c) { m_trail.push_back(new (m_region) C(c));  }

        void updt_params(params_ref const& p);
        void set_solver(sat::solver* s) override { m_solver = s; m_drat = s->get_config().m_drat; }
        void set_lookahead(sat::lookahead* s) override { m_lookahead = s; }
        void init_search() override;
        double get_reward(literal l, ext_constraint_idx idx, sat::literal_occs_fun& occs) const override;
        bool is_extended_binary(ext_justification_idx idx, literal_vector& r) override;
        bool is_external(bool_var v) override;
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

        // decompile
        bool extract_pb(std::function<void(unsigned sz, literal const* c, unsigned k)>& card,
                        std::function<void(unsigned sz, literal const* c, unsigned const* coeffs, unsigned k)>& pb) override;

        bool to_formulas(std::function<expr_ref(sat::literal)>& l2e, expr_ref_vector& fmls) override;

        // internalize
        sat::literal internalize(expr* e, bool sign, bool root, bool learned) override;
        void attach_th_var(enode* n, th_solver* th, theory_var v) { m_egraph.add_th_var(n, v, th->get_id()); }
        euf::enode* mk_enode(expr* e, unsigned n, enode* const* args) { return m_egraph.mk(e, n, args); }

        void update_model(model_ref& mdl);

        func_decl_ref_vector const& unhandled_functions() { return m_unhandled_functions; }       
    };
};
