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
#include "ast/rewriter/th_rewriter.h"
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
            unsigned m_ackerman;
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
        };
        struct scope {
            unsigned m_var_lim;
        };
        typedef trail_stack<solver> euf_trail_stack;


        size_t* to_ptr(sat::literal l) { return TAG(size_t*, reinterpret_cast<size_t*>((size_t)(l.index() << 4)), 1); }
        size_t* to_ptr(size_t jst) { return TAG(size_t*, reinterpret_cast<size_t*>(jst), 2); }
        bool is_literal(size_t* p) const { return GET_TAG(p) == 1; }
        bool is_justification(size_t* p) const { return GET_TAG(p) == 2; }
        sat::literal get_literal(size_t* p) {
            unsigned idx = static_cast<unsigned>(reinterpret_cast<size_t>(UNTAG(size_t*, p)));
            return sat::to_literal(idx >> 4);
        }
        size_t get_justification(size_t* p) const {
            return reinterpret_cast<size_t>(UNTAG(size_t*, p));
        }

        ast_manager&          m;
        sat::sat_internalizer& si;
        smt_params            m_config;
        euf::egraph           m_egraph;
        euf_trail_stack       m_trail;
        stats                 m_stats;
        th_rewriter           m_rewriter;
        func_decl_ref_vector  m_unhandled_functions;
        

        sat::solver*           m_solver { nullptr };
        sat::lookahead*        m_lookahead { nullptr };
        ast_manager*           m_to_m;
        sat::sat_internalizer* m_to_si;
        scoped_ptr<euf::ackerman>   m_ackerman;

        ptr_vector<expr>                                m_var2expr;
        ptr_vector<size_t>                              m_explain;
        unsigned                                        m_num_scopes { 0 };
        unsigned_vector                                 m_var_trail;
        svector<scope>                                  m_scopes;
        scoped_ptr_vector<th_solver>                    m_solvers;
        ptr_vector<th_solver>                           m_id2solver;

        constraint* m_conflict { nullptr };
        constraint* m_eq       { nullptr };
        constraint* m_lit      { nullptr };

        // internalization
        bool visit(expr* e) override;
        bool visited(expr* e) override;
        bool post_visit(expr* e, bool sign, bool root) override;        
        sat::literal attach_lit(sat::literal lit, expr* e);
        void add_distinct_axiom(app* e, euf::enode* const* args);
        void add_not_distinct_axiom(app* e, euf::enode* const* args);
        void axiomatize_basic(enode* n);
        bool internalize_root(app* e, bool sign, ptr_vector<enode> const& args);
        euf::enode* mk_true();
        euf::enode* mk_false();

        // replay
        expr_ref_vector      m_reinit_exprs;
        
        void start_reinit(unsigned num_scopes);
        void finish_reinit();

        // extensions
        th_solver* get_solver(family_id fid, func_decl* f);
        th_solver* get_solver(sort* s) { return get_solver(s->get_family_id(), nullptr); }
        th_solver* get_solver(func_decl* f) { return get_solver(f->get_family_id(), f); }
        th_solver* get_solver(expr* e);
        th_solver* get_solver(sat::bool_var v);
        void add_solver(family_id fid, th_solver* th);
        void init_ackerman();

        // model building
        bool include_func_interp(func_decl* f);
        void register_macros(model& mdl);
        void dependencies2values(deps_t& deps, expr_ref_vector& values, model_ref& mdl);
        void collect_dependencies(deps_t& deps);        
        void values2model(deps_t const& deps, expr_ref_vector const& values, model_ref& mdl);

        // solving
        void propagate_literals();
        void propagate_th_eqs();
        void get_antecedents(literal l, constraint& j, literal_vector& r, bool probing);

        // proofs
        void log_antecedents(std::ostream& out, literal l, literal_vector const& r);
        void log_antecedents(literal l, literal_vector const& r);
        void log_node(expr* n);
        bool m_drat_initialized{ false };
        void init_drat();

        // invariant
        void check_eqc_bool_assignment() const;
        void check_missing_bool_enode_propagation() const;        

        constraint& mk_constraint(constraint*& c, constraint::kind_t k);
        constraint& conflict_constraint() { return mk_constraint(m_conflict, constraint::kind_t::conflict); }
        constraint& eq_constraint() { return mk_constraint(m_eq, constraint::kind_t::eq); }
        constraint& lit_constraint() { return mk_constraint(m_lit, constraint::kind_t::lit); }

    public:
       solver(ast_manager& m, sat::sat_internalizer& si, params_ref const& p = params_ref()):
            m(m),
            si(si),
            m_egraph(m),
            m_trail(*this),
            m_rewriter(m),
            m_unhandled_functions(m),
            m_solver(nullptr),
            m_lookahead(nullptr),
            m_to_m(&m),
            m_to_si(&si),
            m_reinit_exprs(m)
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
           scoped_set_translate(solver& s, ast_manager& m, sat::sat_internalizer& si) :
               s(s) {
               s.m_to_m = &m;
               s.m_to_si = &si;
           }
           ~scoped_set_translate() {
               s.m_to_m = &s.m;
               s.m_to_si = &s.si;
           }
       };

        sat::solver& s() { return *m_solver; }
        sat::solver const& s() const { return *m_solver; }
        sat::sat_internalizer& get_si() { return si; }
        ast_manager& get_manager() { return m; }
        enode* get_enode(expr* e) { return m_egraph.find(e); }
        sat::literal get_literal(expr* e) const { return literal(si.to_bool_var(e), false); }
        sat::literal get_literal(enode* e) const { return get_literal(e->get_expr()); }
        smt_params const& get_config() { return m_config; }
        region& get_region() { return m_trail.get_region(); }
        template <typename C>
        void push(C const& c) { m_trail.push(c);  }
        euf_trail_stack& get_trail_stack() { return m_trail; }

        void updt_params(params_ref const& p);
        void set_solver(sat::solver* s) override { m_solver = s; }
        void set_lookahead(sat::lookahead* s) override { m_lookahead = s; }
        void init_search() override;
        double get_reward(literal l, ext_constraint_idx idx, sat::literal_occs_fun& occs) const override;
        bool is_extended_binary(ext_justification_idx idx, literal_vector& r) override;
        bool is_external(bool_var v) override;
        bool propagate(literal l, ext_constraint_idx idx) override;
        bool unit_propagate() override;
        bool propagate(enode* a, enode* b, ext_justification_idx);
        bool set_root(literal l, literal r) override;
        void flush_roots() override;

        void get_antecedents(literal l, ext_justification_idx idx, literal_vector & r, bool probing) override;
        void add_antecedent(enode* a, enode* b);
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

        bool use_drat() { return s().get_config().m_drat && (init_drat(), true);  }
        sat::drat& get_drat() { return s().get_drat(); }

        // decompile
        bool extract_pb(std::function<void(unsigned sz, literal const* c, unsigned k)>& card,
                        std::function<void(unsigned sz, literal const* c, unsigned const* coeffs, unsigned k)>& pb) override;

        bool to_formulas(std::function<expr_ref(sat::literal)>& l2e, expr_ref_vector& fmls) override;

        // internalize
        sat::literal internalize(expr* e, bool sign, bool root, bool learned) override;
        void internalize(expr* e, bool learned) override;
        void attach_th_var(enode* n, th_solver* th, theory_var v) { m_egraph.add_th_var(n, v, th->get_id()); }
        void attach_node(euf::enode* n);
        euf::enode* mk_enode(expr* e, unsigned n, enode* const* args) { return m_egraph.mk(e, n, args); }
        expr* bool_var2expr(sat::bool_var v) { return m_var2expr.get(v, nullptr); }
        void unhandled_function(func_decl* f);
        th_rewriter& get_rewriter() { return m_rewriter; }
        bool is_shared(euf::enode* n) const;

        void update_model(model_ref& mdl);

        func_decl_ref_vector const& unhandled_functions() { return m_unhandled_functions; }       
    };    
};

inline std::ostream& operator<<(std::ostream& out, euf::solver const& s) {
    return s.display(out);
}
