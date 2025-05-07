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
#include "ast/ast_util.h"
#include "ast/euf/euf_egraph.h"
#include "ast/euf/euf_mam.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/converters/model_converter.h"
#include "sat/sat_extension.h"
#include "sat/smt/atom2bool_var.h"
#include "sat/smt/sat_th.h"
#include "sat/smt/euf_ackerman.h"
#include "sat/smt/user_solver.h"
#include "sat/smt/euf_relevancy.h"
#include "sat/smt/euf_proof_checker.h"
#include "smt/params/smt_params.h"


namespace euf {
    typedef sat::literal literal;
    typedef sat::ext_constraint_idx ext_constraint_idx;
    typedef sat::ext_justification_idx ext_justification_idx;
    typedef sat::literal_vector literal_vector;
    typedef sat::bool_var bool_var;

    class constraint {
    public:
        enum class kind_t { conflict, eq, lit };
    private:
        kind_t m_kind;
        enode* m_node = nullptr;
    public:
        constraint(kind_t k) : m_kind(k) {}
        constraint(enode* n): m_kind(kind_t::lit), m_node(n) {}
        kind_t kind() const { return m_kind; }
        enode* node() const { SASSERT(kind() == kind_t::lit); return m_node; }
        static constraint& from_idx(size_t z) {
            return *reinterpret_cast<constraint*>(sat::constraint_base::idx2mem(z));
        }
        size_t to_index() const { return sat::constraint_base::mem2base(this); }
    };

    class clause_pp {
        solver& s;
        sat::literal_vector const& lits;
    public:
        clause_pp(solver& s, sat::literal_vector const& lits):s(s), lits(lits) {}
        std::ostream& display(std::ostream& out) const;
    };

    class eq_proof_hint : public th_proof_hint {
        symbol th;
        unsigned m_lit_head, m_lit_tail, m_cc_head, m_cc_tail;
    public:
        eq_proof_hint(symbol const& th, unsigned lh, unsigned lt, unsigned ch, unsigned ct):
            th(th), m_lit_head(lh), m_lit_tail(lt), m_cc_head(ch), m_cc_tail(ct) {}
        expr* get_hint(euf::solver& s) const override;
    };

    class smt_proof_hint : public th_proof_hint {
        symbol   m_name;
        unsigned m_lit_head, m_lit_tail, m_eq_head, m_eq_tail, m_deq_head, m_deq_tail;
    public:
        smt_proof_hint(symbol const& n, unsigned lh, unsigned lt, unsigned ch, unsigned ct, unsigned dh, unsigned dt):
            m_name(n), m_lit_head(lh), m_lit_tail(lt), m_eq_head(ch), m_eq_tail(ct), m_deq_head(dh), m_deq_tail(dt) {}
        expr* get_hint(euf::solver& s) const override;
    };

    class solver : public sat::extension, public th_internalizer, public th_decompile, public sat::clause_eh, public mam_solver {
        typedef top_sort<euf::enode> deps_t;
        friend class ackerman;
        friend class eq_proof_hint;
        friend class smt_proof_hint;
        class user_sort;
        struct stats {
            unsigned m_ackerman;
            unsigned m_final_checks;
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
        };
        struct scope {
            unsigned m_var_lim;
            scope(unsigned l) : m_var_lim(l) {}
        };

        size_t* to_ptr(sat::literal l) { return TAG(size_t*, reinterpret_cast<size_t*>((size_t)(l.index() << 4)), 1); }
        size_t* to_ptr(size_t jst) { return TAG(size_t*, reinterpret_cast<size_t*>(jst), 2); }
        bool is_literal(size_t* p) const { return GET_TAG(p) == 1; }
        bool is_justification(size_t* p) const { return GET_TAG(p) == 2; }
        sat::literal get_literal(size_t* p) const {
            unsigned idx = static_cast<unsigned>(reinterpret_cast<size_t>(UNTAG(size_t*, p)));
            return sat::to_literal(idx >> 4);
        }
        size_t get_justification(size_t* p) const {
            return reinterpret_cast<size_t>(UNTAG(size_t*, p));
        }

        std::function<::solver*(void)>   m_mk_solver;
        user_propagator::on_clause_eh_t  m_on_clause;
        ast_manager&                     m;
        sat::sat_internalizer&           si;
        relevancy                        m_relevancy;
        smt_params                       m_config;
        euf::egraph                      m_egraph;
        trail_stack                      m_trail;
        stats                            m_stats;
        th_rewriter                      m_rewriter;
        func_decl_ref_vector             m_unhandled_functions;
        sat::lookahead*                  m_lookahead = nullptr;
        ast_manager*                     m_to_m = nullptr;
        sat::sat_internalizer*           m_to_si;
        scoped_ptr<euf::ackerman>        m_ackerman;
        void*                            m_on_clause_ctx = nullptr;
        user_solver::solver*             m_user_propagator = nullptr;
        th_solver*                       m_qsolver = nullptr;
        unsigned                         m_generation = 0;
        std::string                      m_reason_unknown; 
        mutable ptr_vector<expr>         m_todo;

        ptr_vector<expr>                 m_bool_var2expr;
        ptr_vector<size_t>               m_explain;
        euf::cc_justification            m_explain_cc;
        enode_pair_vector                m_hint_eqs;
        sat::literal_vector              m_hint_lits;
        unsigned                         m_num_scopes = 0;
        unsigned_vector                  m_var_trail;
        svector<scope>                   m_scopes;
        scoped_ptr_vector<th_solver>     m_solvers;
        ptr_vector<th_solver>            m_id2solver;
        

        constraint* m_conflict = nullptr;
        constraint* m_eq = nullptr;

        // proofs 
        bool                             m_proof_initialized = false;
        ast_pp_util                      m_clause_visitor;
        bool                             m_display_all_decls = false;
        smt_proof_checker                m_smt_proof_checker;

        typedef std::pair<expr*, expr*> expr_pair;
        literal_vector      m_proof_literals;
        svector<expr_pair>  m_proof_eqs, m_proof_deqs, m_expr_pairs;        
        unsigned m_lit_head = 0, m_lit_tail = 0, m_cc_head = 0, m_cc_tail = 0;
        unsigned m_eq_head = 0, m_eq_tail = 0, m_deq_head = 0, m_deq_tail = 0;
        symbol                           m_euf = symbol("euf");
        symbol                           m_smt = symbol("smt");            
        expr_ref_vector                  m_clause;
        expr_ref_vector                  m_expr_args;
        vector<sat::literal_vector>      m_top_level_clauses;


        // internalization
        bool visit(expr* e) override;
        bool visited(expr* e) override;
        bool post_visit(expr* e, bool sign, bool root) override;

        void add_distinct_axiom(app* e, euf::enode* const* args);
        void add_not_distinct_axiom(app* e, euf::enode* const* args);
        void axiomatize_basic(enode* n);
        bool internalize_root(app* e, bool sign, ptr_vector<enode> const& args);
        euf::enode* mk_true();
        euf::enode* mk_false();

        vector<std::pair<expr_ref, expr_ref>> m_initial_values;

        // replay
        typedef std::tuple<expr_ref, unsigned, sat::bool_var> reinit_t;
        vector<reinit_t>    m_reinit;

        void start_reinit(unsigned num_scopes);        
        void finish_reinit();
        void relevancy_reinit(expr* e);

        // extensions
        th_solver* get_solver(family_id fid, func_decl* f);
        th_solver* sort2solver(sort* s) { return get_solver(s->get_family_id(), nullptr); }
        th_solver* func_decl2solver(func_decl* f) { return get_solver(f->get_family_id(), f); }
        th_solver* quantifier2solver();
        th_solver* expr2solver(expr* e);
        th_solver* bool_var2solver(sat::bool_var v);
        void add_solver(th_solver* th);
        void init_ackerman();

        // model building
        expr_ref_vector m_values;
        obj_map<expr, enode*> m_values2root;        
        model_ref m_qmodel;
        bool include_func_interp(func_decl* f);
        void register_macros(model& mdl);
        void dependencies2values(user_sort& us, deps_t& deps, model_ref& mdl);
        void collect_dependencies(user_sort& us, deps_t& deps);
        void values2model(deps_t const& deps, model_ref& mdl);
        void validate_model(model& mdl);

        // solving
        void propagate_literal(enode* n, enode* ante);
        void propagate_th_eqs();
        bool is_self_propagated(th_eq const& e);
        void get_euf_antecedents(literal l, constraint& j, literal_vector& r, bool probing);
        void new_diseq(enode* a, enode* b, literal lit);
        bool merge_shared_bools();

        // proofs
        void log_antecedents(std::ostream& out, literal l, literal_vector const& r);
        void log_antecedents(literal l, literal_vector const& r, th_proof_hint* hint);
        void log_justification(literal l, th_explain const& jst);
        void log_justifications(literal l, unsigned explain_size, bool is_euf);
        enode_pair get_justification_eq(size_t j);
        void log_rup(literal l, literal_vector const& r);


        eq_proof_hint* mk_hint(symbol const& th, literal lit);

        void init_proof();
        void on_clause(unsigned n, literal const* lits, sat::status st) override;
        void on_lemma(unsigned n, literal const* lits, sat::status st);
        void on_proof(unsigned n, literal const* lits, sat::status st);
        void on_check(unsigned n, literal const* lits, sat::status st);
        void on_clause_eh(unsigned n, literal const* lits, sat::status st);
        std::ostream& display_literals(std::ostream& out, unsigned n, sat::literal const* lits);
        void display_assume(std::ostream& out, unsigned n, literal const* lits);
        void display_inferred(std::ostream& out, unsigned n, literal const* lits, expr* proof_hint);        
        void display_deleted(std::ostream& out, unsigned n, literal const* lits);
        std::ostream& display_hint(std::ostream& out, expr* proof_hint);
        app_ref status2proof_hint(sat::status st);

        // relevancy
        bool is_propagated(sat::literal lit);
        // invariant
        void check_eqc_bool_assignment() const;
        void check_missing_bool_enode_propagation() const;
        void check_missing_eq_propagation() const;
        

        // diagnosis
        std::ostream& display_justification_ptr(std::ostream& out, size_t* j) const;

        // constraints
        constraint& mk_constraint(constraint*& c, constraint::kind_t k);
        constraint& conflict_constraint() { return mk_constraint(m_conflict, constraint::kind_t::conflict); }
        constraint& eq_constraint() { return mk_constraint(m_eq, constraint::kind_t::eq); }
        constraint& lit_constraint(enode* n);        

        // user propagator
        void check_for_user_propagator() {
            if (!m_user_propagator)
                throw default_exception("user propagator must be initialized");
        }

    public:
        solver(ast_manager& m, sat::sat_internalizer& si, params_ref const& p = params_ref());

        ~solver() override {
            if (m_conflict) dealloc(sat::constraint_base::mem2base_ptr(m_conflict));
            if (m_eq) dealloc(sat::constraint_base::mem2base_ptr(m_eq));
            m_trail.reset();
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

        struct scoped_generation {
            solver& s;
            unsigned m_g;
            scoped_generation(solver& s, unsigned g):
                s(s),
                m_g(s.m_generation) {
                s.m_generation = g;
            }
            ~scoped_generation() {
                s.m_generation = m_g;
            }
        };
        unsigned get_max_generation(expr* e) const;

        // accessors
        
        sat::sat_internalizer& get_si() { return si; }
        ast_manager& get_manager() override { return m; }
        enode* get_enode(expr* e) const { return m_egraph.find(e); }
        enode* bool_var2enode(sat::bool_var b) const {
            expr* e = m_bool_var2expr.get(b, nullptr);
            return e ? get_enode(e) : nullptr;
        }
        sat::literal expr2literal(expr* e) const { return enode2literal(get_enode(e)); }
        sat::literal enode2literal(enode* n) const { return sat::literal(n->bool_var(), false); }
        lbool value(enode* n) const { return s().value(enode2literal(n)); }
        smt_params const& get_config() const { return m_config; }
        region& get_region() override { return m_trail.get_region(); }
        egraph& get_egraph() override { return m_egraph; }
        th_solver* fid2solver(family_id fid) const { return m_id2solver.get(fid, nullptr); }

        template <typename C>
        void push(C const& c) { m_trail.push(c); }
        template <typename V>
        void push_vec(ptr_vector<V>& vec, V* val) {
            vec.push_back(val);
            push(push_back_trail< V*, false>(vec));
        }
        template <typename V>
        void push_vec(svector<V>& vec, V val) {
            vec.push_back(val);
            push(push_back_trail< V, false>(vec));
        }
        trail_stack& get_trail_stack() { return m_trail; }
        trail_stack& get_trail() override { return m_trail; }

        void updt_params(params_ref const& p);
        void set_solver(sat::solver* s) override { m_solver = s; use_drat(); }
        void set_lookahead(sat::lookahead* s) override { m_lookahead = s; }
        void init_search() override;
        double get_reward(literal l, ext_constraint_idx idx, sat::literal_occs_fun& occs) const override;
        bool is_extended_binary(ext_justification_idx idx, literal_vector& r) override;
        bool is_external(bool_var v) override;
        bool propagated(literal l, ext_constraint_idx idx) override;
        bool unit_propagate() override;
        bool can_propagate() override;
        bool should_research(sat::literal_vector const& core) override;
        void add_assumptions(sat::literal_set& assumptions) override;
        bool tracking_assumptions() override;
        std::string reason_unknown() override { return m_reason_unknown; }

        void propagate(literal lit, ext_justification_idx idx);
        bool propagate(enode* a, enode* b, ext_justification_idx idx);
        void set_conflict(ext_justification_idx idx);

        void propagate(literal lit, th_explain* p) { propagate(lit, p->to_index()); }
        bool propagate(enode* a, enode* b, th_explain* p) { return propagate(a, b, p->to_index()); }
        size_t* to_justification(sat::literal l) { return to_ptr(l); }
        void set_conflict(th_explain* p) { set_conflict(p->to_index()); }
        bool inconsistent() const { return s().inconsistent() || m_egraph.inconsistent(); }

        bool set_root(literal l, literal r) override;
        void flush_roots() override;

        void get_antecedents(literal l, ext_justification_idx idx, literal_vector& r, bool probing) override;
        void get_eq_antecedents(enode* a, enode* b, literal_vector& r);
        void get_th_antecedents(literal l, th_explain& jst, literal_vector& r, bool probing);
        void add_eq_antecedent(bool probing, enode* a, enode* b);
        void explain_diseq(ptr_vector<size_t>& ex, cc_justification* cc, enode* a, enode* b);
        void add_explain(size_t* p) { m_explain.push_back(p); }
        void reset_explain() { m_explain.reset(); }
        void set_eliminated(bool_var v) override;
        bool decide(bool_var& var, lbool& phase) override;
        bool get_case_split(bool_var& var, lbool& phase) override;
        void asserted(literal l) override;
        sat::check_result check() override;
        lbool resolve_conflict() override;
        void push() override;
        void pop(unsigned n) override;
        void user_push() override;
        void user_pop(unsigned n) override;
        void pre_simplify() override;
        void simplify() override;
        // have a way to replace l by r in all constraints
        void clauses_modifed() override;
        lbool get_phase(bool_var v) override;
        std::ostream& display(std::ostream& out) const override;
        std::ostream& display_justification(std::ostream& out, ext_justification_idx idx) const override;
        std::ostream& display_constraint(std::ostream& out, ext_constraint_idx idx) const override;
        euf::egraph::b_pp bpp(enode* n) const { return m_egraph.bpp(n); }
        clause_pp pp(literal_vector const& lits) { return clause_pp(*this, lits); }
        void collect_statistics(statistics& st) const override;
        extension* copy(sat::solver* s) override;
        enode* copy(solver& dst_ctx, enode* src_n);
        void find_mutexes(literal_vector& lits, vector<literal_vector>& mutexes) override;
        void gc() override;
        void pop_reinit() override;
        bool validate() override;
        void init_use_list(sat::ext_use_list& ul) override;
        bool is_blocked(literal l, ext_constraint_idx) override;
        bool check_model(sat::model const& m) const override;
        void gc_vars(unsigned num_vars) override;
        bool resource_limits_exceeded() const override { return false; } // TODO


        // proof
        bool use_drat() { return m_solver && s().get_config().m_drat && (init_proof(), true); }
        sat::drat& get_drat() { return s().get_drat(); }

        void set_tmp_bool_var(sat::bool_var b, expr* e);
        bool visit_clause(std::ostream& out, unsigned n, literal const* lits);
        void display_assert(std::ostream& out, unsigned n, literal const* lits);
        void visit_expr(std::ostream& out, expr* e);
        std::ostream& display_expr(std::ostream& out, expr* e);        
        void on_instantiation(unsigned n, sat::literal const* lits, unsigned k, euf::enode* const* bindings);
        expr_ref_vector& expr_args() { m_expr_args.reset(); return m_expr_args; }
        smt_proof_hint* mk_smt_hint(symbol const& n, literal_vector const& lits, enode_pair_vector const& eqs) {
            return mk_smt_hint(n, lits.size(), lits.data(), eqs.size(), eqs.data());
        }
        smt_proof_hint* mk_smt_hint(symbol const& n, enode_pair_vector const& eqs) {
            return mk_smt_hint(n, 0, nullptr, eqs.size(), eqs.data());
        }
        smt_proof_hint* mk_smt_hint(symbol const& n, literal_vector const& lits) {
            return mk_smt_hint(n, lits.size(), lits.data(), 0, (expr_pair const*) nullptr);            
        }
        smt_proof_hint* mk_smt_hint(symbol const& n, unsigned nl, literal const* lits, unsigned ne, expr_pair const* eqs, unsigned nd = 0, expr_pair const* deqs = nullptr); 
        smt_proof_hint* mk_smt_hint(symbol const& n, unsigned nl, literal const* lits, unsigned ne = 0, enode_pair const* eqs = nullptr); 
        smt_proof_hint* mk_smt_hint(symbol const& n, literal lit, unsigned ne, expr_pair const* eqs) { return mk_smt_hint(n, 1, &lit, ne, eqs); }
        smt_proof_hint* mk_smt_hint(symbol const& n, literal lit) { return mk_smt_hint(n, 1, &lit, 0, (expr_pair const*)nullptr); }
        smt_proof_hint* mk_smt_hint(symbol const& n, literal l1, literal l2) { literal ls[2] = {l1,l2}; return mk_smt_hint(n, 2, ls, 0, (expr_pair const*)nullptr); }
        smt_proof_hint* mk_smt_hint(symbol const& n, literal lit, expr* a, expr* b) { expr_pair e(a, b); return mk_smt_hint(n, 1, &lit, 1, &e); }
        smt_proof_hint* mk_smt_hint(symbol const& n, literal lit, enode* a, enode* b) { expr_pair e(a->get_expr(), b->get_expr()); return mk_smt_hint(n, 1, &lit, 1, &e); }
        smt_proof_hint* mk_smt_prop_hint(symbol const& n, literal lit, expr* a, expr* b) { expr_pair e(a, b); return mk_smt_hint(n, 1, &lit, 0, nullptr, 1, &e); }        
        smt_proof_hint* mk_smt_prop_hint(symbol const& n, literal lit, enode* a, enode* b) { return mk_smt_prop_hint(n, lit, a->get_expr(), b->get_expr()); }
        smt_proof_hint* mk_smt_hint(symbol const& n, enode* a, enode* b) { expr_pair e(a->get_expr(), b->get_expr()); return mk_smt_hint(n, 0, nullptr, 1, &e); }
        smt_proof_hint* mk_smt_clause(symbol const& n, unsigned nl, literal const* lits);
        th_proof_hint* mk_cc_proof_hint(sat::literal_vector const& ante, app* a, app* b);
        th_proof_hint* mk_tc_proof_hint(sat::literal const* ternary_clause);
        sat::status mk_tseitin_status(sat::literal a) { return mk_tseitin_status(1, &a); }
        sat::status mk_tseitin_status(sat::literal a, sat::literal b);
        sat::status mk_tseitin_status(unsigned n, sat::literal const* lits);
        sat::status mk_distinct_status(sat::literal a) { return mk_distinct_status(1, &a); }
        sat::status mk_distinct_status(sat::literal a, sat::literal b) { sat::literal lits[2] = { a, b }; return mk_distinct_status(2, lits); }
        sat::status mk_distinct_status(sat::literal_vector const& lits) { return mk_distinct_status(lits.size(), lits.data()); }
        sat::status mk_distinct_status(unsigned n, sat::literal const* lits);

        scoped_ptr<std::ostream> m_proof_out;

        // decompile
        bool extract_pb(std::function<void(unsigned sz, literal const* c, unsigned k)>& card,
            std::function<void(unsigned sz, literal const* c, unsigned const* coeffs, unsigned k)>& pb) override;

        bool to_formulas(std::function<expr_ref(sat::literal)>& l2e, expr_ref_vector& fmls) override;

        // internalize
        sat::literal internalize(expr* e, bool sign, bool root) override;
        void internalize(expr* e) override;
        sat::literal mk_literal(expr* e);
        void attach_th_var(enode* n, th_solver* th, theory_var v) { m_egraph.add_th_var(n, v, th->get_id()); }
        void attach_node(euf::enode* n);
        expr_ref mk_eq(expr* e1, expr* e2);
        expr_ref mk_eq(euf::enode* n1, euf::enode* n2) { return mk_eq(n1->get_expr(), n2->get_expr()); }
        euf::enode* e_internalize(expr* e);
        euf::enode* mk_enode(expr* e, unsigned n, enode* const* args);
        void set_bool_var2expr(sat::bool_var v, expr* e) { m_var_trail.push_back(v);  m_bool_var2expr.setx(v, e, nullptr); }
        expr* bool_var2expr(sat::bool_var v) const { return m_bool_var2expr.get(v, nullptr); }
        expr_ref literal2expr(sat::literal lit) const { expr* e = bool_var2expr(lit.var()); return (e && lit.sign()) ? expr_ref(mk_not(m, e), m) : expr_ref(e, m); }
        unsigned generation() const { return m_generation; }

        sat::literal attach_lit(sat::literal lit, expr* e);
        void unhandled_function(func_decl* f);
        th_rewriter& get_rewriter() { return m_rewriter; }
        void rewrite(expr_ref& e) { m_rewriter(e); }
        bool is_shared(euf::enode* n) const;
        bool is_beta_redex(euf::enode* p, euf::enode* n) const;
        bool enable_ackerman_axioms(expr* n) const;
        bool is_fixed(euf::enode* n, expr_ref& val, sat::literal_vector& explain);

        // void add_assertion(expr* f);
        // expr_ref_vector const& get_assertions() { return m_assertions; }
        void add_clause(unsigned n, sat::literal const* lits);
        vector <sat::literal_vector> const& top_level_clauses() const { return m_top_level_clauses; }
        model_ref get_sls_model();

        // relevancy

        bool relevancy_enabled() const { return m_relevancy.enabled(); }
        void disable_relevancy(expr* e) { IF_VERBOSE(0, verbose_stream() << "disabling relevancy " << mk_pp(e, m) << "\n"); m_relevancy.set_enabled(false); }
        void add_root(unsigned n, sat::literal const* lits) { m_relevancy.add_root(n, lits); }
        void add_root(sat::literal_vector const& lits) { add_root(lits.size(), lits.data()); }
        void add_root(sat::literal lit) { add_root(1, &lit); }
        void add_root(sat::literal lit1, sat::literal lit2) { sat::literal lits[2] = { lit1, lit2, }; add_root(2, lits); }
        void add_aux(sat::literal_vector const& lits) { add_aux(lits.size(), lits.data()); }
        void add_aux(unsigned n, sat::literal const* lits) { m_relevancy.add_def(n, lits); }
        void add_aux(sat::literal a) { sat::literal lits[1] = { a }; add_aux(1, lits); }
        void add_aux(sat::literal a, sat::literal b) { sat::literal lits[2] = {a, b}; add_aux(2, lits); } 
        void add_aux(sat::literal a, sat::literal b, sat::literal c) { sat::literal lits[3] = { a, b, c }; add_aux(3, lits); }
        void mark_relevant(sat::literal lit) { m_relevancy.mark_relevant(lit); }
        bool is_relevant(enode* n) const override { return m_relevancy.is_relevant(n); }
        bool is_relevant(bool_var v) const;
        bool is_relevant(sat::literal lit) const { return is_relevant(lit.var()); }
        void relevant_eh(euf::enode* n);

        relevancy& get_relevancy() { return m_relevancy; }

        // model construction
        void save_model(model_ref& mdl);
        void update_model(model_ref& mdl, bool validate);
        obj_map<expr, enode*> const& values2root();
        void model_updated(model_ref& mdl);
        expr* node2value(enode* n) const;
        void display_validation_failure(std::ostream& out, model& mdl, enode* n);

        // diagnostics
        func_decl_ref_vector const& unhandled_functions() { return m_unhandled_functions; }

        // clause tracing
        void register_on_clause(
            void* ctx,
            user_propagator::on_clause_eh_t& on_clause);

        // user propagator
        void user_propagate_init(
            void* ctx,
            user_propagator::push_eh_t& push_eh,
            user_propagator::pop_eh_t& pop_eh,
            user_propagator::fresh_eh_t& fresh_eh);
        bool watches_fixed(enode* n) const;
        void assign_fixed(enode* n, expr* val, unsigned sz, literal const* explain);
        void assign_fixed(enode* n, expr* val, literal_vector const& explain) { assign_fixed(n, val, explain.size(), explain.data()); }
        void assign_fixed(enode* n, expr* val, literal explain) { assign_fixed(n, val, 1, &explain); }

        void user_propagate_register_final(user_propagator::final_eh_t& final_eh) {
            check_for_user_propagator();
            m_user_propagator->register_final(final_eh);
        }
        void user_propagate_register_fixed(user_propagator::fixed_eh_t& fixed_eh) {
            check_for_user_propagator();
            m_user_propagator->register_fixed(fixed_eh);
        }
        void user_propagate_register_eq(user_propagator::eq_eh_t& eq_eh) {
            check_for_user_propagator();
            m_user_propagator->register_eq(eq_eh);
        }
        void user_propagate_register_diseq(user_propagator::eq_eh_t& diseq_eh) {
            check_for_user_propagator();
            m_user_propagator->register_diseq(diseq_eh);
        }
        void user_propagate_register_created(user_propagator::created_eh_t& ceh) {
            check_for_user_propagator();
            m_user_propagator->register_created(ceh);
        }
        void user_propagate_register_decide(user_propagator::decide_eh_t& ceh) {
            check_for_user_propagator();
            m_user_propagator->register_decide(ceh);
        }
        void user_propagate_register_expr(expr* e) {
            check_for_user_propagator();
            m_user_propagator->add_expr(e);
        }

        void user_propagate_initialize_value(expr* var, expr* value);

        // solver factory
        ::solver* mk_solver() { return m_mk_solver(); }
        void set_mk_solver(std::function<::solver*(void)>& mk) { m_mk_solver = mk; }


    };

    inline std::ostream& operator<<(std::ostream& out, clause_pp const& p) {
        return p.display(out);
    }

};

inline std::ostream& operator<<(std::ostream& out, euf::solver const& s) {
    return s.display(out);
}
