/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    theory_seq.h

Abstract:

    Native theory solver for sequences.

Author:

    Nikolaj Bjorner (nbjorner) 2015-6-12

Revision History:

--*/
#pragma once

#include "ast/seq_decl_plugin.h"
#include "ast/rewriter/th_rewriter.h"
#include "ast/rewriter/seq_skolem.h"
#include "ast/rewriter/seq_eq_solver.h"
#include "ast/ast_trail.h"
#include "util/scoped_vector.h"
#include "util/scoped_ptr_vector.h"
#include "ast/rewriter/seq_rewriter.h"
#include "util/union_find.h"
#include "util/obj_ref_hashtable.h"
#include "smt/smt_theory.h"
#include "smt/smt_arith_value.h"
#include "smt/theory_seq_empty.h"
#include "smt/seq_axioms.h"
#include "smt/seq_regex.h"
#include "smt/seq_offset_eq.h"

namespace smt {

    class theory_seq : public theory, public seq::eq_solver_context {
        friend class seq_regex;

        struct assumption {
            enode* n1, *n2;
            literal lit;
            assumption(enode* n1, enode* n2): n1(n1), n2(n2), lit(null_literal) {}
            assumption(literal lit): n1(nullptr), n2(nullptr), lit(lit) {}
        };
        typedef scoped_dependency_manager<assumption> dependency_manager;
        typedef dependency_manager::dependency dependency;        

        struct expr_dep {
            expr* v;
            expr* e;
            dependency* d;
            expr_dep(expr* v, expr* e, dependency* d): v(v), e(e), d(d) {}
            expr_dep():v(nullptr), e(nullptr), d(nullptr) {}
        };
        typedef svector<expr_dep> eqdep_map_t;
        typedef union_find<theory_seq> th_union_find;

        class seq_value_proc;
        struct validate_model_proc;
        struct compare_depth;
        
        // cache to track evaluations under equalities
        class eval_cache {
            eqdep_map_t             m_map;
            expr_ref_vector         m_trail;
        public:
            eval_cache(ast_manager& m): m_trail(m) {}
            bool find(expr* v, expr_dep& r) const { 
                return v->get_id() < m_map.size() && m_map[v->get_id()].e && (r = m_map[v->get_id()], true); 
            }
            void insert(expr_dep const& r) { 
                m_trail.push_back(r.v); 
                m_trail.push_back(r.e);
                m_map.reserve(2*r.v->get_id() + 1);
                m_map[r.v->get_id()] = r;
            }
            void reset() { m_map.reset(); m_trail.reset(); }
        };
        
        // map from variables to representatives 
        // + a cache for normalization.
        class solution_map {
            enum map_update { INS, DEL };
            ast_manager&           m;
            dependency_manager&    m_dm;
            eqdep_map_t            m_map;            
            eval_cache             m_cache;
            expr_ref_vector        m_lhs, m_rhs;
            ptr_vector<dependency> m_deps;
            svector<map_update>    m_updates;
            unsigned_vector        m_limit;

            bool find(expr* v, expr_dep& r) const { 
                return v->get_id() < m_map.size() && m_map[v->get_id()].e && (r = m_map[v->get_id()], true); 
            }
            void insert(expr_dep const& r) { 
                m_map.reserve(2*r.v->get_id() + 1);                
                m_map[r.v->get_id()] = r;
            }
            void add_trail(map_update op, expr* l, expr* r, dependency* d);
        public:
            solution_map(ast_manager& m, dependency_manager& dm): 
                m(m),  m_dm(dm), m_cache(m), m_lhs(m), m_rhs(m) {}
            bool  empty() const { return m_map.empty(); }
            void  update(expr* e, expr* r, dependency* d);
            void  add_cache(expr_dep& r) { m_cache.insert(r); }
            bool  find_cache(expr* v, expr_dep& r) { return m_cache.find(v, r); }
            expr* find(expr* e, dependency*& d);
            expr* find(expr* e);
            bool  find1(expr* a, expr*& b, dependency*& dep);
            void  find_rec(expr* e, svector<expr_dep>& finds);
            bool  is_root(expr* e) const;
            void  cache(expr* e, expr* r, dependency* d);
            void  reset_cache() { m_cache.reset(); }
            void  push_scope() { m_limit.push_back(m_updates.size()); }
            void  pop_scope(unsigned num_scopes);
            void  display(std::ostream& out) const;
            eqdep_map_t::iterator begin() { return m_map.begin(); }
            eqdep_map_t::iterator end() { return m_map.end(); }
        };

        // Table of current disequalities
        class exclusion_table {
        public:
            typedef obj_pair_hashtable<expr, expr> table_t;
        protected:
            ast_manager&                      m;
            table_t                           m_table;
            expr_ref_vector                   m_lhs, m_rhs;
            unsigned_vector                   m_limit;
        public:
            exclusion_table(ast_manager& m): m(m), m_lhs(m), m_rhs(m) {}
            ~exclusion_table() { }
            bool empty() const { return m_table.empty(); }
            void update(expr* e, expr* r);
            bool contains(expr* e, expr* r) const;
            void push_scope() { m_limit.push_back(m_lhs.size()); }
            void pop_scope(unsigned num_scopes);
            void display(std::ostream& out) const;            
            table_t::iterator begin() const { return m_table.begin(); }
            table_t::iterator end() const { return m_table.end(); }
        };

        // Asserted or derived equality with dependencies
        class depeq : public seq::eq {
            unsigned         m_id;
            dependency*      m_dep;
        public:            
            depeq(unsigned id, expr_ref_vector& l, expr_ref_vector& r, dependency* d):
                eq(l, r), m_id(id), m_dep(d) {}
            dependency* dep() const { return m_dep; }
            unsigned id() const { return m_id; }
        };

        depeq mk_eqdep(expr* l, expr* r, dependency* dep) {
            expr_ref_vector ls(m), rs(m);
            m_util.str.get_concat_units(l, ls);
            m_util.str.get_concat_units(r, rs);
            return depeq(m_eq_id++, ls, rs, dep);
        }        

        depeq mk_eqdep(expr_ref_vector const& l, expr_ref_vector const& r, dependency* dep) {
            expr_ref_vector ls(m), rs(m);
            for (expr* e : l)
                m_util.str.get_concat_units(e, ls);
            for (expr* e : r)
                m_util.str.get_concat_units(e, rs);
            return depeq(m_eq_id++, ls, rs, dep);
        }        

        // equalities that are decomposed by conacatenations
        typedef std::pair<expr_ref_vector, expr_ref_vector> decomposed_eq;

        class ne {      
            expr_ref                 m_l, m_r;
            vector<decomposed_eq>    m_eqs;
            literal_vector           m_lits;
            dependency*              m_dep;
        public:
            ne(expr_ref const& l, expr_ref const& r, dependency* dep):
                m_l(l), m_r(r), m_dep(dep) {
                    expr_ref_vector ls(l.get_manager()); ls.push_back(l);
                    expr_ref_vector rs(r.get_manager()); rs.push_back(r);
                    m_eqs.push_back(std::make_pair(ls, rs));
                }

            ne(expr_ref const& _l, expr_ref const& _r, vector<decomposed_eq> const& eqs, literal_vector const& lits, dependency* dep):
                m_l(_l), m_r(_r),
                m_eqs(eqs),
                m_lits(lits),
                m_dep(dep) {
                }

            vector<decomposed_eq> const& eqs() const { return m_eqs; }
            decomposed_eq const& operator[](unsigned i) const { return m_eqs[i]; }

            literal_vector const& lits() const { return m_lits; }
            literal lits(unsigned i) const { return m_lits[i]; }
            dependency* dep() const { return m_dep; }
            expr_ref const& l() const { return m_l; }
            expr_ref const& r() const { return m_r; }
        };

        class nc {
            expr_ref                 m_contains;
            literal                  m_len_gt;
            dependency*              m_dep;
        public:
            nc(expr_ref const& c, literal len_gt, dependency* dep):
                m_contains(c), 
                m_len_gt(len_gt),
                m_dep(dep) {}

            dependency* deps() const { return m_dep; }
            expr_ref const& contains() const { return m_contains; }
            literal len_gt() const { return m_len_gt; }
        };

        class apply {
        public:
            virtual ~apply() {}
            virtual void operator()(theory_seq& th) = 0;
        };

        class replay_length_coherence : public apply {
            expr_ref m_e;
        public:
            replay_length_coherence(ast_manager& m, expr* e) : m_e(e, m) {}
            ~replay_length_coherence() override {}
            void operator()(theory_seq& th) override {
                th.check_length_coherence(m_e);
                m_e.reset();
            }
        };

        class replay_fixed_length : public apply {
            expr_ref m_e;
        public:
            replay_fixed_length(ast_manager& m, expr* e) : m_e(e, m) {}
            ~replay_fixed_length() override {}
            void operator()(theory_seq& th) override {
                th.fixed_length(m_e);
                m_e.reset();
            }
        };

        class replay_axiom : public apply {
            expr_ref m_e;
        public:
            replay_axiom(ast_manager& m, expr* e) : m_e(e, m) {}
            ~replay_axiom() override {}
            void operator()(theory_seq& th) override {
                th.enque_axiom(m_e);
                m_e.reset();
            }
        };

        class replay_unit_literal : public apply {
            expr_ref m_e;
            bool     m_sign;
        public:
            replay_unit_literal(ast_manager& m, expr* e, bool sign) : m_e(e, m), m_sign(sign) {}
            ~replay_unit_literal() override {}
            void operator()(theory_seq& th) override {
                literal lit = th.mk_literal(m_e);
                if (m_sign) lit.neg();
                th.add_axiom(lit);
                m_e.reset();
            }

        };

        class replay_is_axiom : public apply {
            expr_ref m_e;
        public:
            replay_is_axiom(ast_manager& m, expr* e) : m_e(e, m) {}
            ~replay_is_axiom() override {}
            void operator()(theory_seq& th) override {
                th.check_int_string(m_e);
                m_e.reset();
            }
        };

        class push_replay : public trail {
            theory_seq& th;
            apply* m_apply;
        public:
            push_replay(theory_seq& th, apply* app): th(th), m_apply(app) {}
            void undo() override {
                th.m_replay.push_back(m_apply);
            }
        };

        class pop_branch : public trail {
            theory_seq& th;
            unsigned k;
        public:
            pop_branch(theory_seq& th, unsigned k): th(th), k(k) {}
            void undo() override {
                th.m_branch_start.erase(k);
            }
        };


        void erase_index(unsigned idx, unsigned i);

        struct stats {
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(stats)); }
            unsigned m_num_splits;
            unsigned m_num_reductions;
            unsigned m_check_length_coherence;
            unsigned m_branch_variable;
            unsigned m_branch_nqs;
            unsigned m_solve_nqs;
            unsigned m_solve_eqs;
            unsigned m_add_axiom;
            unsigned m_extensionality;
            unsigned m_fixed_length;
            unsigned m_propagate_contains;
            unsigned m_int_string;
            unsigned m_ubv_string;
        };
        typedef hashtable<rational, rational::hash_proc, rational::eq_proc> rational_set;

        dependency_manager         m_dm;
        solution_map               m_rep;        // unification representative.
        scoped_vector<depeq>       m_eqs;        // set of current equations.
        scoped_vector<ne>          m_nqs;        // set of current disequalities.
        scoped_vector<nc>          m_ncs;        // set of non-contains constraints.
        scoped_vector<expr*>       m_lts;        // set of asserted str.<, str.<= literals
        bool                       m_lts_checked; 
        unsigned                   m_eq_id;
        th_union_find              m_find;
        seq_offset_eq              m_offset_eq;

        obj_ref_map<ast_manager, expr, bool>    m_overlap_lhs;
        obj_ref_map<ast_manager, expr, bool>    m_overlap_rhs;


        seq_factory*               m_factory;    // value factory
        exclusion_table            m_exclude;    // set of asserted disequalities.
        expr_ref_vector            m_axioms;     // list of axioms to add.
        obj_hashtable<expr>        m_axiom_set;
        unsigned                   m_axioms_head; // index of first axiom to add.
        bool                       m_incomplete;             // is the solver (clearly) incomplete for the fragment.
        expr_ref_vector            m_int_string;
        expr_ref_vector            m_ubv_string;         // list all occurrences of str.from_ubv that have been seen
        obj_hashtable<expr>        m_has_ubv_axiom;      // keep track of ubv that have been axiomatized within scope.
        obj_hashtable<expr>        m_has_length;         // is length applied
        expr_ref_vector            m_length;             // length applications themselves
        obj_map<expr, unsigned>    m_length_limit_map;   // sequences that have length limit predicates
        expr_ref_vector            m_length_limit;       // length limit predicates
        scoped_ptr_vector<apply>   m_replay;        // set of actions to replay
        model_generator* m_mg;
        th_rewriter      m_rewrite;               // rewriter that converts strings to character concats
        th_rewriter      m_str_rewrite;           // rewriter that coonverts character concats to strings
        seq_rewriter     m_seq_rewrite;
        seq_util         m_util;
        arith_util       m_autil;
        seq::skolem      m_sk;
        seq_axioms       m_ax;
        seq::eq_solver   m_eq;
        seq_regex        m_regex;
        arith_value      m_arith_value;
        trail_stack      m_trail_stack;
        stats            m_stats;
        ptr_vector<expr> m_todo, m_concat;
        expr_ref_vector  m_ls, m_rs, m_lhs, m_rhs;
        expr_ref_pair_vector m_new_eqs;

        unsigned                       m_max_unfolding_depth;
        literal                        m_max_unfolding_lit;

        expr*                          m_unhandled_expr;
        bool                           m_has_seq;
        bool                           m_new_solution;     // new solution added
        bool                           m_new_propagation;  // new propagation to core

        obj_hashtable<expr>            m_fixed;            // string variables that are fixed length.
        obj_hashtable<expr>            m_is_digit;         // expressions that have been constrained to be digits

        final_check_status final_check_eh() override;
        bool internalize_atom(app* atom, bool) override;
        bool internalize_term(app*) override;
        void internalize_eq_eh(app * atom, bool_var v) override;
        void new_eq_eh(theory_var, theory_var) override;
        void new_diseq_eh(theory_var, theory_var) override;
        void assign_eh(bool_var v, bool is_true) override;
        bool can_propagate() override;
        void propagate() override;
        void push_scope_eh() override;
        void pop_scope_eh(unsigned num_scopes) override;
        void restart_eh() override;
        void relevant_eh(app* n) override;
        bool should_research(expr_ref_vector &) override;
        void add_theory_assumptions(expr_ref_vector & assumptions) override;
        theory* mk_fresh(context* new_ctx) override { return alloc(theory_seq, *new_ctx); }
        char const * get_name() const override { return "seq"; }
        bool include_func_interp(func_decl* f) override { return m_util.str.is_nth_u(f); }
        bool is_safe_to_copy(bool_var v) const override;
        theory_var mk_var(enode* n) override;
        void apply_sort_cnstr(enode* n, sort* s) override;
        void display(std::ostream & out) const override;
        void collect_statistics(::statistics & st) const override;
        model_value_proc * mk_value(enode * n, model_generator & mg) override;
        void init_model(model_generator & mg) override;
        void finalize_model(model_generator & mg) override;
        void init_search_eh() override;
        void validate_model(model& mdl) override;

        void init_model(expr_ref_vector const& es);
        app* get_ite_value(expr* a);
        void get_ite_concat(ptr_vector<expr>& head, ptr_vector<expr>& tail);
        
        int find_fst_non_empty_idx(expr_ref_vector const& x);
        expr* find_fst_non_empty_var(expr_ref_vector const& x);
        bool has_len_offset(expr_ref_vector const& ls, expr_ref_vector const& rs, int & diff);
        
        // final check 
        bool simplify_and_solve_eqs();   // solve unitary equalities
        bool reduce_length_eq();
        bool branch_unit_variable();     // branch on XYZ = abcdef
        bool branch_binary_variable();   // branch on abcX = Ydefg 
        bool branch_variable();          // branch on 
        bool branch_ternary_variable(); // branch on XabcY = Zdefg 
        bool branch_quat_variable();     // branch on XabcY = ZdefgT
        bool len_based_split();          // split based on len offset
        bool branch_variable_mb();       // branch on a variable, model based on length
        bool branch_variable_eq();       // branch on a variable, by an alignment among variable boundaries.
        bool is_solved(); 
        bool check_length_coherence();
        bool check_length_coherence0(expr* e);
        bool check_length_coherence(expr* e);
        bool fixed_length(bool is_zero = false);
        bool fixed_length(expr* e, bool is_zero);
        bool branch_variable_eq(depeq const& e);
        bool branch_binary_variable(depeq const& e);
        bool can_align_from_lhs(expr_ref_vector const& ls, expr_ref_vector const& rs);
        bool can_align_from_rhs(expr_ref_vector const& ls, expr_ref_vector const& rs);
        bool branch_ternary_variable_rhs(depeq const& e);
        bool branch_ternary_variable_lhs(depeq const& e);
        literal mk_alignment(expr* e1, expr* e2);
        bool branch_quat_variable(depeq const& e);
        bool len_based_split(depeq const& e);
        bool is_unit_eq(expr_ref_vector const& ls, expr_ref_vector const& rs);
        bool propagate_length_coherence(expr* e);  
        bool split_lengths(dependency* dep,
                           expr_ref_vector const& ls, expr_ref_vector const& rs, 
                           vector<rational> const& ll, vector<rational> const& rl);
        bool set_empty(expr* x);
        bool is_complex(depeq const& e);
        lbool regex_are_equal(expr* r1, expr* r2);
        void add_unhandled_expr(expr* e);

        bool check_extensionality();
        bool check_contains();
        bool check_lts();
        dependency* m_eq_deps { nullptr };
        bool solve_eqs(unsigned start);
        bool solve_eq(unsigned idx);
        bool simplify_eq(expr_ref_vector& l, expr_ref_vector& r, dependency* dep);
        bool lift_ite(expr_ref_vector const& l, expr_ref_vector const& r, dependency* dep);
        obj_pair_hashtable<expr, expr> m_nth_eq2_cache;
        bool solve_nth_eq(expr_ref_vector const& ls, expr_ref_vector const& rs, dependency* dep);

        bool solve_binary_eq(expr_ref_vector const& l, expr_ref_vector const& r, dependency* dep);
        bool propagate_max_length(expr* l, expr* r, dependency* dep);

        bool get_length(expr* s, expr_ref& len, literal_vector& lits);
        bool reduce_length(expr* l, expr* r, literal_vector& lits);
        bool reduce_length_eq(expr_ref_vector const& ls, expr_ref_vector const& rs, dependency* deps);
        bool reduce_length(unsigned i, unsigned j, bool front, expr_ref_vector const& ls, expr_ref_vector const& rs, dependency* deps);

        expr_ref mk_empty(sort* s) { return expr_ref(m_util.str.mk_empty(s), m); }
        expr_ref mk_concat(unsigned n, expr*const* es) { return expr_ref(m_util.str.mk_concat(n, es, es[0]->get_sort()), m); }
        expr_ref mk_concat(unsigned n, expr*const* es, sort* s) { return expr_ref(m_util.str.mk_concat(n, es, s), m); }
        expr_ref mk_concat(expr_ref_vector const& es, sort* s) { return mk_concat(es.size(), es.data(), s); }
        expr_ref mk_concat(expr_ref_vector const& es) { SASSERT(!es.empty());  return expr_ref(m_util.str.mk_concat(es.size(), es.data(), es[0]->get_sort()), m); }
        expr_ref mk_concat(ptr_vector<expr> const& es) { SASSERT(!es.empty()); return mk_concat(es.size(), es.data(), es[0]->get_sort()); }
        expr_ref mk_concat(expr* e1, expr* e2) { return expr_ref(m_util.str.mk_concat(e1, e2), m); }
        expr_ref mk_concat(expr* e1, expr* e2, expr* e3) { return expr_ref(m_util.str.mk_concat(e1, e2, e3), m); }
        bool solve_nqs(unsigned i);
        bool solve_ne(unsigned i);
        bool solve_nc(unsigned i);
        bool check_ne_literals(unsigned idx, unsigned& num_undef_lits);
        bool propagate_ne2lit(unsigned idx);
        bool propagate_ne2eq(unsigned idx);
        bool propagate_ne2eq(unsigned idx, expr_ref_vector const& es);
        bool reduce_ne(unsigned idx);
        bool branch_nqs();
        lbool branch_nq(ne const& n);

        struct cell {
            cell*       m_parent;
            expr*       m_expr;
            dependency* m_dep;
            unsigned    m_last;
            cell(cell* p, expr* e, dependency* d): m_parent(p), m_expr(e), m_dep(d), m_last(0) {}
        };
        scoped_ptr_vector<cell> m_all_cells;
        cell* mk_cell(cell* p, expr* e, dependency* d);
        void unfold(cell* c, ptr_vector<cell>& cons);
        void display_explain(std::ostream& out, unsigned indent, expr* e);
        bool explain_eq(expr* e1, expr* e2, dependency*& dep);
        bool explain_empty(expr_ref_vector& es, dependency*& dep);

        // asserting consequences
        void linearize(dependency* dep, enode_pair_vector& eqs, literal_vector& lits) const;
        bool propagate_lit(dependency* dep, literal lit) { return propagate_lit(dep, 0, nullptr, lit); }
        bool propagate_lit(dependency* dep, unsigned n, literal const* lits, literal lit);
        bool propagate_eq(dependency* dep, enode* n1, enode* n2);
        bool propagate_eq(literal lit, expr* e1, expr* e2, bool add_to_eqs);
        bool propagate_eq(dependency* dep, literal_vector const& lits, expr* e1, expr* e2, bool add_to_eqs = true);
        bool propagate_eq(dependency* dep, expr* e1, expr* e2, bool add_to_eqs = true);
        bool propagate_eq(dependency* dep, literal lit, expr* e1, expr* e2, bool add_to_eqs = true);
        void set_conflict(dependency* dep, literal_vector const& lits = literal_vector());
        void set_conflict(enode_pair_vector const& eqs, literal_vector const& lits);

        // self-validation
        void validate_axiom(literal_vector const& lits);
        void validate_conflict(enode_pair_vector const& eqs, literal_vector const& lits);
        void validate_assign(literal lit, enode_pair_vector const& eqs, literal_vector const& lits);
        void validate_assign_eq(enode* a, enode* b, enode_pair_vector const& eqs, literal_vector const& lits);
        void validate_fmls(enode_pair_vector const& eqs, literal_vector const& lits, expr_ref_vector& fmls);
        expr_ref elim_skolem(expr* e);

        u_map<unsigned> m_branch_start;
        void insert_branch_start(unsigned k, unsigned s);
        unsigned find_branch_start(unsigned k);
        bool find_branch_candidate(unsigned& start, dependency* dep, expr_ref_vector const& ls, expr_ref_vector const& rs);
        expr_ref_vector expand_strings(expr_ref_vector const& es);
        bool can_be_equal(unsigned szl, expr* const* ls, unsigned szr, expr* const* rs) const;
        bool assume_equality(expr* l, expr* r);

        // variable solving utilities
        bool is_var(expr* b) const;
        bool add_solution(expr* l, expr* r, dependency* dep);
        bool is_unit_nth(expr* a) const;
        expr_ref mk_nth(expr* s, expr* idx);
        bool canonize(expr* e, dependency*& eqs, expr_ref& result);
        bool canonize(expr* e, expr_ref_vector& es, dependency*& eqs, bool& change);
        bool canonize(expr_ref_vector const& es, expr_ref_vector& result, dependency*& eqs, bool& change);
        ptr_vector<expr> m_expand_todo;
        bool expand(expr* e, dependency*& eqs, expr_ref& result);
        bool expand1(expr* e, dependency*& eqs, expr_ref& result);
        expr_ref try_expand(expr* e, dependency*& eqs);
        void add_dependency(dependency*& dep, enode* a, enode* b);
    
        // terms whose meaning are encoded using axioms.
        void enque_axiom(expr* e);
        void deque_axiom(expr* e);
        void add_axiom(literal l1, literal l2 = null_literal, literal l3 = null_literal, literal l4 = null_literal, literal l5 = null_literal);        
        void add_axiom(literal_vector& lits);
        
        bool has_length(expr *e) const { return m_has_length.contains(e); }
        void add_length(expr* l);
        bool add_length_to_eqc(expr* n);
        bool enforce_length(expr_ref_vector const& es, vector<rational>& len);
        void enforce_length_coherence(enode* n1, enode* n2);

        void add_length_limit(expr* s, unsigned k, bool is_searching);

        // model-check the functions that convert integers to strings and the other way.
        void add_int_string(expr* e);
        bool check_int_string();
        bool check_int_string(expr* e);
        bool branch_itos();
        bool branch_itos(expr* e);

        // functions that convert ubv to string
        void add_ubv_string(expr* e);
        bool check_ubv_string();
        bool check_ubv_string(expr* e);

        expr_ref add_elim_string_axiom(expr* n);
        void add_in_re_axiom(expr* n);
        literal mk_simplified_literal(expr* n);
        literal mk_eq_empty(expr* n, bool phase = true);
        literal mk_seq_eq(expr* a, expr* b);
        void tightest_prefix(expr* s, expr* x);
        expr_ref mk_sub(expr* a, expr* b);
        expr_ref mk_add(expr* a, expr* b);
        expr_ref mk_len(expr* s);
        dependency* mk_join(dependency* deps, literal lit);
        dependency* mk_join(dependency* deps, literal_vector const& lits);


        // arithmetic integration
        bool get_num_value(expr* s, rational& val) const;
        bool lower_bound(expr* s, rational& lo) const;
        bool lower_bound2(expr* s, rational& lo);
        bool upper_bound(expr* s, rational& hi) const;

        void mk_decompose(expr* e, expr_ref& head, expr_ref& tail);

        // unfold definitions based on length limits
        void propagate_length_limit(expr* n);

        void set_incomplete(app* term);

        void propagate_not_prefix(expr* e);
        void propagate_not_suffix(expr* e);
        void ensure_nth(literal lit, expr* s, expr* idx);
        bool canonizes(bool sign, expr* e);
        void propagate_non_empty(literal lit, expr* s);
        bool propagate_is_conc(expr* e, expr* conc);
        void propagate_step(literal lit, expr* n);
        void propagate_accept(literal lit, expr* e);
        void new_eq_eh(dependency* dep, enode* n1, enode* n2);

        // diagnostics
        std::ostream& display_equations(std::ostream& out) const;
        std::ostream& display_equation(std::ostream& out, depeq const& e) const;
        std::ostream& display_disequations(std::ostream& out) const;
        std::ostream& display_disequation(std::ostream& out, ne const& e) const;
        std::ostream& display_deps(std::ostream& out, dependency* deps) const;
        std::ostream& display_deps(std::ostream& out, literal_vector const& lits, enode_pair_vector const& eqs) const;
        std::ostream& display_deps_smt2(std::ostream& out, literal_vector const& lits, enode_pair_vector const& eqs) const;
        std::ostream& display_nc(std::ostream& out, nc const& nc) const;
        std::ostream& display_lit(std::ostream& out, literal l) const;
    public:
        theory_seq(context& ctx);
        ~theory_seq() override;

        void init() override;
        // model building
        app* mk_value(app* a);

        trail_stack& get_trail_stack() { return m_trail_stack; }
        void merge_eh(theory_var, theory_var, theory_var v1, theory_var v2) {}
        void after_merge_eh(theory_var r1, theory_var r2, theory_var v1, theory_var v2) { }
        void unmerge_eh(theory_var v1, theory_var v2) {}

        // eq_solver callbacks
        void add_consequence(bool uses_eq, expr_ref_vector const& clause) override;
        void  add_solution(expr* var, expr* term) override { SASSERT(var != term); add_solution(var, term, m_eq_deps); }
        expr* expr2rep(expr* e) override;
        bool  get_length(expr* e, rational& r) override;
    };
};


