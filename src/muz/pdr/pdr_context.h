/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    pdr_context.h

Abstract:

    PDR for datalog

Author:

    Nikolaj Bjorner (nbjorner) 2011-11-20.

Revision History:

--*/

#ifndef PDR_CONTEXT_H_
#define PDR_CONTEXT_H_

#ifdef _CYGWIN
#undef min
#undef max
#endif
#include <deque>
#include "pdr_manager.h"
#include "pdr_prop_solver.h"
#include "pdr_reachable_cache.h"
#include "fixedpoint_params.hpp"


namespace datalog {
    class rule_set;
    class context;
};

namespace pdr {

    class pred_transformer;
    class model_node;
    class context;

    typedef obj_map<datalog::rule const, app_ref_vector*> rule2inst;
    typedef obj_map<func_decl, pred_transformer*> decl2rel;


    // 
    // Predicate transformer state.
    // A predicate transformer corresponds to the 
    // set of rules that have the same head predicates.
    // 
    
    class pred_transformer {

        struct stats {
            unsigned m_num_propagations;
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
        };

        typedef obj_map<datalog::rule const, expr*> rule2expr;
        typedef obj_map<datalog::rule const, ptr_vector<app> > rule2apps;

        manager&                     pm;        // pdr-manager
        ast_manager&                 m;         // manager
        context&                     ctx;
        
        func_decl_ref                m_head;    // predicate 
        func_decl_ref_vector         m_sig;     // signature
        ptr_vector<pred_transformer> m_use;     // places where 'this' is referenced.
        ptr_vector<datalog::rule>    m_rules;   // rules used to derive transformer
        prop_solver                  m_solver;  // solver context
        vector<expr_ref_vector>      m_levels;  // level formulas
        expr_ref_vector              m_invariants;      // properties that are invariant.
        obj_map<expr, unsigned>      m_prop2level;      // map property to level where it occurs.
        obj_map<expr, datalog::rule const*> m_tag2rule; // map tag predicate to rule. 
        rule2expr                    m_rule2tag;        // map rule to predicate tag.
        rule2inst                    m_rule2inst;       // map rules to instantiations of indices
        rule2expr                    m_rule2transition; // map rules to transition 
        rule2apps                    m_rule2vars;       // map rule to auxiliary variables
        expr_ref                     m_transition;      // transition relation.
        expr_ref                     m_initial_state;   // initial state.
        reachable_cache              m_reachable; 
        ptr_vector<func_decl>        m_predicates;
        stats                        m_stats;

        void init_sig();
        void ensure_level(unsigned level);
        bool add_property1(expr * lemma, unsigned lvl);  // add property 'p' to state at level lvl.
        void add_child_property(pred_transformer& child, expr* lemma, unsigned lvl); 
        void mk_assumptions(func_decl* head, expr* fml, expr_ref_vector& result);

        // Initialization
        void init_rules(decl2rel const& pts, expr_ref& init, expr_ref& transition);
        void init_rule(decl2rel const& pts, datalog::rule const& rule, expr_ref& init,                                      
                       ptr_vector<datalog::rule const>& rules, expr_ref_vector& transition);
        void init_atom(decl2rel const& pts, app * atom, app_ref_vector& var_reprs, expr_ref_vector& conj, unsigned tail_idx);

        void simplify_formulas(tactic& tac, expr_ref_vector& fmls);

        // Debugging
        bool check_filled(app_ref_vector const& v) const;
        
        void add_premises(decl2rel const& pts, unsigned lvl, datalog::rule& rule, expr_ref_vector& r);

    public:
        pred_transformer(context& ctx, manager& pm, func_decl* head);
        ~pred_transformer();

        void add_rule(datalog::rule* r) { m_rules.push_back(r); }
        void add_use(pred_transformer* pt) { if (!m_use.contains(pt)) m_use.insert(pt); }
        void initialize(decl2rel const& pts);

        func_decl* head() const { return m_head; }
        ptr_vector<datalog::rule> const& rules() const { return m_rules; }
        func_decl* sig(unsigned i) { init_sig(); return m_sig[i].get(); } // signature 
        func_decl* const* sig() { init_sig(); return m_sig.c_ptr(); }
        unsigned  sig_size() { init_sig(); return m_sig.size(); }
        expr*  transition() const { return m_transition; }
        expr*  initial_state() const { return m_initial_state; }
        expr*  rule2tag(datalog::rule const* r) { return m_rule2tag.find(r); }
        unsigned get_num_levels() { return m_levels.size(); }
        expr_ref get_cover_delta(func_decl* p_orig, int level);
        void     add_cover(unsigned level, expr* property);
        context& get_context() { return ctx; }

        std::ostream& display(std::ostream& strm) const;

        void collect_statistics(statistics& st) const;
        void reset_statistics();

        bool is_reachable(expr* state);
        void remove_predecessors(expr_ref_vector& literals);
        void find_predecessors(datalog::rule const& r, ptr_vector<func_decl>& predicates) const;
        datalog::rule const& find_rule(model_core const& model) const;
        expr* get_transition(datalog::rule const& r) { return m_rule2transition.find(&r); }
        ptr_vector<app>& get_aux_vars(datalog::rule const& r) { return m_rule2vars.find(&r); }

        bool propagate_to_next_level(unsigned level);
        void propagate_to_infinity(unsigned level);
        void add_property(expr * lemma, unsigned lvl);  // add property 'p' to state at level.

        lbool is_reachable(model_node& n, expr_ref_vector* core, bool& uses_level);
        bool is_invariant(unsigned level, expr* co_state, bool inductive, bool& assumes_level, expr_ref_vector* core = 0);
        bool check_inductive(unsigned level, expr_ref_vector& state, bool& assumes_level);

        expr_ref get_formulas(unsigned level, bool add_axioms);

        void simplify_formulas();

        expr_ref get_propagation_formula(decl2rel const& pts, unsigned level);

        manager& get_pdr_manager() const { return pm; }
        ast_manager& get_manager() const { return m; }

        void add_premises(decl2rel const& pts, unsigned lvl, expr_ref_vector& r);

        void close(expr* e);

        app_ref_vector& get_inst(datalog::rule const* r) { return *m_rule2inst.find(r);}

        void inherit_properties(pred_transformer& other);

        void ground_free_vars(expr* e, app_ref_vector& vars, ptr_vector<app>& aux_vars);

        prop_solver& get_solver() { return m_solver; }
        prop_solver const& get_solver() const { return m_solver; }

        void set_use_farkas(bool f) { get_solver().set_use_farkas(f); }
        bool get_use_farkas() const { return get_solver().get_use_farkas(); }
        class scoped_farkas {
            bool m_old;
            pred_transformer& m_p;
        public:
            scoped_farkas(pred_transformer& p, bool v): m_old(p.get_use_farkas()), m_p(p) {
                p.set_use_farkas(v);
            }
            ~scoped_farkas() { m_p.set_use_farkas(m_old); }
        };

    };


    // structure for counter-example search.
    class model_node {
        model_node*            m_parent;
        model_node*            m_next;
        model_node*            m_prev;
        pred_transformer&      m_pt;
        expr_ref               m_state;
        model_ref              m_model;
        ptr_vector<model_node> m_children;
        unsigned               m_level;       
        unsigned               m_orig_level;
        unsigned               m_depth;
        bool                   m_closed;
        datalog::rule const*   m_rule;
    public:
        model_node(model_node* parent, expr_ref& state, pred_transformer& pt, unsigned level):
            m_parent(parent), m_next(0), m_prev(0), m_pt(pt), m_state(state), m_model(0), 
            m_level(level), m_orig_level(level), m_depth(0), m_closed(false), m_rule(0) {
            model_node* p = m_parent;
            if (p) {
                p->m_children.push_back(this);
                SASSERT(p->m_level == level+1);
                SASSERT(p->m_level > 0);
                m_depth = p->m_depth+1;
                if (p && p->is_closed()) {
                    p->set_open();
                }
            }
        }
        void set_model(model_ref& m) { m_model = m; }
        unsigned level() const { return m_level; }
        unsigned orig_level() const { return m_orig_level; }
        unsigned depth() const { return m_depth; }
        void     increase_level() { ++m_level; }
        expr_ref const& state() const { return m_state; }
        ptr_vector<model_node> const& children() { return m_children; }
        pred_transformer& pt() const { return m_pt; }
        model_node* parent() const { return m_parent; }
        model* get_model_ptr() const { return m_model.get(); }
        model const&  get_model() const { return *m_model; }
        unsigned index() const;

        bool is_closed() const { return m_closed; }
        bool is_open() const { return !is_closed(); }

        bool is_1closed() {
            if (is_closed()) return true;
            if (m_children.empty()) return false;
            for (unsigned i = 0; i < m_children.size(); ++i) {
                if (m_children[i]->is_open()) return false;
            }
            return true;
        }

        void check_pre_closed();
        void set_closed();     
        void set_open();
        void set_pre_closed() { TRACE("pdr", tout << state() << "\n";); m_closed = true; }
        void reset() { m_children.reset(); }

        void set_rule(datalog::rule const* r) { m_rule = r; }
        datalog::rule* get_rule();

        void mk_instantiate(datalog::rule_ref& r0, datalog::rule_ref& r1, expr_ref_vector& binding);

        std::ostream& display(std::ostream& out, unsigned indent);

        void dequeue(model_node*& root);
        void enqueue(model_node* n);
        model_node* next() const { return m_next; }
        bool is_goal() const { return 0 != next(); }
    };

    class model_search {
        typedef ptr_vector<model_node> model_nodes;
        bool               m_bfs;
        model_node*        m_root;
        model_node*        m_goal;
        vector<obj_map<expr, model_nodes > > m_cache;
        obj_map<expr, model_nodes>& cache(model_node const& n);
        void erase_children(model_node& n, bool backtrack);
        void remove_node(model_node& n, bool backtrack);
        void enqueue_leaf(model_node* n); // add leaf to priority queue.
        void update_models();
        void set_leaf(model_node& n); // Set node as leaf, remove children.
        unsigned num_goals() const; 

    public:
        model_search(bool bfs): m_bfs(bfs), m_root(0), m_goal(0) {}
        ~model_search();

        void reset();
        model_node* next();
        void add_leaf(model_node& n); // add fresh node.
        
        void set_root(model_node* n);
        model_node& get_root() const { return *m_root; }
        std::ostream& display(std::ostream& out) const; 
        expr_ref get_trace(context const& ctx);        
        proof_ref get_proof_trace(context const& ctx);
        void backtrack_level(bool uses_level, model_node& n);
        void remove_goal(model_node& n);

        void well_formed();
    };

    struct model_exception { };
    struct inductive_exception {};


    // 'state' is unsatisfiable at 'level' with 'core'. 
    // Minimize or weaken core.
    class core_generalizer {
    protected:
        context& m_ctx;
    public:
        typedef vector<std::pair<expr_ref_vector,bool> > cores;
        core_generalizer(context& ctx): m_ctx(ctx) {}
        virtual ~core_generalizer() {}
        virtual void operator()(model_node& n, expr_ref_vector& core, bool& uses_level) = 0;
        virtual void operator()(model_node& n, expr_ref_vector const& core, bool uses_level, cores& new_cores) {
            new_cores.push_back(std::make_pair(core, uses_level));
            if (!core.empty()) {
                (*this)(n, new_cores.back().first, new_cores.back().second);
            }
        }
        virtual void collect_statistics(statistics& st) const {}
        virtual void reset_statistics() {}
    };

    class context {

        struct stats {
            unsigned m_num_nodes;
            unsigned m_max_depth;
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
        };
        
        smt_params&    m_fparams;
        fixedpoint_params const&    m_params;
        ast_manager&         m;
        datalog::context*    m_context;
        manager              m_pm;  
        decl2rel             m_rels;         // Map from relation predicate to fp-operator.       
        func_decl_ref        m_query_pred;
        pred_transformer*    m_query;
        mutable model_search m_search;
        lbool                m_last_result;
        unsigned             m_inductive_lvl;
        unsigned             m_expanded_lvl;
        ptr_vector<core_generalizer>  m_core_generalizers;
        stats                m_stats;
        volatile bool        m_cancel;
        model_converter_ref  m_mc;
        proof_converter_ref  m_pc;
        
        // Functions used by search.
        void solve_impl();
        bool check_reachability(unsigned level);        
        void propagate(unsigned max_prop_lvl);
        void close_node(model_node& n);
        void check_pre_closed(model_node& n);
        void expand_node(model_node& n);
        lbool expand_state(model_node& n, expr_ref_vector& cube, bool& uses_level);
        void create_children(model_node& n);
        expr_ref mk_sat_answer() const;
        expr_ref mk_unsat_answer() const;
        
        // Generate inductive property
        void get_level_property(unsigned lvl, expr_ref_vector& res, vector<relation_info> & rs) const;


        // Initialization
        class classifier_proc;
        void init_core_generalizers(datalog::rule_set& rules);

        bool check_invariant(unsigned lvl);
        bool check_invariant(unsigned lvl, func_decl* fn);

        void checkpoint();

        void init_rules(datalog::rule_set& rules, decl2rel& transformers);

        void simplify_formulas();

        void reset_core_generalizers();

        void validate();
        void validate_proof();
        void validate_search();
        void validate_model();

    public:       
        
        /**
           Initial values of predicates are stored in corresponding relations in dctx.
           
           We check whether there is some reachable state of the relation checked_relation.
        */
        context(
            smt_params&        fparams,
            fixedpoint_params const&  params,
            ast_manager&       m);

        ~context();
        
        smt_params&       get_fparams() const { return m_fparams; }
        fixedpoint_params const& get_params() const { return m_params; }
        ast_manager&      get_manager() const { return m; }
        manager&          get_pdr_manager() { return m_pm; }
        decl2rel const&   get_pred_transformers() const { return m_rels; }
        pred_transformer& get_pred_transformer(func_decl* p) const { return *m_rels.find(p); }
        datalog::context& get_context() const { SASSERT(m_context); return *m_context; }
        expr_ref          get_answer();

        bool              is_dl() const { return m_fparams.m_arith_mode == AS_DIFF_LOGIC; }
        bool              is_utvpi() const { return m_fparams.m_arith_mode == AS_UTVPI; }

        void collect_statistics(statistics& st) const;
        void reset_statistics();

        std::ostream& display(std::ostream& strm) const;        

        void display_certificate(std::ostream& strm) const;

        lbool solve();

        void cancel();

        void cleanup();

        void reset();

        void set_query(func_decl* q) { m_query_pred = q; }

        void set_unsat() { m_last_result = l_false; }

        void set_model_converter(model_converter_ref& mc) { m_mc = mc; }

        model_converter_ref get_model_converter() { return m_mc; }

        void set_proof_converter(proof_converter_ref& pc) { m_pc = pc; }

        void update_rules(datalog::rule_set& rules);

        void set_axioms(expr* axioms) { m_pm.set_background(axioms); }

        unsigned get_num_levels(func_decl* p);

        expr_ref get_cover_delta(int level, func_decl* p_orig, func_decl* p);

        void add_cover(int level, func_decl* pred, expr* property);

        model_ref get_model();

        proof_ref get_proof() const;

        model_node& get_root() const { return m_search.get_root(); }

    };

};

#endif
