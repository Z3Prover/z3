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

#ifndef _PDR_CONTEXT_H_
#define _PDR_CONTEXT_H_

#ifdef _CYGWIN
#undef min
#undef max
#endif
#include <deque>
#include "pdr_manager.h"
#include "dl_base.h"
#include "pdr_prop_solver.h"
#include "pdr_reachable_cache.h"
#include "pdr_quantifiers.h"

namespace datalog {
    class rule_set;
    class context;
};

namespace pdr {

    class pred_transformer;
    class model_node;
    class context;

    typedef obj_map<datalog::rule const, qinst*> qinst_map;
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
        qinst_map                    m_rule2qinst;      // map tag to quantifier instantiation.
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
        void ground_free_vars(expr* e, app_ref_vector& vars, ptr_vector<app>& aux_vars);

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
        expr*  transition() const { return m_transition; }
        expr*  initial_state() const { return m_initial_state; }
        bool   has_quantifiers() const { return !m_rule2qinst.empty(); }
        qinst* get_quantifiers(datalog::rule const* r) const { qinst* q = 0; m_rule2qinst.find(r, q); return q; }
        expr*  rule2tag(datalog::rule const* r) { return m_rule2tag.find(r); }
        unsigned get_num_levels() { return m_levels.size(); }
        expr_ref get_cover_delta(func_decl* p_orig, int level);
        void     add_cover(unsigned level, expr* property);

        std::ostream& display(std::ostream& strm) const;

        void collect_statistics(statistics& st) const;

        bool is_reachable(expr* state);
        void remove_predecessors(expr_ref_vector& literals);
        void find_predecessors(datalog::rule const& r, ptr_vector<func_decl>& predicates) const;
        void find_predecessors(model_core const& model, ptr_vector<func_decl>& preds) const;
        datalog::rule const& find_rule(model_core const& model) const;
        expr* get_transition(datalog::rule const& r) { return m_rule2transition.find(&r); }
        void  get_aux_vars(datalog::rule const& r, ptr_vector<app>& vs) { m_rule2vars.find(&r, vs); }

        bool propagate_to_next_level(unsigned level);
        void add_property(expr * lemma, unsigned lvl);  // add property 'p' to state at level.

        lbool is_reachable(model_node& n, expr_ref_vector* core);
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

    };


    // structure for counter-example search.
    class model_node {
        model_node*            m_parent;
        pred_transformer&      m_pt;
        expr_ref               m_state;
        model_ref              m_model;
        ptr_vector<model_node> m_children;
        unsigned               m_level;       
        unsigned               m_orig_level;
        unsigned               m_depth;
        bool                   m_closed;
    public:
        model_node(model_node* parent, expr_ref& state, pred_transformer& pt, unsigned level):
            m_parent(parent), m_pt(pt), m_state(state), m_model(0), 
                m_level(level), m_orig_level(level), m_depth(0), m_closed(false) {
            if (m_parent) {
                m_parent->m_children.push_back(this);
                SASSERT(m_parent->m_level == level+1);
                SASSERT(m_parent->m_level > 0);
                m_depth = m_parent->m_depth+1;
            }
        }
        void set_model(model_ref& m) { m_model = m; }
        unsigned level() const { return m_level; }
        unsigned orig_level() const { return m_orig_level; }
        unsigned depth() const { return m_depth; }
        void     increase_level() { ++m_level; }
        expr*    state() const { return m_state; }
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

        void set_closed();     
        void set_pre_closed() { m_closed = true; }
        void reset() { m_children.reset(); }

        expr_ref get_trace() const;
        void mk_instantiate(datalog::rule_ref& r0, datalog::rule_ref& r1, expr_ref_vector& binding);

        std::ostream& display(std::ostream& out, unsigned indent);
    };

    class model_search {
        bool               m_bfs;
        model_node*        m_root;
        std::deque<model_node*> m_leaves;
        vector<obj_map<expr, unsigned> > m_cache;
        
        obj_map<expr, unsigned>& cache(model_node const& n);
        void erase_children(model_node& n);
        void erase_leaf(model_node& n);
        void remove_node(model_node& n);
        void enqueue_leaf(model_node& n); // add leaf to priority queue.
    public:
        model_search(bool bfs): m_bfs(bfs), m_root(0) {}
        ~model_search();

        void reset();
        model_node* next();
        bool is_repeated(model_node& n) const;
        void add_leaf(model_node& n); // add fresh node.
        void set_leaf(model_node& n); // Set node as leaf, remove children.

        void set_root(model_node* n);
        model_node& get_root() const { return *m_root; }
        std::ostream& display(std::ostream& out) const; 
        expr_ref get_trace() const;
        proof_ref get_proof_trace(context const& ctx) const;
        void backtrack_level(bool uses_level, model_node& n);
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
    };

    class context {

        struct stats {
            unsigned m_num_nodes;
            unsigned m_max_depth;
            stats() { reset(); }
            void reset() { memset(this, 0, sizeof(*this)); }
        };
        
        front_end_params&    m_fparams;
        params_ref const&    m_params;
        ast_manager&         m;
        datalog::context*    m_context;
        quantifier_model_checker m_quantifier_inst;
        manager              m_pm;  
        decl2rel             m_rels;         // Map from relation predicate to fp-operator.       
        func_decl_ref        m_query_pred;
        pred_transformer*    m_query;
        model_search         m_search;
        lbool                m_last_result;
        unsigned             m_inductive_lvl;
        ptr_vector<core_generalizer>  m_core_generalizers;
        stats                m_stats;
        volatile bool        m_cancel;
        model_converter_ref  m_mc;
        proof_converter_ref  m_pc;
        
        // Functions used by search.
        void solve_impl();
        bool check_reachability(unsigned level);        
        void check_quantifiers();
        bool has_quantifiers() const;
        void propagate(unsigned max_prop_lvl);
        void close_node(model_node& n);
        void check_pre_closed(model_node& n);
        void expand_node(model_node& n);
        lbool expand_state(model_node& n, expr_ref_vector& cube);
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

    public:       
        
        /**
           Initial values of predicates are stored in corresponding relations in dctx.
           
           We check whether there is some reachable state of the relation checked_relation.
        */
        context(
            front_end_params&  fparams,
            params_ref const&  params,
            ast_manager&       m);

        ~context();
        
        front_end_params& get_fparams() const { return m_fparams; }
        params_ref const& get_params() const { return m_params; }
        ast_manager&      get_manager() const { return m; }
        manager&          get_pdr_manager() { return m_pm; }
        decl2rel const&   get_pred_transformers() const { return m_rels; }
        pred_transformer& get_pred_transformer(func_decl* p) const { return *m_rels.find(p); }
        datalog::context& get_context() const { SASSERT(m_context); return *m_context; }
        expr_ref          get_answer();

        bool              is_dl() const { return m_fparams.m_arith_mode == AS_DIFF_LOGIC; }


        void collect_statistics(statistics& st) const;

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

        void refine(qi& q, datalog::rule_set& rules) { m_quantifier_inst.refine(q, rules); }

        unsigned get_num_levels(func_decl* p);

        expr_ref get_cover_delta(int level, func_decl* p_orig, func_decl* p);

        void add_cover(int level, func_decl* pred, expr* property);

        void get_model(model_ref& md);

        proof_ref get_proof() const;

    };

};

#endif
