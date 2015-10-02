/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_model_finder.cpp

Abstract:

    Model finding goodies for universally quantified formulas.

Author:

    Leonardo de Moura (leonardo) 2010-12-17.

Revision History:

--*/
#include"smt_model_finder.h"
#include"smt_context.h"
#include"ast_util.h"
#include"macro_util.h"
#include"arith_decl_plugin.h"
#include"bv_decl_plugin.h"
#include"array_decl_plugin.h"
#include"arith_simplifier_plugin.h"
#include"bv_simplifier_plugin.h"
#include"pull_quant.h"
#include"var_subst.h"
#include"backtrackable_set.h"
#include"for_each_expr.h"
#include"ast_pp.h"
#include"ast_ll_pp.h"
#include"well_sorted.h"
#include"model_pp.h"
#include"ast_smt2_pp.h"
#include"cooperate.h"
#include"tactic_exception.h"

namespace smt {

    namespace mf {

        // -----------------------------------
        //
        // Auxiliary stuff
        //
        // -----------------------------------

        // Append the new elements of v2 into v1. v2 should not be used after this operation, since it may suffer destructive updates.
        template<typename T>
        void dappend(ptr_vector<T> & v1, ptr_vector<T> & v2) {
            if (v2.empty())
                return;
            if (v1.empty()) {
                v1.swap(v2);
                return;
            }
            typename ptr_vector<T>::iterator it  = v2.begin(); 
            typename ptr_vector<T>::iterator end = v2.end(); 
            for (; it != end; ++it) {
                if (!v1.contains(*it))
                    v1.push_back(*it);
            }
            v2.finalize();
        }

        class evaluator {
        public:
            virtual expr * eval(expr * n, bool model_completion) = 0;
        };

        // -----------------------------------
        //
        // Instantiation sets
        //
        // -----------------------------------

        /**
           \brief Instantiation sets are the S_{k,j} sets in the Complete quantifier instantiation paper.
        */
        class instantiation_set {
            ast_manager &           m_manager;
            obj_map<expr, unsigned> m_elems; // and the associated generation
            obj_map<expr, expr *>   m_inv;
            expr_mark               m_visited;
        public:
            instantiation_set(ast_manager & m):m_manager(m) {}
            
            ~instantiation_set() {  
                obj_map<expr, unsigned>::iterator it  = m_elems.begin();
                obj_map<expr, unsigned>::iterator end = m_elems.end();
                for (; it != end; ++it) {
                    m_manager.dec_ref((*it).m_key);
                }
                m_elems.reset();
            }

            obj_map<expr, unsigned> const & get_elems() const { return m_elems; }

            void insert(expr * n, unsigned generation) {
                if (m_elems.contains(n) || contains_model_value(n))
                    return;
                TRACE("model_finder", tout << mk_pp(n, m_manager) << "\n";);
                m_manager.inc_ref(n);
                m_elems.insert(n, generation);
                SASSERT(!m_manager.is_model_value(n));
            }

            void remove(expr * n) {
                // We can only remove n if it is in m_elems, AND m_inv was not initialized yet.
                SASSERT(m_elems.contains(n));
                SASSERT(m_inv.empty());
                m_elems.erase(n);
                m_manager.dec_ref(n);
            }
            
            void display(std::ostream & out) const {
                obj_map<expr, unsigned>::iterator it  = m_elems.begin();
                obj_map<expr, unsigned>::iterator end = m_elems.end();
                for (; it != end; ++it) {
                    out << mk_bounded_pp((*it).m_key, m_manager) << " [" << (*it).m_value << "]\n";
                }
                out << "inverse:\n";
                obj_map<expr, expr *>::iterator it2   = m_inv.begin();
                obj_map<expr, expr *>::iterator end2  = m_inv.end();
                for (; it2 != end2; ++it2) {
                    out << mk_bounded_pp((*it2).m_key, m_manager) << " -> " << mk_bounded_pp((*it2).m_value, m_manager) << "\n";
                }
            }

            expr * get_inv(expr * v) const {
                expr * t = 0;
                m_inv.find(v, t);
                return t;
            }
            
            unsigned get_generation(expr * t) const {
                unsigned gen = 0;
                m_elems.find(t, gen);
                return gen;
            }

            void mk_inverse(evaluator & ev) {
                obj_map<expr, unsigned>::iterator it  = m_elems.begin();
                obj_map<expr, unsigned>::iterator end = m_elems.end();
                for (; it != end; ++it) {
                    expr *     t = (*it).m_key;
                    SASSERT(!contains_model_value(t));
                    unsigned gen = (*it).m_value;
                    expr * t_val = ev.eval(t, true);
                    TRACE("model_finder", tout << mk_pp(t, m_manager) << "\n";);

                    expr * old_t = 0;
                    if (m_inv.find(t_val, old_t)) {
                        unsigned old_t_gen = 0;
                        SASSERT(m_elems.contains(old_t));
                        m_elems.find(old_t, old_t_gen);
                        if (gen < old_t_gen) {
                            m_inv.insert(t_val, t);
                        }
                    }
                    else {
                        m_inv.insert(t_val, t);
                    }
                }
            }

            obj_map<expr, expr *> const & get_inv_map() const {
                return m_inv;
            }

            struct is_model_value {};
            void operator()(expr *n) {
                if (m_manager.is_model_value(n)) {
                    throw is_model_value();
                }
            }

            bool contains_model_value(expr* n) {
                if (m_manager.is_model_value(n)) {
                    return true;
                }
                if (is_app(n) && to_app(n)->get_num_args() == 0) {
                    return false;
                }
                m_visited.reset();
                try {
                    for_each_expr(*this, m_visited, n);
                }
                catch (is_model_value) {
                    return true;
                }
                return false;
            }
        };

        /**
           During model construction time, 
           we solve several constraints that impose restrictions
           on how the model for the ground formulas may be extended to
           a model to the relevant universal quantifiers.
           
           The class node and its subclasses are used to solve
           these constraints.
        */
        
        // -----------------------------------
        //
        // nodes
        //
        // -----------------------------------

        /**
           \brief Base class used to solve model construction constraints.
        */
        class node {
            unsigned            m_id;
            node *              m_find;
            unsigned            m_eqc_size;
            
            sort *              m_sort; // sort of the elements in the instantiation set.
            
            bool                m_mono_proj;     // relevant for integers & reals & bit-vectors
            bool                m_signed_proj;   // relevant for bit-vectors.
            ptr_vector<node>    m_avoid_set;
            ptr_vector<expr>    m_exceptions;
            
            instantiation_set * m_set;

            expr *              m_else;
            func_decl *         m_proj;

        public:
            node(unsigned id, sort * s):
                m_id(id),
                m_find(0),
                m_eqc_size(1),
                m_sort(s),
                m_mono_proj(false),
                m_signed_proj(false),
                m_set(0),
                m_else(0),
                m_proj(0) {
            }

            ~node() {
                if (m_set)
                    dealloc(m_set);
            }

            unsigned get_id() const { return m_id; }

            sort * get_sort() const { return m_sort; }

            bool is_root() const { return m_find == 0; }

            node * get_root() const {
                node * curr = const_cast<node*>(this);
                while (!curr->is_root()) {
                    curr = curr->m_find;
                }
                SASSERT(curr->is_root());
                return curr;
            }

            void merge(node * other) {
                node * r1 = get_root();
                node * r2 = other->get_root();
                SASSERT(r1->m_set == 0);
                SASSERT(r2->m_set == 0);
                SASSERT(r1->get_sort() == r2->get_sort());
                if (r1 == r2)
                    return;
                if (r1->m_eqc_size > r2->m_eqc_size)
                    std::swap(r1, r2);
                r1->m_find      = r2;
                r2->m_eqc_size += r1->m_eqc_size;
                if (r1->m_mono_proj)
                    r2->m_mono_proj = true;
                if (r1->m_signed_proj)
                    r2->m_signed_proj = true;
                dappend(r2->m_avoid_set,  r1->m_avoid_set);
                dappend(r2->m_exceptions, r1->m_exceptions);
            }

            void insert_avoid(node * n) {
                ptr_vector<node> & as = get_root()->m_avoid_set;
                if (!as.contains(n))
                    as.push_back(n);
            }

            void insert_exception(expr * n) {
                ptr_vector<expr> & ex = get_root()->m_exceptions;
                if (!ex.contains(n))
                    ex.push_back(n);
            }
            
            void set_mono_proj() {
                get_root()->m_mono_proj = true;
            }

            bool is_mono_proj() const {
                return get_root()->m_mono_proj;
            }

            void set_signed_proj() {
                get_root()->m_signed_proj = true;
            }

            bool is_signed_proj() const {
                return get_root()->m_signed_proj;
            }

            void mk_instantiation_set(ast_manager & m) {
                SASSERT(is_root());
                m_set = alloc(instantiation_set, m);
            }

            void insert(expr * n, unsigned generation) {
                SASSERT(is_ground(n));
                get_root()->m_set->insert(n, generation);
            }

            void display(std::ostream & out, ast_manager & m) const {
                if (is_root()) {
                    out << "root node ------\n";
                    out << "@" << m_id << " mono: " << m_mono_proj << " signed: " << m_signed_proj << ", sort: " << mk_pp(m_sort, m) << "\n";
                    out << "avoid-set: ";
                    ptr_vector<node>::const_iterator it1  = m_avoid_set.begin();
                    ptr_vector<node>::const_iterator end1 = m_avoid_set.end();
                    for (; it1 != end1; ++it1) {
                        out << "@" << (*it1)->get_root()->get_id() << " ";
                    }
                    out << "\n";
                    out << "exceptions: ";
                    ptr_vector<expr>::const_iterator it2  = m_exceptions.begin();
                    ptr_vector<expr>::const_iterator end2 = m_exceptions.end();
                    for (; it2 != end2; ++it2) {
                        out << mk_bounded_pp((*it2), m) << " ";
                    }
                    out << "\n";
                    if (m_else)
                        out << "else: " << mk_pp(m_else, m, 6) << "\n";
                    if (m_proj)
                        out << "projection: " << m_proj->get_name() << "\n";
                    if (m_set) {
                        out << "instantiation-set:\n";
                        m_set->display(out);
                    }
                    out << "----------------\n";
                }
                else {
                    out << "@" << m_id << " -> @" << get_root()->get_id() << "\n";
                }
            }

            instantiation_set const * get_instantiation_set() const { return get_root()->m_set; }

            instantiation_set * get_instantiation_set() { return get_root()->m_set; }

            ptr_vector<expr> const & get_exceptions() const { return get_root()->m_exceptions; }
            
            ptr_vector<node> const & get_avoid_set() const { return get_root()->m_avoid_set; }

            // return true if m_avoid_set.contains(this)
            bool must_avoid_itself() const {
                node * r = get_root();
                ptr_vector<node>::const_iterator it  = m_avoid_set.begin();
                ptr_vector<node>::const_iterator end = m_avoid_set.end();
                for (; it != end; ++it) {
                    if (r == (*it)->get_root())
                        return true;
                }
                return false;
            }

            void set_else(expr * e) {
                SASSERT(!is_mono_proj());
                SASSERT(get_root()->m_else == 0);
                get_root()->m_else = e;
            }
            
            expr * get_else() const { 
                return get_root()->m_else;
            }

            void set_proj(func_decl * f) {
                SASSERT(get_root()->m_proj == 0);
                get_root()->m_proj = f;
            }
            
            func_decl * get_proj() const {
                return get_root()->m_proj;
            }
        };

        typedef std::pair<ast *, unsigned> ast_idx_pair;
        typedef pair_hash<obj_ptr_hash<ast>, unsigned_hash> ast_idx_pair_hash;
        typedef map<ast_idx_pair, node *, ast_idx_pair_hash, default_eq<ast_idx_pair> > key2node;
        
        /**
           \brief Auxiliary class for processing the "Almost uninterpreted fragment" described in the paper:
           Complete instantiation for quantified SMT formulas

           The idea is to create node objects based on the information produced by the quantifier_analyzer.
        */
        class auf_solver : public evaluator {
            ast_manager &             m_manager;
            arith_simplifier_plugin * m_asimp;
            bv_simplifier_plugin *    m_bvsimp;
            ptr_vector<node>          m_nodes;
            unsigned                  m_next_node_id;
            key2node                  m_uvars;
            key2node                  m_A_f_is;

            context *                 m_context;

            // Mapping from sort to auxiliary constant. 
            // This auxiliary constant is used as a "witness" that is asserted as different from a 
            // finite number of terms. 
            // It is only safe to use this constant for infinite sorts.
            obj_map<sort, app *>      m_sort2k; 
            expr_ref_vector           m_ks; // range of m_sort2k
            
            // Support for evaluating expressions in the current model.
            proto_model *             m_model;
            obj_map<expr, expr *>     m_eval_cache[2];            
            expr_ref_vector           m_eval_cache_range;

            ptr_vector<node>          m_root_nodes;

            expr_ref_vector *         m_new_constraints;

            void reset_sort2k() {
                m_sort2k.reset();
                m_ks.reset();
            }

            void reset_eval_cache() {
                m_eval_cache[0].reset();
                m_eval_cache[1].reset();
                m_eval_cache_range.reset();
            }
            
            node * mk_node(key2node & m, ast * n, unsigned i, sort * s) {
                node * r = 0;
                ast_idx_pair k(n, i);
                if (m.find(k, r)) {
                    SASSERT(r->get_sort() == s);
                    return r;
                }
                r = alloc(node, m_next_node_id, s);
                m_next_node_id++;
                m.insert(k, r);
                m_nodes.push_back(r);
                return r;
            }

            void display_key2node(std::ostream & out, key2node const & m) const {
                key2node::iterator it  = m.begin();
                key2node::iterator end = m.end();
                for (; it != end; ++it) {
                    ast  *   a  = (*it).m_key.first;
                    unsigned i  = (*it).m_key.second;
                    node *   n  = (*it).m_value;
                    out << "#" << a->get_id() << ":" << i << " -> @" << n->get_id() << "\n";
                }
            }

            void display_A_f_is(std::ostream & out) const {
                key2node::iterator it  = m_A_f_is.begin();
                key2node::iterator end = m_A_f_is.end();
                for (; it != end; ++it) {
                    func_decl * f  = static_cast<func_decl*>((*it).m_key.first);
                    unsigned    i  = (*it).m_key.second;
                    node *      n  = (*it).m_value;
                    out << f->get_name() << ":" << i << " -> @" << n->get_id() << "\n";
                }
            }

            void flush_nodes() {
                std::for_each(m_nodes.begin(), m_nodes.end(), delete_proc<node>());
            }

        public:
            auf_solver(ast_manager & m, simplifier & s):
                m_manager(m),
                m_next_node_id(0),
                m_context(0),
                m_ks(m),
                m_model(0),
                m_eval_cache_range(m),
                m_new_constraints(0) {
                m_asimp  = static_cast<arith_simplifier_plugin*>(s.get_plugin(m.mk_family_id("arith")));
                m_bvsimp = static_cast<bv_simplifier_plugin*>(s.get_plugin(m.mk_family_id("bv")));
            }

            ~auf_solver() {
                flush_nodes();
                reset_eval_cache();
            }
        
            void set_context(context * ctx) {
                SASSERT(m_context==0);
                m_context = ctx;
            }
            
            ast_manager & get_manager() const { return m_manager; }
            
            arith_simplifier_plugin * get_arith_simp() const { return m_asimp; }

            bv_simplifier_plugin * get_bv_simp() const { return m_bvsimp; }
            
            void reset() {
                flush_nodes();
                m_nodes.reset();
                m_next_node_id = 0;
                m_uvars.reset();
                m_A_f_is.reset();
                m_root_nodes.reset();
                reset_sort2k();
            }

            void set_model(proto_model * m) {
                reset_eval_cache();
                m_model = m;
            }

            proto_model * get_model() const { 
                SASSERT(m_model);
                return m_model;
            }
            
            node * get_uvar(quantifier * q, unsigned i) { 
                SASSERT(i < q->get_num_decls());
                sort * s = q->get_decl_sort(q->get_num_decls() - i - 1);
                return mk_node(m_uvars, q, i, s); 
            }

            node * get_A_f_i(func_decl * f, unsigned i) { 
                SASSERT(i < f->get_arity());
                sort * s = f->get_domain(i);
                return mk_node(m_A_f_is, f, i, s); 
            }

            instantiation_set const * get_uvar_inst_set(quantifier * q, unsigned i) const {
                SASSERT(!has_quantifiers(q->get_expr()));
                ast_idx_pair k(q, i);
                node * r = 0;
                if (m_uvars.find(k, r))
                    return r->get_instantiation_set();
                return 0;
            }
            
            void mk_instantiation_sets() {
                ptr_vector<node>::const_iterator it  = m_nodes.begin();
                ptr_vector<node>::const_iterator end = m_nodes.end();
                for (; it != end; ++it) {
                    node * curr = *it;
                    if (curr->is_root()) {
                        curr->mk_instantiation_set(m_manager);
                    }
                }
            }

            // For each instantiation_set, reemove entries that do not evaluate to values.
            void cleanup_instantiation_sets() {
                ptr_vector<expr> to_delete;
                ptr_vector<node>::const_iterator it  = m_nodes.begin();
                ptr_vector<node>::const_iterator end = m_nodes.end();
                for (; it != end; ++it) {
                    node * curr = *it;
                    if (curr->is_root()) {
                        instantiation_set * s = curr->get_instantiation_set();
                        to_delete.reset();
                        obj_map<expr, unsigned> const & elems = s->get_elems();
                        for (obj_map<expr, unsigned>::iterator it = elems.begin(); it != elems.end(); it++) {
                            expr * n     = it->m_key;
                            expr * n_val = eval(n, true);
                            if (!n_val || !m_manager.is_value(n_val))
                                to_delete.push_back(n);
                        }
                        for (ptr_vector<expr>::iterator it = to_delete.begin(); it != to_delete.end(); it++) {
                            s->remove(*it);
                        }
                    }
                }
            }

            void display_nodes(std::ostream & out) const {
                display_key2node(out, m_uvars);
                display_A_f_is(out);                
                ptr_vector<node>::const_iterator it  = m_nodes.begin();
                ptr_vector<node>::const_iterator end = m_nodes.end();
                for (; it != end; ++it) {
                    (*it)->display(out, m_manager);
                }
            }

            virtual expr * eval(expr * n, bool model_completion) {
                expr * r = 0;
                if (m_eval_cache[model_completion].find(n, r)) {
                    return r;
                }
                expr_ref tmp(m_manager);
                if (!m_model->eval(n, tmp, model_completion)) {
                    r = 0;
                    TRACE("model_finder", tout << "eval\n" << mk_pp(n, m_manager) << "\n-----> null\n";);
                }
                else {
                    r = tmp;
                    TRACE("model_finder", tout << "eval\n" << mk_pp(n, m_manager) << "\n----->\n" << mk_pp(r, m_manager) << "\n";);
                }
                m_eval_cache[model_completion].insert(n, r);
                m_eval_cache_range.push_back(r);
                return r;
            }
        private:

            /**
               \brief Collect the interpretations of n->get_exceptions()
               and the interpretations of the m_else of nodes in n->get_avoid_set()
            */
            void collect_exceptions_values(node * n, ptr_buffer<expr> & r) {
                ptr_vector<expr> const & exceptions   = n->get_exceptions();
                ptr_vector<node> const & avoid_set    = n->get_avoid_set();
                
                ptr_vector<expr>::const_iterator it1  = exceptions.begin();
                ptr_vector<expr>::const_iterator end1 = exceptions.end();
                for (; it1 != end1; ++it1) {
                    expr * val = eval(*it1, true);
                    SASSERT(val != 0);
                    r.push_back(val);
                }
                
                ptr_vector<node>::const_iterator it2  = avoid_set.begin();
                ptr_vector<node>::const_iterator end2 = avoid_set.end();
                for (; it2 != end2; ++it2) {
                    node * n = (*it2)->get_root();
                    if (!n->is_mono_proj() && n->get_else() != 0) {
                        expr * val = eval(n->get_else(), true);
                        SASSERT(val != 0);
                        r.push_back(val);
                    }
                }
            }

            /**
               \brief Return an expr t from the instantiation set of \c n s.t. forall e in n.get_exceptions()
               eval(t) != eval(e) and forall m in n.get_avoid_set() eval(t) != eval(m.get_else())
               If there t1 and t2 satisfying this condition, break ties using the generation of them.

               Return 0 if such t does not exist.
            */
            expr * pick_instance_diff_exceptions(node * n, ptr_buffer<expr> const & ex_vals) {
                instantiation_set const *           s = n->get_instantiation_set();
                obj_map<expr, unsigned> const & elems = s->get_elems();

                expr *    t_result   = 0;
                unsigned  gen_result = UINT_MAX; 
                obj_map<expr, unsigned>::iterator it1  = elems.begin();
                obj_map<expr, unsigned>::iterator end1 = elems.end();
                for (; it1 != end1; ++it1) {
                    expr *     t = (*it1).m_key;
                    unsigned gen = (*it1).m_value;
                    expr * t_val = eval(t, true);
                    SASSERT(t_val != 0);
                    ptr_buffer<expr>::const_iterator it2  = ex_vals.begin();
                    ptr_buffer<expr>::const_iterator end2 = ex_vals.end();
                    for (; it2 != end2; ++it2) {
                        if (!m_manager.are_distinct(t_val, *it2))
                            break;
                    }
                    if (it2 == end2 && (t_result == 0 || gen < gen_result)) {
                        t_result   = t;
                        gen_result = gen;
                    }
                }
                return t_result;
            }

            bool is_infinite(sort * s) const {
                // we should not assume that uninterpreted sorts are infinite in benchmarks with quantifiers.
                return 
                    !m_manager.is_uninterp(s) &&
                    s->is_infinite();
            }

            /**
               \brief Return a fresh constant k that is used as a witness for elements that must be different from 
               a set of values.
            */
            app * get_k_for(sort * s) {
                SASSERT(is_infinite(s));
                app * r = 0;
                if (m_sort2k.find(s, r))
                    return r;
                r = m_manager.mk_fresh_const("k", s);
                m_sort2k.insert(s, r);
                m_ks.push_back(r);
                return r;
            }

            /**
               \brief Get the interpretation for k in m_model.
               If m_model does not provide an interpretation for k, then 
               create a fresh one.

               Remark: this method uses get_fresh_value, so it may fail.
            */
            expr * get_k_interp(app * k) {
                sort * s = m_manager.get_sort(k);
                SASSERT(is_infinite(s));
                func_decl * k_decl = k->get_decl();
                expr * r = m_model->get_const_interp(k_decl);
                if (r != 0)
                    return r;
                r = m_model->get_fresh_value(s);
                if (r == 0)
                    return 0;
                m_model->register_decl(k_decl, r);
                SASSERT(m_model->get_const_interp(k_decl) == r);
                TRACE("model_finder", tout << mk_pp(r, m_manager) << "\n";);
                return r;
            }

            /**
               \brief Assert k to be different from the set of exceptions.

               It invokes get_k_interp that may fail.
            */
            bool assert_k_diseq_exceptions(app * k, ptr_vector<expr> const & exceptions) {
                TRACE("assert_k_diseq_exceptions", tout << "assert_k_diseq_exceptions, " << "k: " << mk_pp(k, m_manager) << "\nexceptions:\n";
                      for (unsigned i = 0; i < exceptions.size(); i++) tout << mk_pp(exceptions[i], m_manager) << "\n";);
                expr * k_interp = get_k_interp(k);
                if (k_interp == 0)
                    return false;
                ptr_vector<expr>::const_iterator it  = exceptions.begin();
                ptr_vector<expr>::const_iterator end = exceptions.end();
                for (; it != end; ++it) {
                    expr * ex     = *it;
                    expr * ex_val = eval(ex, true);
                    if (!m_manager.are_distinct(k_interp, ex_val)) {
                        SASSERT(m_new_constraints);
                        // This constraint cannot be asserted into m_context during model construction.
                        // We must save it, and assert it during a restart.
                        m_new_constraints->push_back(m_manager.mk_not(m_manager.mk_eq(k, ex)));
                    }
                }
                return true;
            }
            
            void set_projection_else(node * n) {
                SASSERT(n->is_root());
                SASSERT(!n->is_mono_proj());
                instantiation_set const * s           = n->get_instantiation_set();
                ptr_vector<expr> const & exceptions   = n->get_exceptions();
                ptr_vector<node> const & avoid_set    = n->get_avoid_set();
                obj_map<expr, unsigned> const & elems = s->get_elems();
                SASSERT(!elems.empty());
                if (!exceptions.empty() || !avoid_set.empty()) {
                    ptr_buffer<expr> ex_vals;
                    collect_exceptions_values(n, ex_vals);
                    expr * e = pick_instance_diff_exceptions(n, ex_vals);
                    if (e != 0) {
                        n->set_else(e);
                        return;
                    }
                    sort * s = n->get_sort();
                    TRACE("model_finder", tout << "trying to create k for " << mk_pp(s, m_manager) << ", is_infinite: " << is_infinite(s) << "\n";);
                    if (is_infinite(s)) {
                        app * k = get_k_for(s);
                        if (assert_k_diseq_exceptions(k, exceptions)) {
                            n->insert(k, 0); // add k to the instantiation set
                            n->set_else(k);
                            return;
                        }
                    }
                    // TBD: add support for the else of bitvectors. 
                    // Idea: get the term t with the minimal interpreation and use t - 1.
                }
                n->set_else((*(elems.begin())).m_key);
            }

            /**
               \brief If m_mono_proj is true and n is int or bv, then for each e in n->get_exceptions(),
               we must add e-1 and e+1 to the instantiation set.
               If sort->get_sort() is real, then we do nothing and hope for the best.
            */
            void add_mono_exceptions(node * n) {
                SASSERT(n->is_mono_proj());
                sort * s = n->get_sort();
                arith_simplifier_plugin * as = get_arith_simp();
                bv_simplifier_plugin    * bs = get_bv_simp();
                bool is_int = as->is_int_sort(s);
                bool is_bv  = bs->is_bv_sort(s);
                if (!is_int && !is_bv)
                    return;
                poly_simplifier_plugin * ps = as;
                if (is_bv)
                    ps = bs;
                ps->set_curr_sort(s);
                expr_ref one(m_manager);
                one = ps->mk_one();
                ptr_vector<expr> const & exceptions  = n->get_exceptions();
                ptr_vector<expr>::const_iterator it  = exceptions.begin();
                ptr_vector<expr>::const_iterator end = exceptions.end();
                for (; it != end; ++it) {
                    expr * e = *it;
                    expr_ref e_plus_1(m_manager);
                    expr_ref e_minus_1(m_manager);
                    TRACE("mf_simp_bug", tout << "e:\n" << mk_ismt2_pp(e, m_manager) << "\none:\n" << mk_ismt2_pp(one, m_manager) << "\n";);
                    ps->mk_add(e, one, e_plus_1); 
                    ps->mk_sub(e, one, e_minus_1);
                    // Note: exceptions come from quantifiers bodies. So, they have generation 0.
                    n->insert(e_plus_1, 0);
                    n->insert(e_minus_1, 0);
                }
            }

            void get_instantiation_set_values(node * n, ptr_buffer<expr> & values) {
                instantiation_set const * s           = n->get_instantiation_set();
                obj_hashtable<expr> already_found;
                obj_map<expr, unsigned> const & elems = s->get_elems();
                obj_map<expr, unsigned>::iterator it  = elems.begin();
                obj_map<expr, unsigned>::iterator end = elems.end();
                for (; it != end; ++it) {
                    expr *     t = (*it).m_key;
                    expr * t_val = eval(t, true);
                    if (!already_found.contains(t_val)) {
                        values.push_back(t_val);
                        already_found.insert(t_val);
                    }
                }
                TRACE("model_finder_bug", tout << "values for the instantiation_set of @" << n->get_id() << "\n";
                      ptr_buffer<expr>::const_iterator it  = values.begin();
                      ptr_buffer<expr>::const_iterator end = values.end();
                      for (; it != end; ++it) {
                          expr * v = *it;
                          tout << mk_pp(v, m_manager) << "\n";
                      });
            }

            struct numeral_lt {
                poly_simplifier_plugin * m_p;
                numeral_lt(poly_simplifier_plugin * p):m_p(p) {}
                bool operator()(expr * e1, expr * e2) {
                    rational v1, v2;
                    if (m_p->is_numeral(e1, v1) && m_p->is_numeral(e2, v2)) {
                        return v1 < v2;
                    }
                    else {
                        return e1->get_id() < e2->get_id();
                    }
                }
            };

            struct signed_bv_lt {
                bv_simplifier_plugin * m_bs;
                unsigned               m_bv_size;
                signed_bv_lt(bv_simplifier_plugin * bs, unsigned sz):m_bs(bs), m_bv_size(sz) {}
                bool operator()(expr * e1, expr * e2) {
                    rational v1, v2;
                    if (m_bs->is_numeral(e1, v1) && m_bs->is_numeral(e2, v2)) {
                        v1 = m_bs->norm(v1, m_bv_size, true);
                        v2 = m_bs->norm(v2, m_bv_size, true);
                        return v1 < v2;
                    }
                    else {
                        return e1->get_id() < e2->get_id();
                    }
                }
            };

            void sort_values(node * n, ptr_buffer<expr> & values) {
                sort * s = n->get_sort();
                if (get_arith_simp()->is_arith_sort(s)) {
                    std::sort(values.begin(), values.end(), numeral_lt(get_arith_simp()));
                }
                else if (!n->is_signed_proj()) {
                    std::sort(values.begin(), values.end(), numeral_lt(get_bv_simp()));
                }
                else {
                    bv_simplifier_plugin * bs = get_bv_simp();
                    std::sort(values.begin(), values.end(), signed_bv_lt(bs, bs->get_bv_size(s)));
               }
            }

            void mk_mono_proj(node * n) {
                add_mono_exceptions(n);
                ptr_buffer<expr> values;
                get_instantiation_set_values(n, values);
                sort_values(n, values);
                sort * s = n->get_sort();
                arith_simplifier_plugin * as = get_arith_simp();
                bv_simplifier_plugin    * bs = get_bv_simp();
                bool is_arith  = as->is_arith_sort(s);
                bool is_signed = n->is_signed_proj();
                unsigned sz = values.size();
                SASSERT(sz > 0);
                func_decl * p = m_manager.mk_fresh_func_decl(1, &s, s);
                expr * pi     = values[sz - 1];
                expr_ref var(m_manager);
                var = m_manager.mk_var(0, s);
                for (unsigned i = sz - 1; i >= 1; i--) {
                    expr_ref c(m_manager);
                    if (is_arith) 
                        as->mk_lt(var, values[i], c);
                    else if (!is_signed)
                        bs->mk_ult(var, values[i], c);
                    else
                        bs->mk_slt(var, values[i], c);
                    pi = m_manager.mk_ite(c, values[i-1], pi);
                }
                func_interp * rpi = alloc(func_interp, m_manager, 1);
                rpi->set_else(pi);
                m_model->register_decl(p, rpi, true);
                n->set_proj(p);
            }

            void mk_simple_proj(node * n) {
                set_projection_else(n);
                ptr_buffer<expr> values;
                get_instantiation_set_values(n, values);
                sort * s        = n->get_sort();
                expr * else_val = eval(n->get_else(), true);
                func_decl *   p  = m_manager.mk_fresh_func_decl(1, &s, s);
                func_interp * pi = alloc(func_interp, m_manager, 1);
                pi->set_else(else_val);
                m_model->register_decl(p, pi, true);
                ptr_buffer<expr>::const_iterator it  = values.begin();
                ptr_buffer<expr>::const_iterator end = values.end();
                for (; it != end; ++it) {
                    expr * v = *it;
                    pi->insert_new_entry(&v, v);
                }
                n->set_proj(p);
            }
            
            void mk_projections() {
                ptr_vector<node>::const_iterator it  = m_root_nodes.begin();
                ptr_vector<node>::const_iterator end = m_root_nodes.end();
                for (; it != end; ++it) {
                    node * n = *it;
                    SASSERT(n->is_root());
                    if (n->is_mono_proj())
                        mk_mono_proj(n);
                    else
                        mk_simple_proj(n);
                }
            }
            
            /**
               \brief Store in r the partial functions that have A_f_i nodes.
            */
            void collect_partial_funcs(func_decl_set & r) {
                key2node::iterator it  = m_A_f_is.begin();
                key2node::iterator end = m_A_f_is.end();
                for (; it != end; ++it) {
                    func_decl * f = to_func_decl((*it).m_key.first);
                    if (!r.contains(f)) {
                        func_interp * fi = m_model->get_func_interp(f);
                        if (fi == 0) {
                            fi = alloc(func_interp, m_manager, f->get_arity());
                            m_model->register_decl(f, fi);
                            SASSERT(fi->is_partial());
                        }
                        if (fi->is_partial()) {
                            r.insert(f);
                        }
                    }
                }
            }
            
            /**
               \brief Make sorts associated with nodes that must avoid themselves finite.
               Only uninterpreted sorts are considered.
               This is a trick to be able to handle atoms of the form X = Y
               where X and Y are variables. See paper "Complete Quantifier Instantiation"
               for more details.
            */
            void mk_sorts_finite() {
                ptr_vector<node>::const_iterator it  = m_root_nodes.begin();
                ptr_vector<node>::const_iterator end = m_root_nodes.end();
                for (; it != end; ++it) {
                    node * n = *it;
                    SASSERT(n->is_root());
                    sort * s = n->get_sort();
                    if (m_manager.is_uninterp(s) && 
                        // Making all uninterpreted sorts finite.
                        // n->must_avoid_itself() && 
                        !m_model->is_finite(s)) {
                        m_model->freeze_universe(s);
                    }
                }
            }

            void add_elem_to_empty_inst_sets() {
                ptr_vector<node>::const_iterator it  = m_root_nodes.begin();
                ptr_vector<node>::const_iterator end = m_root_nodes.end();
                for (; it != end; ++it) {
                    node * n = *it;
                    SASSERT(n->is_root());
                    instantiation_set const * s           = n->get_instantiation_set();
                    obj_map<expr, unsigned> const & elems = s->get_elems();
                    if (elems.empty()) {
                        // The method get_some_value cannot be used if n->get_sort() is an uninterpreted sort or is a sort built using uninterpreted sorts 
                        // (e.g., (Array S S) where S is uninterpreted). The problem is that these sorts do not have a fixed interpretation.
                        // Moreover, a model assigns an arbitrary intepretation to these sorts using "model_values" a model value.
                        // If these module values "leak" inside the logical context, they may affect satisfiability.
                        // 
                        sort * ns = n->get_sort();
                        if (m_manager.is_fully_interp(ns))
                            n->insert(m_model->get_some_value(ns), 0);
                        else
                            n->insert(m_manager.mk_fresh_const("elem", ns), 0);
                    }
                }
            }

            /**
               \brief Store in m_root_nodes the roots from m_nodes.
             */
            void collect_root_nodes() {
                m_root_nodes.reset();
                ptr_vector<node>::const_iterator it  = m_nodes.begin();
                ptr_vector<node>::const_iterator end = m_nodes.end();
                for (; it != end; ++it) {
                    node * n = *it;
                    if (n->is_root())
                        m_root_nodes.push_back(n);
                }
            }
            
            /**
               \brief Return the projection function for f at argument i.
               Return 0, if there is none. 

               \remark This method assumes that mk_projections was already
               invoked.
               
               \remark f may have a non partial interpretation on m_model.
               This may happen because the evaluator uses model_completion.
               In the beginning of fix_model() we collected all f with
               partial interpretations. During the process of computing the
               projections we used the evalutator with model_completion,
               and it may have fixed the "else" case of some partial interpretations.
               This is ok, because in the "limit" the "else" of the interpretation
               is irrelevant after the projections are applied.
            */
            func_decl * get_f_i_proj(func_decl * f, unsigned i) {
                node * r = 0;
                ast_idx_pair k(f, i);
                if (!m_A_f_is.find(k, r))
                    return 0;
                return r->get_proj();
            }
            
            /**
               \brief Complete the interpretation of the functions that were 
               collected in the beginning of fix_model().
             */
            void complete_partial_funcs(func_decl_set const & partial_funcs) {
                func_decl_set::iterator it  = partial_funcs.begin();
                func_decl_set::iterator end = partial_funcs.end();
                for (; it != end; ++it) {
                    func_decl * f    = *it;
                    // Complete the current interpretation
                    m_model->complete_partial_func(f);
                    
                    unsigned arity   = f->get_arity();
                    func_interp * fi = m_model->get_func_interp(f);
                    if (fi->is_constant())
                        continue; // there is no point in using the projection for fi, since fi is the constant function.
                    
                    expr_ref_vector args(m_manager);
                    bool has_proj = false;
                    for (unsigned i = 0; i < arity; i++) {
                        var * v = m_manager.mk_var(i, f->get_domain(i));
                        func_decl * pi = get_f_i_proj(f, i);
                        if (pi != 0) {
                            args.push_back(m_manager.mk_app(pi, v));
                            has_proj = true;
                        }
                        else {
                            args.push_back(v);
                        }
                    }
                    if (has_proj) {
                        // f_aux will be assigned to the old interpretation of f.
                        func_decl *   f_aux  = m_manager.mk_fresh_func_decl(f->get_name(), symbol::null, arity, f->get_domain(), f->get_range());
                        func_interp * new_fi = alloc(func_interp, m_manager, arity);
                        new_fi->set_else(m_manager.mk_app(f_aux, args.size(), args.c_ptr()));
                        TRACE("model_finder", tout << "Setting new interpretation for " << f->get_name() << "\n" << 
                              mk_pp(new_fi->get_else(), m_manager) << "\n";);
                        m_model->reregister_decl(f, new_fi, f_aux);
                    }
                }
            }

            void mk_inverse(node * n) {
                SASSERT(n->is_root());
                instantiation_set * s                 = n->get_instantiation_set();
                s->mk_inverse(*this);
            }
            
            void mk_inverses() {
                ptr_vector<node>::const_iterator it  = m_root_nodes.begin();
                ptr_vector<node>::const_iterator end = m_root_nodes.end();
                for (; it != end; ++it) {
                    node * n = *it;
                    SASSERT(n->is_root());
                    mk_inverse(n);
                }
            }

        public:
            void fix_model(expr_ref_vector & new_constraints) {
                cleanup_instantiation_sets();
                m_new_constraints = &new_constraints;
                func_decl_set partial_funcs;
                collect_partial_funcs(partial_funcs);
                reset_eval_cache(); // will start using model_completion
                collect_root_nodes();
                add_elem_to_empty_inst_sets();
                mk_sorts_finite();
                mk_projections();
                mk_inverses();
                complete_partial_funcs(partial_funcs);
                TRACE("model_finder", tout << "after auf_solver fixing the model\n";
                      display_nodes(tout);
                      tout << "NEW MODEL:\n";
                      model_pp(tout, *m_model););
            }
        };


        // -----------------------------------
        //
        // qinfo class & subclasses
        //
        // -----------------------------------

        /*
           During quantifier internalizations time, we collect bits of
           information about the quantifier structure. These bits are
           instances of subclasses of qinfo.
        */
        
        /**
           \brief Generic bit of information collected when analyzing quantifiers.
           The subclasses are defined in the .cpp file.
        */
        class qinfo {
        public:
            virtual ~qinfo() {}
            virtual char const * get_kind() const = 0;
            virtual bool is_equal(qinfo const * qi) const = 0;
            virtual void display(std::ostream & out) const { out << "[" << get_kind() << "]"; }
            
            // AUF fragment solver
            virtual void process_auf(quantifier * q, auf_solver & s, context * ctx) = 0;
            virtual void populate_inst_sets(quantifier * q, auf_solver & s, context * ctx) = 0;
            // second pass... actually we may need to reach a fixpoint, but if it cannot be found
            // in two passes, the fixpoint is not finite.
            virtual void populate_inst_sets2(quantifier * q, auf_solver & s, context * ctx) {}

            // Macro/Hint support
            virtual void populate_inst_sets(quantifier * q, func_decl * mhead, ptr_vector<instantiation_set> & uvar_inst_sets, context * ctx) {}
        };

        class f_var : public qinfo {
        protected:
            func_decl * m_f;
            unsigned    m_arg_i;
            unsigned    m_var_j;
        public:
            f_var(func_decl * f, unsigned i, unsigned j):m_f(f), m_arg_i(i), m_var_j(j) {}
            virtual ~f_var() {}

            virtual char const * get_kind() const { 
                return "f_var"; 
            }
            
            virtual bool is_equal(qinfo const * qi) const {
                if (qi->get_kind() != get_kind())
                    return false;
                f_var const * other = static_cast<f_var const *>(qi);
                return m_f == other->m_f && m_arg_i == other->m_arg_i && m_var_j == other->m_var_j;
            }
            
            virtual void display(std::ostream & out) const {
                out << "(" << m_f->get_name() << ":" << m_arg_i << " -> v!" << m_var_j << ")";
            }

            virtual void process_auf(quantifier * q, auf_solver & s, context * ctx) {
                node * n1 = s.get_A_f_i(m_f, m_arg_i);
                node * n2 = s.get_uvar(q, m_var_j);
                CTRACE("model_finder", n1->get_sort() != n2->get_sort(),
                       ast_manager & m = ctx->get_manager();
                       tout << "sort bug:\n" << mk_ismt2_pp(q->get_expr(), m) << "\n" << mk_ismt2_pp(q, m) << "\n";
                       tout << "decl(0): " << q->get_decl_name(0) << "\n";
                       tout << "f: " << m_f->get_name() << " i: " << m_arg_i << "\n";
                       tout << "v: " << m_var_j << "\n";
                       n1->get_root()->display(tout, m);
                       n2->get_root()->display(tout, m);
                       tout << "f signature: ";
                       for (unsigned i = 0; i < m_f->get_arity(); i++) tout << mk_pp(m_f->get_domain(i), m) << " ";
                       tout << "-> " << mk_pp(m_f->get_range(), m) << "\n";
                       );
                                               
                n1->merge(n2);
            }

            virtual void populate_inst_sets(quantifier * q, auf_solver & s, context * ctx) {
                node * A_f_i = s.get_A_f_i(m_f, m_arg_i);
                enode_vector::const_iterator it  = ctx->begin_enodes_of(m_f);
                enode_vector::const_iterator end = ctx->end_enodes_of(m_f);
                for (; it != end; it++) {
                    enode * n = *it;
                    if (ctx->is_relevant(n)) {
                        // Remark: it is incorrect to use
                        // n->get_arg(m_arg_i)->get_root()
                        // instead of
                        // n->get_arg(m_arg_i)
                        //
                        // Due to model based quantifier instantiation, some equivalence
                        // classes are merged by accident.
                        // So, using n->get_arg(m_arg_i)->get_root(), we may miss
                        // a necessary instantiation.
                        enode * e_arg = n->get_arg(m_arg_i);
                        expr * arg    = e_arg->get_owner();
                        A_f_i->insert(arg, e_arg->get_generation());                        
                    }
                }
            }

            virtual void populate_inst_sets(quantifier * q, func_decl * mhead, ptr_vector<instantiation_set> & uvar_inst_sets, context * ctx) {
                if (m_f != mhead)
                    return;
                uvar_inst_sets.reserve(m_var_j+1, 0);
                if (uvar_inst_sets[m_var_j] == 0)
                    uvar_inst_sets[m_var_j] = alloc(instantiation_set, ctx->get_manager());
                instantiation_set * s = uvar_inst_sets[m_var_j];
                SASSERT(s != 0);
                
                enode_vector::const_iterator it  = ctx->begin_enodes_of(m_f);
                enode_vector::const_iterator end = ctx->end_enodes_of(m_f);
                for (; it != end; it++) {
                    enode * n = *it;
                    if (ctx->is_relevant(n)) {
                        enode * e_arg = n->get_arg(m_arg_i);
                        expr * arg    = e_arg->get_owner();
                        s->insert(arg, e_arg->get_generation());                        
                    }
                }
            }
        };

        class f_var_plus_offset : public f_var {
            expr_ref    m_offset;
        public:
            f_var_plus_offset(ast_manager & m, func_decl * f, unsigned i, unsigned j, expr * offset):
                f_var(f, i, j),
                m_offset(offset, m) {
            }
            virtual ~f_var_plus_offset() {}

            virtual char const * get_kind() const { 
                return "f_var_plus_offset"; 
            }
            
            virtual bool is_equal(qinfo const * qi) const {
                if (qi->get_kind() != get_kind())
                    return false;
                f_var_plus_offset const * other = static_cast<f_var_plus_offset const *>(qi);
                return m_f == other->m_f && m_arg_i == other->m_arg_i && m_var_j == other->m_var_j && m_offset.get() == other->m_offset.get();
            }
            
            virtual void display(std::ostream & out) const {
                out << "(" << m_f->get_name() << ":" << m_arg_i << " - " << 
                    mk_bounded_pp(m_offset.get(), m_offset.get_manager()) << " -> v!" << m_var_j << ")";
            }

            virtual void process_auf(quantifier * q, auf_solver & s, context * ctx) {
                // just create the nodes
                /* node * A_f_i = */ s.get_A_f_i(m_f, m_arg_i);
                /* node * S_j   = */ s.get_uvar(q, m_var_j);
            }

            virtual void populate_inst_sets(quantifier * q, auf_solver & s, context * ctx) {
                // S_j is not necessary equal to A_f_i.
                node * A_f_i =  s.get_A_f_i(m_f, m_arg_i)->get_root();
                node * S_j   =  s.get_uvar(q, m_var_j)->get_root();
                if (A_f_i == S_j) {
                    // there is no finite fixpoint... we just copy the i-th arguments of A_f_i - m_offset
                    // hope for the best...
                    arith_simplifier_plugin * as = s.get_arith_simp();
                    bv_simplifier_plugin * bs    = s.get_bv_simp();
                    node * S_j = s.get_uvar(q, m_var_j);
                    enode_vector::const_iterator it  = ctx->begin_enodes_of(m_f);
                    enode_vector::const_iterator end = ctx->end_enodes_of(m_f);
                    for (; it != end; it++) {
                        enode * n = *it;
                        if (ctx->is_relevant(n)) {
                            enode * e_arg = n->get_arg(m_arg_i);
                            expr * arg    = e_arg->get_owner();
                            expr_ref arg_minus_k(ctx->get_manager());
                            if (bs->is_bv(arg))
                                bs->mk_sub(arg, m_offset, arg_minus_k);
                            else
                                as->mk_sub(arg, m_offset, arg_minus_k);
                            S_j->insert(arg_minus_k, e_arg->get_generation());
                        }
                    }
                }
                else {
                    // A_f_i != S_j, there is hope for a finite fixpoint.
                    // So, we just populate A_f_i
                    f_var::populate_inst_sets(q, s, ctx);
                    // I must also propagate the monotonicity flag since A_f_i and S_j are not in the
                    // same equivalence class.
                    if (A_f_i->is_mono_proj())
                        S_j->set_mono_proj();
                    if (S_j->is_mono_proj())
                        A_f_i->set_mono_proj();
                }
            }

            template<bool PLUS>
            void copy_instances(node * from, node * to, auf_solver & s) {
                arith_simplifier_plugin * as = s.get_arith_simp();
                bv_simplifier_plugin * bs    = s.get_bv_simp();
                poly_simplifier_plugin * ps  = as;
                if (bs->is_bv_sort(from->get_sort()))
                    ps = bs;
                instantiation_set const * from_s        = from->get_instantiation_set();
                obj_map<expr, unsigned> const & elems_s = from_s->get_elems();
                obj_map<expr, unsigned>::iterator it  = elems_s.begin();
                obj_map<expr, unsigned>::iterator end = elems_s.end();
                for (; it != end; ++it) {
                    expr * n = (*it).m_key;
                    expr_ref n_k(m_offset.get_manager());
                    if (PLUS)
                        ps->mk_add(n, m_offset, n_k);
                    else
                        ps->mk_sub(n, m_offset, n_k);
                    to->insert(n_k, (*it).m_value);
                }
            }

            virtual void populate_inst_sets2(quantifier * q, auf_solver & s, context * ctx) {
                node * A_f_i = s.get_A_f_i(m_f, m_arg_i)->get_root();
                node * S_j   = s.get_uvar(q, m_var_j)->get_root();
                // If A_f_i == S_j, then there is no finite fixpoint, so we do nothing here.
                if (A_f_i != S_j) {
                    //  enforce
                    //  A_f_i - k \subset S_j
                    //  S_j + k   \subset A_f_i
                    copy_instances<false>(A_f_i, S_j, s);
                    copy_instances<true>(S_j, A_f_i, s);
                }
            }

            virtual void populate_inst_sets(quantifier * q, func_decl * mhead, ptr_vector<instantiation_set> & uvar_inst_sets, context * ctx) {
                // ignored when in macro
            }

        };


        /**
           \brief auf_arr is a term (pattern) of the form:
           
           FORM :=  GROUND-TERM
                |   (select FORM VAR)
                
           Store in arrays, all enodes that match the pattern     
        */
        void get_auf_arrays(app * auf_arr, context * ctx, ptr_buffer<enode> & arrays) {
            if (is_ground(auf_arr)) {
                if (ctx->e_internalized(auf_arr)) {
                    enode * e = ctx->get_enode(auf_arr);
                    if (ctx->is_relevant(e)) {
                        arrays.push_back(e);
                    }
                }
            }
            else {
                app * nested_array = to_app(auf_arr->get_arg(0));
                ptr_buffer<enode> nested_arrays;
                get_auf_arrays(nested_array, ctx, nested_arrays);
                ptr_buffer<enode>::const_iterator it  = nested_arrays.begin();
                ptr_buffer<enode>::const_iterator end = nested_arrays.end();
                for (; it != end; ++it) {
                    enode * curr = *it;
                    enode_vector::iterator it2  = curr->begin_parents();
                    enode_vector::iterator end2 = curr->end_parents();
                    for (; it2 != end2; ++it2) {
                        enode * p = *it2;
                        if (ctx->is_relevant(p) && p->get_owner()->get_decl() == auf_arr->get_decl()) {
                            arrays.push_back(p);
                        }
                    }
                }
            }
        }
        
        class select_var : public qinfo {
        protected:
            ast_manager & m_manager; 
            app *         m_select; // It must satisfy is_auf_select... see bool is_auf_select(expr * t) const
            unsigned      m_arg_i;
            unsigned      m_var_j;

            app * get_array() const { return to_app(m_select->get_arg(0)); }

            func_decl * get_array_func_decl(app * ground_array, auf_solver & s) {
                expr * ground_array_interp = s.eval(ground_array, false);
                if (ground_array_interp != 0 && s.get_model()->is_array_value(ground_array_interp))
                    return to_func_decl(to_app(ground_array_interp)->get_decl()->get_parameter(0).get_ast());
                return 0;
            }

        public:
            select_var(ast_manager & m, app * s, unsigned i, unsigned j):m_manager(m), m_select(s), m_arg_i(i), m_var_j(j) {}
            virtual ~select_var() {}

            virtual char const * get_kind() const {
                return "select_var"; 
            }
            
            virtual bool is_equal(qinfo const * qi) const {
                if (qi->get_kind() != get_kind())
                    return false;
                select_var const * other = static_cast<select_var const *>(qi);
                return m_select == other->m_select && m_arg_i == other->m_arg_i && m_var_j == other->m_var_j;
            }
            
            virtual void display(std::ostream & out) const {
                out << "(" << mk_bounded_pp(m_select, m_manager) << ":" << m_arg_i << " -> v!" << m_var_j << ")";
            }

            virtual void process_auf(quantifier * q, auf_solver & s, context * ctx) {
                ptr_buffer<enode> arrays;
                get_auf_arrays(get_array(), ctx, arrays);
                TRACE("select_var", 
                      tout << "enodes matching: "; display(tout); tout << "\n";
                      ptr_buffer<enode>::const_iterator it  = arrays.begin();
                      ptr_buffer<enode>::const_iterator end = arrays.end();
                      for (; it != end; ++it) {
                          tout << "#" << (*it)->get_owner()->get_id() << "\n" << mk_pp((*it)->get_owner(), m_manager) << "\n";
                      });
                node * n1 = s.get_uvar(q, m_var_j);                
                ptr_buffer<enode>::const_iterator it  = arrays.begin();
                ptr_buffer<enode>::const_iterator end = arrays.end();
                for (; it != end; ++it) {
                    app * ground_array = (*it)->get_owner();
                    func_decl * f = get_array_func_decl(ground_array, s);
                    if (f) {
                        SASSERT(m_arg_i >= 1);
                        node * n2 = s.get_A_f_i(f, m_arg_i - 1);
                        n1->merge(n2);
                    }
                }
            }

            virtual void populate_inst_sets(quantifier * q, auf_solver & s, context * ctx) {
                ptr_buffer<enode> arrays;
                get_auf_arrays(get_array(), ctx, arrays);
                ptr_buffer<enode>::const_iterator it  = arrays.begin();
                ptr_buffer<enode>::const_iterator end = arrays.end();
                for (; it != end; ++it) {
                    enode * curr = (*it);
                    app * ground_array = curr->get_owner();
                    func_decl * f = get_array_func_decl(ground_array, s);
                    if (f) {
                        node * A_f_i  = s.get_A_f_i(f, m_arg_i - 1);
                        enode_vector::iterator it2  = curr->begin_parents();
                        enode_vector::iterator end2 = curr->end_parents();
                        for (; it2 != end2; ++it2) {
                            enode * p = *it2; 
                            if (ctx->is_relevant(p) && p->get_owner()->get_decl() == m_select->get_decl()) {
                                SASSERT(m_arg_i < p->get_owner()->get_num_args());
                                enode * e_arg = p->get_arg(m_arg_i);
                                A_f_i->insert(e_arg->get_owner(), e_arg->get_generation());
                            }
                        }
                    }
                }
            }
        };
        
        class var_pair : public qinfo {
        protected:
            unsigned    m_var_i;
            unsigned    m_var_j;
        public:
            var_pair(unsigned i, unsigned j):m_var_i(i), m_var_j(j) {
                if (m_var_i > m_var_j)
                    std::swap(m_var_i, m_var_j);
            }
            
            virtual ~var_pair() {}

            virtual bool is_equal(qinfo const * qi) const {
                if (qi->get_kind() != get_kind())
                    return false;
                var_pair const * other = static_cast<var_pair const *>(qi);
                return m_var_i == other->m_var_i && m_var_j == other->m_var_j; 
            }
            
            virtual void display(std::ostream & out) const {
                out << "(" << get_kind() << ":v!" << m_var_i << ":v!" << m_var_j << ")";
            }

            virtual void populate_inst_sets(quantifier * q, auf_solver & s, context * ctx) {
                // do nothing
            }
        };

        class x_eq_y : public var_pair {
        public:
            x_eq_y(unsigned i, unsigned j):var_pair(i, j) {}
            virtual char const * get_kind() const { return "x_eq_y"; }

            virtual void process_auf(quantifier * q, auf_solver & s, context * ctx) {
                node * n1 = s.get_uvar(q, m_var_i);
                node * n2 = s.get_uvar(q, m_var_j);
                n1->insert_avoid(n2);
                if (n1 != n2)
                    n2->insert_avoid(n1);
            }
        };

        class x_neq_y : public var_pair {
        public:
            x_neq_y(unsigned i, unsigned j):var_pair(i, j) {}
            virtual char const * get_kind() const { return "x_neq_y"; }

            virtual void process_auf(quantifier * q, auf_solver & s, context * ctx) {
                node * n1 = s.get_uvar(q, m_var_i);
                node * n2 = s.get_uvar(q, m_var_j);
                n1->merge(n2);
            }
        };
        
        class x_leq_y : public var_pair {
        public:
            x_leq_y(unsigned i, unsigned j):var_pair(i, j) {}
            virtual char const * get_kind() const { return "x_leq_y"; }

            virtual void process_auf(quantifier * q, auf_solver & s, context * ctx) {
                node * n1 = s.get_uvar(q, m_var_i);
                node * n2 = s.get_uvar(q, m_var_j);
                n1->merge(n2);
                n1->set_mono_proj();
            }
        };

        // signed bit-vector comparison
        class x_sleq_y : public x_leq_y {
        public:
            x_sleq_y(unsigned i, unsigned j):x_leq_y(i, j) {}
            virtual char const * get_kind() const { return "x_sleq_y"; }
            
            virtual void process_auf(quantifier * q, auf_solver & s, context * ctx) {
                node * n1 = s.get_uvar(q, m_var_i);
                node * n2 = s.get_uvar(q, m_var_j);
                n1->merge(n2);
                n1->set_mono_proj();
                n1->set_signed_proj();
            }
        };
        
        class var_expr_pair : public qinfo {
        protected:
            unsigned    m_var_i;
            expr_ref    m_t;
        public:
            var_expr_pair(ast_manager & m, unsigned i, expr * t):
                m_var_i(i), m_t(t, m) {}
            ~var_expr_pair() {}
            
            virtual bool is_equal(qinfo const * qi) const {
                if (qi->get_kind() != get_kind())
                    return false;
                var_expr_pair const * other = static_cast<var_expr_pair const *>(qi);
                return m_var_i == other->m_var_i && m_t.get() == other->m_t.get();
            }
            
            virtual void display(std::ostream & out) const {
                out << "(" << get_kind() << ":v!" << m_var_i << ":" << mk_bounded_pp(m_t.get(), m_t.get_manager()) << ")";
            }
        };
        
        class x_eq_t : public var_expr_pair {
        public:
            x_eq_t(ast_manager & m, unsigned i, expr * t):
                var_expr_pair(m, i, t) {}
            virtual char const * get_kind() const { return "x_eq_t"; }

            virtual void process_auf(quantifier * q, auf_solver & s, context * ctx) {
                node * n1 = s.get_uvar(q, m_var_i);
                n1->insert_exception(m_t);
            }

            virtual void populate_inst_sets(quantifier * q, auf_solver & slv, context * ctx) {
                unsigned num_vars = q->get_num_decls();
                ast_manager & m = ctx->get_manager();
                sort * s = q->get_decl_sort(num_vars - m_var_i - 1);
                if (m.is_uninterp(s)) {
                    // For uninterpreted sorst, we add all terms in the context.
                    // See Section 4.1 in the paper "Complete Quantifier Instantiation"
                    node * S_q_i = slv.get_uvar(q, m_var_i);
                    ptr_vector<enode>::const_iterator it  = ctx->begin_enodes();
                    ptr_vector<enode>::const_iterator end = ctx->end_enodes();
                    for (; it != end; ++it) {
                        enode * n = *it;
                        if (ctx->is_relevant(n) && get_sort(n->get_owner()) == s) {
                            S_q_i->insert(n->get_owner(), n->get_generation());
                        }
                    }
                }
            }
        };

        class x_neq_t : public var_expr_pair {
        public:
            x_neq_t(ast_manager & m, unsigned i, expr * t):
                var_expr_pair(m, i, t) {}
            virtual char const * get_kind() const { return "x_neq_t"; }

            virtual void process_auf(quantifier * q, auf_solver & s, context * ctx) {
                // make sure that S_q_i is create.
                s.get_uvar(q, m_var_i);
            }

            virtual void populate_inst_sets(quantifier * q, auf_solver & s, context * ctx) {
                node * S_q_i = s.get_uvar(q, m_var_i);
                S_q_i->insert(m_t, 0);
            }
        };
        
        class x_gle_t : public var_expr_pair {
        public:
            x_gle_t(ast_manager & m, unsigned i, expr * t):
                var_expr_pair(m, i, t) {}
            virtual char const * get_kind() const { return "x_gle_t"; }

            virtual void process_auf(quantifier * q, auf_solver & s, context * ctx) {
                // make sure that S_q_i is create.
                node * n1 = s.get_uvar(q, m_var_i);
                n1->set_mono_proj();
            }

            virtual void populate_inst_sets(quantifier * q, auf_solver & s, context * ctx) {
                node * S_q_i = s.get_uvar(q, m_var_i);
                S_q_i->insert(m_t, 0);
            }
        };

        class cond_macro {
        protected:
            ast_manager &         m_manager;
            func_decl *           m_f;
            expr *                m_def;
            expr *                m_cond;
            bool                  m_ineq;
            bool                  m_satisfy_atom;
            bool                  m_hint;
            unsigned              m_weight;
        public:
            cond_macro(ast_manager & m, func_decl * f, expr * def, expr * cond, bool ineq, bool satisfy_atom, bool hint, unsigned weight):
                m_manager(m),
                m_f(f),
                m_def(def),
                m_cond(cond),
                m_ineq(ineq),
                m_satisfy_atom(satisfy_atom),
                m_hint(hint),
                m_weight(weight) {
                m_manager.inc_ref(m_def);
                m_manager.inc_ref(m_cond);
                SASSERT(!m_hint || m_cond == 0);
            }
            
            ~cond_macro() {
                m_manager.dec_ref(m_def);
                m_manager.dec_ref(m_cond);
            }

            func_decl * get_f() const { return m_f; }
            
            expr * get_def() const { return m_def; }
            
            expr * get_cond() const { return m_cond; }

            bool is_unconditional() const { return m_cond == 0 || m_manager.is_true(m_cond); }

            bool satisfy_atom() const { return m_satisfy_atom; }

            bool is_hint() const { return m_hint; }

            bool is_equal(cond_macro const * other) const {
                return m_f == other->m_f && m_def == other->m_def && m_cond == other->m_cond;
            }

            void display(std::ostream & out) const {
                out << "[" << m_f->get_name() << " -> " << mk_bounded_pp(m_def, m_manager, 6);
                if (m_hint)
                    out << " *hint*";
                else 
                    out << " when " << mk_bounded_pp(m_cond, m_manager, 6);
                out << "] weight: " << m_weight;
            }

            unsigned get_weight() const { return m_weight; }
        };

        // -----------------------------------
        //
        // quantifier_info & quantifier_analyzer
        //
        // -----------------------------------

        class quantifier_analyzer;
        
        /**
           \brief Store relevant information regarding a particular universal quantifier.
           This information is populated by quantifier_analyzer.
           The information is used to (try to) build a model that satisfy the universal quantifier
           (when it is marked as relevant in the end of the search).
        */
        class quantifier_info {
            quantifier_ref           m_flat_q; // flat version of the quantifier
            bool                     m_is_auf;
            bool                     m_has_x_eq_y;
            ptr_vector<qinfo>        m_qinfo_vect;
            func_decl_set            m_ng_decls; // declarations used in non-ground applications (basic_family operators are ignored here).
            ptr_vector<cond_macro>   m_cond_macros;
            func_decl *              m_the_one; // the macro head used to satisfy the quantifier. this is useful for model checking
            // when the quantifier is satisfied by a macro/hint, it may not be processed by the AUF solver.
            // in this case, the quantifier_info stores the instantiation sets.
            ptr_vector<instantiation_set>  * m_uvar_inst_sets;
            bool                     m_cancel;

            friend class quantifier_analyzer;

            void checkpoint() {
                cooperate("quantifier_info");
                if (m_cancel)
                    throw tactic_exception(TACTIC_CANCELED_MSG);
            }

            void insert_qinfo(qinfo * qi) {
                // I'm assuming the number of qinfo's per quantifier is small. So, the linear search is not a big deal.
                ptr_vector<qinfo>::iterator it  = m_qinfo_vect.begin();            
                ptr_vector<qinfo>::iterator end = m_qinfo_vect.end();            
                for (; it != end; ++it) {
                    checkpoint();
                    if (qi->is_equal(*it)) {
                        dealloc(qi);
                        return;
                    }
                }
                m_qinfo_vect.push_back(qi);
                TRACE("model_finder", tout << "new quantifier qinfo: "; qi->display(tout); tout << "\n";);
            }

            void insert_macro(cond_macro * m) {
                m_cond_macros.push_back(m);
            }

        public:
            typedef ptr_vector<cond_macro>::const_iterator macro_iterator;

            quantifier_info(ast_manager & m, quantifier * q):
                m_flat_q(m),
                m_is_auf(true),
                m_has_x_eq_y(false),
                m_the_one(0),
                m_uvar_inst_sets(0),
                m_cancel(false) {
                if (has_quantifiers(q->get_expr())) {
                    static bool displayed_flat_msg = false;
                    if (!displayed_flat_msg) {
                        // [Leo]: This warning message is not usefult.
                        // warning_msg("For problems containing quantifiers, the model finding capabilities of Z3 work better when the formula does not contain nested quantifiers. You can use PULL_NESTED_QUANTIFIERS=true to eliminate nested quantifiers.");
                        displayed_flat_msg = true;
                    }
                    proof_ref pr(m);
                    expr_ref  new_q(m);
                    pull_quant pull(m);
                    pull(q, new_q, pr);
                    SASSERT(is_well_sorted(m, new_q));
                    m_flat_q = to_quantifier(new_q);
                }
                else {
                    m_flat_q = q;
                }
                CTRACE("model_finder_bug", has_quantifiers(m_flat_q->get_expr()),
                       tout << mk_pp(q, m) << "\n" << mk_pp(m_flat_q, m) << "\n";);
                SASSERT(!has_quantifiers(m_flat_q->get_expr()));
            }
            
            ~quantifier_info() {
                std::for_each(m_qinfo_vect.begin(), m_qinfo_vect.end(), delete_proc<qinfo>());
                std::for_each(m_cond_macros.begin(), m_cond_macros.end(), delete_proc<cond_macro>());
                reset_the_one();
            }

            bool is_auf() const { return m_is_auf; }

            quantifier * get_flat_q() const { return m_flat_q; }
            
            bool unary_function_fragment() const {
                unsigned sz = m_ng_decls.size();
                if (sz > 1)
                    return false;
                if (sz == 0)
                    return true;
                func_decl * f = *(m_ng_decls.begin());
                return f->get_arity() == 1;
            }

            bool has_cond_macros() const {
                return !m_cond_macros.empty();
            }

            macro_iterator begin_macros() const {
                return m_cond_macros.begin();
            }

            macro_iterator end_macros() const {
                return m_cond_macros.end();
            }

            void set_the_one(func_decl * m) {
                m_the_one = m;
            }

            func_decl * get_the_one() const {
                return m_the_one;
            }

            bool contains_ng_decl(func_decl * f) const {
                return m_ng_decls.contains(f);
            }

            void display(std::ostream & out) const {
                ast_manager & m = m_flat_q.get_manager();
                out << "info for (flat) quantifier:\n" << mk_pp(m_flat_q.get(), m) << "\n";
                out << "IS_AUF: " << m_is_auf << ", has x=y: " << m_has_x_eq_y << "\n";
                out << "unary function fragment: " << unary_function_fragment() << "\n";
                out << "ng decls: ";
                func_decl_set::iterator it1  = m_ng_decls.begin();
                func_decl_set::iterator end1 = m_ng_decls.end();
                for (; it1 != end1; ++it1) {
                    out << (*it1)->get_name() << " ";
                }
                out << "\ninfo bits:\n";
                ptr_vector<qinfo>::const_iterator it2  = m_qinfo_vect.begin();
                ptr_vector<qinfo>::const_iterator end2 = m_qinfo_vect.end();
                for (; it2 != end2; ++it2) {
                    out << "  "; (*it2)->display(out); out << "\n";
                }
                out << "\nmacros:\n";
                ptr_vector<cond_macro>::const_iterator it3  = m_cond_macros.begin();
                ptr_vector<cond_macro>::const_iterator end3 = m_cond_macros.end();
                for (; it3 != end3; ++it3) {
                    out << "  "; (*it3)->display(out); out << "\n";
                }
            }

            void process_auf(auf_solver & s, context * ctx) {
                for (unsigned i = 0; i < m_flat_q->get_num_decls(); i++) {
                    // make sure a node exists for each variable.
                    s.get_uvar(m_flat_q, i);
                }
                ptr_vector<qinfo>::const_iterator it  = m_qinfo_vect.begin();
                ptr_vector<qinfo>::const_iterator end = m_qinfo_vect.end();
                for (; it != end; ++it) {
                    (*it)->process_auf(m_flat_q, s, ctx);
                }
            }

            void populate_inst_sets(auf_solver & s, context * ctx) {
                ptr_vector<qinfo>::const_iterator it  = m_qinfo_vect.begin();
                ptr_vector<qinfo>::const_iterator end = m_qinfo_vect.end();
                for (; it != end; ++it)
                    (*it)->populate_inst_sets(m_flat_q, s, ctx);
                // second pass
                it  = m_qinfo_vect.begin();
                for (; it != end; ++it)
                    (*it)->populate_inst_sets2(m_flat_q, s, ctx);
            }

            func_decl_set const & get_ng_decls() const {
                return m_ng_decls;
            }

            void populate_macro_based_inst_sets(context * ctx, evaluator & ev) {
                SASSERT(m_the_one != 0);
                if (m_uvar_inst_sets != 0)
                    return;
                m_uvar_inst_sets = alloc(ptr_vector<instantiation_set>);
                ptr_vector<qinfo>::const_iterator it  = m_qinfo_vect.begin();
                ptr_vector<qinfo>::const_iterator end = m_qinfo_vect.end();
                for (; it != end; ++it)
                    (*it)->populate_inst_sets(m_flat_q, m_the_one, *m_uvar_inst_sets, ctx);
                ptr_vector<instantiation_set>::iterator it2  = m_uvar_inst_sets->begin();
                ptr_vector<instantiation_set>::iterator end2 = m_uvar_inst_sets->end();
                for (; it2 != end2; ++it2) {
                    instantiation_set * s = *it2;
                    if (s != 0)
                        s->mk_inverse(ev);
                }
            }

            instantiation_set * get_macro_based_inst_set(unsigned vidx, context * ctx, evaluator & ev) {
                if (m_the_one == 0)
                    return 0;
                populate_macro_based_inst_sets(ctx, ev);
                return m_uvar_inst_sets->get(vidx, 0);
            }

            void reset_the_one() {
                m_the_one = 0;
                if (m_uvar_inst_sets) {
                    std::for_each(m_uvar_inst_sets->begin(), m_uvar_inst_sets->end(), delete_proc<instantiation_set>());
                    dealloc(m_uvar_inst_sets);
                    m_uvar_inst_sets = 0;
                }
            }

            void set_cancel(bool f) { m_cancel = f; }
        };
        
        /**
           \brief Functor used to traverse/analyze a quantifier and
           fill the structure quantifier_info.
        */
        class quantifier_analyzer {
            ast_manager &        m_manager;
            macro_util           m_mutil;
            array_util           m_array_util;
            arith_util           m_arith_util;
            bv_util              m_bv_util;
            bool                 m_cancel;

            quantifier_info *    m_info;

            typedef enum { POS, NEG } polarity;
            
            polarity neg(polarity p) { return p == POS ? NEG : POS; }
            
            obj_hashtable<expr>  m_pos_cache;
            obj_hashtable<expr>  m_neg_cache;
            typedef std::pair<expr *, polarity> entry;
            svector<entry>       m_ftodo;
            ptr_vector<expr>     m_ttodo;

            void insert_qinfo(qinfo * qi) {
                SASSERT(m_info);
                m_info->insert_qinfo(qi);
            }

            arith_simplifier_plugin * get_arith_simp() const { return m_mutil.get_arith_simp(); }
            bv_simplifier_plugin * get_bv_simp() const { return m_mutil.get_bv_simp(); }

            bool is_var_plus_ground(expr * n, bool & inv, var * & v, expr_ref & t) const {
                return get_arith_simp()->is_var_plus_ground(n, inv, v, t) || get_bv_simp()->is_var_plus_ground(n, inv, v, t);
            }

            bool is_var_plus_ground(expr * n, var * & v, expr_ref & t) {
                bool inv;
                TRACE("is_var_plus_ground", tout << mk_pp(n, m_manager) << "\n";
                      tout << "is_var_plus_ground: " << is_var_plus_ground(n, inv, v, t) << "\n";
                      tout << "inv: " << inv << "\n";);
                return is_var_plus_ground(n, inv, v, t) && !inv;
            }

            bool is_add(expr * n) const {
                return m_mutil.is_add(n);
            }

            bool is_zero(expr * n) const {
                if (get_bv_simp()->is_bv(n))
                    return get_bv_simp()->is_zero_safe(n);
                else 
                    return get_arith_simp()->is_zero_safe(n);
            }

            bool is_times_minus_one(expr * n, expr * & arg) const {
                return m_mutil.is_times_minus_one(n, arg);
            }

            bool is_le(expr * n) const { 
                return m_mutil.is_le(n);
            }
            
            bool is_le_ge(expr * n) const {
                return m_mutil.is_le_ge(n);
            }

            bool is_signed_le(expr * n) const { 
                return m_bv_util.is_bv_sle(n); 
            }
            
            expr * mk_one(sort * s) { 
                return m_bv_util.is_bv_sort(s) ? m_bv_util.mk_numeral(rational(1), s) : m_arith_util.mk_numeral(rational(1), s); 
            }
            
            void mk_sub(expr * t1, expr * t2, expr_ref & r) const {
                m_mutil.mk_sub(t1, t2, r);
            }

            void mk_add(expr * t1, expr * t2, expr_ref & r) const {
                m_mutil.mk_add(t1, t2, r);
            }

            bool is_var_and_ground(expr * lhs, expr * rhs, var * & v, expr_ref & t, bool & inv) const {
                inv = false; // true if invert the sign
                TRACE("is_var_and_ground", tout << "is_var_and_ground: " << mk_ismt2_pp(lhs, m_manager) << " " << mk_ismt2_pp(rhs, m_manager) << "\n";);
                if (is_var(lhs) && is_ground(rhs)) {
                    v = to_var(lhs);
                    t = rhs;
                    TRACE("is_var_and_ground", tout << "var and ground\n";);
                    return true;
                }
                else if (is_var(rhs) && is_ground(lhs)) {
                    v = to_var(rhs);
                    t = lhs;
                    TRACE("is_var_and_ground", tout << "ground and var\n";);
                    return true;
                }
                else {
                    expr_ref tmp(m_manager);
                    if (is_var_plus_ground(lhs, inv, v, tmp) && is_ground(rhs)) {
                        if (inv)
                            mk_sub(tmp, rhs, t);
                        else
                            mk_sub(rhs, tmp, t);
                        return true;
                    }
                    if (is_var_plus_ground(rhs, inv, v, tmp) && is_ground(lhs)) {
                        if (inv)
                            mk_sub(tmp, lhs, t);
                        else
                            mk_sub(lhs, tmp, t);
                        return true;
                    }
                }
                return false;
            }

            bool is_var_and_ground(expr * lhs, expr * rhs, var * & v, expr_ref & t) const {
                bool inv;
                return is_var_and_ground(lhs, rhs, v, t, inv);
            }
            
            bool is_x_eq_t_atom(expr * n, var * & v, expr_ref & t) const {
                if (!is_app(n))
                    return false;
                if (m_manager.is_eq(n))
                    return is_var_and_ground(to_app(n)->get_arg(0), to_app(n)->get_arg(1), v, t);
                return false;
            }

            bool is_var_minus_var(expr * n, var * & v1, var * & v2) const {
                if (!is_add(n))
                    return false;
                expr * arg1 = to_app(n)->get_arg(0);
                expr * arg2 = to_app(n)->get_arg(1);
                if (!is_var(arg1))
                    std::swap(arg1, arg2);
                if (!is_var(arg1))
                    return false;
                expr * arg2_2;
                if (!is_times_minus_one(arg2, arg2_2))
                    return false;
                if (!is_var(arg2_2))
                    return false;
                v1 = to_var(arg1);
                v2 = to_var(arg2_2);
                return true;
            }

            bool is_var_and_var(expr * lhs, expr * rhs, var * & v1, var * & v2) const {
                if (is_var(lhs) && is_var(rhs)) {
                    v1 = to_var(lhs);
                    v2 = to_var(rhs);
                    return true;
                }
                return 
                    (is_var_minus_var(lhs, v1, v2) && is_zero(rhs)) ||
                    (is_var_minus_var(rhs, v1, v2) && is_zero(lhs));
            }

            bool is_x_eq_y_atom(expr * n, var * & v1, var * & v2) const {
                return m_manager.is_eq(n) && is_var_and_var(to_app(n)->get_arg(0), to_app(n)->get_arg(1), v1, v2);
            }

            bool is_x_gle_y_atom(expr * n, var * & v1, var * & v2) const {
                return is_le_ge(n) && is_var_and_var(to_app(n)->get_arg(0), to_app(n)->get_arg(1), v1, v2);
            }

            bool is_x_gle_t_atom(expr * atom, bool sign, var * & v, expr_ref & t) {
                if (!is_app(atom))
                    return false;
                if (sign) {
                    bool r = is_le_ge(atom) && is_var_and_ground(to_app(atom)->get_arg(0), to_app(atom)->get_arg(1), v, t);
                    CTRACE("is_x_gle_t", r, tout << "is_x_gle_t: " << mk_ismt2_pp(atom, m_manager) << "\n--->\n" 
                           << mk_ismt2_pp(v, m_manager) << " " << mk_ismt2_pp(t, m_manager) << "\n";
                           tout << "sign: " << sign << "\n";);
                    return r;
                }
                else {
                    if (is_le_ge(atom)) {
                        expr_ref tmp(m_manager);
                        bool le = is_le(atom);
                        bool inv   = false;
                        if (is_var_and_ground(to_app(atom)->get_arg(0), to_app(atom)->get_arg(1), v, tmp, inv)) {
                            if (inv)
                                le = !le;
                            sort * s = m_manager.get_sort(tmp);
                            expr_ref one(m_manager);
                            one = mk_one(s);
                            if (le)
                                mk_add(tmp, one, t);
                            else
                                mk_sub(tmp, one, t);
                            TRACE("is_x_gle_t", tout << "is_x_gle_t: " << mk_ismt2_pp(atom, m_manager) << "\n--->\n" 
                                  << mk_ismt2_pp(v, m_manager) << " " << mk_ismt2_pp(t, m_manager) << "\n";
                                  tout << "sign: " << sign << "\n";);
                            return true;
                        }
                    }
                    return false;
                }
            }

            void reset_cache() {
                m_pos_cache.reset();
                m_neg_cache.reset();
            }
            
            obj_hashtable<expr> & get_cache(polarity pol) { 
                return pol == POS ? m_pos_cache : m_neg_cache; 
            }

            void visit_formula(expr * n, polarity pol) {
                if (is_ground(n))
                    return; // ground terms do not need to be visited.
                obj_hashtable<expr> & c = get_cache(pol);
                if (!c.contains(n)) { 
                    m_ftodo.push_back(entry(n, pol));  
                    c.insert(n);
                } 
            }

            void visit_term(expr * n) {
                // ground terms do not need to be visited.
                if (!is_ground(n) && !m_pos_cache.contains(n)) {
                    m_ttodo.push_back(n);
                    m_pos_cache.insert(n);
                }
            }
            
            /**
               \brief Process unintrepreted applications.
            */
            void process_u_app(app * t) {
                unsigned num_args = t->get_num_args();
                for (unsigned i = 0; i < num_args; i++) {
                    expr * arg = t->get_arg(i);
                    if (is_var(arg)) {
                        SASSERT(t->get_decl()->get_domain(i) == to_var(arg)->get_sort());
                        insert_qinfo(alloc(f_var, t->get_decl(), i, to_var(arg)->get_idx()));
                        continue;
                    }
                    
                    var * v;
                    expr_ref k(m_manager);
                    if (is_var_plus_ground(arg, v, k)) {
                        insert_qinfo(alloc(f_var_plus_offset, m_manager, t->get_decl(), i, v->get_idx(), k.get()));
                        continue;
                    }
                    
                    visit_term(arg);
                }
            }


            /**
               \brief A term \c t is said to be a auf_select if
               it is of ther form
               
               (select a i) Where:
               
               where a is ground or is_auf_select(a) == true
               and the indices are ground terms or variables.
            */
            bool is_auf_select(expr * t) const {
                if (!m_array_util.is_select(t))
                    return false;
                expr * a = to_app(t)->get_arg(0);
                if (!is_ground(a) && !is_auf_select(a))
                    return false;
                unsigned num_args = to_app(t)->get_num_args();
                for (unsigned i = 1; i < num_args; i++) {
                    expr * arg = to_app(t)->get_arg(i);
                    if (!is_ground(arg) && !is_var(arg))
                        return false;
                }
                return true;
            }

            /**
               \brief Process intrepreted applications.
            */
            void process_i_app(app * t) {
                if (is_auf_select(t)) {
                    unsigned num_args = t->get_num_args();
                    app * array = to_app(t->get_arg(0));
                    visit_term(array); // array may be a nested array.
                    for (unsigned i = 1; i < num_args; i++) {
                        expr * arg = t->get_arg(i);
                        if (is_var(arg)) {
                            insert_qinfo(alloc(select_var, m_manager, t, i, to_var(arg)->get_idx()));
                        }
                        else {
                            SASSERT(is_ground(arg));
                        }
                    }
                }
                else {
                    unsigned num_args = t->get_num_args();
                    for (unsigned i = 0; i < num_args; i++)
                        visit_term(t->get_arg(i));
                }
            }

            void process_app(app * t) {
                SASSERT(!is_ground(t));
                
                if (t->get_family_id() != m_manager.get_basic_family_id()) {
                    m_info->m_ng_decls.insert(t->get_decl());
                }
                
                if (is_uninterp(t)) {
                    process_u_app(t);
                }
                else {
                    process_i_app(t);
                }
            }
            
            void process_terms_on_stack() {
                while (!m_ttodo.empty()) {
                    expr * curr = m_ttodo.back();
                    m_ttodo.pop_back();
                    
                    if (m_manager.is_bool(curr)) {
                        // formula nested in a term.
                        visit_formula(curr, POS);
                        visit_formula(curr, NEG);
                        continue;
                    }
                    
                    if (is_app(curr)) {
                        process_app(to_app(curr));
                    }
                    else if (is_var(curr)) {
                        m_info->m_is_auf = false; // unexpected occurrence of variable.
                    }
                    else {
                        SASSERT(is_quantifier(curr)); // no nested quantifiers
                        UNREACHABLE();
                    }
                }
            }

            void process_literal(expr * atom, bool sign) {
                CTRACE("model_finder_bug", is_ground(atom), tout << mk_pp(atom, m_manager) << "\n";);
                SASSERT(!is_ground(atom));
                SASSERT(m_manager.is_bool(atom));
                
                if (is_var(atom)) {
                    if (sign) {
                        // atom (not X) can be viewed as X != true
                        insert_qinfo(alloc(x_neq_t, m_manager, to_var(atom)->get_idx(), m_manager.mk_true()));
                    }
                    else {
                        // atom X can be viewed as X != false
                        insert_qinfo(alloc(x_neq_t, m_manager, to_var(atom)->get_idx(), m_manager.mk_false()));
                    }
                    return;
                }
                
                if (is_app(atom)) {
                    var * v, * v1, * v2;
                    expr_ref t(m_manager);
                    if (is_x_eq_t_atom(atom, v, t)) {
                        if (sign)
                            insert_qinfo(alloc(x_neq_t, m_manager, v->get_idx(), t));
                        else
                            insert_qinfo(alloc(x_eq_t, m_manager, v->get_idx(), t));
                    }
                    else if (is_x_eq_y_atom(atom, v1, v2)) {
                        if (sign)
                            insert_qinfo(alloc(x_neq_y, v1->get_idx(), v2->get_idx()));
                        else {
                            m_info->m_has_x_eq_y = true; // this atom is in the fringe of AUF
                            insert_qinfo(alloc(x_eq_y, v1->get_idx(), v2->get_idx()));
                        }
                    }
                    else if (sign && is_x_gle_y_atom(atom, v1, v2)) {
                        if (is_signed_le(atom))
                            insert_qinfo(alloc(x_sleq_y, v1->get_idx(), v2->get_idx()));
                        else
                            insert_qinfo(alloc(x_leq_y, v1->get_idx(), v2->get_idx()));
                    }
                    else if (is_x_gle_t_atom(atom, sign, v, t)) {
                        insert_qinfo(alloc(x_gle_t, m_manager, v->get_idx(), t));
                    }
                    else {
                        process_app(to_app(atom));
                    }
                    return;
                }
                
                SASSERT(is_quantifier(atom));
                UNREACHABLE();
            }

            void process_literal(expr * atom, polarity pol) { 
                process_literal(atom, pol == NEG); 
            }
            
            void process_or(app * n, polarity p) {
                unsigned num_args = n->get_num_args();
                for (unsigned i = 0; i < num_args; i++) 
                    visit_formula(n->get_arg(i), p);
            }

            void process_ite(app * n, polarity p) {
                visit_formula(n->get_arg(0), p);
                visit_formula(n->get_arg(0), neg(p));
                visit_formula(n->get_arg(1), p);
                visit_formula(n->get_arg(2), p);
            }

            void process_iff(app * n) {
                visit_formula(n->get_arg(0), POS);
                visit_formula(n->get_arg(0), NEG);
                visit_formula(n->get_arg(1), POS);
                visit_formula(n->get_arg(1), NEG);
            }

            void checkpoint() {
                cooperate("quantifier_analyzer");
                if (m_cancel)
                    throw tactic_exception(TACTIC_CANCELED_MSG);
            }
            
            void process_formulas_on_stack() {
                while (!m_ftodo.empty()) {
                    checkpoint();
                    entry & e = m_ftodo.back();
                    expr * curr  = e.first;
                    polarity pol = e.second;
                    m_ftodo.pop_back();
                    if (is_app(curr)) {
                        if (to_app(curr)->get_family_id() == m_manager.get_basic_family_id() && m_manager.is_bool(curr)) {
                            switch (static_cast<basic_op_kind>(to_app(curr)->get_decl_kind())) {
                            case OP_AND:
                            case OP_IMPLIES:
                            case OP_XOR:
                                UNREACHABLE(); // simplifier eliminated ANDs, IMPLIEs, and XORs
                                break;
                            case OP_OR:
                                process_or(to_app(curr), pol);
                                break;
                            case OP_NOT:
                                visit_formula(to_app(curr)->get_arg(0), neg(pol));
                                break;
                            case OP_ITE:
                                process_ite(to_app(curr), pol);
                                break;
                            case OP_IFF:
                                process_iff(to_app(curr));
                                break;
                            case OP_EQ:
                                if (m_manager.is_bool(to_app(curr)->get_arg(0))) {
                                    process_iff(to_app(curr));
                                }
                                else {
                                    process_literal(curr, pol);
                                }
                                break;
                            default:
                                process_literal(curr, pol);
                                break;
                            }
                        }
                        else {
                            process_literal(curr, pol);
                        }
                    }
                    else if (is_var(curr)) {
                        SASSERT(m_manager.is_bool(curr));
                        process_literal(curr, pol);
                    }
                    else {
                        SASSERT(is_quantifier(curr));
                        UNREACHABLE(); // can't happen, the quantifier is supposed to be flat.
                    }
                }
            }

            void process_formula(expr * n) {
                SASSERT(m_manager.is_bool(n));
                visit_formula(n, POS);
            }
            
            void process_clause(expr * cls) {
                SASSERT(is_clause(m_manager, cls));
                unsigned num_lits = get_clause_num_literals(m_manager, cls);
                for (unsigned i = 0; i < num_lits; i++) {
                    expr * lit = get_clause_literal(m_manager, cls, i);
                    SASSERT(is_literal(m_manager, lit));
                    expr * atom;
                    bool   sign;
                    get_literal_atom_sign(m_manager, lit, atom, sign);
                    if (!is_ground(atom))
                        process_literal(atom, sign);
                }
            }

            void collect_macro_candidates(quantifier * q) {
                macro_util::macro_candidates candidates(m_manager);
                m_mutil.collect_macro_candidates(q, candidates);
                unsigned num_candidates = candidates.size();
                for (unsigned i = 0; i < num_candidates; i++) {
                    cond_macro * m = alloc(cond_macro, m_manager, candidates.get_f(i), candidates.get_def(i), candidates.get_cond(i), 
                                           candidates.ineq(i), candidates.satisfy_atom(i), candidates.hint(i), q->get_weight());
                    m_info->insert_macro(m);
                }
            }
            
 
        public:
            quantifier_analyzer(ast_manager & m, simplifier & s):
                m_manager(m),
                m_mutil(m, s),
                m_array_util(m), 
                m_arith_util(m),
                m_bv_util(m),
                m_cancel(false),
                m_info(0) {
            }
            
                
            void operator()(quantifier_info * d) {
                m_info = d;
                quantifier * q = d->get_flat_q();
                expr * e = q->get_expr();
                SASSERT(!has_quantifiers(e));
                reset_cache();
                SASSERT(m_ttodo.empty());
                SASSERT(m_ftodo.empty());
                
                if (is_clause(m_manager, e)) {
                    process_clause(e);
                }
                else {
                    process_formula(e);
                }

                while (!m_ftodo.empty() || !m_ttodo.empty()) {
                    process_formulas_on_stack();
                    process_terms_on_stack();
                }

                collect_macro_candidates(q);
                
                m_info = 0;
            }

            void set_cancel(bool f) { 
                m_cancel = f; 
                if (m_info) m_info->set_cancel(f);
            }

        };

        /**
           \brief Base class for macro solvers.
        */
        class base_macro_solver {
        protected:
            ast_manager &                                  m_manager;
            obj_map<quantifier, quantifier_info *> const & m_q2info;
            proto_model *                                  m_model;

            quantifier_info * get_qinfo(quantifier * q) const {
                quantifier_info * qi = 0;
                m_q2info.find(q, qi);
                SASSERT(qi != 0);
                return qi;
            }

            void set_else_interp(func_decl * f, expr * f_else) {
                SASSERT(f_else != 0);
                func_interp * fi = m_model->get_func_interp(f);
                if (fi == 0) {
                    fi = alloc(func_interp, m_manager, f->get_arity());
                    m_model->register_decl(f, fi);
                }
                fi->set_else(f_else);
            }

            virtual bool process(ptr_vector<quantifier> const & qs, ptr_vector<quantifier> & new_qs, ptr_vector<quantifier> & residue) = 0;

        public:
            base_macro_solver(ast_manager & m, obj_map<quantifier, quantifier_info *> const & q2i):
                m_manager(m),
                m_q2info(q2i),
                m_model(0) {
            }
            
            virtual ~base_macro_solver() {}

            /**
               \brief Try to satisfy quantifiers in qs by using macro definitions.
               Store in new_qs the quantifiers that were not satisfied.
               Store in residue a subset of the quantifiers that were satisfied but contain information useful for the auf_solver.
            */
            void operator()(proto_model * m, ptr_vector<quantifier> const & qs, ptr_vector<quantifier> & new_qs, ptr_vector<quantifier> & residue) {
                m_model = m;
                ptr_vector<quantifier> curr_qs(qs);
                while (process(curr_qs, new_qs, residue)) {
                    curr_qs.swap(new_qs);
                    new_qs.reset();
                }
            }
        };

        
        /**
           \brief The simple macro solver satisfies quantifiers that contain
           (conditional) macros for a function f that does not occur in any other quantifier.
           
           Since f does not occur in any other quantifier, I don't need to track the dependencies
           of f. That is, recursive definition cannot be created. 
        */
        class simple_macro_solver : public base_macro_solver {
        protected:
            /**
               \brief Return true if \c f is in (qs\{q})
            */
            bool contains(func_decl * f, ptr_vector<quantifier> const & qs, quantifier * q) {
                ptr_vector<quantifier>::const_iterator it  = qs.begin();
                ptr_vector<quantifier>::const_iterator end = qs.end();
                for (; it != end; ++it) {
                    quantifier * other = *it;
                    if (q == other)
                        continue;
                    quantifier_info * other_qi = get_qinfo(other);
                    if (other_qi->contains_ng_decl(f))
                        return true;
                }
                return false;
            }

            bool process(quantifier * q, ptr_vector<quantifier> const & qs) {
                quantifier_info * qi = get_qinfo(q);
                quantifier_info::macro_iterator it  = qi->begin_macros();
                quantifier_info::macro_iterator end = qi->end_macros();
                for (; it != end; ++it) {
                    cond_macro * m = *it;
                    if (!m->satisfy_atom())
                        continue;
                    func_decl * f  = m->get_f();
                    if (!contains(f, qs, q)) {
                        qi->set_the_one(f);
                        expr * f_else = m->get_def();
                        SASSERT(f_else != 0);
                        // Remark: I can ignore the conditions of m because
                        // I know the (partial) interpretation of f satisfied the ground part.
                        // MBQI will force extra instantiations if the the (partial) interpretation of f
                        // does not satisfy the quantifier.
                        // In all other cases the "else" of f will satisfy the quantifier. 
                        set_else_interp(f, f_else);
                        TRACE("model_finder", tout << "satisfying the quantifier using simple macro:\n";
                              m->display(tout); tout << "\n";);
                        return true; // satisfied quantifier
                    }
                }
                return false;
            }

            virtual bool process(ptr_vector<quantifier> const & qs, ptr_vector<quantifier> & new_qs, ptr_vector<quantifier> & residue) {
                bool removed = false;
                ptr_vector<quantifier>::const_iterator it  = qs.begin();
                ptr_vector<quantifier>::const_iterator end = qs.end();
                for (; it != end; ++it) {
                    if (process(*it, qs))
                        removed = true;
                    else
                        new_qs.push_back(*it);
                }
                return removed;
            }

        public:
            simple_macro_solver(ast_manager & m, obj_map<quantifier, quantifier_info *> const & q2i):
                base_macro_solver(m, q2i) {}
        };


        class hint_solver : public base_macro_solver {
            /*
              This solver tries to satisfy quantifiers by using macros, cond_macros and hints.
              The idea is to satisfy a set of quantifiers Q = Q_{f_1} union ... union Q_{f_n}
              where Q_{f_i} is the set of quantifiers that contain the function f_i.
              Let f_i = def_i be macros (in this solver conditions are ignored).
              Let Q_{f_i = def_i} be the set of quantifiers where f_i = def_i is a macro.
              Then, the set Q can be satisfied using f_1 = def_1 ... f_n = d_n
              when
              
              Q_{f_1} union ... union Q_{f_n} = Q_{f_1 = def_1} ... Q_{f_n = d_n} (*)

              So, given a set of macros f_1 = def_1, ..., f_n = d_n, it is very easy to check
              whether they can be used to satisfy all quantifiers that use f_1, ..., f_n in
              non ground terms.

              We can find the sets of f_1 = def_1, ..., f_n = def_n that satisfy Q using
              the following search procedure
                    find(Q)
                      for each f_i = def_i in Q
                          R = greedy(Q_{f_i = def_1}, Q_f_i \ Q_{f_i = def_i}, {f_i}, {f_i = def_i})
                          if (R != empty-set)
                            return R
                    greedy(Satisfied, Residue, F, F_DEF)
                      if Residue = empty-set return F_DEF
                      for each f_j = def_j in Residue such that f_j not in F
                          New-Satisfied = Satisfied union Q_{f_j = def_j}
                          New-Residue = (Residue union Q_{f_j}) \ New-Satisfied
                          R = greedy(New-Satisfied, New-Residue, F \union {f_j}, F_DEF union {f_j = def_j})
                          if (R != empty-set)
                             return R

              This search may be too expensive, and is exponential on the number of different function
              symbols.
              Some observations to prune the search space.
              1) If f_i occurs in a quantifier without macros, then f_i and any macro using it can be ignored during the search.
              2) If f_i = def_i is not a macro in a quantifier q, and there is no other f_j = def_j (i != j) in q,
                 then f_i = def_i can be ignored during the search.
            */

            typedef obj_hashtable<quantifier> quantifier_set;
            typedef obj_map<func_decl, quantifier_set *> q_f;
            typedef obj_pair_map<func_decl, expr, quantifier_set *> q_f_def;
            typedef obj_pair_hashtable<func_decl, expr> f_def_set;
            typedef obj_hashtable<expr> expr_set;
            typedef obj_map<func_decl, expr_set *> f2defs; 
            
            q_f                        m_q_f;
            q_f_def                    m_q_f_def;
            ptr_vector<quantifier_set> m_qsets;
            f2defs                     m_f2defs;
            ptr_vector<expr_set>       m_esets;

            void insert_q_f(quantifier * q, func_decl * f) {
                SASSERT(!m_forbidden.contains(f));
                quantifier_set * s = 0;
                if (!m_q_f.find(f, s)) {
                    s = alloc(quantifier_set);
                    m_q_f.insert(f, s);
                    m_qsets.push_back(s);
                }
                SASSERT(s != 0);
                s->insert(q);
            }

            void insert_f2def(func_decl * f, expr * def) {
                expr_set * s = 0;
                if (!m_f2defs.find(f, s)) {
                    s = alloc(expr_set);
                    m_f2defs.insert(f, s);
                    m_esets.push_back(s);
                }
                SASSERT(s != 0);
                s->insert(def);
            }

            void insert_q_f_def(quantifier * q, func_decl * f, expr * def) {
                SASSERT(!m_forbidden.contains(f));
                quantifier_set * s = 0;
                if (!m_q_f_def.find(f, def, s)) {
                    s = alloc(quantifier_set);
                    m_q_f_def.insert(f, def, s);
                    insert_f2def(f, def);
                    m_qsets.push_back(s);
                }
                SASSERT(s != 0);
                s->insert(q);
            }

            quantifier_set * get_q_f(func_decl * f) {
                quantifier_set * s = 0;
                m_q_f.find(f, s);
                SASSERT(s != 0);
                return s;
            }

            quantifier_set * get_q_f_def(func_decl * f, expr * def) {
                quantifier_set * s = 0;
                m_q_f_def.find(f, def, s);
                SASSERT(s != 0);
                return s;
            }

            expr_set * get_f_defs(func_decl * f) {
                expr_set * s = 0;
                m_f2defs.find(f, s);
                SASSERT(s != 0);
                return s;
            }

            void reset_q_fs() {
                std::for_each(m_qsets.begin(), m_qsets.end(), delete_proc<quantifier_set>());
                std::for_each(m_esets.begin(), m_esets.end(), delete_proc<expr_set>());
                m_q_f.reset();
                m_q_f_def.reset();
                m_qsets.reset();
                m_f2defs.reset();
                m_esets.reset();
            }

            func_decl_set              m_forbidden;
            func_decl_set              m_candidates;

            bool is_candidate(quantifier * q) const {
                quantifier_info * qi = get_qinfo(q);
                quantifier_info::macro_iterator it  = qi->begin_macros();
                quantifier_info::macro_iterator end = qi->end_macros();
                for (; it != end; ++it) {
                    cond_macro * m = *it;
                    if (m->satisfy_atom() && !m_forbidden.contains(m->get_f()))
                        return true;
                }
                return false;
            }

            void register_decls_as_forbidden(quantifier * q) {
                quantifier_info * qi = get_qinfo(q);
                func_decl_set const & ng_decls = qi->get_ng_decls();
                func_decl_set::iterator it  = ng_decls.begin();
                func_decl_set::iterator end = ng_decls.end();
                for (; it != end; ++it) {
                    m_forbidden.insert(*it);
                }
            }

            void preprocess(ptr_vector<quantifier> const & qs, ptr_vector<quantifier> & qcandidates, ptr_vector<quantifier> & non_qcandidates) {
                ptr_vector<quantifier> curr(qs);
                while (true) {
                    ptr_vector<quantifier>::iterator it  = curr.begin();
                    ptr_vector<quantifier>::iterator end = curr.end();
                    for (; it != end; ++it) {
                        quantifier * q = *it;
                        if (is_candidate(q)) {
                            qcandidates.push_back(q);
                        }
                        else {
                            register_decls_as_forbidden(q);
                            non_qcandidates.push_back(q);
                        }
                    }
                    if (curr.size() == qcandidates.size())
                        return;
                    SASSERT(qcandidates.size() < curr.size());
                    curr.swap(qcandidates);
                    qcandidates.reset();
                }
            }

            void mk_q_f_defs(ptr_vector<quantifier> const & qs) {
                ptr_vector<quantifier>::const_iterator it  = qs.begin();
                ptr_vector<quantifier>::const_iterator end = qs.end();
                for (; it != end; ++it) {
                    quantifier *      q  = *it;
                    quantifier_info * qi = get_qinfo(q);
                    func_decl_set const & ng_decls = qi->get_ng_decls();
                    func_decl_set::iterator it2  = ng_decls.begin();
                    func_decl_set::iterator end2 = ng_decls.end();
                    for (; it2 != end2; ++it2) {
                        func_decl * f = *it2;
                        if (!m_forbidden.contains(f))
                            insert_q_f(q, f);
                    }
                    quantifier_info::macro_iterator it3  = qi->begin_macros();
                    quantifier_info::macro_iterator end3 = qi->end_macros();
                    for (; it3 != end3; ++it3) {
                        cond_macro * m = *it3;
                        if (m->satisfy_atom() && !m_forbidden.contains(m->get_f())) {
                            insert_q_f_def(q, m->get_f(), m->get_def());
                            m_candidates.insert(m->get_f());
                        }
                    }
                }
            }
            
            static void display_quantifier_set(std::ostream & out, quantifier_set const * s) {
                quantifier_set::iterator it  = s->begin();
                quantifier_set::iterator end = s->end();
                for (; it != end; ++it) {
                    quantifier * q = *it;
                    out << q->get_qid() << " ";
                }
                out << "\n";
            }
            
            void display_qcandidates(std::ostream & out, ptr_vector<quantifier> const & qcandidates) const {
                ptr_vector<quantifier>::const_iterator it1  = qcandidates.begin();
                ptr_vector<quantifier>::const_iterator end1 = qcandidates.end();
                for (; it1 != end1; ++it1) {
                    quantifier * q = *it1;
                    out << q->get_qid() << " ->\n" << mk_pp(q, m_manager) << "\n";
                    quantifier_info * qi = get_qinfo(q);
                    qi->display(out);
                    out << "------\n";
                }
                out << "Sets Q_f\n";
                q_f::iterator it2 = m_q_f.begin();
                q_f::iterator end2 = m_q_f.end();
                for (; it2 != end2; ++it2) {
                    func_decl * f = (*it2).m_key;
                    quantifier_set * s = (*it2).m_value;
                    out << f->get_name() << " -> "; display_quantifier_set(out, s);
                }
                out << "Sets Q_{f = def}\n";
                q_f_def::iterator it3  = m_q_f_def.begin();
                q_f_def::iterator end3 = m_q_f_def.end();
                for (; it3 != end3; ++it3) {
                    func_decl * f = (*it3).get_key1();
                    expr * def    = (*it3).get_key2();
                    quantifier_set * s = (*it3).get_value();
                    out << f->get_name() << " " << mk_pp(def, m_manager) << " ->\n"; display_quantifier_set(out, s);
                }
            }
            
            //
            // Search: main procedures
            //

            struct ev_handler {
                hint_solver * m_owner;
                
                void operator()(quantifier * q, bool ins) {
                    quantifier_info * qi = m_owner->get_qinfo(q);
                    qi->set_the_one(0);
                }

                ev_handler(hint_solver * o):
                    m_owner(o) {
                }
            };


            typedef backtrackable_set<quantifier_set, quantifier *> qset;
            typedef backtrackable_set<quantifier_set, quantifier *, ev_handler> qsset;            
            typedef obj_map<func_decl, expr *> f2def;

            qset         m_residue;
            qsset        m_satisfied;
            f2def        m_fs; // set of function symbols (and associated interpretation) that were used to satisfy the quantifiers in m_satisfied.

            struct found_satisfied_subset {};

            void display_search_state(std::ostream & out) const {
                out << "fs:\n";
                f2def::iterator it3  = m_fs.begin();
                f2def::iterator end3 = m_fs.end();
                for (; it3 != end3; ++it3) {
                    out << (*it3).m_key->get_name() << " ";
                }
                out << "\nsatisfied:\n";
                qsset::iterator it  = m_satisfied.begin();
                qsset::iterator end = m_satisfied.end();
                for (; it != end; ++it) {
                    out << (*it)->get_qid() << " ";
                }
                out << "\nresidue:\n";
                qset::iterator it2  = m_residue.begin();
                qset::iterator end2 = m_residue.end();
                for (; it2 != end2; ++it2) {
                    out << (*it2)->get_qid() << " ";
                }
                out << "\n";
            }
            
            bool check_satisfied_residue_invariant() {
                qsset::iterator it  = m_satisfied.begin();
                qsset::iterator end = m_satisfied.end();
                for (; it != end; ++it) {
                    quantifier * q = *it;
                    SASSERT(!m_residue.contains(q));
                    quantifier_info * qi = get_qinfo(q);
                    SASSERT(qi != 0);
                    SASSERT(qi->get_the_one() != 0);
                }
                return true;
            }

            
            bool update_satisfied_residue(func_decl * f, expr * def) {
                bool useful = false;
                SASSERT(check_satisfied_residue_invariant());
                quantifier_set * q_f     = get_q_f(f);
                quantifier_set * q_f_def = get_q_f_def(f, def);
                quantifier_set::iterator it  = q_f_def->begin();
                quantifier_set::iterator end = q_f_def->end();
                for (; it != end; ++it) {
                    quantifier * q = *it;
                    if (!m_satisfied.contains(q)) {
                        useful = true;
                        m_residue.erase(q);
                        m_satisfied.insert(q);
                        quantifier_info * qi = get_qinfo(q);
                        SASSERT(qi->get_the_one() == 0);
                        qi->set_the_one(f); // remark... event handler will reset it during backtracking.
                    }
                }
                if (!useful)
                    return false;
                it  = q_f->begin();
                end = q_f->end();
                for (; it != end; ++it) {
                    quantifier * q = *it;
                    if (!m_satisfied.contains(q)) {
                        m_residue.insert(q);
                    }
                }
                SASSERT(check_satisfied_residue_invariant());
                return true;
            }
            
            /**
               \brief Extract from m_residue, func_decls that can be used as macros to satisfy it.
               The candidates must not be elements of m_fs.
            */
            void get_candidates_from_residue(func_decl_set & candidates) {
                qset::iterator it  = m_residue.begin();
                qset::iterator end = m_residue.end();
                for (; it != end; ++it) {
                    quantifier * q = *it;
                    quantifier_info * qi = get_qinfo(q);

                    quantifier_info::macro_iterator it2  = qi->begin_macros();
                    quantifier_info::macro_iterator end2 = qi->end_macros();
                    for (; it2 != end2; ++it2) {
                        cond_macro * m = *it2;
                        func_decl * f  = m->get_f();
                        if (m->satisfy_atom() && !m_forbidden.contains(f) && !m_fs.contains(f)) {
                            candidates.insert(f);
                        }
                    }
                }
            }

#define GREEDY_MAX_DEPTH 10 /* to avoid too expensive search spaces */

            /**
              \brief Try to reduce m_residue using the macros of f.
            */
            void greedy(func_decl * f, unsigned depth) {
                if (depth >= GREEDY_MAX_DEPTH)
                    return; // failed

                TRACE("model_finder_hint", 
                      tout << "greedy depth: " << depth << ", f: " << f->get_name() << "\n";
                      display_search_state(tout););

                expr_set * s = get_f_defs(f);
                expr_set::iterator it  = s->begin();
                expr_set::iterator end = s->end();
                for (; it != end; ++it) {
                    expr * def = *it;
                    
                    SASSERT(!m_fs.contains(f));

                    m_satisfied.push_scope();
                    m_residue.push_scope();
                    m_fs.insert(f, def);

                    if (update_satisfied_residue(f, def)) {
                        // update was useful
                        greedy(depth + 1); // greedy throws exception in case of success
                        // reachable iff greedy failed.
                    }
                    
                    m_satisfied.pop_scope();
                    m_residue.pop_scope();
                    m_fs.erase(f);
                }
            }

            /**
               \brief Try to reduce m_residue (if not empty) by selecting a function f
               that is a macro in the residue.
            */
            void greedy(unsigned depth) {
                if (m_residue.empty()) {
                    TRACE("model_finder_hint", 
                          tout << "found subset that is satisfied by macros\n";
                          display_search_state(tout););
                    throw found_satisfied_subset();
                }
                func_decl_set candidates;
                get_candidates_from_residue(candidates);

                TRACE("model_finder_hint", tout << "candidates from residue:\n";
                      func_decl_set::iterator it  = candidates.begin();
                      func_decl_set::iterator end = candidates.end();
                      for (; it != end; ++it) {
                          tout << (*it)->get_name() << " ";
                      }
                      tout << "\n";);

                func_decl_set::iterator it  = candidates.begin();
                func_decl_set::iterator end = candidates.end();
                for (; it != end; ++it) {
                    greedy(*it, depth);
                }
            }

            /**
               \brief Try to find a set of quantifiers by starting to use the macros of f.
               This is the "find" procedure in the comments above.
               The set of satisfied quantifiers is in m_satisfied, and the remaining to be
               satisfied in m_residue. When the residue becomes empty we throw the exception found_satisfied_subset.
            */
            void process(func_decl * f) {
                SASSERT(m_satisfied.empty());
                SASSERT(m_residue.empty());
                greedy(f, 0);
            }

            /**
               \brief Copy the quantifiers from qcandidates to new_qs that are not in m_satisfied.
            */
            void copy_non_satisfied(ptr_vector<quantifier> const & qcandidates, ptr_vector<quantifier> & new_qs) {
                ptr_vector<quantifier>::const_iterator it  = qcandidates.begin();
                ptr_vector<quantifier>::const_iterator end = qcandidates.end();
                for (; it != end; ++it) {
                    quantifier * q = *it;
                    if (!m_satisfied.contains(q))
                        new_qs.push_back(q);
                }
            }

            /**
               \brief Use m_fs to set the interpreation of the function symbols that were used to satisfy the
               quantifiers in m_satisfied.
            */
            void set_interp() {
                f2def::iterator it  = m_fs.begin();
                f2def::iterator end = m_fs.end();
                for (; it != end; ++it) {
                    func_decl * f = (*it).m_key;
                    expr * def    = (*it).m_value;
                    set_else_interp(f, def);
                }
            }

            void reset() {
                reset_q_fs();
                m_forbidden.reset();
                m_candidates.reset();
                m_satisfied.reset();
                m_residue.reset();
                m_fs.reset();
            }

            virtual bool process(ptr_vector<quantifier> const & qs, ptr_vector<quantifier> & new_qs, ptr_vector<quantifier> & residue) {
                reset();
                ptr_vector<quantifier> qcandidates;
                preprocess(qs, qcandidates, new_qs);
                if (qcandidates.empty()) {
                    SASSERT(new_qs.size() == qs.size());
                    return false;
                }
                mk_q_f_defs(qcandidates);
                TRACE("model_finder_hint", tout << "starting hint-solver search using:\n"; display_qcandidates(tout, qcandidates););
                func_decl_set::iterator it  = m_candidates.begin();
                func_decl_set::iterator end = m_candidates.end();
                for (; it != end; ++it) {
                    func_decl * f = *it;
                    try {
                        process(f);
                    }
                    catch (found_satisfied_subset) {
                        set_interp();
                        copy_non_satisfied(qcandidates, new_qs);
                        return true;
                    }
                }
                // failed... copy everything to new_qs
                new_qs.append(qcandidates);
                return false;
            }

        public:
            hint_solver(ast_manager & m, obj_map<quantifier, quantifier_info *> const & q2i):
                base_macro_solver(m, q2i),
                m_satisfied(ev_handler(this)) {
            }

            virtual ~hint_solver() {
                reset();
            }

        };


        /**
           \brief Satisfy clauses that are not in the AUF fragment but define conditional macros.
           These clauses are eliminated even if the symbol being defined occurs in other quantifiers.
           The auf_solver is ineffective in these clauses.

           \remark Full macros are used even if they are in the AUF fragment.
        */
        class non_auf_macro_solver : public base_macro_solver {
            func_decl_dependencies &               m_dependencies;
            qi_params const *                      m_qi_params;

            bool add_macro(func_decl * f, expr * f_else) {
                TRACE("non_auf_macro_solver", tout << "trying to add macro for " << f->get_name() << "\n" << mk_pp(f_else, m_manager) << "\n";);
                func_decl_set * s = m_dependencies.mk_func_decl_set();
                m_dependencies.collect_ng_func_decls(f_else, s);
                if (!m_dependencies.insert(f, s)) {
                    TRACE("non_auf_macro_solver", tout << "failed to add macro\n";);
                    return false; // cyclic dependency
                }
                set_else_interp(f, f_else);
                return true;
            }

            // Return true if r1 is a better macro than r2.
            bool is_better_macro(cond_macro * r1, cond_macro * r2) {
                if (r2 == 0 || !r1->is_hint())
                    return true;
                if (!r2->is_hint())
                    return false;
                SASSERT(r1->is_hint() && r2->is_hint());
                if (is_ground(r1->get_def()) && !is_ground(r2->get_def()))
                    return true;
                return false;
            }
            
            cond_macro * get_macro_for(func_decl * f, quantifier * q) {
                cond_macro * r = 0;
                quantifier_info * qi = get_qinfo(q);
                quantifier_info::macro_iterator it  = qi->begin_macros();
                quantifier_info::macro_iterator end = qi->end_macros();
                for (; it != end; ++it) {
                    cond_macro * m = *it;
                    if (m->get_f() == f && !m->is_hint() && is_better_macro(m, r))
                        r = m;
                }
                return r;
            }

            typedef std::pair<cond_macro *, quantifier *> mq_pair;

            void collect_candidates(ptr_vector<quantifier> const & qs, obj_map<func_decl, mq_pair> & full_macros, func_decl_set & cond_macros) {
                ptr_vector<quantifier>::const_iterator it  = qs.begin();
                ptr_vector<quantifier>::const_iterator end = qs.end();
                for (; it != end; ++it) {
                    quantifier * q = *it;
                    quantifier_info * qi = get_qinfo(q);
                    quantifier_info::macro_iterator it2  = qi->begin_macros();
                    quantifier_info::macro_iterator end2 = qi->end_macros();
                    for (; it2 != end2; ++it2) {
                        cond_macro * m = *it2;
                        if (!m->is_hint()) {
                            func_decl * f = m->get_f();
                            TRACE("non_auf_macro_solver", tout << "considering macro for: " << f->get_name() << "\n";
                                  m->display(tout); tout << "\n";);
                            SASSERT(m_qi_params != 0);
                            if (m->is_unconditional() && (!qi->is_auf() || m->get_weight() >= m_qi_params->m_mbqi_force_template)) {
                                full_macros.insert(f, std::make_pair(m, q));
                                cond_macros.erase(f);
                            }
                            else if (!full_macros.contains(f) && !qi->is_auf())
                                cond_macros.insert(f);
                        }
                    }
                }
            }

            void process_full_macros(obj_map<func_decl, mq_pair> const & full_macros, obj_hashtable<quantifier> & removed) {
                obj_map<func_decl, mq_pair>::iterator it  = full_macros.begin();
                obj_map<func_decl, mq_pair>::iterator end = full_macros.end();
                for (; it != end; ++it) {
                    func_decl * f  = (*it).m_key;
                    cond_macro * m = (*it).m_value.first;
                    quantifier * q = (*it).m_value.second;
                    SASSERT(m->is_unconditional());
                    if (add_macro(f, m->get_def())) {
                        get_qinfo(q)->set_the_one(f);
                        removed.insert(q);
                    }
                }
            }

            void process(func_decl * f, ptr_vector<quantifier> const & qs, obj_hashtable<quantifier> & removed) {
                expr_ref fi_else(m_manager);
                ptr_buffer<quantifier> to_remove;
                ptr_vector<quantifier>::const_iterator it  = qs.begin();
                ptr_vector<quantifier>::const_iterator end = qs.end();
                for (; it != end; ++it) {
                    quantifier * q = *it;
                    if (removed.contains(q))
                        continue;
                    cond_macro * m = get_macro_for(f, q);
                    if (!m)
                        continue;
                    SASSERT(!m->is_hint());
                    if (m->is_unconditional())
                        return; // f is part of a full macro... ignoring it.
                    to_remove.push_back(q);
                    if (fi_else.get() == 0) {
                        fi_else = m->get_def();
                    }
                    else {
                        fi_else = m_manager.mk_ite(m->get_cond(), m->get_def(), fi_else);
                    }
                }
                if (fi_else.get() != 0 && add_macro(f, fi_else)) {
                    ptr_buffer<quantifier>::iterator it2  = to_remove.begin();
                    ptr_buffer<quantifier>::iterator end2 = to_remove.end();
                    for (; it2 != end2; ++it2) {
                        get_qinfo(*it2)->set_the_one(f);
                        removed.insert(*it2);
                    }
                }
            }

            void process_cond_macros(func_decl_set const & cond_macros, ptr_vector<quantifier> const & qs, obj_hashtable<quantifier> & removed) {
                func_decl_set::iterator it  = cond_macros.begin();
                func_decl_set::iterator end = cond_macros.end();
                for (; it != end; ++it) {
                    process(*it, qs, removed);
                }
            }

            virtual bool process(ptr_vector<quantifier> const & qs, ptr_vector<quantifier> & new_qs, ptr_vector<quantifier> & residue) {
                obj_map<func_decl, mq_pair> full_macros;
                func_decl_set cond_macros;
                obj_hashtable<quantifier> removed;

                // Possible improvement: sort full_macros & cond_macros using an user provided precedence function.

                collect_candidates(qs, full_macros, cond_macros);
                process_full_macros(full_macros, removed);
                process_cond_macros(cond_macros, qs, removed);

                ptr_vector<quantifier>::const_iterator it  = qs.begin();
                ptr_vector<quantifier>::const_iterator end = qs.end();
                for (; it != end; ++it) {
                    quantifier * q = *it;
                    if (removed.contains(q))
                        continue;
                    new_qs.push_back(q);
                    residue.push_back(q);
                }
                return !removed.empty();
            }

        public:
            non_auf_macro_solver(ast_manager & m, obj_map<quantifier, quantifier_info *> const & q2i, func_decl_dependencies & d):
                base_macro_solver(m, q2i),
                m_dependencies(d),
                m_qi_params(0) {
            }

            void set_params(qi_params const & p) {
                SASSERT(m_qi_params == 0);
                m_qi_params = &p;
            }
        };
    };
    
    // -----------------------------------
    //
    // model finder 
    //
    // -----------------------------------
    
    model_finder::model_finder(ast_manager & m, simplifier & s):
        m_manager(m),
        m_context(0),
        m_analyzer(alloc(quantifier_analyzer, m, s)),
        m_auf_solver(alloc(auf_solver, m, s)),
        m_dependencies(m),
        m_sm_solver(alloc(simple_macro_solver, m, m_q2info)),
        m_hint_solver(alloc(hint_solver, m, m_q2info)),
        m_nm_solver(alloc(non_auf_macro_solver, m, m_q2info, m_dependencies)),
        m_cancel(false),
        m_new_constraints(m) {
    }
    
    model_finder::~model_finder() {
        reset();
    }
        
    mf::quantifier_info * model_finder::get_quantifier_info(quantifier * q) const {
        quantifier_info * info = 0;
        m_q2info.find(q, info);
        SASSERT(info != 0);
        return info;
    }
        
    void model_finder::set_context(context * ctx) {
        SASSERT(m_context == 0); 
        m_context = ctx;
        m_auf_solver->set_context(ctx);
        m_nm_solver->set_params(ctx->get_fparams());
    }
            
    void model_finder::register_quantifier(quantifier * q) {
        TRACE("model_finder", tout << "registering:\n" << mk_pp(q, m_manager) << "\n";);
        quantifier_info * new_info = alloc(quantifier_info, m_manager, q);
        m_q2info.insert(q, new_info);
        m_quantifiers.push_back(q);
        m_analyzer->operator()(new_info);
        TRACE("model_finder", tout << "after analyzer:\n"; new_info->display(tout););
    }
    
    void model_finder::push_scope() {
        m_scopes.push_back(scope());
        scope & s = m_scopes.back();
        s.m_quantifiers_lim = m_quantifiers.size();
    }
    
    void model_finder::restore_quantifiers(unsigned old_size) {
        unsigned curr_size = m_quantifiers.size(); 
        SASSERT(old_size <= curr_size);
        for (unsigned i = old_size; i < curr_size; i++) {
            quantifier * q = m_quantifiers[i];
            SASSERT(m_q2info.contains(q));
            quantifier_info * info = get_quantifier_info(q);
            dealloc(info);
            m_q2info.erase(q);
        }
        m_quantifiers.shrink(old_size);
    }
    
    void model_finder::pop_scope(unsigned num_scopes) {
        unsigned lvl      = m_scopes.size();
        SASSERT(num_scopes <= lvl);
        unsigned new_lvl  = lvl - num_scopes;
        scope & s         = m_scopes[new_lvl];
        restore_quantifiers(s.m_quantifiers_lim);
        m_scopes.shrink(new_lvl);
    }
    
    void model_finder::reset() {
        m_scopes.reset();
        m_dependencies.reset();
        restore_quantifiers(0);
        SASSERT(m_q2info.empty());
        SASSERT(m_quantifiers.empty());
    }
    
    void model_finder::init_search_eh() {
        // do nothing in the current version
    }

    void model_finder::collect_relevant_quantifiers(ptr_vector<quantifier> & qs) const {
        ptr_vector<quantifier>::const_iterator it  = m_quantifiers.begin();
        ptr_vector<quantifier>::const_iterator end = m_quantifiers.end();
        for (; it != end; ++it) {
            quantifier * q = *it;
            if (m_context->is_relevant(q) && m_context->get_assignment(q) == l_true)
                qs.push_back(q);
        }
    }

    void model_finder::process_auf(ptr_vector<quantifier> const & qs, proto_model * m) {
        m_auf_solver->reset();
        m_auf_solver->set_model(m);

        ptr_vector<quantifier>::const_iterator it  = qs.begin();
        ptr_vector<quantifier>::const_iterator end = qs.end();
        for (; it != end; ++it) {
            quantifier * q       = *it;
            quantifier_info * qi = get_quantifier_info(q);
            qi->process_auf(*(m_auf_solver.get()), m_context);
        }
        m_auf_solver->mk_instantiation_sets();
        it  = qs.begin();
        for (; it != end; ++it) {
            quantifier * q       = *it;
            quantifier_info * qi = get_quantifier_info(q);
            qi->populate_inst_sets(*(m_auf_solver.get()), m_context);
        }
        m_auf_solver->fix_model(m_new_constraints);
        TRACE("model_finder", 
              ptr_vector<quantifier>::const_iterator it  = qs.begin();
              ptr_vector<quantifier>::const_iterator end = qs.end();
              for (; it != end; ++it) {
                  quantifier * q = *it;
                  quantifier_info * qi = get_quantifier_info(q);
                  quantifier * fq = qi->get_flat_q();
                  tout << "#" << fq->get_id() << " ->\n" << mk_pp(fq, m_manager) << "\n";
              }
              m_auf_solver->display_nodes(tout););
    }

    void model_finder::process_simple_macros(ptr_vector<quantifier> & qs, ptr_vector<quantifier> & residue, proto_model * m) {
        ptr_vector<quantifier> new_qs;
        m_sm_solver->operator()(m, qs, new_qs, residue);
        qs.swap(new_qs);
        TRACE("model_finder", tout << "model after processing simple macros:\n"; model_pp(tout, *m););
    }

    void model_finder::process_hint_macros(ptr_vector<quantifier> & qs, ptr_vector<quantifier> & residue, proto_model * m) {
        ptr_vector<quantifier> new_qs;
        m_hint_solver->operator()(m, qs, new_qs, residue);
        qs.swap(new_qs);
        TRACE("model_finder", tout << "model after processing simple macros:\n"; model_pp(tout, *m););
    }
    
    void model_finder::process_non_auf_macros(ptr_vector<quantifier> & qs, ptr_vector<quantifier> & residue, proto_model * m) {
        ptr_vector<quantifier> new_qs;
        m_nm_solver->operator()(m, qs, new_qs, residue);
        qs.swap(new_qs);
        TRACE("model_finder", tout << "model after processing non auf macros:\n"; model_pp(tout, *m););
    }

    /**
       \brief Clean leftovers from previous invocations to fix_model.
    */
    void model_finder::cleanup_quantifier_infos(ptr_vector<quantifier> const & qs) {
        ptr_vector<quantifier>::const_iterator it  = qs.begin();
        ptr_vector<quantifier>::const_iterator end = qs.end();
        for (; it != end; ++it) {
            quantifier_info * qi = get_quantifier_info(*it);
            qi->reset_the_one();
        }
    }

    /**
       \brief Try to satisfy quantifiers by modifying the model while preserving the satisfiability
       of all ground formulas asserted into the logical context.
    */
    void model_finder::fix_model(proto_model * m) {
        if (m_quantifiers.empty())
            return;
        ptr_vector<quantifier> qs;
        ptr_vector<quantifier> residue;
        collect_relevant_quantifiers(qs);
        if (qs.empty())
            return;
        TRACE("model_finder", tout << "trying to satisfy quantifiers, given model:\n"; model_pp(tout, *m););
        cleanup_quantifier_infos(qs);
        m_dependencies.reset();

        process_simple_macros(qs, residue, m);
        process_hint_macros(qs, residue, m);
        process_non_auf_macros(qs, residue, m);
        qs.append(residue);
        process_auf(qs, m);
    }

    quantifier * model_finder::get_flat_quantifier(quantifier * q) const {
        quantifier_info * qinfo = get_quantifier_info(q);
        SASSERT(qinfo);
        return qinfo->get_flat_q();
    }

    /**
       \brief Return the instantiation set associated with var i of q.

       \remark q is the quantifier before flattening.
    */
    mf::instantiation_set const * model_finder::get_uvar_inst_set(quantifier * q, unsigned i) const {
        quantifier * flat_q = get_flat_quantifier(q);
        SASSERT(flat_q->get_num_decls() >= q->get_num_decls());
        instantiation_set const * r = m_auf_solver->get_uvar_inst_set(flat_q, flat_q->get_num_decls() - q->get_num_decls() + i);
        TRACE("model_finder", tout << "q: #" << q->get_id() << "\n" << mk_pp(q,m_manager) << "\nflat_q: " << mk_pp(flat_q, m_manager)
              << "\ni: " << i << " " << flat_q->get_num_decls() - q->get_num_decls() + i << "\n";);
        if (r != 0)
            return r;
        // quantifier was not processed by AUF solver... 
        // it must have been satisfied by "macro"/"hint".
        quantifier_info * qinfo = get_quantifier_info(q);
        SASSERT(qinfo);
        SASSERT(qinfo->get_the_one() != 0);
        
        return qinfo->get_macro_based_inst_set(i, m_context, *(m_auf_solver.get()));
    }

    /**
       \brief Return an expression in the instantiation-set of q:i that evaluates to val.

       \remark q is the quantifier before flattening.

       Store in generation the generation of the result
    */
    expr * model_finder::get_inv(quantifier * q, unsigned i, expr * val, unsigned & generation) const {
        instantiation_set const * s = get_uvar_inst_set(q, i);
        if (s == 0)
            return 0;
        expr * t = s->get_inv(val);
        if (t != 0) {
            generation = s->get_generation(t);
        }
        return t;
    }
    
    /**
       \brief Assert constraints restricting the possible values of the skolem constants can be assigned to.
       The idea is to restrict them to the values in the instantiation sets.
    
       \remark q is the quantifier before flattening.

       Return true if something was asserted.
    */
    bool model_finder::restrict_sks_to_inst_set(context * aux_ctx, quantifier * q, expr_ref_vector const & sks) {
        // Note: we currently add instances of q instead of flat_q.
        // If the user wants instances of flat_q, it should use PULL_NESTED_QUANTIFIERS=true. This option
        // will guarantee that q == flat_q.
        //
        // Since we only care about q (and its bindings), it only makes sense to restrict the variables of q.
        bool asserted_something = false;
        quantifier * flat_q = get_flat_quantifier(q);
        unsigned num_decls      = q->get_num_decls();
        unsigned flat_num_decls = flat_q->get_num_decls();
        unsigned num_sks        = sks.size();
        // Remark: sks were created for the flat version of q.
        SASSERT(num_sks == flat_num_decls);
        SASSERT(flat_num_decls >= num_decls);
        SASSERT(num_sks >= num_decls);
        for (unsigned i = 0; i < num_decls; i++) {
            expr * sk = sks.get(num_decls - i - 1);
            instantiation_set const * s = get_uvar_inst_set(q, i);
            if (s == 0)
                continue; // nothing to do
            obj_map<expr, expr *> const & inv = s->get_inv_map();
            if (inv.empty())
                continue; // nothing to do
            ptr_buffer<expr> eqs;
            obj_map<expr, expr *>::iterator it  = inv.begin();
            obj_map<expr, expr *>::iterator end = inv.end();
            for (; it != end; ++it) {
                expr * val = (*it).m_key;
                eqs.push_back(m_manager.mk_eq(sk, val));
            }
            expr_ref new_cnstr(m_manager);
            new_cnstr = m_manager.mk_or(eqs.size(), eqs.c_ptr());
            TRACE("model_finder", tout << "assert_restriction:\n" << mk_pp(new_cnstr, m_manager) << "\n";);
            aux_ctx->assert_expr(new_cnstr);
            asserted_something = true;
        }
        return asserted_something;
    }

    void model_finder::restart_eh() {
        unsigned sz = m_new_constraints.size();
        if (sz > 0) {
            for (unsigned i = 0; i < sz; i++) {
                expr * c = m_new_constraints.get(i);
                TRACE("model_finder_bug_detail", tout << "asserting new constraint: " << mk_pp(c, m_manager) << "\n";);
                m_context->internalize(c, true);
                literal l(m_context->get_literal(c));
                m_context->mark_as_relevant(l);         
                // asserting it as an AXIOM
                m_context->assign(l, b_justification());
            }
            m_new_constraints.reset();
        }
    }

    void model_finder::set_cancel(bool f) {
        m_cancel = f;
        m_analyzer->set_cancel(f);
    }

};
