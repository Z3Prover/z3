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
#include "util/backtrackable_set.h"
#include "ast/ast_util.h"
#include "ast/macros/macro_util.h"
#include "ast/arith_decl_plugin.h"
#include "ast/bv_decl_plugin.h"
#include "ast/array_decl_plugin.h"
#include "ast/normal_forms/pull_quant.h"
#include "ast/rewriter/var_subst.h"
#include "ast/macros/cond_macro.h"
#include "ast/macros/quantifier_macro_info.h"
#include "ast/for_each_expr.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "ast/well_sorted.h"
#include "ast/ast_smt2_pp.h"
#include "model/model_pp.h"
#include "model/model_macro_solver.h"
#include "smt/smt_model_finder.h"
#include "smt/smt_context.h"
#include "tactic/tactic_exception.h"

namespace smt {

    namespace mf {

        // -----------------------------------
        //
        // Auxiliary stuff
        //
        // -----------------------------------


        class evaluator {
        public:
            virtual ~evaluator() = default;
            virtual expr* eval(expr* n, bool model_completion) = 0;
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
            ast_manager&            m;
            obj_map<expr, unsigned> m_elems; // and the associated generation
            obj_map<expr, expr*>    m_inv;
            expr_mark               m_visited;
        public:
            instantiation_set(ast_manager& m) :m(m) {}

            ~instantiation_set() {
                for (auto const& kv : m_elems) {
                    m.dec_ref(kv.m_key);
                }
            }

            obj_map<expr, unsigned> const& get_elems() const { return m_elems; }

            void insert(expr* n, unsigned generation) {
                if (m_elems.contains(n) || contains_model_value(n)) {
                    return;
                }
                m.inc_ref(n);
                m_elems.insert(n, generation);
                SASSERT(!m.is_model_value(n));
            }

            void remove(expr* n) {
                // We can only remove n if it is in m_elems, AND m_inv was not initialized yet.
                SASSERT(m_elems.contains(n));
                SASSERT(m_inv.empty());
                m_elems.erase(n);
                TRACE("model_finder", tout << mk_pp(n, m) << "\n";);
                m.dec_ref(n);
            }

            void display(std::ostream& out) const {
                for (auto const& kv : m_elems) {
                    out << mk_bounded_pp(kv.m_key, m) << " [" << kv.m_value << "]\n";
                }
                out << "inverse:\n";
                for (auto const& kv : m_inv) {
                    out << mk_bounded_pp(kv.m_key, m) << " -> " << mk_bounded_pp(kv.m_value, m) << "\n";
                }
            }

            expr* get_inv(expr* v) const {
                expr* t = nullptr;
                m_inv.find(v, t);
                return t;
            }

            unsigned get_generation(expr* t) const {
                unsigned gen = 0;
                m_elems.find(t, gen);
                return gen;
            }

            void mk_inverse(evaluator& ev) {
                for (auto const& kv : m_elems) {
                    expr* t = kv.m_key;
                    SASSERT(!contains_model_value(t));
                    unsigned gen = kv.m_value;
                    expr* t_val = ev.eval(t, true);
                    if (!t_val) break;
                    TRACE("model_finder", tout << mk_pp(t, m) << " " << mk_pp(t_val, m) << "\n";);

                    expr* old_t = nullptr;
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

            obj_map<expr, expr*> const& get_inv_map() const {
                return m_inv;
            }

            struct is_model_value {};
            void operator()(expr* n) {
                if (m.is_model_value(n)) {
                    throw is_model_value();
                }
            }

            bool contains_model_value(expr* n) {
                if (m.is_model_value(n)) {
                    return true;
                }
                if (is_app(n) && to_app(n)->get_num_args() == 0) {
                    return false;
                }
                m_visited.reset();
                try {
                    for_each_expr(*this, m_visited, n);
                }
                catch (const is_model_value&) {
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

        /**
           \brief Base class used to solve model construction constraints.
        */
        class node {
            unsigned            m_id;
            node* m_find{ nullptr };
            unsigned            m_eqc_size{ 1 };

            sort* m_sort; // sort of the elements in the instantiation set.

            bool                m_mono_proj{ false };     // relevant for integers & reals & bit-vectors
            bool                m_signed_proj{ false };   // relevant for bit-vectors.
            ptr_vector<node>    m_avoid_set;
            ptr_vector<expr>    m_exceptions;

            scoped_ptr<instantiation_set> m_set;
            expr* m_else{ nullptr };
            func_decl* m_proj{ nullptr };

            // Append the new elements of v2 into v1. v2 should not be used after this operation, since it may suffer destructive updates.
            template<typename T>
            void dappend(ptr_vector<T>& v1, ptr_vector<T>& v2) {
                if (v2.empty())
                    return;
                if (v1.empty()) {
                    v1.swap(v2);
                    return;
                }
                for (T* t : v2) {
                    if (!v1.contains(t))
                        v1.push_back(t);
                }
                v2.finalize();
            }
        public:
            node(unsigned id, sort* s) :
                m_id(id),
                m_sort(s) {
            }

            ~node() {}

            unsigned get_id() const { return m_id; }

            sort* get_sort() const { return m_sort; }

            bool is_root() const { return m_find == nullptr; }

            node* get_root() const {
                node* curr = const_cast<node*>(this);
                while (!curr->is_root()) {
                    curr = curr->m_find;
                }
                SASSERT(curr->is_root());
                return curr;
            }

            void merge(node* other) {
                node* r1 = get_root();
                node* r2 = other->get_root();
                SASSERT(!r1->m_set);
                SASSERT(!r2->m_set);
                SASSERT(r1->get_sort() == r2->get_sort());
                if (r1 == r2)
                    return;
                if (r1->m_eqc_size > r2->m_eqc_size)
                    std::swap(r1, r2);
                r1->m_find = r2;
                r2->m_eqc_size    += r1->m_eqc_size;
                r2->m_mono_proj   |= r1->m_mono_proj;
                r2->m_signed_proj |= r1->m_signed_proj;
                dappend(r2->m_avoid_set, r1->m_avoid_set);
                dappend(r2->m_exceptions, r1->m_exceptions);
            }

            void insert_avoid(node* n) {
                ptr_vector<node>& as = get_root()->m_avoid_set;
                if (!as.contains(n))
                    as.push_back(n);
            }

            void insert_exception(expr* n) {
                ptr_vector<expr>& ex = get_root()->m_exceptions;
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

            void mk_instantiation_set(ast_manager& m) {
                SASSERT(is_root());
                SASSERT(!m_set);
                m_set = alloc(instantiation_set, m);
            }

            void insert(expr* n, unsigned generation) {
                SASSERT(is_ground(n));
                get_root()->m_set->insert(n, generation);
            }

            void display(std::ostream& out, ast_manager& m) const {
                if (is_root()) {
                    out << "root node ------\n";
                    out << "@" << m_id << " mono: " << m_mono_proj << " signed: " << m_signed_proj << ", sort: " << mk_pp(m_sort, m) << "\n";
                    out << "avoid-set: ";
                    for (node* n : m_avoid_set) {
                        out << "@" << n->get_root()->get_id() << " ";
                    }
                    out << "\n";
                    out << "exceptions: ";
                    for (expr* e : m_exceptions) {
                        out << mk_bounded_pp(e, m) << " ";
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

            instantiation_set const* get_instantiation_set() const { return get_root()->m_set.get(); }

            instantiation_set* get_instantiation_set() { return get_root()->m_set.get(); }

            ptr_vector<expr> const& get_exceptions() const { return get_root()->m_exceptions; }

            ptr_vector<node> const& get_avoid_set() const { return get_root()->m_avoid_set; }

            // return true if m_avoid_set.contains(this)
            bool must_avoid_itself() const {
                node* r = get_root();
                for (node* n : m_avoid_set) {
                    if (r == n->get_root())
                        return true;
                }
                return false;
            }

            void set_else(expr* e) {
                SASSERT(!is_mono_proj());
                SASSERT(get_root()->m_else == nullptr);
                get_root()->m_else = e;
            }

            expr* get_else() const {
                return get_root()->m_else;
            }

            void set_proj(func_decl* f) {
                SASSERT(get_root()->m_proj == nullptr);
                get_root()->m_proj = f;
            }

            func_decl* get_proj() const {
                return get_root()->m_proj;
            }
        };


        typedef std::pair<ast*, unsigned> ast_idx_pair;
        typedef pair_hash<obj_ptr_hash<ast>, unsigned_hash> ast_idx_pair_hash;
        typedef map<ast_idx_pair, node*, ast_idx_pair_hash, default_eq<ast_idx_pair> > key2node;


        /**
           \brief Auxiliary class for processing the "Almost uninterpreted fragment" described in the paper:
           Complete instantiation for quantified SMT formulas

           The idea is to create node objects based on the information produced by the quantifier_analyzer.
        */
        class auf_solver : public evaluator {
            ast_manager& m;
            arith_util                m_arith;
            bv_util                   m_bv;
            array_util                m_array;
            ptr_vector<node>          m_nodes;
            unsigned                  m_next_node_id{ 0 };
            key2node                  m_uvars;
            key2node                  m_A_f_is;

            // Mapping from sort to auxiliary constant.
            // This auxiliary constant is used as a "witness" that is asserted as different from a
            // finite number of terms.
            // It is only safe to use this constant for infinite sorts.
            obj_map<sort, app*>       m_sort2k;
            expr_ref_vector           m_ks; // range of m_sort2k

            // Support for evaluating expressions in the current model.
            proto_model*              m_model{ nullptr };
            obj_map<expr, expr*>      m_eval_cache[2];
            expr_ref_vector           m_eval_cache_range;

            ptr_vector<node>          m_root_nodes;

            expr_ref_vector*          m_new_constraints{ nullptr };
            random_gen                m_rand;
            func_decl_set             m_specrels;


            void reset_sort2k() {
                m_sort2k.reset();
                m_ks.reset();
            }

            void reset_eval_cache() {
                m_eval_cache[0].reset();
                m_eval_cache[1].reset();
                m_eval_cache_range.reset();
            }

            node* mk_node(key2node& map, ast* n, unsigned i, sort* s) {
                node* r = nullptr;
                ast_idx_pair k(n, i);
                if (map.find(k, r)) {
                    SASSERT(r->get_sort() == s);
                    return r;
                }
                r = alloc(node, m_next_node_id, s);
                m_next_node_id++;
                map.insert(k, r);
                m_nodes.push_back(r);
                return r;
            }

            void display_key2node(std::ostream& out, key2node const& m) const {
                for (auto const& kv : m) {
                    ast* a = kv.m_key.first;
                    unsigned i = kv.m_key.second;
                    node* n = kv.m_value;
                    out << "#" << a->get_id() << ":" << i << " -> @" << n->get_id() << "\n";
                }
            }

            void display_A_f_is(std::ostream& out) const {
                for (auto const& kv : m_A_f_is) {
                    func_decl* f = static_cast<func_decl*>(kv.m_key.first);
                    unsigned    i = kv.m_key.second;
                    node* n = kv.m_value;
                    out << f->get_name() << ":" << i << " -> @" << n->get_id() << "\n";
                }
            }

            void flush_nodes() {
                std::for_each(m_nodes.begin(), m_nodes.end(), delete_proc<node>());
            }

        public:
            auf_solver(ast_manager& m) :
                m(m),
                m_arith(m),
                m_bv(m),
                m_array(m),
                m_ks(m),
                m_eval_cache_range(m),
                m_rand(static_cast<unsigned>(m.limit().count())) {
                m.limit().inc();
            }

            virtual ~auf_solver() {
                flush_nodes();
                reset_eval_cache();
            }

            ast_manager& get_manager() const { return m; }

            void reset() {
                m_specrels.reset();
                flush_nodes();
                m_nodes.reset();
                m_next_node_id = 0;
                m_uvars.reset();
                m_A_f_is.reset();
                m_root_nodes.reset();
                reset_sort2k();
            }

            void set_specrels(context& c) {
                m_specrels.reset();
                c.get_specrels(m_specrels);
            }

            void set_model(proto_model* m) {
                reset_eval_cache();
                m_model = m;
            }

            proto_model* get_model() const {
                SASSERT(m_model);
                return m_model;
            }

            node* get_uvar(quantifier* q, unsigned i) {
                SASSERT(i < q->get_num_decls());
                sort* s = q->get_decl_sort(q->get_num_decls() - i - 1);
                return mk_node(m_uvars, q, i, s);
            }

            node* get_A_f_i(func_decl* f, unsigned i) {
                SASSERT(i < f->get_arity());
                sort* s = f->get_domain(i);
                return mk_node(m_A_f_is, f, i, s);
            }

            instantiation_set const* get_uvar_inst_set(quantifier* q, unsigned i) const {
                ast_idx_pair k(q, i);
                node* r = nullptr;
                if (m_uvars.find(k, r))
                    return r->get_instantiation_set();
                return nullptr;
            }

            void mk_instantiation_sets() {
                for (node* curr : m_nodes) {
                    if (curr->is_root()) {
                        curr->mk_instantiation_set(m);
                    }
                }
            }

            // For each instantiation_set, remove entries that do not evaluate to values.
            ptr_vector<expr> to_delete;

            bool should_cleanup(expr* e) {
                if (!e)
                    return true;
                if (m.is_value(e))
                    return false;
                if (m_array.is_array(e))
                    return false;
                if (!is_app(e))
                    return true;
                if (to_app(e)->get_num_args() == 0)
                    return true;
                return !contains_array(e);
            }

            struct found_array {};
            expr_mark m_visited;
            void operator()(expr* n) {
                if (m_array.is_array(n))
                    throw found_array();
            }
            bool contains_array(expr* e) {
                m_visited.reset();
                try {
                    for_each_expr(*this, m_visited, e);
                }
                catch (const found_array&) {
                    return true;
                }
                return false;                
            }

           
            void cleanup_instantiation_sets() {
                for (node* curr : m_nodes) {
                    if (curr->is_root()) {
                        instantiation_set* s = curr->get_instantiation_set();
                        to_delete.reset();
                        obj_map<expr, unsigned> const& elems = s->get_elems();
                        for (auto const& kv : elems) {
                            expr* n = kv.m_key;
                            expr* n_val = eval(n, true);
                            if (should_cleanup(n_val)) {
                                TRACE("model_finder", tout << "cleanup " << s << " " << mk_pp(n, m) << " " << mk_pp(n_val, m) << "\n";);
                                to_delete.push_back(n);
                            }
                        }
                        for (expr* e : to_delete) {
                            s->remove(e);
                        }
                    }
                }
            }

            void display_nodes(std::ostream& out) const {
                display_key2node(out, m_uvars);
                display_A_f_is(out);
                for (node* n : m_nodes) {
                    n->display(out, m);
                }
            }

            expr* eval(expr* n, bool model_completion) override {
                expr* r = nullptr;
                if (m_eval_cache[model_completion].find(n, r)) {
                    return r;
                }
                expr_ref tmp(m);
                if (!m_model->eval(n, tmp, model_completion)) {
                    r = nullptr;
                    TRACE("model_finder", tout << "eval\n" << mk_pp(n, m) << "\n-----> null\n";);
                }
                else {
                    r = tmp;
                    TRACE("model_finder", tout << "eval\n" << mk_pp(n, m) << "\n----->\n" << mk_pp(r, m) << "\n";);
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
            void collect_exceptions_values(node* n, ptr_buffer<expr>& r) {

                for (expr* e : n->get_exceptions()) {
                    expr* val = eval(e, true);
                    if (val)
                        r.push_back(val);
                }

                for (node* a : n->get_avoid_set()) {
                    node* p = a->get_root();
                    if (!p->is_mono_proj() && p->get_else() != nullptr) {
                        expr* val = eval(p->get_else(), true);
                        if (val)
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
            expr* pick_instance_diff_exceptions(node* n, ptr_buffer<expr> const& ex_vals) {
                instantiation_set const* s = n->get_instantiation_set();
                obj_map<expr, unsigned> const& elems = s->get_elems();

                expr* t_result = nullptr;
                unsigned  gen_result = UINT_MAX;
                for (auto const& kv : elems) {
                    expr* t = kv.m_key;
                    unsigned gen = kv.m_value;
                    expr* t_val = eval(t, true);
                    if (!t_val)
                        return t_result;
                    bool found = false;
                    for (expr* v : ex_vals) {
                        if (!m.are_distinct(t_val, v)) {
                            found = true;
                            break;
                        }
                    }
                    if (!found && (t_result == nullptr || gen < gen_result)) {
                        t_result = t;
                        gen_result = gen;
                    }
                }
                return t_result;
            }

            // we should not assume that uninterpreted sorts are infinite in benchmarks with quantifiers.
            bool is_infinite(sort* s) const { return !m.is_uninterp(s) && s->is_infinite(); }

            /**
               \brief Return a fresh constant k that is used as a witness for elements that must be different from
               a set of values.
            */
            app* get_k_for(sort* s) {
                SASSERT(is_infinite(s));
                app* r = nullptr;
                if (m_sort2k.find(s, r))
                    return r;
                r = m.mk_fresh_const("k", s);
                m_model->register_aux_decl(r->get_decl());
                m_sort2k.insert(s, r);
                m_ks.push_back(r);
                TRACE("model_finder", tout << sort_ref(s, m) << " := " << "\n";);
                return r;
            }

            /**
               \brief Get the interpretation for k in m_model.
               If m_model does not provide an interpretation for k, then
               create a fresh one.

               Remark: this method uses get_fresh_value, so it may fail.
            */
            expr* get_k_interp(app* k) {
                sort* s = k->get_sort();
                SASSERT(is_infinite(s));
                func_decl* k_decl = k->get_decl();
                expr* r = m_model->get_const_interp(k_decl);
                if (r != nullptr)
                    return r;
                r = m_model->get_fresh_value(s);
                if (r == nullptr)
                    return nullptr;
                m_model->register_decl(k_decl, r);
                SASSERT(m_model->get_const_interp(k_decl) == r);
                TRACE("model_finder", tout << mk_pp(r, m) << "\n";);
                return r;
            }

            /**
               \brief Assert k to be different from the set of exceptions.

               It invokes get_k_interp that may fail.
            */
            bool assert_k_diseq_exceptions(app* k, ptr_vector<expr> const& exceptions) {
                TRACE("assert_k_diseq_exceptions", tout << "assert_k_diseq_exceptions, " << "k: " << mk_pp(k, m) << "\nexceptions:\n";
                for (expr* e : exceptions) tout << mk_pp(e, m) << "\n";);
                expr* k_interp = get_k_interp(k);
                if (k_interp == nullptr)
                    return false;
                for (expr* ex : exceptions) {
                    expr* ex_val = eval(ex, true);
                    if (ex_val && !m.are_distinct(k_interp, ex_val)) {
                        SASSERT(m_new_constraints);
                        // This constraint cannot be asserted into m_context during model construction.
                        // We must save it, and assert it during a restart.
                        m_new_constraints->push_back(m.mk_not(m.mk_eq(k, ex)));
                    }
                }
                return true;
            }

            void set_projection_else(node* n) {
                TRACE("model_finder", n->display(tout, m););
                SASSERT(n->is_root());
                SASSERT(!n->is_mono_proj());
                instantiation_set const* s = n->get_instantiation_set();
                ptr_vector<expr> const& exceptions = n->get_exceptions();
                ptr_vector<node> const& avoid_set = n->get_avoid_set();
                obj_map<expr, unsigned> const& elems = s->get_elems();
                if (elems.empty()) return;
                if (!exceptions.empty() || !avoid_set.empty()) {
                    ptr_buffer<expr> ex_vals;
                    collect_exceptions_values(n, ex_vals);
                    expr* e = pick_instance_diff_exceptions(n, ex_vals);
                    if (e != nullptr) {
                        n->set_else(e);
                        return;
                    }
                    sort* s = n->get_sort();
                    TRACE("model_finder", tout << "trying to create k for " << mk_pp(s, m) << ", is_infinite: " << is_infinite(s) << "\n";);
                    if (is_infinite(s)) {
                        app* k = get_k_for(s);
                        if (assert_k_diseq_exceptions(k, exceptions)) {
                            n->insert(k, 0); // add k to the instantiation set
                            n->set_else(k);
                            return;
                        }
                    }
                    // TBD: add support for the else of bitvectors.
                    // Idea: get the term t with the minimal interpretation and use t - 1.
                }
                n->set_else((*(elems.begin())).m_key);
            }

            /**
               \brief If m_mono_proj is true and n is int or bv, then for each e in n->get_exceptions(),
               we must add e-1 and e+1 to the instantiation set.
               If sort->get_sort() is real, then we do nothing and hope for the best.
            */
            void add_mono_exceptions(node* n) {
                SASSERT(n->is_mono_proj());
                sort* s = n->get_sort();
                arith_rewriter arw(m);
                bv_rewriter brw(m);
                ptr_vector<expr> const& exceptions = n->get_exceptions();
                expr_ref e_minus_1(m), e_plus_1(m);
                if (m_arith.is_int(s)) {
                    expr_ref one(m_arith.mk_int(1), m);
                    arith_rewriter arith_rw(m);
                    for (expr* e : exceptions) {
                        arith_rw.mk_sub(e, one, e_minus_1);
                        arith_rw.mk_add(e, one, e_plus_1);
                        TRACE("mf_simp_bug", tout << "e:\n" << mk_ismt2_pp(e, m) << "\none:\n" << mk_ismt2_pp(one, m) << "\n";);
                        // Note: exceptions come from quantifiers bodies. So, they have generation 0.
                        n->insert(e_plus_1, 0);
                        n->insert(e_minus_1, 0);
                    }
                }
                else if (m_bv.is_bv_sort(s)) {
                    expr_ref one(m_bv.mk_numeral(rational(1), s), m);
                    bv_rewriter bv_rw(m);
                    for (expr* e : exceptions) {
                        bv_rw.mk_add(e, one, e_plus_1);
                        bv_rw.mk_sub(e, one, e_minus_1);
                        TRACE("mf_simp_bug", tout << "e:\n" << mk_ismt2_pp(e, m) << "\none:\n" << mk_ismt2_pp(one, m) << "\n";);
                        // Note: exceptions come from quantifiers bodies. So, they have generation 0.
                        n->insert(e_plus_1, 0);
                        n->insert(e_minus_1, 0);
                    }
                }
                else {
                    return;
                }
            }

            void get_instantiation_set_values(node* n, ptr_buffer<expr>& values) {
                instantiation_set const* s = n->get_instantiation_set();
                obj_hashtable<expr> already_found;
                obj_map<expr, unsigned> const& elems = s->get_elems();
                for (auto const& kv : elems) {
                    expr* t = kv.m_key;
                    expr* t_val = eval(t, true);
                    bool found = false;
                    if (t_val && !m.is_unique_value(t_val))                         
                        for (expr* v : values)
                            found |= m.are_equal(v, t_val);
                    if (t_val && !found && !already_found.contains(t_val)) {
                        values.push_back(t_val);
                        already_found.insert(t_val);
                    }
                }
                TRACE("model_finder_bug", tout << "values for the instantiation_set of @" << n->get_id() << "\n";
                for (expr* v : values) {
                    tout << mk_pp(v, m) << "\n";
                });
            }

            template<class T>
            struct numeral_lt {
                T& m_util;
                numeral_lt(T& a) : m_util(a) {}
                bool operator()(expr* e1, expr* e2) {
                    rational v1, v2;
                    if (m_util.is_numeral(e1, v1) && m_util.is_numeral(e2, v2)) {
                        return v1 < v2;
                    }
                    else {
                        return e1->get_id() < e2->get_id();
                    }
                }
            };


            struct signed_bv_lt {
                bv_util& m_bv;
                unsigned               m_bv_size;
                signed_bv_lt(bv_util& bv, unsigned sz) :m_bv(bv), m_bv_size(sz) {}
                bool operator()(expr* e1, expr* e2) {
                    rational v1, v2;
                    if (m_bv.is_numeral(e1, v1) && m_bv.is_numeral(e2, v2)) {
                        v1 = m_bv.norm(v1, m_bv_size, true);
                        v2 = m_bv.norm(v2, m_bv_size, true);
                        return v1 < v2;
                    }
                    else {
                        return e1->get_id() < e2->get_id();
                    }
                }
            };

            void sort_values(node* n, ptr_buffer<expr>& values) {
                sort* s = n->get_sort();
                if (m_arith.is_int(s) || m_arith.is_real(s)) {
                    std::sort(values.begin(), values.end(), numeral_lt<arith_util>(m_arith));
                }
                else if (!n->is_signed_proj()) {
                    std::sort(values.begin(), values.end(), numeral_lt<bv_util>(m_bv));
                }
                else {
                    std::sort(values.begin(), values.end(), signed_bv_lt(m_bv, m_bv.get_bv_size(s)));
                }
            }

            void mk_mono_proj(node* n) {
                add_mono_exceptions(n);
                ptr_buffer<expr> values;
                get_instantiation_set_values(n, values);
                if (values.empty()) return;
                sort_values(n, values);
                sort* s = n->get_sort();
                bool is_arith = m_arith.is_int(s) || m_arith.is_real(s);
                bool is_signed = n->is_signed_proj();
                unsigned sz = values.size();
                SASSERT(sz > 0);
                expr* pi = values[sz - 1];
                expr_ref var(m);
                var = m.mk_var(0, s);
                for (unsigned i = sz - 1; i >= 1; i--) {
                    expr_ref c(m);
                    if (is_arith)
                        c = m_arith.mk_lt(var, values[i]);
                    else if (!is_signed)
                        c = m.mk_not(m_bv.mk_ule(values[i], var));
                    else
                        c = m.mk_not(m_bv.mk_sle(values[i], var));
                    pi = m.mk_ite(c, values[i - 1], pi);
                }
                func_interp* rpi = alloc(func_interp, m, 1);
                rpi->set_else(pi);
                func_decl* p = m.mk_fresh_func_decl(1, &s, s);
                m_model->register_aux_decl(p, rpi);
                n->set_proj(p);
                TRACE("model_finder", n->display(tout << p->get_name() << "\n", m););
            }

            void mk_simple_proj(node* n) {
                set_projection_else(n);
                ptr_buffer<expr> values;
                get_instantiation_set_values(n, values);
                sort* s = n->get_sort();
                func_decl* p = m.mk_fresh_func_decl(1, &s, s);
                func_interp* pi = alloc(func_interp, m, 1);
                m_model->register_aux_decl(p, pi);
                if (n->get_else()) {
                    expr* else_val = eval(n->get_else(), true);
                    if (else_val)
                        pi->set_else(else_val);
                }
                for (expr* v : values) 
                    pi->insert_new_entry(&v, v);
                
                n->set_proj(p);
                TRACE("model_finder", n->display(tout << p->get_name() << "\n", m););
            }

            void mk_projections() {
                for (node* n : m_root_nodes) {
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
            void collect_partial_funcs(func_decl_set& r) {
                for (auto const& kv : m_A_f_is) {
                    func_decl* f = to_func_decl(kv.m_key.first);
                    if (!r.contains(f)) {
                        func_interp* fi = m_model->get_func_interp(f);
                        if (fi == nullptr) {
                            fi = alloc(func_interp, m, f->get_arity());
                            TRACE("model_finder", tout << "register " << f->get_name() << "\n";);
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
                for (node* n : m_root_nodes) {
                    SASSERT(n->is_root());
                    sort* s = n->get_sort();
                    if (m.is_uninterp(s) &&
                        // Making all uninterpreted sorts finite.
                        // n->must_avoid_itself() &&
                        !m_model->is_finite(s)) {
                        m_model->freeze_universe(s);
                    }
                }
            }

            void add_elem_to_empty_inst_sets() {
                obj_map<sort, expr*> sort2elems;
                ptr_vector<node> need_fresh;
                for (node* n : m_root_nodes) {
                    SASSERT(n->is_root());
                    instantiation_set const* s = n->get_instantiation_set();
                    TRACE("model_finder", s->display(tout););
                    obj_map<expr, unsigned> const& elems = s->get_elems();
                    if (elems.empty()) {
                        // The method get_some_value cannot be used if n->get_sort() is an uninterpreted sort or is a sort built using uninterpreted sorts
                        // (e.g., (Array S S) where S is uninterpreted). The problem is that these sorts do not have a fixed interpretation.
                        // Moreover, a model assigns an arbitrary interpretation to these sorts using "model_values" a model value.
                        // If these module values "leak" inside the logical context, they may affect satisfiability.
                        //
                        sort* ns = n->get_sort();
                        if (m.is_fully_interp(ns)) {
                            n->insert(m_model->get_some_value(ns), 0);
                        }
                        else {
                            need_fresh.push_back(n);
                        }
                    }
                    else {
                        sort2elems.insert(n->get_sort(), elems.begin()->m_key);
                    }
                }
                expr_ref_vector trail(m);
                for (node* n : need_fresh) {
                    expr* e;
                    sort* s = n->get_sort();
                    if (!sort2elems.find(s, e)) {
                        e = m.mk_fresh_const("elem", s);
                        trail.push_back(e);
                        sort2elems.insert(s, e);
                    }
                    n->insert(e, 0);
                    TRACE("model_finder", tout << "fresh constant: " << mk_pp(e, m) << "\n";);
                }
            }

            /**
               \brief Store in m_root_nodes the roots from m_nodes.
             */
            void collect_root_nodes() {
                m_root_nodes.reset();
                for (node* n : m_nodes) {
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
               projections we used the evaluator with model_completion,
               and it may have fixed the "else" case of some partial interpretations.
               This is ok, because in the "limit" the "else" of the interpretation
               is irrelevant after the projections are applied.
            */
            func_decl* get_f_i_proj(func_decl* f, unsigned i) {
                node* r = nullptr;
                ast_idx_pair k(f, i);
                if (!m_A_f_is.find(k, r))
                    return nullptr;
                return r->get_proj();
            }

            /**
               \brief Complete the interpretation of the functions that were
               collected in the beginning of fix_model().
             */
            void complete_partial_funcs(func_decl_set const& partial_funcs) {
                for (func_decl* f : partial_funcs) {

                    // Complete the current interpretation
                    m_model->complete_partial_func(f, true);

                    if (m_specrels.contains(f))
                        continue;

                    unsigned arity = f->get_arity();
                    func_interp* fi = m_model->get_func_interp(f);
                    if (fi->is_constant())
                        continue; // there is no point in using the projection for fi, since fi is the constant function.

                    expr_ref_vector args(m);
                    bool has_proj = false;
                    for (unsigned i = 0; i < arity; i++) {
                        var* v = m.mk_var(i, f->get_domain(i));
                        func_decl* pi = get_f_i_proj(f, i);
                        if (pi != nullptr) {
                            args.push_back(m.mk_app(pi, v));
                            has_proj = true;
                        }
                        else {
                            args.push_back(v);
                        }
                    }
                    if (has_proj) {
                        // f_aux will be assigned to the old interpretation of f.
                        func_decl* f_aux = m.mk_fresh_func_decl(f->get_name(), symbol::null, arity, f->get_domain(), f->get_range());
                        func_interp* new_fi = alloc(func_interp, m, arity);
                        new_fi->set_else(m.mk_app(f_aux, args.size(), args.data()));
                        TRACE("model_finder", tout << "Setting new interpretation for " << f->get_name() << "\n" <<
                            mk_pp(new_fi->get_else(), m) << "\n";
                        tout << "old interpretation: " << mk_pp(fi->get_interp(), m) << "\n";);
                        m_model->reregister_decl(f, new_fi, f_aux);
                    }
                }
            }

            void mk_inverse(node* n) {
                SASSERT(n->is_root());
                instantiation_set* s = n->get_instantiation_set();
                s->mk_inverse(*this);
            }

            void mk_inverses() {
                unsigned offset = m_rand();
                for (unsigned i = m_root_nodes.size(); i-- > 0; ) {
                    node* n = m_root_nodes[(i + offset) % m_root_nodes.size()];
                    SASSERT(n->is_root());
                    mk_inverse(n);
                }
            }

        public:
            void fix_model(expr_ref_vector& new_constraints) {
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

            bool is_default_representative(expr* t) {
                app* tt = nullptr;
                return t && m_sort2k.find(t->get_sort(), tt) && (tt == t);
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
        protected:
            ast_manager& m;
        public:
            qinfo(ast_manager& m) :m(m) {}
            virtual ~qinfo() {}
            virtual char const* get_kind() const = 0;
            virtual bool is_equal(qinfo const* qi) const = 0;
            virtual void display(std::ostream& out) const { out << "[" << get_kind() << "]"; }

            // AUF fragment solver
            virtual void process_auf(quantifier* q, auf_solver& s, context* ctx) = 0;
            virtual void populate_inst_sets(quantifier* q, auf_solver& s, context* ctx) = 0;
            // second pass... actually we may need to reach a fixpoint, but if it cannot be found
            // in two passes, the fixpoint is not finite.
            virtual void populate_inst_sets2(quantifier* q, auf_solver& s, context* ctx) {}

            // Macro/Hint support
            virtual void populate_inst_sets(quantifier* q, func_decl* mhead, ptr_vector<instantiation_set>& uvar_inst_sets, context* ctx) {}
        };

        class f_var : public qinfo {
        protected:
            func_decl* m_f;
            unsigned    m_arg_i;
            unsigned    m_var_j;
        public:
            f_var(ast_manager& m, func_decl* f, unsigned i, unsigned j) : qinfo(m), m_f(f), m_arg_i(i), m_var_j(j) {}
            ~f_var() override {}

            char const* get_kind() const override {
                return "f_var";
            }

            bool is_equal(qinfo const* qi) const override {
                if (qi->get_kind() != get_kind())
                    return false;
                f_var const* other = static_cast<f_var const*>(qi);
                return m_f == other->m_f && m_arg_i == other->m_arg_i && m_var_j == other->m_var_j;
            }

            void display(std::ostream& out) const override {
                out << "(" << m_f->get_name() << ":" << m_arg_i << " -> v!" << m_var_j << ")";
            }

            void process_auf(quantifier* q, auf_solver& s, context* ctx) override {
                node* n1 = s.get_A_f_i(m_f, m_arg_i);
                node* n2 = s.get_uvar(q, m_var_j);
                CTRACE("model_finder", n1->get_sort() != n2->get_sort(),
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

            void populate_inst_sets(quantifier* q, auf_solver& s, context* ctx) override {
                node* A_f_i = s.get_A_f_i(m_f, m_arg_i);
                for (enode* n : ctx->enodes_of(m_f)) {
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
                        enode* e_arg = n->get_arg(m_arg_i);
                        expr* arg = e_arg->get_expr();
                        A_f_i->insert(arg, e_arg->get_generation());
                    }
                }
            }

            void populate_inst_sets(quantifier* q, func_decl* mhead, ptr_vector<instantiation_set>& uvar_inst_sets, context* ctx) override {
                if (m_f != mhead)
                    return;
                uvar_inst_sets.reserve(m_var_j + 1, 0);
                if (uvar_inst_sets[m_var_j] == 0)
                    uvar_inst_sets[m_var_j] = alloc(instantiation_set, ctx->get_manager());
                instantiation_set* s = uvar_inst_sets[m_var_j];
                SASSERT(s != nullptr);

                for (enode* n : ctx->enodes_of(m_f)) {
                    if (ctx->is_relevant(n)) {
                        enode* e_arg = n->get_arg(m_arg_i);
                        expr* arg = e_arg->get_expr();
                        s->insert(arg, e_arg->get_generation());
                    }
                }
            }
        };

        class f_var_plus_offset : public f_var {
            expr_ref    m_offset;
        public:
            f_var_plus_offset(ast_manager& m, func_decl* f, unsigned i, unsigned j, expr* offset) :
                f_var(m, f, i, j),
                m_offset(offset, m) {
            }
            ~f_var_plus_offset() override {}

            char const* get_kind() const override {
                return "f_var_plus_offset";
            }

            bool is_equal(qinfo const* qi) const override {
                if (qi->get_kind() != get_kind())
                    return false;
                f_var_plus_offset const* other = static_cast<f_var_plus_offset const*>(qi);
                return m_f == other->m_f && m_arg_i == other->m_arg_i && m_var_j == other->m_var_j && m_offset.get() == other->m_offset.get();
            }

            void display(std::ostream& out) const override {
                out << "(" << m_f->get_name() << ":" << m_arg_i << " - " <<
                    mk_bounded_pp(m_offset.get(), m_offset.get_manager()) << " -> v!" << m_var_j << ")";
            }

            void process_auf(quantifier* q, auf_solver& s, context* ctx) override {
                // just create the nodes
                /* node * A_f_i = */ s.get_A_f_i(m_f, m_arg_i);
                /* node * S_j   = */ s.get_uvar(q, m_var_j);
            }

            void populate_inst_sets(quantifier* q, auf_solver& s, context* ctx) override {
                // S_j is not necessary equal to A_f_i.
                node* A_f_i = s.get_A_f_i(m_f, m_arg_i)->get_root();
                node* S_j = s.get_uvar(q, m_var_j)->get_root();
                if (A_f_i == S_j) {
                    // there is no finite fixpoint... we just copy the i-th arguments of A_f_i - m_offset
                    // hope for the best...
                    node* S_j = s.get_uvar(q, m_var_j);
                    for (enode* n : ctx->enodes_of(m_f)) {
                        if (ctx->is_relevant(n)) {
                            arith_rewriter arith_rw(m);
                            bv_util bv(m);
                            bv_rewriter bv_rw(m);
                            enode* e_arg = n->get_arg(m_arg_i);
                            expr* arg = e_arg->get_expr();
                            expr_ref arg_minus_k(m);
                            if (bv.is_bv(arg))
                                bv_rw.mk_sub(arg, m_offset, arg_minus_k);
                            else
                                arith_rw.mk_sub(arg, m_offset, arg_minus_k);
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
            void copy_instances(node* from, node* to, auf_solver& s) {
                instantiation_set const* from_s = from->get_instantiation_set();
                obj_map<expr, unsigned> const& elems_s = from_s->get_elems();

                arith_rewriter arith_rw(m_offset.get_manager());
                bv_rewriter bv_rw(m_offset.get_manager());
                bool is_bv = bv_util(m_offset.get_manager()).is_bv_sort(from->get_sort());

                for (auto const& kv : elems_s) {
                    expr* n = kv.m_key;
                    expr_ref n_k(m_offset.get_manager());
                    if (PLUS) {
                        if (is_bv) {
                            bv_rw.mk_add(n, m_offset, n_k);
                        }
                        else {
                            arith_rw.mk_add(n, m_offset, n_k);
                        }
                    }
                    else {
                        if (is_bv) {
                            bv_rw.mk_sub(n, m_offset, n_k);
                        }
                        else {
                            arith_rw.mk_sub(n, m_offset, n_k);
                        }
                    }
                    to->insert(n_k, kv.m_value);
                }
            }

            void populate_inst_sets2(quantifier* q, auf_solver& s, context* ctx) override {
                node* A_f_i = s.get_A_f_i(m_f, m_arg_i)->get_root();
                node* S_j = s.get_uvar(q, m_var_j)->get_root();
                // If A_f_i == S_j, then there is no finite fixpoint, so we do nothing here.
                if (A_f_i != S_j) {
                    //  enforce
                    //  A_f_i - k \subset S_j
                    //  S_j + k   \subset A_f_i
                    copy_instances<false>(A_f_i, S_j, s);
                    copy_instances<true>(S_j, A_f_i, s);
                }
            }

            void populate_inst_sets(quantifier* q, func_decl* mhead, ptr_vector<instantiation_set>& uvar_inst_sets, context* ctx) override {
                // ignored when in macro
            }

        };


        /**
           \brief auf_arr is a term (pattern) of the form:

           FORM :=  GROUND-TERM
                |   (select FORM VAR)

           Store in arrays, all enodes that match the pattern
        */
        void get_auf_arrays(app* auf_arr, context* ctx, ptr_buffer<enode>& arrays) {
            if (is_ground(auf_arr)) {
                if (ctx->e_internalized(auf_arr)) {
                    enode* e = ctx->get_enode(auf_arr);
                    if (ctx->is_relevant(e)) {
                        arrays.push_back(e);
                    }
                }
            }
            else {
                app* nested_array = to_app(auf_arr->get_arg(0));
                ptr_buffer<enode> nested_arrays;
                get_auf_arrays(nested_array, ctx, nested_arrays);
                for (enode* curr : nested_arrays) {
                    enode_vector::iterator it2 = curr->begin_parents();
                    enode_vector::iterator end2 = curr->end_parents();
                    for (; it2 != end2; ++it2) {
                        enode* p = *it2;
                        if (ctx->is_relevant(p) && p->get_expr()->get_decl() == auf_arr->get_decl()) {
                            arrays.push_back(p);
                        }
                    }
                }
            }
        }

        class select_var : public qinfo {
        protected:
            array_util    m_array;
            app* m_select; // It must satisfy is_auf_select... see bool is_auf_select(expr * t) const
            unsigned      m_arg_i;
            unsigned      m_var_j;

            app* get_array() const { return to_app(m_select->get_arg(0)); }

            func_decl* get_array_func_decl(app* ground_array, auf_solver& s) {
                TRACE("model_evaluator", tout << expr_ref(ground_array, m) << "\n";);
                expr* ground_array_interp = s.eval(ground_array, false);
                if (ground_array_interp && m_array.is_as_array(ground_array_interp))
                    return m_array.get_as_array_func_decl(ground_array_interp);
                return nullptr;
            }

        public:
            select_var(ast_manager& m, app* s, unsigned i, unsigned j) :qinfo(m), m_array(m), m_select(s), m_arg_i(i), m_var_j(j) {}
            ~select_var() override {}

            char const* get_kind() const override {
                return "select_var";
            }

            bool is_equal(qinfo const* qi) const override {
                if (qi->get_kind() != get_kind())
                    return false;
                select_var const* other = static_cast<select_var const*>(qi);
                return m_select == other->m_select && m_arg_i == other->m_arg_i && m_var_j == other->m_var_j;
            }

            void display(std::ostream& out) const override {
                out << "(" << mk_bounded_pp(m_select, m) << ":" << m_arg_i << " -> v!" << m_var_j << ")";
            }

            void process_auf(quantifier* q, auf_solver& s, context* ctx) override {
                ptr_buffer<enode> arrays;
                get_auf_arrays(get_array(), ctx, arrays);
                TRACE("select_var",
                    tout << "enodes matching: "; display(tout); tout << "\n";
                for (enode* n : arrays) {
                    tout << "#" << n->get_expr_id() << "\n" << mk_pp(n->get_expr(), m) << "\n";
                });
                node* n1 = s.get_uvar(q, m_var_j);
                for (enode* n : arrays) {
                    app* ground_array = n->get_expr();
                    func_decl* f = get_array_func_decl(ground_array, s);
                    if (f) {
                        SASSERT(m_arg_i >= 1);
                        node* n2 = s.get_A_f_i(f, m_arg_i - 1);
                        n1->merge(n2);
                    }
                }
            }

            void populate_inst_sets(quantifier* q, auf_solver& s, context* ctx) override {
                ptr_buffer<enode> arrays;
                get_auf_arrays(get_array(), ctx, arrays);
                for (enode* curr : arrays) {
                    app* ground_array = curr->get_expr();
                    func_decl* f = get_array_func_decl(ground_array, s);
                    if (f) {
                        node* A_f_i = s.get_A_f_i(f, m_arg_i - 1);
                        enode_vector::iterator it2 = curr->begin_parents();
                        enode_vector::iterator end2 = curr->end_parents();
                        for (; it2 != end2; ++it2) {
                            enode* p = *it2;
                            if (ctx->is_relevant(p) && p->get_expr()->get_decl() == m_select->get_decl()) {
                                SASSERT(m_arg_i < p->get_expr()->get_num_args());
                                enode* e_arg = p->get_arg(m_arg_i);
                                A_f_i->insert(e_arg->get_expr(), e_arg->get_generation());
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
            var_pair(ast_manager& m, unsigned i, unsigned j) : qinfo(m), m_var_i(i), m_var_j(j) {
                if (m_var_i > m_var_j)
                    std::swap(m_var_i, m_var_j);
            }

            ~var_pair() override {}

            bool is_equal(qinfo const* qi) const override {
                if (qi->get_kind() != get_kind())
                    return false;
                var_pair const* other = static_cast<var_pair const*>(qi);
                return m_var_i == other->m_var_i && m_var_j == other->m_var_j;
            }

            void display(std::ostream& out) const override {
                out << "(" << get_kind() << ":v!" << m_var_i << ":v!" << m_var_j << ")";
            }

            void populate_inst_sets(quantifier* q, auf_solver& s, context* ctx) override {
                // do nothing
            }
        };

        class x_eq_y : public var_pair {
        public:
            x_eq_y(ast_manager& m, unsigned i, unsigned j) :var_pair(m, i, j) {}
            char const* get_kind() const override { return "x_eq_y"; }

            void process_auf(quantifier* q, auf_solver& s, context* ctx) override {
                node* n1 = s.get_uvar(q, m_var_i);
                node* n2 = s.get_uvar(q, m_var_j);
                n1->insert_avoid(n2);
                if (n1 != n2)
                    n2->insert_avoid(n1);
            }
        };

        class x_neq_y : public var_pair {
        public:
            x_neq_y(ast_manager& m, unsigned i, unsigned j) :var_pair(m, i, j) {}
            char const* get_kind() const override { return "x_neq_y"; }

            void process_auf(quantifier* q, auf_solver& s, context* ctx) override {
                node* n1 = s.get_uvar(q, m_var_i);
                node* n2 = s.get_uvar(q, m_var_j);
                n1->merge(n2);
            }
        };

        class x_leq_y : public var_pair {
        public:
            x_leq_y(ast_manager& m, unsigned i, unsigned j) :var_pair(m, i, j) {}
            char const* get_kind() const override { return "x_leq_y"; }

            void process_auf(quantifier* q, auf_solver& s, context* ctx) override {
                node* n1 = s.get_uvar(q, m_var_i);
                node* n2 = s.get_uvar(q, m_var_j);
                n1->merge(n2);
                n1->set_mono_proj();
            }
        };

        // signed bit-vector comparison
        class x_sleq_y : public x_leq_y {
        public:
            x_sleq_y(ast_manager& m, unsigned i, unsigned j) :x_leq_y(m, i, j) {}
            char const* get_kind() const override { return "x_sleq_y"; }

            void process_auf(quantifier* q, auf_solver& s, context* ctx) override {
                node* n1 = s.get_uvar(q, m_var_i);
                node* n2 = s.get_uvar(q, m_var_j);
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
            var_expr_pair(ast_manager& m, unsigned i, expr* t) :
                qinfo(m),
                m_var_i(i), m_t(t, m) {}
            ~var_expr_pair() override {}

            bool is_equal(qinfo const* qi) const override {
                if (qi->get_kind() != get_kind())
                    return false;
                var_expr_pair const* other = static_cast<var_expr_pair const*>(qi);
                return m_var_i == other->m_var_i && m_t.get() == other->m_t.get();
            }

            void display(std::ostream& out) const override {
                out << "(" << get_kind() << ":v!" << m_var_i << ":" << mk_bounded_pp(m_t.get(), m) << ")";
            }
        };

        class x_eq_t : public var_expr_pair {
        public:
            x_eq_t(ast_manager& m, unsigned i, expr* t) :
                var_expr_pair(m, i, t) {}
            char const* get_kind() const override { return "x_eq_t"; }

            void process_auf(quantifier* q, auf_solver& s, context* ctx) override {
                node* n1 = s.get_uvar(q, m_var_i);
                n1->insert_exception(m_t);
            }

            void populate_inst_sets(quantifier* q, auf_solver& slv, context* ctx) override {
                unsigned num_vars = q->get_num_decls();
                sort* s = q->get_decl_sort(num_vars - m_var_i - 1);
                if (m.is_uninterp(s)) {
                    // For uninterpreted sorts, we add all terms in the context.
                    // See Section 4.1 in the paper "Complete Quantifier Instantiation"
                    node* S_q_i = slv.get_uvar(q, m_var_i);
                    for (enode* n : ctx->enodes()) {
                        if (ctx->is_relevant(n) && n->get_expr()->get_sort() == s) {
                            S_q_i->insert(n->get_expr(), n->get_generation());
                        }
                    }
                }
            }
        };

        class x_neq_t : public var_expr_pair {
        public:
            x_neq_t(ast_manager& m, unsigned i, expr* t) :
                var_expr_pair(m, i, t) {}
            char const* get_kind() const override { return "x_neq_t"; }

            void process_auf(quantifier* q, auf_solver& s, context* ctx) override {
                // make sure that S_q_i is create.
                s.get_uvar(q, m_var_i);
            }

            void populate_inst_sets(quantifier* q, auf_solver& s, context* ctx) override {
                node* S_q_i = s.get_uvar(q, m_var_i);
                S_q_i->insert(m_t, 0);
            }
        };

        class x_gle_t : public var_expr_pair {
        public:
            x_gle_t(ast_manager& m, unsigned i, expr* t) :
                var_expr_pair(m, i, t) {}
            char const* get_kind() const override { return "x_gle_t"; }

            void process_auf(quantifier* q, auf_solver& s, context* ctx) override {
                // make sure that S_q_i is create.
                node* n1 = s.get_uvar(q, m_var_i);
                n1->set_mono_proj();
            }

            void populate_inst_sets(quantifier* q, auf_solver& s, context* ctx) override {
                node* S_q_i = s.get_uvar(q, m_var_i);
                S_q_i->insert(m_t, 0);
            }
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
        class quantifier_info : public quantifier_macro_info {
            model_finder& m_mf;
            quantifier_ref           m_q;      // original quantifier

            ptr_vector<qinfo>        m_qinfo_vect;
            ptr_vector<instantiation_set>* m_uvar_inst_sets;

            friend class quantifier_analyzer;

            void checkpoint() {
                m_mf.checkpoint("quantifier_info");
            }

            void insert_qinfo(qinfo* qi) {
                // I'm assuming the number of qinfo's per quantifier is small. So, the linear search is not a big deal.
                scoped_ptr<qinfo> q(qi);
                for (qinfo* qi2 : m_qinfo_vect) {
                    checkpoint();
                    if (qi->is_equal(qi2)) {
                        return;
                    }
                }
                m_qinfo_vect.push_back(q.detach());
                TRACE("model_finder", tout << "new quantifier qinfo: "; qi->display(tout); tout << "\n";);
            }

        public:
            typedef ptr_vector<cond_macro>::const_iterator macro_iterator;

            static quantifier_ref mk_flat(ast_manager& m, quantifier* q) {
                if (has_quantifiers(q->get_expr()) && !m.is_lambda_def(q)) {
                    proof_ref pr(m);
                    expr_ref  new_q(m);
                    pull_quant pull(m);
                    pull(q, new_q, pr);
                    SASSERT(is_well_sorted(m, new_q));
                    return quantifier_ref(to_quantifier(new_q), m);
                }
                else
                    return quantifier_ref(q, m);
            }

            quantifier_info(model_finder& mf, ast_manager& m, quantifier* q) :
                quantifier_macro_info(m, mk_flat(m, q)),
                m_mf(mf),
                m_q(q, m),
                m_uvar_inst_sets(nullptr) {
                CTRACE("model_finder_bug", has_quantifiers(m_flat_q->get_expr()),
                    tout << mk_pp(q, m) << "\n" << mk_pp(m_flat_q, m) << "\n";);
            }

            ~quantifier_info() override {
                std::for_each(m_qinfo_vect.begin(), m_qinfo_vect.end(), delete_proc<qinfo>());
                reset_the_one();
            }

            std::ostream& display(std::ostream& out) const override {
                quantifier_macro_info::display(out);
                out << "\ninfo bits:\n";
                for (qinfo* qi : m_qinfo_vect) {
                    out << "  "; qi->display(out); out << "\n";
                }
                return out;
            }

            void process_auf(auf_solver& s, context* ctx) {
                for (unsigned i = 0; i < m_flat_q->get_num_decls(); i++) {
                    // make sure a node exists for each variable.
                    s.get_uvar(m_flat_q, i);
                }
                for (qinfo* qi : m_qinfo_vect) {
                    qi->process_auf(m_flat_q, s, ctx);
                }
            }

            void populate_inst_sets(auf_solver& s, context* ctx) {
                for (qinfo* qi : m_qinfo_vect) {
                    qi->populate_inst_sets(m_flat_q, s, ctx);
                }
                // second pass
                for (qinfo* qi : m_qinfo_vect) {
                    checkpoint();
                    qi->populate_inst_sets2(m_flat_q, s, ctx);
                }
            }


            void populate_macro_based_inst_sets(context* ctx, evaluator& ev) {
                SASSERT(m_the_one != 0);
                if (m_uvar_inst_sets != nullptr)
                    return;
                m_uvar_inst_sets = alloc(ptr_vector<instantiation_set>);
                for (qinfo* qi : m_qinfo_vect)
                    qi->populate_inst_sets(m_flat_q, m_the_one, *m_uvar_inst_sets, ctx);
                for (instantiation_set* s : *m_uvar_inst_sets) {
                    if (s != nullptr)
                        s->mk_inverse(ev);
                }
            }

            instantiation_set* get_macro_based_inst_set(unsigned vidx, context* ctx, evaluator& ev) {
                if (m_the_one == nullptr)
                    return nullptr;
                populate_macro_based_inst_sets(ctx, ev);
                return m_uvar_inst_sets->get(vidx, 0);
            }

            void reset_the_one() override {
                quantifier_macro_info::reset_the_one();
                if (m_uvar_inst_sets) {
                    std::for_each(m_uvar_inst_sets->begin(), m_uvar_inst_sets->end(), delete_proc<instantiation_set>());
                    dealloc(m_uvar_inst_sets);
                    m_uvar_inst_sets = nullptr;
                }
            }
        };

        /**
           \brief Functor used to traverse/analyze a quantifier and
           fill the structure quantifier_info.
        */
        class quantifier_analyzer {
            model_finder& m_mf;
            ast_manager& m;
            macro_util           m_mutil;
            array_util           m_array_util;
            arith_util           m_arith_util;
            bv_util              m_bv_util;

            quantifier_info* m_info;

            typedef enum { POS, NEG } polarity;

            polarity neg(polarity p) { return p == POS ? NEG : POS; }

            obj_hashtable<expr>  m_pos_cache;
            obj_hashtable<expr>  m_neg_cache;
            typedef std::pair<expr*, polarity> entry;
            svector<entry>       m_ftodo;
            ptr_vector<expr>     m_ttodo;

            void insert_qinfo(qinfo* qi) {
                SASSERT(m_info);
                m_info->insert_qinfo(qi);
            }

            bool is_var_plus_ground(expr* n, bool& inv, var*& v, expr_ref& t) {
                return m_mutil.is_var_plus_ground(n, inv, v, t);
            }

            bool is_var_plus_ground(expr* n, var*& v, expr_ref& t) {
                bool inv;
                TRACE("is_var_plus_ground", tout << mk_pp(n, m) << "\n";
                tout << "is_var_plus_ground: " << is_var_plus_ground(n, inv, v, t) << "\n";
                tout << "inv: " << inv << "\n";);
                return is_var_plus_ground(n, inv, v, t) && !inv;
            }

            bool is_add(expr* n) const {
                return m_mutil.is_add(n);
            }

            bool is_zero(expr* n) const {
                return m_mutil.is_zero_safe(n);
            }

            bool is_times_minus_one(expr* n, expr*& arg) const {
                return m_mutil.is_times_minus_one(n, arg);
            }

            bool is_le(expr* n) const {
                return m_mutil.is_le(n);
            }

            bool is_le_ge(expr* n) const {
                return m_mutil.is_le_ge(n);
            }

            bool is_signed_le(expr* n) const {
                return m_bv_util.is_bv_sle(n);
            }

            expr* mk_one(sort* s) {
                return m_bv_util.is_bv_sort(s) ? m_bv_util.mk_numeral(rational(1), s) : m_arith_util.mk_numeral(rational(1), s);
            }

            void mk_sub(expr* t1, expr* t2, expr_ref& r) const {
                m_mutil.mk_sub(t1, t2, r);
            }

            void mk_add(expr* t1, expr* t2, expr_ref& r) const {
                m_mutil.mk_add(t1, t2, r);
            }

            bool is_var_and_ground(expr* lhs, expr* rhs, var*& v, expr_ref& t, bool& inv) {
                inv = false; // true if invert the sign
                TRACE("is_var_and_ground", tout << "is_var_and_ground: " << mk_ismt2_pp(lhs, m) << " " << mk_ismt2_pp(rhs, m) << "\n";);
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
                    expr_ref tmp(m);
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

            bool is_var_and_ground(expr* lhs, expr* rhs, var*& v, expr_ref& t) {
                bool inv;
                return is_var_and_ground(lhs, rhs, v, t, inv);
            }

            bool is_x_eq_t_atom(expr* n, var*& v, expr_ref& t) {
                if (!is_app(n))
                    return false;
                if (m.is_eq(n))
                    return is_var_and_ground(to_app(n)->get_arg(0), to_app(n)->get_arg(1), v, t);
                return false;
            }

            bool is_var_minus_var(expr* n, var*& v1, var*& v2) {
                if (!is_add(n))
                    return false;
                expr* arg1 = to_app(n)->get_arg(0);
                expr* arg2 = to_app(n)->get_arg(1);
                if (!is_var(arg1))
                    std::swap(arg1, arg2);
                if (!is_var(arg1))
                    return false;
                expr* arg2_2;
                if (!is_times_minus_one(arg2, arg2_2))
                    return false;
                if (!is_var(arg2_2))
                    return false;
                v1 = to_var(arg1);
                v2 = to_var(arg2_2);
                return true;
            }

            bool is_var_and_var(expr* lhs, expr* rhs, var*& v1, var*& v2) {
                if (is_var(lhs) && is_var(rhs)) {
                    v1 = to_var(lhs);
                    v2 = to_var(rhs);
                    return true;
                }
                return
                    (is_var_minus_var(lhs, v1, v2) && is_zero(rhs)) ||
                    (is_var_minus_var(rhs, v1, v2) && is_zero(lhs));
            }

            bool is_x_eq_y_atom(expr* n, var*& v1, var*& v2) {
                return m.is_eq(n) && is_var_and_var(to_app(n)->get_arg(0), to_app(n)->get_arg(1), v1, v2);
            }

            bool is_x_gle_y_atom(expr* n, var*& v1, var*& v2) {
                return is_le_ge(n) && is_var_and_var(to_app(n)->get_arg(0), to_app(n)->get_arg(1), v1, v2);
            }

            bool is_x_gle_t_atom(expr* atom, bool sign, var*& v, expr_ref& t) {
                if (!is_app(atom))
                    return false;
                if (sign) {
                    bool r = is_le_ge(atom) && is_var_and_ground(to_app(atom)->get_arg(0), to_app(atom)->get_arg(1), v, t);
                    CTRACE("is_x_gle_t", r, tout << "is_x_gle_t: " << mk_ismt2_pp(atom, m) << "\n--->\n"
                        << mk_ismt2_pp(v, m) << " " << mk_ismt2_pp(t, m) << "\n";
                    tout << "sign: " << sign << "\n";);
                    return r;
                }
                else {
                    if (is_le_ge(atom)) {
                        expr_ref tmp(m);
                        bool le = is_le(atom);
                        bool inv = false;
                        if (is_var_and_ground(to_app(atom)->get_arg(0), to_app(atom)->get_arg(1), v, tmp, inv)) {
                            if (inv)
                                le = !le;
                            sort* s = tmp->get_sort();
                            expr_ref one(m);
                            one = mk_one(s);
                            if (le)
                                mk_add(tmp, one, t);
                            else
                                mk_sub(tmp, one, t);
                            TRACE("is_x_gle_t", tout << "is_x_gle_t: " << mk_ismt2_pp(atom, m) << "\n--->\n"
                                << mk_ismt2_pp(v, m) << " " << mk_ismt2_pp(t, m) << "\n";
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

            obj_hashtable<expr>& get_cache(polarity pol) {
                return pol == POS ? m_pos_cache : m_neg_cache;
            }

            void visit_formula(expr* n, polarity pol) {
                if (is_ground(n))
                    return; // ground terms do not need to be visited.
                obj_hashtable<expr>& c = get_cache(pol);
                if (!c.contains(n)) {
                    m_ftodo.push_back(entry(n, pol));
                    c.insert(n);
                }
            }

            void visit_term(expr* n) {
                // ground terms do not need to be visited.
                if (!is_ground(n) && !m_pos_cache.contains(n)) {
                    m_ttodo.push_back(n);
                    m_pos_cache.insert(n);
                }
            }

            /**
               \brief Process uninterpreted applications.
            */
            void process_u_app(app* t) {
                unsigned num_args = t->get_num_args();
                for (unsigned i = 0; i < num_args; i++) {
                    expr* arg = t->get_arg(i);
                    if (is_var(arg)) {
                        SASSERT(t->get_decl()->get_domain(i) == to_var(arg)->get_sort());
                        insert_qinfo(alloc(f_var, m, t->get_decl(), i, to_var(arg)->get_idx()));
                        continue;
                    }

                    var* v;
                    expr_ref k(m);
                    if (is_var_plus_ground(arg, v, k)) {
                        insert_qinfo(alloc(f_var_plus_offset, m, t->get_decl(), i, v->get_idx(), k.get()));
                        continue;
                    }

                    visit_term(arg);
                }
            }


            /**
               \brief A term \c t is said to be a auf_select if
               it is of the form

               (select a i) Where:

               where a is ground or is_auf_select(a) == true
               and the indices are ground terms or variables.
            */
            bool is_auf_select(expr* t) const {
                if (!m_array_util.is_select(t))
                    return false;
                expr* a = to_app(t)->get_arg(0);
                if (!is_ground(a) && !is_auf_select(a))
                    return false;
                for (expr* arg : *to_app(t)) {
                    if (!is_ground(arg) && !is_var(arg))
                        return false;
                }
                return true;
            }

            /**
               \brief Process interpreted applications.
            */
            void process_i_app(app* t) {
                if (is_auf_select(t)) {
                    unsigned num_args = t->get_num_args();
                    app* array = to_app(t->get_arg(0));
                    visit_term(array); // array may be a nested array.
                    for (unsigned i = 1; i < num_args; i++) {
                        expr* arg = t->get_arg(i);
                        if (is_var(arg)) {
                            insert_qinfo(alloc(select_var, m, t, i, to_var(arg)->get_idx()));
                        }
                        else {
                            SASSERT(is_ground(arg));
                        }
                    }
                }
                else {
                    for (expr* arg : *t) {
                        visit_term(arg);
                    }
                }
            }

            void process_app(app* t) {
                SASSERT(!is_ground(t));

                if (t->get_family_id() != m.get_basic_family_id()) {
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
                    expr* curr = m_ttodo.back();
                    m_ttodo.pop_back();

                    if (m.is_bool(curr)) {
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
                        SASSERT(is_lambda(curr));
                    }
                }
            }

            void process_literal(expr* atom, bool sign) {
                CTRACE("model_finder_bug", is_ground(atom), tout << mk_pp(atom, m) << "\n";);
                SASSERT(!is_ground(atom));
                SASSERT(m.is_bool(atom));

                if (is_var(atom)) {
                    if (sign) {
                        // atom (not X) can be viewed as X != true
                        insert_qinfo(alloc(x_neq_t, m, to_var(atom)->get_idx(), m.mk_true()));
                    }
                    else {
                        // atom X can be viewed as X != false
                        insert_qinfo(alloc(x_neq_t, m, to_var(atom)->get_idx(), m.mk_false()));
                    }
                    return;
                }

                if (is_app(atom)) {
                    var* v, * v1, * v2;
                    expr_ref t(m);
                    if (is_x_eq_t_atom(atom, v, t)) {
                        if (sign)
                            insert_qinfo(alloc(x_neq_t, m, v->get_idx(), t));
                        else
                            insert_qinfo(alloc(x_eq_t, m, v->get_idx(), t));
                    }
                    else if (is_x_eq_y_atom(atom, v1, v2)) {
                        if (sign)
                            insert_qinfo(alloc(x_neq_y, m, v1->get_idx(), v2->get_idx()));
                        else {
                            m_info->m_has_x_eq_y = true; // this atom is in the fringe of AUF
                            insert_qinfo(alloc(x_eq_y, m, v1->get_idx(), v2->get_idx()));
                        }
                    }
                    else if (sign && is_x_gle_y_atom(atom, v1, v2)) {
                        if (is_signed_le(atom))
                            insert_qinfo(alloc(x_sleq_y, m, v1->get_idx(), v2->get_idx()));
                        else
                            insert_qinfo(alloc(x_leq_y, m, v1->get_idx(), v2->get_idx()));
                    }
                    else if (is_x_gle_t_atom(atom, sign, v, t)) {
                        insert_qinfo(alloc(x_gle_t, m, v->get_idx(), t));
                    }
                    else {
                        process_app(to_app(atom));
                    }
                    return;
                }

                SASSERT(is_quantifier(atom));
                UNREACHABLE();
            }

            void process_literal(expr* atom, polarity pol) {
                process_literal(atom, pol == NEG);
            }

            void process_and_or(app* n, polarity p) {
                for (expr* arg : *n)
                    visit_formula(arg, p);
            }

            void process_ite(app* n, polarity p) {
                visit_formula(n->get_arg(0), p);
                visit_formula(n->get_arg(0), neg(p));
                visit_formula(n->get_arg(1), p);
                visit_formula(n->get_arg(2), p);
            }

            void process_iff(app* n) {
                visit_formula(n->get_arg(0), POS);
                visit_formula(n->get_arg(0), NEG);
                visit_formula(n->get_arg(1), POS);
                visit_formula(n->get_arg(1), NEG);
            }

            void checkpoint() {
                m_mf.checkpoint("quantifier_analyzer");
            }

            void process_formulas_on_stack() {
                while (!m_ftodo.empty()) {
                    checkpoint();
                    entry& e = m_ftodo.back();
                    expr* curr = e.first;
                    polarity pol = e.second;
                    m_ftodo.pop_back();
                    if (is_app(curr)) {
                        if (to_app(curr)->get_family_id() == m.get_basic_family_id() && m.is_bool(curr)) {
                            switch (static_cast<basic_op_kind>(to_app(curr)->get_decl_kind())) {
                            case OP_IMPLIES:
                            case OP_XOR:
                                UNREACHABLE(); // simplifier eliminated ANDs, IMPLIEs, and XORs
                                break;
                            case OP_OR:
                            case OP_AND:
                                process_and_or(to_app(curr), pol);
                                break;
                            case OP_NOT:
                                visit_formula(to_app(curr)->get_arg(0), neg(pol));
                                break;
                            case OP_ITE:
                                process_ite(to_app(curr), pol);
                                break;
                            case OP_EQ:
                                if (m.is_bool(to_app(curr)->get_arg(0))) {
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
                        SASSERT(m.is_bool(curr));
                        process_literal(curr, pol);
                    }
                    else {
                        SASSERT(is_quantifier(curr));
                    }
                }
            }

            void process_formula(expr* n) {
                SASSERT(m.is_bool(n));
                visit_formula(n, POS);
            }

            void process_clause(expr* cls) {
                SASSERT(is_clause(m, cls));
                unsigned num_lits = get_clause_num_literals(m, cls);
                for (unsigned i = 0; i < num_lits; i++) {
                    expr* lit = get_clause_literal(m, cls, i);
                    SASSERT(is_literal(m, lit));
                    expr* atom;
                    bool   sign;
                    get_literal_atom_sign(m, lit, atom, sign);
                    if (!is_ground(atom))
                        process_literal(atom, sign);
                }
            }


        public:
            quantifier_analyzer(model_finder& mf, ast_manager& m) :
                m_mf(mf),
                m(m),
                m_mutil(m),
                m_array_util(m),
                m_arith_util(m),
                m_bv_util(m),
                m_info(nullptr) {
            }


            void operator()(quantifier_info* d) {
                m_info = d;
                quantifier* q = d->get_flat_q();
                if (m.is_lambda_def(q)) return;
                expr* e = q->get_expr();
                reset_cache();
                if (!m.inc()) return;
                m_ttodo.reset();
                m_ftodo.reset();

                if (is_clause(m, e)) {
                    process_clause(e);
                }
                else {
                    process_formula(e);
                }

                while (!m_ftodo.empty() || !m_ttodo.empty()) {
                    process_formulas_on_stack();
                    process_terms_on_stack();
                }

                m_info = nullptr;
            }

        };
    }


    // -----------------------------------
    //
    // model finder
    //
    // -----------------------------------

    model_finder::model_finder(ast_manager& m) :
        m(m),
        m_context(nullptr),
        m_analyzer(alloc(quantifier_analyzer, *this, m)),
        m_auf_solver(alloc(auf_solver, m)),
        m_dependencies(m),
        m_new_constraints(m) {
    }

    model_finder::~model_finder() {
        reset();
    }

    void model_finder::checkpoint() {
        checkpoint("model_finder");
    }

    void model_finder::checkpoint(char const* msg) {
        if (m_context && m_context->get_cancel_flag())
            throw tactic_exception(m_context->get_manager().limit().get_cancel_msg());
    }

    mf::quantifier_info* model_finder::get_quantifier_info(quantifier* q) {
        mf::quantifier_info* qi = nullptr;
        if (!m_q2info.find(q, qi)) {
            register_quantifier(q);
            qi = m_q2info[q];
        }
        return qi;
    }

    void model_finder::set_context(context* ctx) {
        SASSERT(m_context == nullptr);
        m_context = ctx;
    }

    void model_finder::register_quantifier(quantifier* q) {
        TRACE("model_finder", tout << "registering:\n" << q->get_id() << ": " << q << " " << &m_q2info << " " << mk_pp(q, m) << "\n";);
        quantifier_info* new_info = alloc(quantifier_info, *this, m, q);
        m_q2info.insert(q, new_info);
        m_quantifiers.push_back(q);
        m_analyzer->operator()(new_info);
        TRACE("model_finder", tout << "after analyzer:\n"; new_info->display(tout););
    }

    void model_finder::push_scope() {
        m_scopes.push_back(scope());
        scope& s = m_scopes.back();
        s.m_quantifiers_lim = m_quantifiers.size();
    }

    void model_finder::restore_quantifiers(unsigned old_size) {
        unsigned curr_size = m_quantifiers.size();
        SASSERT(old_size <= curr_size);
        for (unsigned i = old_size; i < curr_size; i++) {
            quantifier* q = m_quantifiers[i];
            SASSERT(m_q2info.contains(q));
            quantifier_info* info = get_quantifier_info(q);
            m_q2info.erase(q);
            dealloc(info);
        }
        m_quantifiers.shrink(old_size);
    }

    void model_finder::pop_scope(unsigned num_scopes) {
        unsigned lvl = m_scopes.size();
        SASSERT(num_scopes <= lvl);
        unsigned new_lvl = lvl - num_scopes;
        scope& s = m_scopes[new_lvl];
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

    void model_finder::collect_relevant_quantifiers(ptr_vector<quantifier>& qs) const {
        for (quantifier* q : m_quantifiers) {
            if (m_context->is_relevant(q) && m_context->get_assignment(q) == l_true)
                qs.push_back(q);
        }
    }


    void model_finder::process_auf(ptr_vector<quantifier> const& qs, proto_model* mdl) {
        m_auf_solver->reset();
        m_auf_solver->set_model(mdl);
        m_auf_solver->set_specrels(*m_context);

        for (quantifier* q : qs) {
            quantifier_info* qi = get_quantifier_info(q);
            qi->process_auf(*(m_auf_solver.get()), m_context);
        }
        m_auf_solver->mk_instantiation_sets();

        for (quantifier* q : qs) {
            quantifier_info* qi = get_quantifier_info(q);
            qi->populate_inst_sets(*(m_auf_solver.get()), m_context);
        }
        m_auf_solver->fix_model(m_new_constraints);
        TRACE("model_finder",
            for (quantifier* q : qs) {
                quantifier_info* qi = get_quantifier_info(q);
                quantifier* fq = qi->get_flat_q();
                tout << "#" << fq->get_id() << " ->\n" << mk_pp(fq, m) << "\n";
            }
        m_auf_solver->display_nodes(tout););
    }

    quantifier_macro_info* model_finder::operator()(quantifier* q) {
        return m_q2info[q];
    }

    void model_finder::process_simple_macros(ptr_vector<quantifier>& qs, ptr_vector<quantifier>& residue, proto_model* mdl) {
        simple_macro_solver sms(m, *this);
        sms(*mdl, qs, residue);
        TRACE("model_finder", tout << "model after processing simple macros:\n"; model_pp(tout, *mdl););
    }

    void model_finder::process_hint_macros(ptr_vector<quantifier>& qs, ptr_vector<quantifier>& residue, proto_model* mdl) {
        hint_macro_solver hms(m, *this);
        hms(*mdl, qs, residue);
        TRACE("model_finder", tout << "model after processing simple macros:\n"; model_pp(tout, *mdl););
    }

    void model_finder::process_non_auf_macros(ptr_vector<quantifier>& qs, ptr_vector<quantifier>& residue, proto_model* mdl) {
        non_auf_macro_solver nas(m, *this, m_dependencies);
        nas.set_mbqi_force_template(m_context->get_fparams().m_mbqi_force_template);
        nas(*mdl, qs, residue);
        TRACE("model_finder", tout << "model after processing non auf macros:\n"; model_pp(tout, *mdl););
    }

    /**
       \brief Clean leftovers from previous invocations to fix_model.
    */
    void model_finder::cleanup_quantifier_infos(ptr_vector<quantifier> const& qs) {
        for (quantifier* q : qs) {
            get_quantifier_info(q)->reset_the_one();
        }
    }

    /**
       \brief Try to satisfy quantifiers by modifying the model while preserving the satisfiability
       of all ground formulas asserted into the logical context.
    */
    void model_finder::fix_model(proto_model* m) {
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

    quantifier* model_finder::get_flat_quantifier(quantifier* q) {
        quantifier_info* qinfo = get_quantifier_info(q);
        return qinfo->get_flat_q();
    }

    /**
       \brief Return the instantiation set associated with var i of q.

       \remark q is the quantifier before flattening.
    */
    mf::instantiation_set const* model_finder::get_uvar_inst_set(quantifier* q, unsigned i) {
        quantifier* flat_q = get_flat_quantifier(q);
        SASSERT(flat_q->get_num_decls() >= q->get_num_decls());
        mf::instantiation_set const* r = m_auf_solver->get_uvar_inst_set(flat_q, flat_q->get_num_decls() - q->get_num_decls() + i);
        TRACE("model_finder", tout << "q: #" << q->get_id() << "\n" << mk_pp(q, m) << "\nflat_q: " << mk_pp(flat_q, m)
            << "\ni: " << i << " " << flat_q->get_num_decls() - q->get_num_decls() + i << "\n";);
        if (r != nullptr)
            return r;
        // quantifier was not processed by AUF solver...
        // it must have been satisfied by "macro"/"hint".
        quantifier_info* qinfo = get_quantifier_info(q);
        SASSERT(qinfo);
        return qinfo->get_macro_based_inst_set(i, m_context, *(m_auf_solver.get()));
    }

    /**
       \brief Return an expression in the instantiation-set of q:i that evaluates to val.

       \remark q is the quantifier before flattening.

       Store in generation the generation of the result
    */
    expr* model_finder::get_inv(quantifier* q, unsigned i, expr* val, unsigned& generation) {
        instantiation_set const* s = get_uvar_inst_set(q, i);
        if (s == nullptr)
            return nullptr;
        expr* t = s->get_inv(val);
        if (m_auf_solver->is_default_representative(t))
            return val;
        if (t != nullptr) {
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
    bool model_finder::restrict_sks_to_inst_set(context* aux_ctx, quantifier* q, expr_ref_vector const& sks) {
        // Note: we currently add instances of q instead of flat_q.
        // If the user wants instances of flat_q, it should use PULL_NESTED_QUANTIFIERS=true. This option
        // will guarantee that q == flat_q.
        //
        // Since we only care about q (and its bindings), it only makes sense to restrict the variables of q.
        bool asserted_something = false;
        unsigned num_decls = q->get_num_decls();
        // Remark: sks were created for the flat version of q.
        SASSERT(get_flat_quantifier(q)->get_num_decls() == sks.size());
        SASSERT(sks.size() >= num_decls);
        for (unsigned i = 0; i < num_decls; i++) {
            expr* sk = sks.get(num_decls - i - 1);
            instantiation_set const* s = get_uvar_inst_set(q, i);
            if (s == nullptr)
                continue; // nothing to do
            obj_map<expr, expr*> const& inv = s->get_inv_map();
            if (inv.empty())
                continue; // nothing to do
            ptr_buffer<expr> eqs;
            for (auto const& kv : inv) {
                expr* val = kv.m_key;
                eqs.push_back(m.mk_eq(sk, val));
            }
            expr_ref new_cnstr(m);
            new_cnstr = m.mk_or(eqs.size(), eqs.data());
            TRACE("model_finder", tout << "assert_restriction:\n" << mk_pp(new_cnstr, m) << "\n";);
            aux_ctx->assert_expr(new_cnstr);
            asserted_something = true;
        }
        return asserted_something;
    }

    void model_finder::restart_eh() {
        unsigned sz = m_new_constraints.size();
        if (sz > 0) {
            for (unsigned i = 0; i < sz; i++) {
                expr* c = m_new_constraints.get(i);
                TRACE("model_finder_bug_detail", tout << "asserting new constraint: " << mk_pp(c, m) << "\n";);
                m_context->internalize(c, true);
                literal l(m_context->get_literal(c));
                m_context->mark_as_relevant(l);
                // asserting it as an AXIOM
                m_context->assign(l, b_justification());
            }
            m_new_constraints.reset();
        }
    }
}
