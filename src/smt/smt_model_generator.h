/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_model_generator.h

Abstract:

    The model generator builds a (partial) model for the ground
    formulas in the logical context.

    The model finder (smt_model_finder.h) tries to extend the
    partial model to satisfy the quantifiers. Main invariant:
    the new model still satisfies the ground formulas.

    The model checker (smt_model_checker.h) checks whether the (new)
    model satisfies the quantifiers. If it doesn't, new instances are
    added.

Author:

    Leonardo de Moura (leonardo) 2008-10-29.

Revision History:

--*/
#ifndef SMT_MODEL_GENERATOR_H_
#define SMT_MODEL_GENERATOR_H_

#include "ast/ast.h"
#include "smt/smt_types.h"
#include "util/obj_hashtable.h"
#include "util/map.h"

class value_factory;
class proto_model;

namespace smt {
    
    // -----------------------------
    //
    // This module builds an interpretation for each relevant expression in the logical context.
    //
    // 1) The interpretation of boolean constants is their truth value in the logical context.
    //
    // 2) The interpretation of expressions associated with enodes is built using functors (model_value_proc).
    //    Theories as arrays and datatypes many need the interpretation of some expressions to be built before the interpretation of others.
    //    We say this is a dependency. Moreover, some values must be fresh. That is, they should be different
    //    from all other values associated with enodes of a given sort. For example, the array theory
    //    uses fresh values to make sure that some array constants are different from each other.
    //     
    //    So a dependency for building the interpretation of an enode N can be:
    //     a) a fresh value (stub) of sort S: it must be built after the interpretation of all enodes of sort S were assigned.
    // 
    //     b) an enode N': the interpretation of N' must be built before the interpretation of N.
    //
    // We say a 'source' is an fresh value or an enode. Note that every dependency is a source,
    // but not every source is a dependency.
    //
    // We use these dependencies to sort (using a topological sort) the sources. The sorted 'sources' specify the
    // order the interpretations will be built.
    //
    // Assumptions regarding dependencies:
    //
    //  - They are acyclic.
    //
    //  - All dependencies are marked as relevant.
    //
    //  - A fresh value stub of sort S depends (implicitly) on all enodes of sort S (that are not associated with fresh values).
    //    So an enode of sort S may not have a dependency of sort S.
    // 
    // ------------------------------

    /**
       \brief Stub for extra fresh value.
    */
    struct extra_fresh_value {
        sort *   m_sort;
        unsigned m_idx;
        expr *   m_value;
    public:
        extra_fresh_value(sort * s, unsigned idx):m_sort(s), m_idx(idx), m_value(nullptr) {}
        sort * get_sort() const { return m_sort; }
        unsigned get_idx() const { return m_idx; }
        void set_value(expr * n) { SASSERT(m_value == 0); m_value = n; }
        expr * get_value() const { return m_value; }
    };

    /**
       \brief Theories such as arrays and datatypes may need some values to be already available when
       building a value. We say this a dependency. Object of this class are used to track such dependencies.

       Example: to build the value (cons 10 nil), the values 10 and nil should be already available.
    */
    class model_value_dependency {
        bool m_fresh; //!< True if the dependency is a new fresh value;
        union {
            enode *             m_enode; //!< When m_fresh == false, contains an enode dependency.
            extra_fresh_value * m_value; //!< When m_fresh == true, contains the sort of the fresh value
        };
    public:
        model_value_dependency():m_fresh(true), m_value(nullptr) { }
        explicit model_value_dependency(enode * n):m_fresh(false), m_enode(n->get_root()) {}
        explicit model_value_dependency(extra_fresh_value * v) :m_fresh(true), m_value(v) { SASSERT(v); }
        bool is_fresh_value() const { return m_fresh; }
        enode * get_enode() const { SASSERT(!is_fresh_value()); return m_enode; }
        extra_fresh_value * get_value() const { SASSERT(is_fresh_value()); return m_value; }
    };

    std::ostream& operator<<(std::ostream& out, model_value_dependency const& d);

    typedef model_value_dependency source;

    struct source_hash_proc {
        unsigned operator()(source const & s) const { return s.is_fresh_value() ? hash_u_u(17, s.get_value()->get_idx()) : hash_u_u(13, s.get_enode()->get_owner_id()); }
    };

    struct source_eq_proc {
        bool operator()(source const & s1, source const & s2) const {
            if (s1.is_fresh_value() != s2.is_fresh_value())
                return false;
            if (s1.is_fresh_value())
                return s1.get_value()->get_idx() == s2.get_value()->get_idx();
            else
                return s1.get_enode() == s2.get_enode();
        }
    };

    typedef map<source, int, source_hash_proc, source_eq_proc> source2color;

    /**
       \brief Model value builder. This functor is used to specify the dependencies 
       needed to build a value, and to build the actual value.
       
    */
    class model_value_proc {
    public:
        virtual ~model_value_proc() {}
        /**
           \brief Fill result with the dependencies of this functor.
           That is, to invoke mk_value, the dependencies in result must be constructed.
        */
        virtual void get_dependencies(buffer<model_value_dependency> & result) {}
        /**
           \brief The array values has size equal to the size of the argument \c result in get_dependencies.
           It contain the values built for the dependencies.
        */
        virtual app * mk_value(model_generator & m, ptr_vector<expr> & values) = 0;
        /**
           \brief Return true if it is associated with a fresh value.
        */
        virtual bool is_fresh() const { return false; }
    };
    
    /**
       \brief Simple model_value_proc. It has no dependencies, and
       just returns a given expression.
    */
    class expr_wrapper_proc : public model_value_proc {
        app * m_value;
    public:
        expr_wrapper_proc(app * v):m_value(v) {}
        app * mk_value(model_generator & m, ptr_vector<expr> & values) override { return m_value; }
    };

    class fresh_value_proc : public model_value_proc {
        extra_fresh_value * m_value;
    public:
        fresh_value_proc(extra_fresh_value * v):m_value(v) {}
        void get_dependencies(buffer<model_value_dependency> & result) override;
        app * mk_value(model_generator & m, ptr_vector<expr> & values) override { return to_app(values[0]); }
        bool is_fresh() const override { return true; }
    };

    /**
       \brief Auxiliary class used during model generation.
    */
    class model_generator {
        ast_manager &                 m_manager;
        context *                     m_context;
        ptr_vector<extra_fresh_value> m_extra_fresh_values;
        unsigned                      m_fresh_idx;
        obj_map<enode, app *>         m_root2value;
        ast_ref_vector                m_asts;
        proto_model *                 m_model;
        obj_hashtable<func_decl>      m_hidden_ufs;

        void init_model();
        void mk_bool_model();
        void mk_value_procs(obj_map<enode, model_value_proc *> & root2proc, ptr_vector<enode> & roots,  ptr_vector<model_value_proc> & procs);
        void mk_values();
        bool include_func_interp(func_decl * f) const;
        void mk_func_interps();
        void finalize_theory_models();
        void display(std::ostream & out);
        void register_existing_model_values();
        void register_macros();

        bool visit_children(source const & src, ptr_vector<enode> const & roots, obj_map<enode, model_value_proc *> const & root2proc, 
                            source2color & colors, obj_hashtable<sort> & already_traversed, svector<source> & todo);

        void process_source(source const & src, ptr_vector<enode> const & roots, obj_map<enode, model_value_proc *> const & root2proc, 
                            source2color & colors, obj_hashtable<sort> & already_traversed, svector<source> & todo, svector<source> & sorted_sources);

        void top_sort_sources(ptr_vector<enode> const & roots, obj_map<enode, model_value_proc *> const & root2proc, svector<source> & sorted_sources);

    public:
        model_generator(ast_manager & m);
        ~model_generator();

        void reset();
        void set_context(context * c) { SASSERT(m_context == 0); m_context = c; }

        void register_factory(value_factory * f);
        extra_fresh_value * mk_extra_fresh_value(sort * s);
        model_value_proc * mk_model_value(enode* r);
        expr * get_some_value(sort * s);
        proto_model & get_model() { SASSERT(m_model); return *m_model; }
        void register_value(expr * val);
        ast_manager & get_manager() { return m_manager; }
        proto_model * mk_model();

        obj_map<enode, app *> const & get_root2value() const { return m_root2value; }
        app * get_value(enode * n) const;

        void hide(func_decl * f) { 
            if (!m_hidden_ufs.contains(f)) {
                m_hidden_ufs.insert(f);
                m_manager.inc_ref(f); 
            }
        }
    };
};

#endif /* SMT_MODEL_GENERATOR_H_ */


