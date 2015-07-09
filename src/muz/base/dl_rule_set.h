/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    dl_rule_set.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2010-05-17.

Revision History:

--*/
#ifndef DL_RULE_SET_H_
#define DL_RULE_SET_H_

#include"obj_hashtable.h"
#include"dl_rule.h"

namespace datalog {

    class rule_set;

    class rule_dependencies {
    public:
        typedef obj_hashtable<func_decl> item_set;
        typedef obj_map<func_decl, item_set * > deps_type;

        typedef deps_type::iterator iterator;
    private:
        /**
           Map (dependent -> set of master objects)

           Each master object is also present as a key of the map, even if its master set
           is empty.
        */
        deps_type        m_data;
        context &        m_context;
        ptr_vector<expr> m_todo;
        expr_sparse_mark m_visited;


        //we need to take care with removing to avoid memory leaks
        void remove_m_data_entry(func_decl * key);

        //sometimes we need to return reference to an empty set,
        //so we return reference to this one.
        item_set m_empty_item_set;

        item_set & ensure_key(func_decl * pred);
        void insert(func_decl * depending, func_decl * master);
        void populate(rule const* r);
    public:
        rule_dependencies(context& ctx);
        rule_dependencies(const rule_dependencies & o, bool reversed = false);
        ~rule_dependencies();
        void reset();

        void populate(const rule_set & rules);
        void populate(unsigned n, rule * const * rules);
        void restrict(const item_set & allowed);
        void remove(func_decl * itm);
        void remove(const item_set & to_remove);

        bool empty() const { return m_data.empty(); }
        const item_set & get_deps(func_decl * f) const;
        /**
           \brief Number of predicates \c f depends on.
         */
        unsigned in_degree(func_decl * f) const { return get_deps(f).size(); }
        /**
           \brief Number of predicates that depend on \c f.
         */
        unsigned out_degree(func_decl * f) const;
        
        /**
           \brief If the rependency graph is acyclic, put all elements into \c res
             ordered so that elements can depend only on elements that are before them.
             If the graph is not acyclic, return false.
         */
        bool sort_deps(ptr_vector<func_decl> & res);

        iterator begin() const { return m_data.begin(); }
        iterator end() const { return m_data.end(); }

        void display( std::ostream & out ) const;
    };

    class rule_stratifier {
    public:
        typedef func_decl T;
        typedef obj_hashtable<T> item_set;
        typedef ptr_vector<item_set> comp_vector;
        typedef obj_map<T, item_set *> deps_type;
    private:

        const rule_dependencies & m_deps;
        comp_vector m_strats;

        obj_map<T, unsigned> m_preorder_nums;
        ptr_vector<T> m_stack_S;
        ptr_vector<T> m_stack_P;

        obj_map<T, unsigned> m_component_nums;
        comp_vector m_components;
        obj_map<T, unsigned> m_pred_strat_nums;

        unsigned m_next_preorder;
        unsigned m_first_preorder;

        /**
            Finds strongly connected components using the Gabow's algorithm.
        */
        void traverse(T* el);

        /**
            Calls \c traverse to identify strognly connected components and then
            orders them using topological sorting.
        */
        void process();

    public:

        /**
            \remark The \c stratifier object keeps a reference to the \c deps object, so
            it must exist for the whole lifetime of the \c stratifier object.
        */
        rule_stratifier(const rule_dependencies & deps)
            : m_deps(deps), m_next_preorder(0) 
        {
            process();
        }

        ~rule_stratifier();

        /**
            Return vector of components ordered so that the only dependencies are from
            later components to earlier.
        */
        const comp_vector & get_strats() const { return m_strats; }

        unsigned get_predicate_strat(func_decl * pred) const;
        
        void display( std::ostream & out ) const;
    };

    /**
       \brief Datalog "Program" (aka rule set).
    */
    class rule_set {
        friend class rule_dependencies;
    public:
        typedef ptr_vector<func_decl_set> pred_set_vector;
        typedef obj_map<func_decl, rule_vector*> decl2rules;
    private:
        typedef obj_map<func_decl, func_decl_set*> decl2deps;

        context &                    m_context;
        rule_manager &               m_rule_manager;
        rule_ref_vector              m_rules;        //!< all rules
        decl2rules                   m_head2rules;   //!< mapping from head symbol to rules.
        rule_dependencies            m_deps;         //!< dependencies
        scoped_ptr<rule_stratifier>  m_stratifier;   //!< contains stratifier object iff the rule_set is closed
        func_decl_set                m_output_preds; //!< output predicates
        obj_map<func_decl,func_decl*> m_orig2pred;
        obj_map<func_decl,func_decl*> m_pred2orig;
        func_decl_ref_vector          m_refs;


        //sometimes we need to return reference to an empty rule_vector,
        //so we return reference to this one.
        rule_vector                  m_empty_rule_vector;

        void compute_deps();
        void compute_tc_deps();
        bool stratified_negation();
        bool check_min();
    public:
        rule_set(context & ctx);
        rule_set(const rule_set & rs);
        ~rule_set();

        ast_manager & get_manager() const;
        rule_manager & get_rule_manager() const { return const_cast<rule_manager&>(m_rule_manager); }
        context&  get_context() const { return m_context; }


        void inherit_predicates(rule_set const& other);
        void inherit_predicate(rule_set const& other, func_decl* orig, func_decl* pred);
        func_decl* get_orig(func_decl* pred) const;
        func_decl* get_pred(func_decl* orig) const;

        /**
           \brief Add rule \c r to the rule set.
        */
        void add_rule(rule * r);

        /**
           \brief Remove rule \c r from the rule set.
        */
        void del_rule(rule * r);

        /**
           \brief Add all rules from a different rule_set.
        */
        void add_rules(const rule_set& src);
        void replace_rules(const rule_set& other);

        /**
           \brief This method should be invoked after all rules are added to the rule set.
           It will check if the negation is indeed stratified.
           Return true if succeeded.

           \remark If new rules are added, the rule_set will be "reopen".
        */
        bool close();
        void ensure_closed();
        /**
           \brief Undo the effect of the \c close() operation.
         */
        void reopen();
        bool is_closed() const { return m_stratifier != 0; }

        unsigned get_num_rules() const { return m_rules.size(); }
        bool empty() const { return m_rules.size() == 0; }

        rule * get_rule(unsigned i) const { return m_rules[i]; }
        rule * last() const { return m_rules[m_rules.size()-1]; }
        rule_ref_vector const& get_rules() const { return m_rules; }

        const rule_vector & get_predicate_rules(func_decl * pred) const;
        bool contains(func_decl* pred) const { return m_head2rules.contains(pred); }

        const rule_stratifier & get_stratifier() const {
            SASSERT(m_stratifier);
            return *m_stratifier;
        }
        const pred_set_vector & get_strats() const;
        unsigned get_predicate_strat(func_decl * pred) const;
        const rule_dependencies & get_dependencies() const { SASSERT(is_closed()); return m_deps; }

        // split predicats into founded and non-founded.
        void split_founded_rules(func_decl_set& founded, func_decl_set& non_founded);

        void reset();

        void set_output_predicate(func_decl * pred) { m_refs.push_back(pred); m_output_preds.insert(pred); }
        bool is_output_predicate(func_decl * pred) const { return m_output_preds.contains(pred); }
        const func_decl_set & get_output_predicates() const { return m_output_preds; }
        func_decl* get_output_predicate() const { SASSERT(m_output_preds.size() == 1); return *m_output_preds.begin(); }


        void display(std::ostream & out) const;

        /**
           \brief Output rule dependencies.

           The rule set must be closed before calling this function.
         */
        void display_deps(std::ostream & out) const;

        typedef rule * const * iterator;
        iterator begin() const { return m_rules.c_ptr(); }
        iterator end() const { return m_rules.c_ptr()+m_rules.size(); }

        decl2rules::iterator begin_grouped_rules() const { return m_head2rules.begin(); }
        decl2rules::iterator end_grouped_rules() const { return m_head2rules.end(); }

    };

    inline std::ostream& operator<<(std::ostream& out, rule_set const& r) { r.display(out); return out; }


    
};

#endif /* DL_RULE_SET_H_ */

