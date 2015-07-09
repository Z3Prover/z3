/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    smt_quantifier.h

Abstract:

    Quantifier reasoning support for smt::context.

Author:

    Leonardo de Moura (leonardo) 2012-02-16.

Revision History:

--*/
#ifndef SMT_QUANTIFIER_H_
#define SMT_QUANTIFIER_H_

#include"ast.h"
#include"statistics.h"
#include"params.h"
#include"smt_types.h"

class proto_model;
struct smt_params;

namespace smt {
    class quantifier_manager_plugin;
    class quantifier_stat;

    class quantifier_manager {
        struct imp;
        imp *                       m_imp;
    public:
        quantifier_manager(context & ctx, smt_params & fp, params_ref const & p);
        ~quantifier_manager();
        
        context & get_context() const;

        void set_plugin(quantifier_manager_plugin * plugin);

        void add(quantifier * q, unsigned generation);
        void del(quantifier * q);
        bool empty() const;

        bool is_shared(enode * n) const;

        quantifier_stat * get_stat(quantifier * q) const;
        unsigned get_generation(quantifier * q) const;

        bool add_instance(quantifier * q, app * pat, 
                          unsigned num_bindings, 
                          enode * const * bindings, 
                          unsigned max_generation, 
                          unsigned min_top_generation, 
                          unsigned max_top_generation, 
                          ptr_vector<enode> & used_enodes);
        bool add_instance(quantifier * q, unsigned num_bindings, enode * const * bindings, unsigned generation = 0);

        void init_search_eh();
        void assign_eh(quantifier * q);
        void add_eq_eh(enode * n1, enode * n2);
        void relevant_eh(enode * n);
        final_check_status final_check_eh(bool full);
        void restart_eh();

        bool can_propagate() const;
        void propagate();

        enum check_model_result {
            SAT, UNKNOWN, RESTART
        };

        bool model_based() const;
	bool mbqi_enabled(quantifier *q) const; // can mbqi instantiate this quantifier?
        void adjust_model(proto_model * m);
        check_model_result check_model(proto_model * m, obj_map<enode, app *> const & root2value);
        
        void push();
        void pop(unsigned num_scopes);
        void reset();
        
        void set_cancel(bool f);
        void display(std::ostream & out) const;
        void display_stats(std::ostream & out, quantifier * q) const;

        void collect_statistics(::statistics & st) const;
        void reset_statistics();

        ptr_vector<quantifier>::const_iterator begin_quantifiers() const;
        ptr_vector<quantifier>::const_iterator end_quantifiers() const;
    };

    class quantifier_manager_plugin {
    public:
        quantifier_manager_plugin() {}
        virtual ~quantifier_manager_plugin() {}
        
        virtual void set_manager(quantifier_manager & qm) = 0;

        virtual quantifier_manager_plugin * mk_fresh() = 0;

        virtual void add(quantifier * q) = 0;
        virtual void del(quantifier * q) = 0;

        virtual bool is_shared(enode * n) const = 0;
        
        /**
           \brief This method is invoked whenever q is assigned to true.
        */
        virtual void assign_eh(quantifier * q) = 0;
        /**
           \brief This method is invoked whenever n1 and n2 are merged into the same equivalence class.
        */
        virtual void add_eq_eh(enode * n1, enode * n2) = 0;
        /**
           \brief This method is invoked whenever n is marked as relevant.
        */
        virtual void relevant_eh(enode * n) = 0;
        /**
           \brief This method is invoked when a new search() is started.
        */
        virtual void init_search_eh() = 0;
        /**
           \brief Final_check event handler.
        */
        virtual final_check_status final_check_eh(bool full) = 0;
        /**
           \brief This method is invoked whenever the solver restarts.
        */
        virtual void restart_eh() = 0;
        
        /**
           \brief Return true if the quantifier_manager can propagate information 
           information back into the core.
        */
        virtual bool can_propagate() const = 0;
        virtual void propagate() = 0;

        /**
           \brief Return true if the plugin is "model based"
         */
        virtual bool model_based() const = 0;
        
        /**
           \brief Is "model based" instantiate allowed to instantiate this quantifier?
         */
	virtual bool mbqi_enabled(quantifier *q) const {return true;}

        /**
           \brief Give a change to the plugin to adjust the interpretation of unintepreted functions.
           It can basically change the "else" of each uninterpreted function.
        */
        virtual void adjust_model(proto_model * m) = 0;

        /**
           \brief Core invokes this method to check whether the candidate interpretation
           satisfies the quantifiers in the manager.
           It also provides a mapping from enodes to their interpretations.
        */
        virtual quantifier_manager::check_model_result check_model(proto_model * m, obj_map<enode, app *> const & root2value) = 0;
        
        virtual void push() = 0;
        virtual void pop(unsigned num_scopes) = 0;
        
        virtual void set_cancel(bool f) = 0;
    };
};

#endif
