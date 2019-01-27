/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt_relevancy.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-06-04.

Revision History:

--*/
#ifndef SMT_RELEVANCY_H_
#define SMT_RELEVANCY_H_

#include "ast/ast.h"

namespace smt {
    class context;
    class relevancy_propagator;

    class relevancy_eh {
    protected:
        void mark_as_relevant(relevancy_propagator & rp, expr * n);
        void mark_args_as_relevant(relevancy_propagator & rp, app * n);
    public:
        relevancy_eh() {}
        virtual ~relevancy_eh() {}
        /**
           \brief This method is invoked when n is marked as relevant.
        */
        virtual void operator()(relevancy_propagator & rp, expr * n) { operator()(rp); }
        /**
           \brief This method is invoked when atom is assigned to val.
        */
        virtual void operator()(relevancy_propagator & rp, expr * atom, bool val) { operator()(rp); }
        /**
           \brief Fallback for the two previous methods.
        */
        virtual void operator()(relevancy_propagator & rp) {}
    };

    class simple_relevancy_eh : public relevancy_eh {
        expr * m_target;
    public:
        simple_relevancy_eh(expr * t):m_target(t) {}
        ~simple_relevancy_eh() override {}
        void operator()(relevancy_propagator & rp) override;
    };
    
    /**
       \brief Propagate relevancy to m_target if both m_source1 and m_source2 are relevant.
     */
    class pair_relevancy_eh : public relevancy_eh {
        expr * m_source1;
        expr * m_source2;
        expr * m_target;
    public:
        pair_relevancy_eh(expr * s1, expr * s2, expr * t):m_source1(s1), m_source2(s2), m_target(t) {}
        ~pair_relevancy_eh() override {}
        void operator()(relevancy_propagator & rp) override;
    };

    /**
       \brief Relevancy propagator.
       
       The relevancy propagation constraints are specified to the
       relevancy propagator using the methods: 
          - add_handler
          - add_watch
       This class also provides helper methods for specifying commonly used constraints.

       It uses the following API from smt::context
       - find_assignment(expr * n)
          - find_enode(expr * n)
          
       It notifies smt::context that an expression became relevant by invoking
          - relevant_eh(expr * n)
          
       smt::context notifies the relevancy_propagator that a literal was assigned by
       invoking assign_eh(n, bool val)
    */
    class relevancy_propagator {
    protected:
        context & m_context;
    public:
        relevancy_propagator(context & ctx);
        virtual ~relevancy_propagator() {}

        context & get_context() { return m_context; }

        /**
           \brief Install an event handler that is invoked whenever n is marked as relevant.
        */
        virtual void add_handler(expr * n, relevancy_eh * eh) = 0;
        
        /**
           \brief Install an event handler that is invoked whenever n is assigned to the given value.

           The relevancy propagator is notified of new assignments by the method assign_eh.
        */
        virtual void add_watch(expr * n, bool val, relevancy_eh * eh) = 0;

        /**
           \brief Install an event handler that just marks target as relevant whenever n is assigned to the given value.

           The relevancy propagator is notified of new assignments by the method assign_eh.
        */
        virtual void add_watch(expr * n, bool val, expr * target) = 0;

        /**
           \brief smt::context invokes this method whenever the expression is assigned to true/false
        */
        virtual void assign_eh(expr * n, bool val) = 0;

        /**
           \brief Mark the given expression is relevant.
        */
        virtual void mark_as_relevant(expr * n) = 0;

        /**
           \brief Return true if the given expression is marked as relevant.
        */
        virtual bool is_relevant(expr * n) const = 0;

        /**
           \brief Propagate relevancy using the event handlers
           specified by add_handler and add_watch, and the structure
           of the expressions already marked as relevant.
        */
        virtual void propagate() = 0;

        /**
           \brief Return true if it can propagate relevancy.
        */
        virtual bool can_propagate() const = 0;
        
        /**
           \brief Create a backtracking point
        */
        virtual void push() = 0;
        
        /**
           \brief Backtrack.
        */
        virtual void pop(unsigned num_scopes) = 0;

        /**
           \brief Display relevant expressions.
        */
        virtual void display(std::ostream & out) const = 0;

#ifdef Z3DEBUG
        virtual bool check_relevancy(expr_ref_vector const & v) const = 0;
        virtual bool check_relevancy_or(app * n, bool root) const = 0;
#endif     
        // --------------------------
        //
        // Helper method
        //
        // --------------------------

        /**
           \brief Return true if relevancy propagation is enabled.
        */
        bool enabled() const;

        /**
           \Brief Return the region allocator for the smt::context that owns this propagator.
        */
        region & get_region() const;

        /**
           \Brief Return the ast_manager for the smt::context that owns this propagator.
        */
        ast_manager & get_manager() const;
        
        template<typename Eh>
        relevancy_eh * mk_relevancy_eh(Eh const & eh) { return new (get_region()) Eh(eh);  }
        
        /**
           \brief Creates an event handler that marks target as relevant whenever src is marked
           as relevant.
        */
        void add_dependency(expr * src, expr * target);
        
        relevancy_eh * mk_or_relevancy_eh(app * n);
        relevancy_eh * mk_and_relevancy_eh(app * n);
        relevancy_eh * mk_ite_relevancy_eh(app * n);
        relevancy_eh * mk_term_ite_relevancy_eh(app * c, app * t, app * e);
    };

    relevancy_propagator * mk_relevancy_propagator(context & ctx);

};

#endif /* SMT_RELEVANCY_H_ */

