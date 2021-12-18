
#pragma once

#include "ast/ast.h"

namespace user_propagator {

    class callback {
    public:
        virtual ~callback() = default;
        virtual void propagate_cb(unsigned num_fixed, unsigned const* fixed_ids, unsigned num_eqs, unsigned const* eq_lhs, unsigned const* eq_rhs, expr* conseq) = 0;
        virtual unsigned register_cb(expr* e) = 0;
    };
    
    class context_obj {
    public:
        virtual ~context_obj() {}
    };
    
    typedef std::function<void(void*, callback*)> final_eh_t;
    typedef std::function<void(void*, callback*, unsigned, expr*)> fixed_eh_t;
    typedef std::function<void(void*, callback*, unsigned, unsigned)> eq_eh_t;
    typedef std::function<void*(void*, ast_manager&, context_obj*&)> fresh_eh_t;
    typedef std::function<void(void*)>                 push_eh_t;
    typedef std::function<void(void*,unsigned)>        pop_eh_t;
    typedef std::function<void(void*, callback*, expr*, unsigned)> created_eh_t;


    class plugin : public decl_plugin {
    public:

        enum kind_t { OP_USER_PROPAGATE };

        virtual ~plugin() {}

        virtual decl_plugin* mk_fresh() { return alloc(plugin); }

        family_id get_family_id() const { return m_family_id; }

        sort* mk_sort(decl_kind k, unsigned num_parameters, parameter const* parameters) override {
            UNREACHABLE();
            return nullptr;
        }

        func_decl* mk_func_decl(decl_kind k, unsigned num_parameters, parameter const* parameters,
            unsigned arity, sort* const* domain, sort* range) {
            UNREACHABLE();
            return nullptr;
        }

    };

    class core {
    public:

        virtual ~core() {}
        
        virtual void user_propagate_init(
            void* ctx, 
            push_eh_t&                                   push_eh,
            pop_eh_t&                                    pop_eh,
            fresh_eh_t&                                  fresh_eh) {
            throw default_exception("user-propagators are only supported on the SMT solver");
        }        
        
        virtual void user_propagate_register_fixed(fixed_eh_t& fixed_eh) {
            throw default_exception("user-propagators are only supported on the SMT solver");
        }
        
        virtual void user_propagate_register_final(final_eh_t& final_eh) {
            throw default_exception("user-propagators are only supported on the SMT solver");
        }
        
        virtual void user_propagate_register_eq(eq_eh_t& eq_eh) {
            throw default_exception("user-propagators are only supported on the SMT solver");
        }
        
        virtual void user_propagate_register_diseq(eq_eh_t& diseq_eh) {
            throw default_exception("user-propagators are only supported on the SMT solver");
        }
        
        virtual unsigned user_propagate_register(expr* e) { 
            throw default_exception("user-propagators are only supported on the SMT solver");
        }

        /**
         * Create uninterpreted function for the user propagator.
         * When expressions using the function are assigned values, generate a callback
         * into a register_declared_eh(user_ctx, solver_ctx, declared_expr, declare_id) with arguments
         * 1. context and callback context
         * 2. declared_expr: expression using function that was declared at top.
         * 3. declared_id: a unique identifier (unique within the current scope) to track the expression.
         */
        virtual func_decl* user_propagate_declare(symbol const& name, unsigned n, sort* const* domain, sort* range) {
            throw default_exception("user-propagators are only supported on the SMT solver");
        }

        virtual void user_propagate_register_created(created_eh_t& r) {
            throw default_exception("user-propagators are only supported on the SMT solver");
        }

        virtual void user_propagate_clear() {
        }

       
    };

}
