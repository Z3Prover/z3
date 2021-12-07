
#pragma once

#include "ast/ast.h"

namespace user_propagator {

    class callback {
    public:
        virtual ~callback() = default;
        virtual void propagate_cb(unsigned num_fixed, unsigned const* fixed_ids, unsigned num_eqs, unsigned const* eq_lhs, unsigned const* eq_rhs, expr* conseq) = 0;
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

        virtual void user_propagate_clear() {
        }
       
    };

}
