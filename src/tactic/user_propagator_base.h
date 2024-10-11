
#pragma once

#include "ast/ast.h"
#include "util/lbool.h"

namespace user_propagator {

    class callback {
    public:
        virtual ~callback() = default;
        virtual bool propagate_cb(unsigned num_fixed, expr* const* fixed_ids, unsigned num_eqs, expr* const* eq_lhs, expr* const* eq_rhs, expr* conseq) = 0;
        virtual void register_cb(expr* e) = 0;
        virtual bool next_split_cb(expr* e, unsigned idx, lbool phase) = 0;
    };
    
    class context_obj {
    public:
        virtual ~context_obj() = default;
    };
    
    typedef std::function<void(void*, callback*)>                            final_eh_t;
    typedef std::function<void(void*, callback*, expr*, expr*)>              fixed_eh_t;
    typedef std::function<void(void*, callback*, expr*, expr*)>              eq_eh_t;
    typedef std::function<void*(void*, ast_manager&, context_obj*&)>         fresh_eh_t;
    typedef std::function<void(void*, callback*)>                            push_eh_t;
    typedef std::function<void(void*, callback*, unsigned)>                  pop_eh_t;
    typedef std::function<void(void*, callback*, expr*)>                     created_eh_t;
    typedef std::function<void(void*, callback*, expr*, unsigned, bool)>     decide_eh_t;
    typedef std::function<void(void*, expr*, unsigned, unsigned const*, unsigned, expr* const*)>        on_clause_eh_t;

    class plugin : public decl_plugin {
    public:

        static symbol name() { return symbol("user_propagator"); }

        enum kind_t { OP_USER_PROPAGATE };

        decl_plugin* mk_fresh() override { return alloc(plugin); }

        sort* mk_sort(decl_kind k, unsigned num_parameters, parameter const* parameters) override {
            UNREACHABLE();
            return nullptr;
        }

        func_decl* mk_func_decl(decl_kind k, unsigned num_parameters, parameter const* parameters,
            unsigned arity, sort* const* domain, sort* range) override {
            UNREACHABLE();
            return nullptr;
        }

    };

    class core {
    public:

        virtual ~core() = default;
        
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
        
        virtual void user_propagate_register_expr(expr* e) { 
            throw default_exception("user-propagators are only supported on the SMT solver");
        }

        virtual void user_propagate_register_created(created_eh_t& r) {
            throw default_exception("user-propagators are only supported on the SMT solver");
        }

        virtual void user_propagate_register_decide(decide_eh_t& r) {
            throw default_exception("user-propagators are only supported on the SMT solver");
        }

        virtual void user_propagate_clear() {
        }

        virtual void register_on_clause(void*, on_clause_eh_t& r) { 
            throw default_exception("clause logging is only supported on the SMT solver");
        }

        virtual void user_propagate_initialize_value(expr* var, expr* value) {
            throw default_exception("value initialization is only supported on the SMT solver");            
        }

       
    };

}
