/*++
Copyright (c) 2017 Microsoft Corporation, Simon Cruanes

Module Name:

    recfun_decl_plugin.h

Abstract:

    Declaration and definition of (potentially recursive) functions

Author:

    Simon Cruanes 2017-11

Revision History:

--*/

#pragma once

#include "ast/ast.h"
#include "util/obj_hashtable.h"

namespace recfun {
    class case_def;    //<! one possible control path of a function
    class case_pred;   //<! a predicate guarding a given control flow path of a function
    class util;        //<! util for other modules
    class def;         //!< definition of a (recursive) function
    class promise_def; //!< definition to be complete

    enum op_kind {
        OP_FUN_DEFINED, // defined function with one or more cases, possibly recursive
        OP_FUN_CASE_PRED, // predicate guarding a given control flow path
        OP_DEPTH_LIMIT, // predicate enforcing some depth limit
    };

    /*! A predicate `p(t1...tn)`, that, if true, means `f(t1...tn)` is following
        a given path of its control flow and can be unrolled.

        For example, `fact n := if n<2 then 1 else n * fact(n-1)` would have two cases,
        and therefore two case predicates `C_fact_0` and `C_fact_1`, where
        `C_fact_0(t)=true` means `t<2` (first path) and `C_fact_1(t)=true` means `not (t<2)` (second path).
    */

    typedef var_ref_vector vars;

    class replace {
    public:
        virtual void reset() = 0;
        virtual void insert(expr* d, expr* r) = 0;
        virtual expr_ref operator()(expr* e) = 0;
    };

    class case_def {
        friend class def;
        func_decl_ref       m_pred; //<! predicate used for this case
        expr_ref_vector     m_guards; //<! conjunction that is equivalent to this case
        expr_ref            m_rhs; //<! if guard is true, `f(t1...tn) = rhs` holds
        def *               m_def; //<! definition this is a part of
        bool                m_immediate; //<! does `rhs` contain no defined_fun/case_pred?

        case_def(ast_manager & m,
                 family_id fid,
                 def * d,
                 std::string & name,
                 unsigned case_index,
                 sort_ref_vector const & arg_sorts,
                 expr_ref_vector const& guards,
                 expr* rhs);

        void add_guard(expr_ref && e) { m_guards.push_back(e); }
    public:
        func_decl* get_decl() const { return m_pred; }

        app_ref apply_case_predicate(ptr_vector<expr> const & args) const {
            ast_manager& m = m_pred.get_manager();
            return app_ref(m.mk_app(m_pred, args.size(), args.c_ptr()), m);
        }

        def * get_def() const { return m_def; }
        expr_ref_vector const & get_guards() const { return m_guards; }
        expr * get_guards_c_ptr() const { return *m_guards.c_ptr(); }
        expr * get_guard(unsigned i) const { return m_guards[i]; }
        expr * get_rhs() const { return m_rhs; }
        unsigned num_guards() const { return m_guards.size(); }
        bool is_immediate() const { return m_immediate; };
        void set_is_immediate(bool b) { m_immediate = b; }
    };

    // closure for computing whether a `rhs` expression is immediate
    struct is_immediate_pred {
        virtual bool operator()(expr * rhs) = 0;
    };

    class def {
        friend class util;
        friend class promise_def;
        typedef vector<case_def> cases;

        ast_manager &       m;
        symbol              m_name; //<! name of function
        sort_ref_vector     m_domain; //<! type of arguments
        sort_ref            m_range; //<! return type
        vars                m_vars; //<! variables of the function
        cases               m_cases; //!< possible cases
        func_decl_ref       m_decl; //!< generic declaration
        expr_ref            m_rhs;  //!< definition
        family_id           m_fid;

        def(ast_manager &m, family_id fid, symbol const & s, unsigned arity, sort *const * domain, sort* range, bool is_generated);

        // compute cases for a function, given its RHS (possibly containing `ite`).
        void compute_cases(replace& subst, is_immediate_pred &, 
                           unsigned n_vars, var *const * vars, expr* rhs);
        void add_case(std::string & name, unsigned case_index, expr_ref_vector const& conditions, expr* rhs, bool is_imm = false);
        bool contains_ite(expr* e); // expression contains a test?
    public:
        symbol const & get_name() const { return m_name; }
        vars const & get_vars() const { return m_vars; }
        cases & get_cases() { return m_cases; }
        unsigned get_arity() const { return m_domain.size(); }
        sort_ref_vector const & get_domain() const { return m_domain; }
        sort_ref const & get_range() const { return m_range; }
        func_decl * get_decl() const { return m_decl.get(); }
        expr * get_rhs() const { return m_rhs; }

        bool is_fun_macro() const { return m_cases.size() == 1; }
        bool is_fun_defined() const { return !is_fun_macro(); }

    };
    
    // definition to be complete (missing RHS)
    class promise_def {
        friend class util;
        util * u;
        def * d;
        void set_definition(replace& r, unsigned n_vars, var * const * vars, expr * rhs); // call only once
    public:
        promise_def(util * u, def * d) : u(u), d(d) {}
        promise_def(promise_def const & from) : u(from.u), d(from.d) {}
        def * get_def() const { return d; }
    };

    namespace decl {

        class plugin : public decl_plugin {
            typedef obj_map<func_decl, def*> def_map;
            typedef obj_map<func_decl, case_def*> case_def_map;
            

            mutable scoped_ptr<util> m_util;
            def_map                  m_defs;       // function->def
            case_def_map             m_case_defs;  // case_pred->def
            
            ast_manager & m() { return *m_manager; }
        public:
            plugin();
            ~plugin() override;
            void finalize() override;

            util & u() const; // build or return util

            bool is_fully_interp(sort * s) const override { return false; } // might depend on unin sorts
        
            decl_plugin * mk_fresh() override { return alloc(plugin); }
        
            sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) override { 
                UNREACHABLE(); return nullptr; 
            }
        
            func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters, 
                                     unsigned arity, sort * const * domain, sort * range) override;
            
            promise_def mk_def(symbol const& name, unsigned n, sort *const * params, sort * range, bool is_generated = false);

            promise_def ensure_def(symbol const& name, unsigned n, sort *const * params, sort * range, bool is_generated = false);
            
            void set_definition(replace& r, promise_def & d, unsigned n_vars, var * const * vars, expr * rhs);
            
            def* mk_def(replace& subst, symbol const& name, unsigned n, sort ** params, sort * range, unsigned n_vars, var ** vars, expr * rhs);

            bool has_def(func_decl* f) const { return m_defs.contains(f); }
            bool has_defs() const;
            def const& get_def(func_decl* f) const { return *(m_defs[f]); }
            promise_def get_promise_def(func_decl* f) const { return promise_def(&u(), m_defs[f]); }
            def& get_def(func_decl* f) { return *(m_defs[f]); }
            bool has_case_def(func_decl* f) const { return m_case_defs.contains(f); }
            case_def& get_case_def(func_decl* f) { SASSERT(has_case_def(f)); return *(m_case_defs[f]); }

            func_decl_ref_vector get_rec_funs() {
                func_decl_ref_vector result(m());
                for (auto& kv : m_defs) result.push_back(kv.m_key);
                return result;
            }
        };
    }

    // Varus utils for recursive functions
    class util {
        friend class decl::plugin;
        
        ast_manager &           m_manager;
        family_id               m_fid;
        decl::plugin *          m_plugin;

        bool compute_is_immediate(expr * rhs);
        void set_definition(replace& r, promise_def & d, unsigned n_vars, var * const * vars, expr * rhs);

    public:
        util(ast_manager &m);
        ~util();

        ast_manager & m() { return m_manager; }
        decl::plugin& get_plugin() { return *m_plugin; }

        bool is_case_pred(expr * e) const { return is_app_of(e, m_fid, OP_FUN_CASE_PRED); }
        bool is_defined(expr * e) const { return is_app_of(e, m_fid, OP_FUN_DEFINED); }
        bool is_defined(func_decl* f) const { return is_decl_of(f, m_fid, OP_FUN_DEFINED); }
        bool is_generated(func_decl* f) const { return is_defined(f) && f->get_parameter(0).get_int() == 1; }
        bool is_depth_limit(expr * e) const { return is_app_of(e, m_fid, OP_DEPTH_LIMIT); }
        bool owns_app(app * e) const { return e->get_family_id() == m_fid; }

        //<! don't use native theory if recursive function declarations are not populated with defs
        bool has_defs() const { return m_plugin->has_defs(); }

        //<! add a function declaration
        def * decl_fun(symbol const & s, unsigned n_args, sort *const * args, sort * range, bool is_generated);

        def& get_def(func_decl* f) {
            SASSERT(m_plugin->has_def(f));
            return m_plugin->get_def(f);
        }

        case_def& get_case_def(expr* e) {
            SASSERT(is_case_pred(e));
            return m_plugin->get_case_def(to_app(e)->get_decl());
        }

        app* mk_fun_defined(def const & d, unsigned n_args, expr * const * args) {
            return m().mk_app(d.get_decl(), n_args, args);
        }

        app* mk_fun_defined(def const & d, ptr_vector<expr> const & args) {
            return mk_fun_defined(d, args.size(), args.c_ptr());
        }

        func_decl_ref_vector get_rec_funs() {
            return m_plugin->get_rec_funs();
        }

        app_ref mk_depth_limit_pred(unsigned d);

    };
}

