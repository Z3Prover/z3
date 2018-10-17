/*++
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
#include "ast/rewriter/th_rewriter.h"

namespace recfun {
    class case_def; //<! one possible control path of a function
    class case_pred; //<! a predicate guarding a given control flow path of a function
    class util; //<! util for other modules
    class def; //!< definition of a (recursive) function
    class promise_def; //!< definition to be complete

    enum op_kind {
        OP_FUN_DEFINED, // defined function with one or more cases, possibly recursive
        OP_FUN_CASE_PRED, // predicate guarding a given control flow path
        OP_DEPTH_LIMIT, // predicate enforcing some depth limit
    };

    /*! A predicate `p(t1…tn)`, that, if true, means `f(t1…tn)` is following
        a given path of its control flow and can be unrolled.

        For example, `fact n := if n<2 then 1 else n * fact(n-1)` would have two cases,
        and therefore two case predicates `C_fact_0` and `C_fact_1`, where
        `C_fact_0(t)=true` means `t<2` (first path) and `C_fact_1(t)=true` means `¬(t<2)` (second path).
    */
    class case_pred {
        friend class case_def;
        symbol                      m_name; //<! symbol for the predicate
        std::string                 m_name_buf; //<! memory for m_name
        sort_ref_vector const &     m_domain;
        func_decl_ref               m_decl; //<! declaration for the predicate

        case_pred(ast_manager & m, family_id fid, std::string const & s, sort_ref_vector const & args);
    public:
        symbol const & get_name() const { return m_name; }
        sort_ref_vector const & get_domain() const { return m_domain; }
        func_decl * get_decl() const { return m_decl.get(); }
        unsigned get_arity() const { return m_domain.size(); }
    };

    typedef var_ref_vector vars;

    class case_def {
        friend class def;
        case_pred           m_pred; //<! predicate used for this case
        expr_ref_vector     m_guards; //<! conjunction that is equivalent to this case
        expr_ref            m_rhs; //<! if guard is true, `f(t1…tn) = rhs` holds
        def *               m_def; //<! definition this is a part of
        bool                m_immediate; //<! does `rhs` contain no defined_fun/case_pred?

        case_def(ast_manager & m,
                 family_id fid,
                 def * d,
                 std::string & name,
                 sort_ref_vector const & arg_sorts,
                 unsigned num_guards,
                 expr** guards,
                 expr* rhs);

        void add_guard(expr_ref && e) { m_guards.push_back(e); }
    public:
        symbol const& get_name() const { return m_pred.get_name(); }
        case_pred const & get_pred() const { return m_pred; }
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

        ast_manager &       m_manager;
        symbol              m_name; //<! name of function
        sort_ref_vector     m_domain; //<! type of arguments
        sort_ref            m_range; //<! return type
        vars                m_vars; //<! variables of the function
        cases               m_cases; //!< possible cases
        func_decl_ref       m_decl; //!< generic declaration
        family_id           m_fid;
        bool                m_macro;

        def(ast_manager &m, family_id fid, symbol const & s, unsigned arity, sort *const * domain, sort* range);

        // compute cases for a function, given its RHS (possibly containing `ite`).
        void compute_cases(is_immediate_pred &, th_rewriter & th_rw,
                           unsigned n_vars, var *const * vars, expr* rhs);
        void add_case(std::string & name, unsigned n_conds, expr ** conditions, expr* rhs, bool is_imm = false);
        bool contains_ite(expr* e); // expression contains a test?
    public:
        ast_manager & m() const { return m_manager; }
        symbol const & get_name() const { return m_name; }
        vars const & get_vars() const { return m_vars; }
        cases & get_cases() { return m_cases; }
        unsigned get_arity() const { return m_domain.size(); }
        sort_ref_vector const & get_domain() const { return m_domain; }
        sort_ref const & get_range() const { return m_range; }
        func_decl * get_decl() const { return m_decl.get(); }

        bool is_fun_macro() const { return m_macro; }
        bool is_fun_defined() const { return !is_fun_macro(); }

        expr * get_macro_rhs() const {
            SASSERT(is_fun_macro());
            return m_cases[0].get_rhs();
        }
    };
    
    // definition to be complete (missing RHS)
    class promise_def {
        friend class util;
        util * u;
        def * d;
        void set_definition(unsigned n_vars, var * const * vars, expr * rhs); // call only once
    public:
        promise_def(util * u, def * d) : u(u), d(d) {}
        promise_def(promise_def const & from) : u(from.u), d(from.d) {}
        def * get_def() const { return d; }
    };

    // predicate for limiting unrolling depth, to be used in assumptions and conflicts
    class depth_limit_pred {
        friend class util;
        std::string     m_name_buf;
        symbol          m_name;
        unsigned        m_depth;
        func_decl_ref   m_decl;
        unsigned        m_refcount;

        void inc_ref() { m_refcount ++; }
        void dec_ref() { SASSERT(m_refcount > 0); m_refcount --; }
    public:
        depth_limit_pred(ast_manager & m, family_id fid, unsigned d);
        unsigned get_depth() const { return m_depth; }
        symbol const & get_name() const { return m_name; }
        func_decl * get_decl() const { return m_decl.get(); }
    };

    // A reference to `depth_limit_pred`
    typedef obj_ref<depth_limit_pred, util> depth_limit_pred_ref;

    namespace decl {

        class plugin : public decl_plugin {
            typedef map<symbol, def*, symbol_hash_proc, symbol_eq_proc> def_map;
            typedef map<symbol, case_def*, symbol_hash_proc, symbol_eq_proc> case_def_map;

            mutable scoped_ptr<util> m_util;
            def_map                 m_defs; // function->def
            case_def_map            m_case_defs; // case_pred->def
            svector<symbol>         m_def_block;
            
            ast_manager & m() { return *m_manager; }
        public:
            plugin();
            virtual ~plugin() override;
            virtual void finalize() override;

            util & u() const; // build or return util

            virtual bool is_fully_interp(sort * s) const override { return false; } // might depend on unin sorts
        
            virtual decl_plugin * mk_fresh() override { return alloc(plugin); }
        
            virtual sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) override { UNREACHABLE(); return 0; }
        
            virtual func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters, 
                                             unsigned arity, sort * const * domain, sort * range) override;

            promise_def mk_def(symbol const& name, unsigned n, sort *const * params, sort * range);

            void set_definition(promise_def & d, unsigned n_vars, var * const * vars, expr * rhs);

            def* mk_def(symbol const& name, unsigned n, sort ** params, sort * range, unsigned n_vars, var ** vars, expr * rhs);

            bool has_def(const symbol& s) const { return m_defs.contains(s); }
            def const& get_def(const symbol& s) const { return *(m_defs[s]); }
            promise_def get_promise_def(const symbol &s) const { return promise_def(&u(), m_defs[s]); }
            def& get_def(symbol const& s) { return *(m_defs[s]); }
            bool has_case_def(const symbol& s) const { return m_case_defs.contains(s); }
            case_def& get_case_def(symbol const& s) { SASSERT(has_case_def(s)); return *(m_case_defs[s]); }
            bool is_declared(symbol const& s) const { return m_defs.contains(s); }
        private:
            func_decl * mk_fun_pred_decl(unsigned num_parameters, parameter const * parameters, 
                                         unsigned arity, sort * const * domain, sort * range);
            func_decl * mk_fun_defined_decl(decl_kind k,
                                            unsigned num_parameters, parameter const * parameters, 
                                            unsigned arity, sort * const * domain, sort * range);
        };
    }

    // Varus utils for recursive functions
    class util {
        friend class decl::plugin;

        typedef map<int, depth_limit_pred *, int_hash, default_eq<int>> depth_limit_map;
        
        ast_manager &           m_manager;
        family_id               m_family_id;
        th_rewriter             m_th_rw;
        decl::plugin *          m_plugin;
        depth_limit_map         m_dlimit_map;

        bool compute_is_immediate(expr * rhs);
        void set_definition(promise_def & d, unsigned n_vars, var * const * vars, expr * rhs);
    public:
        util(ast_manager &m, family_id);
        virtual ~util();

        ast_manager & m() { return m_manager; }
        th_rewriter & get_th_rewriter() { return m_th_rw; }
        bool is_case_pred(app * e) const { return is_app_of(e, m_family_id, OP_FUN_CASE_PRED); }
        bool is_defined(app * e) const { return is_app_of(e, m_family_id, OP_FUN_DEFINED); }
        bool is_depth_limit(app * e) const { return is_app_of(e, m_family_id, OP_DEPTH_LIMIT); }
        bool owns_app(app * e) const { return e->get_family_id() == m_family_id; }

        //<! add a function declaration
        def * decl_fun(symbol const & s, unsigned n_args, sort *const * args, sort * range);

        def& get_def(symbol const & s) {
            SASSERT(m_plugin->has_def(s));
            return m_plugin->get_def(s);
        }

        case_def& get_case_def(symbol const & s) {
            SASSERT(m_plugin->has_case_def(s));
            return m_plugin->get_case_def(s);
        }

        app* mk_fun_defined(def const & d, unsigned n_args, expr * const * args) {
            return m().mk_app(d.get_decl(), n_args, args);
        }
        app* mk_fun_defined(def const & d, ptr_vector<expr> const & args) {
            return mk_fun_defined(d, args.size(), args.c_ptr());
        }
        app* mk_case_pred(case_pred const & p, ptr_vector<expr> const & args) {
            return m().mk_app(p.get_decl(), args.size(), args.c_ptr());
        }

        void inc_ref(depth_limit_pred * p) { p->inc_ref(); }
        void dec_ref(depth_limit_pred * p) {
            p->dec_ref();
            if (p->m_refcount == 0) {
                m_dlimit_map.remove(p->m_depth);
                dealloc(p);
            }
        }

        depth_limit_pred_ref get_depth_limit_pred(unsigned d);
        app_ref mk_depth_limit_pred(unsigned d);
    };
}

typedef recfun::def recfun_def;
typedef recfun::case_def recfun_case_def;
typedef recfun::depth_limit_pred recfun_depth_limit_pred;
typedef recfun::decl::plugin recfun_decl_plugin;
typedef recfun::util recfun_util;
