/*++
Copyright (c) 2017 Microsoft Corporation, Simon Cruanes

Module Name:

    recfun_decl_plugin.cpp

Abstract:

    Declaration and definition of (potentially recursive) functions

Author:

    Simon Cruanes 2017-11

Revision History:

--*/


#include <functional>
#include <sstream>
#include "ast/expr_functors.h"
#include "ast/recfun_decl_plugin.h"
#include "ast/ast_pp.h"
#include "util/scoped_ptr_vector.h"

#define TRACEFN(x) TRACE("recfun", tout << x << '\n';)
#define VALIDATE_PARAM(m, _pred_) if (!(_pred_)) m.raise_exception("invalid parameter to recfun "  #_pred_);

namespace recfun {


    case_def::case_def(
        ast_manager &m,
        family_id fid,
        def * d,
        std::string & name,
        unsigned case_index,
        sort_ref_vector const & arg_sorts,
        expr_ref_vector const& guards, 
        expr* rhs)
        : m_pred(m),
          m_guards(guards),
          m_rhs(expr_ref(rhs,m)), 
          m_def(d) {        
        parameter p(case_index);
        func_decl_info info(fid, OP_FUN_CASE_PRED, 1, &p);
        m_pred = m.mk_func_decl(symbol(name.c_str()), arg_sorts.size(), arg_sorts.c_ptr(), m.mk_bool_sort(), info);
    }

    def::def(ast_manager &m, family_id fid, symbol const & s,
             unsigned arity, sort* const * domain, sort* range, bool is_generated)
        :   m(m), m_name(s),
            m_domain(m, arity, domain), 
            m_range(range, m), m_vars(m), m_cases(),
            m_decl(m), 
            m_rhs(m),
            m_fid(fid)
    {
        SASSERT(arity == get_arity());        
        parameter p(is_generated);
        func_decl_info info(fid, OP_FUN_DEFINED, 1, &p);
        m_decl = m.mk_func_decl(s, arity, domain, range, info);
    }

    bool def::contains_def(util& u, expr * e) {
        struct def_find_p : public i_expr_pred {
            util& u;
            def_find_p(util& u): u(u) {}
            bool operator()(expr* a) override { return is_app(a) && u.is_defined(to_app(a)->get_decl()); }
        };
        def_find_p p(u);
        check_pred cp(p, m, false);
        return cp(e);
    }

    // does `e` contain any `ite` construct?
    bool def::contains_ite(util& u, expr * e) {
        struct ite_find_p : public i_expr_pred {
            ast_manager & m;
            def& d;
            util& u;
            ite_find_p(ast_manager & m, def& d, util& u) : m(m), d(d), u(u) {}
            bool operator()(expr * e) override { return m.is_ite(e) && d.contains_def(u, e); }
        };
        // ignore ites under quantifiers.
        // this is redundant as the code
        // that unfolds ites uses quantifier-free portion.
        ite_find_p p(m, *this, u);
        check_pred cp(p, m, false);
        return cp(e);
    }

    /*
     * compilation of functions to a list of cases.
     * 
     * We use a backtracking algorithm in a relatively functional style,
     * where the multiple states (corresponding to alternatives) are stored in
     * a region, and deallocated at the end
     */

    // immutable list of choices of `ite` terms (mapping each one's condition to true/false)
    struct choice_lst {
        app *               ite;
        bool                sign;
        choice_lst const *  next; // or null for the last one
        choice_lst(app * ite, bool sign, choice_lst const * next) : ite(ite), sign(sign), next(next) {}
    };

    struct ite_lst {
        app *              ite; // invariant: `is_ite(e)`
        ite_lst const *    next;
        ite_lst(app * ite, ite_lst const * next) : ite(ite), next(next) {}
    };

    // immutable stack of expressions to unfold
    struct unfold_lst {
        expr *              e;
        unfold_lst const *  next; // or null for last one
    };

    // main state for one branch of the search tree.
    struct branch {
        choice_lst const *      path; // choices made so far
        ite_lst const *         to_split; // `ite` terms to make a choice on
        unfold_lst const *      to_unfold; // terms yet to unfold

        branch(unfold_lst const * to_unfold):
            path(nullptr), to_split(nullptr), to_unfold(to_unfold) {}
        branch(choice_lst const * path, ite_lst const * to_split, unfold_lst const * to_unfold) : 
            path(path), to_split(to_split), to_unfold(to_unfold) {}
        branch(branch const & from) : 
            path(from.path), to_split(from.to_split), to_unfold(from.to_unfold) {}
    };

    // state for computing cases from the RHS of a functions' definition
    class case_state {
        region              m_reg;
        vector<branch>      m_branches;

    public:
        case_state() : m_reg(), m_branches() {}
        
        bool empty() const { return m_branches.empty(); }

        branch pop_branch() {
            branch res = m_branches.back();
            m_branches.pop_back();
            return res;
        }

        void push_branch(branch const & b) { m_branches.push_back(b); }

        unfold_lst const * cons_unfold(expr * e, unfold_lst const * next) {
            return new (m_reg) unfold_lst{e, next};
        }
        unfold_lst const * cons_unfold(expr * e1, expr * e2, unfold_lst const * next) {
            return cons_unfold(e1, cons_unfold(e2, next));
        }
        unfold_lst const * mk_unfold_lst(expr * e) {
            return cons_unfold(e, nullptr);
        }

        ite_lst const * cons_ite(app * ite, ite_lst const * next) {
            return new (m_reg) ite_lst{ite, next};
        }

        choice_lst const * cons_choice(app * ite, bool sign, choice_lst const * next) {
            return new (m_reg) choice_lst{ite, sign, next};
        }
    };

    //<! build a substitution and a list of conditions from a path
    static void convert_path(ast_manager & m,
                      choice_lst const * choices,
                      expr_ref_vector & conditions /* out */,
                      replace & subst /* out */)
    {
        for (; choices != nullptr; choices = choices->next) {
            app * ite = choices->ite;
            expr* c = nullptr, *th = nullptr, *el = nullptr;
            VERIFY(m.is_ite(ite, c, th, el));

            // condition to add to the guard
            conditions.push_back(choices->sign ? c : m.mk_not(c));

            // binding to add to the substitution
            subst.insert(ite, choices->sign ? th : el);
        }
    }


    void def::add_case(std::string & name, unsigned case_index, expr_ref_vector const& conditions, expr * rhs, bool is_imm) {
        case_def c(m, m_fid, this, name, case_index, get_domain(), conditions, rhs);
        c.set_is_immediate(is_imm);
        TRACEFN("add_case " << name << " " << mk_pp(rhs, m)
                << " :is_imm " << is_imm
                << " :guards " << conditions);
        m_cases.push_back(c);
    }


    // Compute a set of cases, given the RHS
    void def::compute_cases(util& u,
                            replace& subst, 
                            is_immediate_pred & is_i, 
                            unsigned n_vars, var *const * vars, expr* rhs)
    {
        VERIFY(m_cases.empty() && "cases cannot already be computed");
        SASSERT(n_vars == m_domain.size());

        TRACEFN("compute cases " << mk_pp(rhs, m));

        unsigned case_idx = 0;

        std::string name("case-");       
        name.append(m_name.bare_str());

        m_vars.append(n_vars, vars);
        m_rhs = rhs;

        expr_ref_vector conditions(m);

        // is the function a macro (unconditional body)?
        if (n_vars == 0 || !contains_ite(u, rhs)) {
            // constant function or trivial control flow, only one (dummy) case
            add_case(name, 0, conditions, rhs);
            return;
        }
        
        // analyze control flow of `rhs`, accumulating guards and
        // rebuilding a `ite`-free RHS on the fly for each path in `rhs`.
        // Each such `ite`-free term is converted into a case_def and added to definition.

        case_state st;

        st.push_branch(branch(st.mk_unfold_lst(rhs)));        

        while (! st.empty()) {
            TRACEFN("main loop iter");

            branch b = st.pop_branch();

            // first: unfold expressions, stopping when we meet subterms that are `ite`
            while (b.to_unfold != nullptr) {

                ptr_vector<expr> stack;
                stack.push_back(b.to_unfold->e);
                
                b.to_unfold = b.to_unfold->next;

                while (! stack.empty()) {
                    expr * e = stack.back();
                    stack.pop_back();
                    TRACEFN("unfold: " << mk_pp(e, m));

                    if (m.is_ite(e)) {
                        // need to do a case split on `e`, forking the search space
                        b.to_split = st.cons_ite(to_app(e), b.to_split);
                    } 
                    else if (is_app(e)) {
                        // explore arguments
                        for (expr * arg : *to_app(e)) {
                            if (contains_ite(u, arg)) {
                                stack.push_back(arg);
                            }
                        }
                    } 
                }
            }

            if (b.to_split != nullptr) {
                // split one `ite`, which will lead to distinct (sets of) cases
                app * ite = b.to_split->ite;
                TRACEFN("split: " << mk_pp(ite, m));
                expr* c = nullptr, *th = nullptr, *el = nullptr;
                VERIFY(m.is_ite(ite, c, th, el));

                /* explore both positive choice and negative choice.
                 * each contains a longer path, with `ite` mapping to `true` (resp. `false),
                 * and must unfold the `then` (resp. `else`) branch.
                 * We must also unfold the test itself, for it could contain
                 * tests.
                 */

                branch b_pos(st.cons_choice(ite, true, b.path),
                             b.to_split->next,
                             st.cons_unfold(c, th, b.to_unfold));

                branch b_neg(st.cons_choice(ite, false, b.path),
                             b.to_split->next,
                             st.cons_unfold(c, el, b.to_unfold));

                st.push_branch(b_neg);
                st.push_branch(b_pos);
            }
            else {
                // leaf of the search tree

                conditions.reset();
                subst.reset();
                convert_path(m, b.path, conditions, subst);
                
                // substitute, to get rid of `ite` terms
                expr_ref case_rhs = subst(rhs);
                TRACEFN("case_rhs: " << case_rhs);
                for (unsigned i = 0; i < conditions.size(); ++i) {
                    conditions[i] = subst(conditions.get(i));
                }
                
                // yield new case
                bool is_imm = is_i(case_rhs);
                add_case(name, case_idx++, conditions, case_rhs, is_imm);
            }
        }

        TRACEFN("done analyzing " << get_name());
    }

    /*
     * Main manager for defined functions
     */

    util::util(ast_manager & m)
        : m_manager(m), m_fid(m.get_family_id("recfun")),
          m_plugin(dynamic_cast<decl::plugin*>(m.get_plugin(m_fid))) {
    }

    util::~util() {
    }

    def * util::decl_fun(symbol const& name, unsigned n, sort *const * domain, sort * range, bool is_generated) {
        return alloc(def, m(), m_fid, name, n, domain, range, is_generated);
    }


    void util::set_definition(replace& subst, promise_def & d, unsigned n_vars, var * const * vars, expr * rhs) {
        d.set_definition(subst, n_vars, vars, rhs);
    }

    app_ref util::mk_depth_limit_pred(unsigned d) {
        parameter p(d);
        func_decl_info info(m_fid, OP_DEPTH_LIMIT, 1, &p);
        func_decl* decl = m().mk_const_decl(symbol("recfun-depth-limit"), m().mk_bool_sort(), info);
        return app_ref(m().mk_const(decl), m());
    }

    // used to know which `app` are from this theory
    struct is_imm_pred : is_immediate_pred {
        util & u;
        is_imm_pred(util & u) : u(u) {}
        bool operator()(expr * rhs) override {
            // find an `app` that is an application of a defined function
            struct find : public i_expr_pred {
                util & u;
                find(util & u) : u(u) {}
                bool operator()(expr * e) override {
                    //return is_app(e) ? u.owns_app(to_app(e)) : false;
                    if (! is_app(e)) return false;

                    app * a = to_app(e);
                    return u.is_defined(a);
                }
            };
            find f(u);
            check_pred cp(f, u.m());
            bool contains_defined_fun = cp(rhs);
            return ! contains_defined_fun;
        }
    };

    // set definition 
    void promise_def::set_definition(replace& r, unsigned n_vars, var * const * vars, expr * rhs) {
        SASSERT(n_vars == d->get_arity());
                    
        is_imm_pred is_i(*u);
        d->compute_cases(*u, r, is_i, n_vars, vars, rhs);
    }

    namespace decl {
        plugin::plugin() : decl_plugin(), m_defs(), m_case_defs() {}
        plugin::~plugin() { finalize(); }

        void plugin::finalize() {
            for (auto& kv : m_defs) {
                dealloc(kv.m_value);
            }
            m_defs.reset();
            // m_case_defs does not own its data, no need to deallocate
            m_case_defs.reset();
            m_util = nullptr; // force deletion
        }

        util & plugin::u() const {
            SASSERT(m_manager);
            SASSERT(m_family_id != null_family_id);
            if (!m_util.get()) {
                m_util = alloc(util, *m_manager);
            }
            return *(m_util.get());
        }

        promise_def plugin::mk_def(symbol const& name, unsigned n, sort *const * params, sort * range, bool is_generated) {
            def* d = u().decl_fun(name, n, params, range, is_generated);
            SASSERT(!m_defs.contains(d->get_decl()));
            m_defs.insert(d->get_decl(), d);
            return promise_def(&u(), d);
        }

        promise_def plugin::ensure_def(symbol const& name, unsigned n, sort *const * params, sort * range, bool is_generated) {
            def* d = u().decl_fun(name, n, params, range, is_generated);
            def* d2 = nullptr;
            if (m_defs.find(d->get_decl(), d2)) {
                dealloc(d2);
            }
            m_defs.insert(d->get_decl(), d);
            return promise_def(&u(), d);
        }
        
        void plugin::set_definition(replace& r, promise_def & d, unsigned n_vars, var * const * vars, expr * rhs) {
            u().set_definition(r, d, n_vars, vars, rhs);
            for (case_def & c : d.get_def()->get_cases()) {
                m_case_defs.insert(c.get_decl(), &c);
            }
        }

        bool plugin::has_defs() const {
            return !m_case_defs.empty();            
        }

        def* plugin::mk_def(replace& subst, 
                            symbol const& name, unsigned n, sort ** params, sort * range,
                            unsigned n_vars, var ** vars, expr * rhs) {
            promise_def d = mk_def(name, n, params, range);
            SASSERT(! m_defs.contains(d.get_def()->get_decl()));
            set_definition(subst, d, n_vars, vars, rhs);
            return d.get_def();
        }

        // generic declaration of symbols
        func_decl * plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters, 
                                         unsigned arity, sort * const * domain, sort * range)
        {
            UNREACHABLE();
            return nullptr;            
        }
    }
}
