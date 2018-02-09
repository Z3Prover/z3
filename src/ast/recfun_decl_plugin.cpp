/*++
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
#include "ast/expr_substitution.h"
#include "ast/recfun_decl_plugin.h"
#include "ast/ast_pp.h"
#include "util/scoped_ptr_vector.h"

#define DEBUG(x) TRACE("recfun", tout << x << '\n';)
#define VALIDATE_PARAM(m, _pred_) if (!(_pred_)) m.raise_exception("invalid parameter to recfun "  #_pred_);

namespace recfun {
    case_pred::case_pred(ast_manager & m, family_id fid, std::string const & s, sort_ref_vector const & domain)
        : m_name(), m_name_buf(s), m_domain(domain), m_decl(m)
    {
        m_name = symbol(m_name_buf.c_str());
        func_decl_info info(fid, OP_FUN_CASE_PRED);
        m_decl = m.mk_func_decl(m_name, domain.size(), domain.c_ptr(), m.mk_bool_sort(), info);
    }

    case_def::case_def(ast_manager &m,
                       family_id fid,
                       def * d,
                       std::string & name,
                       sort_ref_vector const & arg_sorts,
                       unsigned num_guards, expr ** guards, expr* rhs)
    : m_pred(m, fid, name, arg_sorts), m_guards(m), m_rhs(expr_ref(rhs,m)), m_def(d) {
        for (unsigned i=0; i<num_guards; ++i) {
            m_guards.push_back(expr_ref(guards[i], m));
        }
    }

    def::def(ast_manager &m, family_id fid, symbol const & s,
             unsigned arity, sort *const * domain, sort* range)
        :   m_manager(m), m_name(s),
            m_domain(m), m_range(range, m), m_vars(m), m_cases(),
            m_decl(m), m_fid(fid), m_macro(false)
    {
        for (unsigned i=0; i < arity; ++i)
            m_domain.push_back(domain[i]);

        SASSERT(arity == get_arity());
        
        func_decl_info info(fid, OP_FUN_DEFINED);
        m_decl = m.mk_func_decl(m_name, arity, domain, range, info);
    }

    // does `e` contain any `ite` construct?
    bool def::contains_ite(expr * e) {
        struct ite_find_p : public i_expr_pred {
            ast_manager & m;
            ite_find_p(ast_manager & m) : m(m) {}
            virtual bool operator()(expr * e) { return m.is_ite(e); }
        };
        ite_find_p p(m());
        check_pred cp(p, m());
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

        branch(choice_lst const * path, ite_lst const * to_split, unfold_lst const * to_unfold) : path(path), to_split(to_split), to_unfold(to_unfold) {}
        branch(branch const & from) : path(from.path), to_split(from.to_split), to_unfold(from.to_unfold) {}
    };

    // state for computing cases from the RHS of a functions' definition
    class case_state {
        region              m_reg;
        ast_manager &       m_manager;
        vector<branch>      m_branches;

    public:
        case_state(ast_manager & m) : m_reg(), m_manager(m), m_branches() {}
        
        bool empty() const { return m_branches.empty(); }
        ast_manager & m() const { return m_manager; }
        region & reg() { return m_reg; }

        branch pop_branch() {
            branch res = m_branches.back();
            m_branches.pop_back();
            return res;
        }

        void push_branch(branch const & b) { m_branches.push_back(b); }


        unfold_lst const * cons_unfold(expr * e, unfold_lst const * next) {
            return new (reg()) unfold_lst{e, next};
        }
        unfold_lst const * cons_unfold(expr * e1, expr * e2, unfold_lst const * next) {
            return cons_unfold(e1, cons_unfold(e2, next));
        }
        unfold_lst const * mk_unfold_lst(expr * e) {
            return cons_unfold(e, nullptr);
        }

        ite_lst const * cons_ite(app * ite, ite_lst const * next) {
            return new (reg()) ite_lst{ite, next};
        }

        choice_lst const * cons_choice(app * ite, bool sign, choice_lst const * next) {
            return new (reg()) choice_lst{ite, sign, next};
        }
    };

    //<! build a substitution and a list of conditions from a path
    void convert_path(ast_manager & m,
                      choice_lst const * choices,
                      expr_ref_vector & conditions /* out */,
                      expr_substitution & subst /* out */)
    {
        for (; choices != nullptr; choices = choices->next) {
            app * ite = choices->ite;
            SASSERT(m.is_ite(ite));

            // condition to add to the guard
            expr * cond0 = ite->get_arg(0);
            conditions.push_back(choices->sign ? cond0 : m.mk_not(cond0));

            // binding to add to the substitution
            subst.insert(ite, choices->sign ? ite->get_arg(1) : ite->get_arg(2));
        }
    }

    // substitute `subst` in `e`
    expr_ref replace_subst(th_rewriter & th_rw, ast_manager & m,
                           expr_substitution & subst, expr * e) {
        th_rw.reset();
        th_rw.set_substitution(&subst);
        expr_ref res(m);
        th_rw(e, res);
        return res;
    }

    void def::add_case(std::string & name, unsigned n_conditions, expr ** conditions, expr * rhs, bool is_imm) {
        case_def c(m(), m_fid, this, name, get_domain(), n_conditions, conditions, rhs);
        c.set_is_immediate(is_imm);
        DEBUG("add_case " << name << " " << mk_pp(rhs, m())
              << " :is_imm " << is_imm
              << " :guards " << mk_pp_vec(n_conditions, (ast**)conditions, m()));
        m_cases.push_back(c);
    }


    // Compute a set of cases, given the RHS
    void def::compute_cases(is_immediate_pred & is_i, th_rewriter & th_rw,
                            unsigned n_vars, var *const * vars, expr* rhs0)
    {
        if (m_cases.size() != 0) {
            DEBUG("bug: cases for " << m_name << " has cases already");
            UNREACHABLE();
        }
        SASSERT(n_vars = m_domain.size());

        DEBUG("compute cases " << mk_pp(rhs0, m()));

        unsigned case_idx = 0;
        std::string name;
        
        name.append("case_");
        name.append(m_name.bare_str());
        name.append("_");

        for (unsigned i=0; i<n_vars; ++i)
            m_vars.push_back(vars[i]);

#if 0
        // simplify `rhs`
        expr_ref simplified_rhs(m());
        expr* rhs;
        th_rw.reset();
        th_rw(rhs0, simplified_rhs); 
        rhs = simplified_rhs.get();

        DEBUG("simplified into " << mk_pp(rhs, m()));
#else
        expr*  rhs = rhs0;
#endif
        
        // is the function a macro (unconditional body)?
        m_macro = n_vars == 0 || !contains_ite(rhs);

        if (m_macro) {
            // constant function or trivial control flow, only one (dummy) case
            name.append("dummy");
            add_case(name, 0, 0, rhs);
            return;
        }
        
        // analyze control flow of `rhs`, accumulating guards and
        // rebuilding a `ite`-free RHS on the fly for each path in `rhs`.
        // Each such `ite`-free term is converted into a case_def and added to definition.

        case_state st(m());
        {
            branch b(nullptr, nullptr, st.mk_unfold_lst(rhs));
            st.push_branch(b);
        }

        while (! st.empty()) {
            DEBUG("main loop iter");

            branch b = st.pop_branch();

            // first: unfold expressions, stopping when we meet subterms that are `ite`
            while (b.to_unfold != nullptr) {

                ptr_vector<expr> stack;
                stack.push_back(b.to_unfold->e);
                
                b.to_unfold = b.to_unfold->next;

                while (! stack.empty()) {
                    expr * e = stack.back();
                    stack.pop_back();

                    if (m().is_ite(e)) {
                        // need to do a case split on `e`, forking the search space
                        b.to_split = st.cons_ite(to_app(e), b.to_split);
                    } else if (is_app(e)) {
                        // explore arguments
                        app * a = to_app(e);

                        for (unsigned i=0; i < a->get_num_args(); ++i)
                            stack.push_back(a->get_arg(i));
                    } 
                }
            }

            if (b.to_split != nullptr) {
                // split one `ite`, which will lead to distinct (sets of) cases
                app * ite = b.to_split->ite;
                SASSERT(m().is_ite(ite));

                /* explore both positive choice and negative choice.
                 * each contains a longer path, with `ite` mapping to `true` (resp. `false),
                 * and must unfold the `then` (resp. `else`) branch.
                 * We must also unfold the test itself, for it could contain
                 * tests.
                 */

                branch b_pos(st.cons_choice(ite, true, b.path),
                             b.to_split->next,
                             st.cons_unfold(ite->get_arg(0), ite->get_arg(1), b.to_unfold));
                branch b_neg(st.cons_choice(ite, false, b.path),
                             b.to_split->next,
                             st.cons_unfold(ite->get_arg(0), ite->get_arg(2), b.to_unfold));

                st.push_branch(b_neg);
                st.push_branch(b_pos);
            }
            else {
                // leaf of the search tree

                expr_ref_vector conditions_raw(m());
                expr_substitution subst(m());
                convert_path(m(), b.path, conditions_raw, subst);
                
                // substitute, to get rid of `ite` terms
                expr_ref case_rhs = replace_subst(th_rw, m(), subst, rhs);
                expr_ref_vector conditions(m());
                for (expr * g : conditions_raw) {
                    expr_ref g_subst(replace_subst(th_rw, m(), subst, g), m());
                    conditions.push_back(g_subst);
                }


                unsigned old_name_len = name.size();
                {   // TODO: optimize? this does many copies
                    std::ostringstream sout;
                    sout << ((unsigned long) case_idx);
                    name.append(sout.str());
                }
                case_idx ++;
                
                // yield new case
                bool is_imm = is_i(case_rhs);
                add_case(name, conditions.size(), conditions.c_ptr(), case_rhs, is_imm);
                name.resize(old_name_len);
            }
        }

        DEBUG("done analysing " << get_name());
    }

    /*
     * Main manager for defined functions
     */

    util::util(ast_manager & m, family_id id)
    : m_manager(m), m_family_id(id), m_th_rw(m), m_plugin(0), m_dlimit_map() {
        m_plugin = dynamic_cast<decl::plugin*>(m.get_plugin(m_family_id));
    }

    util::~util() {
        for (auto & kv : m_dlimit_map) {
            dealloc(kv.m_value);
        }
    }

    def * util::decl_fun(symbol const& name, unsigned n, sort *const * domain, sort * range) {
        return alloc(def, m(), m_family_id, name, n, domain, range);
    }

    void util::set_definition(promise_def & d, unsigned n_vars, var * const * vars, expr * rhs) {
        d.set_definition(n_vars, vars, rhs);
    }

    // get or create predicate for depth limit
    depth_limit_pred_ref util::get_depth_limit_pred(unsigned d) {
        depth_limit_pred * pred = nullptr;
        if (! m_dlimit_map.find(d, pred)) {
            pred = alloc(depth_limit_pred, m(), m_family_id, d);
            m_dlimit_map.insert(d, pred);   
        }
        return depth_limit_pred_ref(pred, *this);
    }

    app_ref util::mk_depth_limit_pred(unsigned d) {
        depth_limit_pred_ref p = get_depth_limit_pred(d);
        app_ref res(m().mk_const(p->get_decl()), m());
        return res;
    }

    // used to know which `app` are from this theory
    struct is_imm_pred : is_immediate_pred {
        util & u;
        is_imm_pred(util & u) : u(u) {}
        bool operator()(expr * rhs) {
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
    void promise_def::set_definition(unsigned n_vars, var * const * vars, expr * rhs) {
        SASSERT(n_vars == d->get_arity());
                    
        is_imm_pred is_i(*u);
        d->compute_cases(is_i, u->get_th_rewriter(), n_vars, vars, rhs);
    }

    depth_limit_pred::depth_limit_pred(ast_manager & m, family_id fid, unsigned d)
    : m_name_buf(), m_name(""), m_depth(d), m_decl(m) {
        // build name, then build decl
        std::ostringstream tmpname;
        tmpname << "depth_limit_" << d << std::flush;
        m_name_buf.append(tmpname.str());
        m_name = symbol(m_name_buf.c_str());
        parameter params[1] = { parameter(d) };
        func_decl_info info(fid, OP_DEPTH_LIMIT, 1, params);
        m_decl = m.mk_const_decl(m_name, m.mk_bool_sort(), info);
    }

    namespace decl {
        plugin::plugin() : decl_plugin(), m_defs(), m_case_defs(), m_def_block() {}
        plugin::~plugin() { finalize(); }

        void plugin::finalize() {
            for (auto& kv : m_defs) {
                dealloc(kv.m_value);
            }
            m_defs.reset();
            // m_case_defs does not own its data, no need to deallocate
            m_case_defs.reset();
            m_util = 0; // force deletion
        }

        util & plugin::u() const {
            SASSERT(m_manager);
            SASSERT(m_family_id != null_family_id);
            if (m_util.get() == 0) {
                m_util = alloc(util, *m_manager, m_family_id);
            }
            return *(m_util.get());
        }

        promise_def plugin::mk_def(symbol const& name, unsigned n, sort *const * params, sort * range) {
            SASSERT(! m_defs.contains(name));
            def* d = u().decl_fun(name, n, params, range);
            m_defs.insert(name, d);
            return promise_def(&u(), d);
        }
        
        void plugin::set_definition(promise_def & d, unsigned n_vars, var * const * vars, expr * rhs) {
            u().set_definition(d, n_vars, vars, rhs);
            for (case_def & c : d.get_def()->get_cases()) {
                m_case_defs.insert(c.get_name(), &c);
            }
        }

        def* plugin::mk_def(symbol const& name, unsigned n, sort ** params, sort * range,
                            unsigned n_vars, var ** vars, expr * rhs) {
            SASSERT(! m_defs.contains(name));
            promise_def d = mk_def(name, n, params, range);
            set_definition(d, n_vars, vars, rhs);
            return d.get_def();
        }

        func_decl * plugin::mk_fun_pred_decl(unsigned num_parameters, parameter const * parameters, 
                                             unsigned arity, sort * const * domain, sort * range)
        {
            VALIDATE_PARAM(m(), m().is_bool(range) && num_parameters == 1 && parameters[0].is_ast());
            func_decl_info info(m_family_id, OP_FUN_CASE_PRED, num_parameters, parameters);
            info.m_private_parameters = true;
            return m().mk_func_decl(symbol(parameters[0].get_symbol()), arity, domain, range, info);
        }

        func_decl * plugin::mk_fun_defined_decl(decl_kind k, unsigned num_parameters,
                                                parameter const * parameters, 
                                                unsigned arity, sort * const * domain, sort * range)
        {
            VALIDATE_PARAM(m(), num_parameters == 1 && parameters[0].is_ast());
            func_decl_info info(m_family_id, k, num_parameters, parameters);
            info.m_private_parameters = true;
            return m().mk_func_decl(symbol(parameters[0].get_symbol()), arity,
                                    domain, range, info);
        }

        // generic declaration of symbols
        func_decl * plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters, 
                                         unsigned arity, sort * const * domain, sort * range)
        {
            switch(k) {
                case OP_FUN_CASE_PRED:
                    return mk_fun_pred_decl(num_parameters, parameters, arity, domain, range);
                case OP_FUN_DEFINED:
                    return mk_fun_defined_decl(k, num_parameters, parameters, arity, domain, range);
                default:
                    UNREACHABLE(); return 0;
            }
        }
    }
}