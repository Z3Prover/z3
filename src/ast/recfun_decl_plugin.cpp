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
#include "ast/for_each_expr.h"
#include "util/scoped_ptr_vector.h"

#define TRACEFN(x) TRACE("recfun", tout << x << '\n';)
#define VALIDATE_PARAM(m, _pred_) if (!(_pred_)) m.raise_exception("invalid parameter to recfun "  #_pred_);

namespace recfun {


    case_def::case_def(
        ast_manager &m,
        family_id fid,
        def * d,
        unsigned case_index,
        sort_ref_vector const & arg_sorts,
        expr_ref_vector const& guards, 
        expr* rhs)
        : m_pred(m),
          m_guards(guards),
          m_rhs(expr_ref(rhs,m)), 
          m_def(d) {
        parameter ps[2] = { parameter(case_index), parameter(d->get_decl()) };
        func_decl_info info(fid, OP_FUN_CASE_PRED, 2, ps);
        m_pred = m.mk_func_decl(symbol("case-def"), arg_sorts.size(), arg_sorts.data(), m.mk_bool_sort(), info);
    }

    def::def(ast_manager &m, family_id fid, symbol const & s,
             unsigned arity, sort* const * domain, sort* range, bool is_generated)
        :   m(m), m_name(s),
            m_domain(m, arity, domain), 
            m_range(range, m), 
            m_vars(m), 
            m_cases(),
            m_decl(m), 
            m_rhs(m),
            m_fid(fid)
    {
        SASSERT(arity == get_arity());        
        parameter p(is_generated);
        func_decl_info info(fid, OP_FUN_DEFINED, 1, &p);
        m_decl = m.mk_func_decl(s, arity, domain, range, info);
    }

    def* def::copy(util& dst, ast_translation& tr) {
        SASSERT(&dst.m() == &tr.to());
        sort_ref_vector domain(tr.to());
        sort_ref range(tr(m_range.get()), tr.to());
        for (auto* s : m_domain)
            domain.push_back(tr(s));
        family_id fid = dst.get_family_id();
        bool is_generated = m_decl->get_parameter(0).get_int() != 0;
        def* r = alloc(def, tr.to(), fid, m_name, domain.size(), domain.data(), range, is_generated);
        r->m_rhs = tr(m_rhs.get());
        for (auto* v : m_vars)
            r->m_vars.push_back(tr(v));
        for (auto const& c1 : m_cases) {
            r->m_cases.push_back(case_def(tr.to()));
            auto& c2 = r->m_cases.back();
            c2.m_pred = tr(c1.m_pred.get());
            c2.m_guards = tr(c1.m_guards);
            c2.m_rhs = tr(c1.m_rhs.get());
            c2.m_def = r;
            c2.m_immediate = c1.m_immediate;
        }
        return r;
    }

    bool util::contains_def(expr * e) {
        struct def_find_p : public i_expr_pred {
            util& u;
            def_find_p(util& u): u(u) {}
            bool operator()(expr* a) override { return is_app(a) && u.is_defined(to_app(a)->get_decl()); }
        };
        def_find_p p(*this);
        check_pred cp(p, m(), false);
        return cp(e);
    }

    bool def::contains_def(util& u, expr * e) {
        return u.contains_def(e);
    }

    // does `e` contain any `ite` construct?
    // subject to the then/else branch using a recursive call,
    // but the guard does not.
    bool def::contains_ite(util& u, expr * e) {
        struct ite_find_p : public i_expr_pred {
            ast_manager & m;
            def& d;
            util& u;
            ite_find_p(ast_manager & m, def& d, util& u) : m(m), d(d), u(u) {}
            bool operator()(expr * e) override { return m.is_ite(e) && !d.contains_def(u, to_app(e)->get_arg(0)) && d.contains_def(u, e); }
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
    };

    // state for computing cases from the RHS of a functions' definition
    class case_state {
        region              m_reg;
        vector<branch>      m_branches;

    public:
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
            expr_ref tgt(choices->sign ? th : el, m);
            tgt = subst(tgt);
            subst.insert(ite, tgt);
        }
    }


    void def::add_case(unsigned case_index, expr_ref_vector const& conditions, expr * rhs, bool is_imm) {
        case_def c(m, m_fid, this, case_index, get_domain(), conditions, rhs);
        c.set_is_immediate(is_imm);
        TRACEFN("add_case " << case_index << " " <<  mk_pp(rhs, m)
                << "\n:is_imm " << is_imm
                << "\n:guards " << conditions);
        m_cases.push_back(c);
    }


    // Compute a set of cases, given the RHS
    void def::compute_cases(util& u,
                            replace& subst, 
                            is_immediate_pred & is_i, 
                            bool is_macro,
                            unsigned n_vars, var *const * vars, expr* rhs)
    {
        VERIFY(m_cases.empty() && "cases cannot already be computed");
        SASSERT(n_vars == m_domain.size());
        TRACEFN("compute cases " << mk_pp(rhs, m));

        if (!is_macro)
            for (expr* e : subterms::all(m_rhs))
                if (is_lambda(e))
                    throw default_exception("recursive definitions with lambdas are not supported");


        unsigned case_idx = 0;
        expr_ref_vector conditions(m);
        m_vars.append(n_vars, vars);
        m_rhs = rhs;        

        // is the function a macro (unconditional body)?
        if (is_macro || n_vars == 0 || !contains_ite(u, rhs)) {
            // constant function or trivial control flow, only one (dummy) case
            add_case(0, conditions, rhs);
            return;
        }

        
        // analyze control flow of `rhs`, accumulating guards and
        // rebuilding a `ite`-free RHS on the fly for each path in `rhs`.
        // Each such `ite`-free term is converted into a case_def and added to definition.

        case_state st;

        st.push_branch(branch(st.mk_unfold_lst(rhs)));        

        while (! st.empty()) {

            branch b = st.pop_branch();

            // first: unfold expressions, stopping when we meet subterms that are `ite`
            while (b.to_unfold != nullptr) {

                ptr_vector<expr> stack;
                stack.push_back(b.to_unfold->e);
                
                b.to_unfold = b.to_unfold->next;

                while (! stack.empty()) {
                    expr * e = stack.back();
                    stack.pop_back();                    

                    expr* cond = nullptr, *th = nullptr, *el = nullptr; 
                    if (m.is_ite(e, cond, th, el) && contains_def(u, cond)) {
                        // skip
                    }
                    if (m.is_ite(e, cond, th, el) && !contains_def(u, th) && !contains_def(u, el)) {
                        // skip
                    }
                    else if (m.is_ite(e)) {
                        // need to do a case split on `e`, forking the search space
                        b.to_split = st.cons_ite(to_app(e), b.to_split);
                    } 
                    else if (is_app(e)) {
                        // explore arguments
                        for (expr * arg : *to_app(e)) 
                            if (contains_ite(u, arg)) 
                                stack.push_back(arg);
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
                for (unsigned i = 0; i < conditions.size(); ++i) 
                    conditions[i] = subst(conditions.get(i));
                
                // yield new case
                bool is_imm = is_i(case_rhs);
                add_case(case_idx++, conditions, case_rhs, is_imm);
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

    def * util::decl_fun(symbol const& name, unsigned n, sort *const * domain, sort * range, bool is_generated) {
        return alloc(def, m(), m_fid, name, n, domain, range, is_generated);
    }

    void util::set_definition(replace& subst, promise_def & d, bool is_macro, unsigned n_vars, var * const * vars, expr * rhs) {
        expr_ref rhs1(rhs, m());
        if (!is_macro)
            rhs1 = get_plugin().redirect_ite(subst, n_vars, vars, rhs);        
        d.set_definition(subst, is_macro, n_vars, vars, rhs1);
    }

    app_ref util::mk_num_rounds_pred(unsigned d) {
        parameter p(d);
        func_decl_info info(m_fid, OP_NUM_ROUNDS, 1, &p);
        func_decl* decl = m().mk_const_decl(symbol("recfun-num-rounds"), m().mk_bool_sort(), info);
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
                    return is_app(e) && u.is_defined(to_app(e));
                }
            };
            find f(u);
            check_pred cp(f, u.m());
            bool contains_defined_fun = cp(rhs);
            return ! contains_defined_fun;
        }
    };

    // set definition 
    void promise_def::set_definition(replace& r, bool is_macro, unsigned n_vars, var * const * vars, expr * rhs) {
        SASSERT(n_vars == d->get_arity());
                    
        d->m_is_macro = is_macro;
        is_imm_pred is_i(*u);
        d->compute_cases(*u, r, is_i, is_macro, n_vars, vars, rhs);
    }

    namespace decl {
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

        void plugin::get_op_names(svector<builtin_name> & op_names, symbol const & logic) {
            op_names.push_back(builtin_name("case-def", OP_FUN_CASE_PRED));
            op_names.push_back(builtin_name("recfun-num-rounds", OP_NUM_ROUNDS));
        }


        promise_def plugin::mk_def(symbol const& name, unsigned n, sort *const * params, sort * range, bool is_generated) {
            def* d = u().decl_fun(name, n, params, range, is_generated);
            SASSERT(!m_defs.contains(d->get_decl()));
            m_defs.insert(d->get_decl(), d);
            return promise_def(&u(), d);
        }

        void plugin::inherit(decl_plugin* _other, ast_translation& tr) {
            plugin* other = static_cast<plugin*>(_other);
            for (auto [k, v] : other->m_defs) {
                func_decl_ref f(tr(k), tr.to());
                if (m_defs.contains(f))
                    continue;
                def* d = v->copy(u(), tr);
                m_defs.insert(f, d);
                for (case_def & c : d->get_cases())
                    m_case_defs.insert(c.get_decl(), &c);                    
            }
            m_has_rec_defs = other->m_has_rec_defs;
        }

        promise_def plugin::ensure_def(symbol const& name, unsigned n, sort *const * params, sort * range, bool is_generated) {
            def* d = u().decl_fun(name, n, params, range, is_generated);
            erase_def(d->get_decl());
            m_defs.insert(d->get_decl(), d);
            return promise_def(&u(), d);
        }

        void plugin::erase_def(func_decl* f) {
            def* d = nullptr;
            if (m_defs.find(f, d)) {
                for (case_def & c : d->get_cases()) 
                    m_case_defs.erase(c.get_decl());
                m_defs.erase(f);
                dealloc(d);
            }
        }
        
        void plugin::set_definition(replace& r, promise_def & d, bool is_macro, unsigned n_vars, var * const * vars, expr * rhs) {
            m_has_rec_defs |= !is_macro;
            u().set_definition(r, d, is_macro, n_vars, vars, rhs);
            for (case_def & c : d.get_def()->get_cases()) 
                m_case_defs.insert(c.get_decl(), &c);
        }

        bool plugin::has_defs() const {
            return !m_case_defs.empty();            
        }

        def* plugin::mk_def(replace& subst, bool is_macro,
                            symbol const& name, unsigned n, sort ** params, sort * range,
                            unsigned n_vars, var ** vars, expr * rhs) {
            promise_def d = mk_def(name, n, params, range, false);
            SASSERT(! m_defs.contains(d.get_def()->get_decl()));
            set_definition(subst, d, is_macro, n_vars, vars, rhs);
            return d.get_def();
        }

        // generic declaration of symbols
        func_decl * plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters, 
                                         unsigned arity, sort * const * domain, sort * range)
        {
            func_decl_info info(get_family_id(), k, num_parameters, parameters);
            switch (k) {
            case OP_FUN_CASE_PRED: 
                SASSERT(num_parameters == 2);
                return m().mk_func_decl(symbol("case-def"), arity, domain, m().mk_bool_sort(), info);
            case OP_NUM_ROUNDS: 
                SASSERT(num_parameters == 1);
                SASSERT(arity == 0);
                return m().mk_const_decl(symbol("recfun-num-rounds"), m().mk_bool_sort(), info);                
            default:
                break;
            }
            UNREACHABLE();
            return nullptr;            
        }

        /**
         * \brief compute ite nesting depth scores with each sub-expression of e.
         * associate with each subterm of e its parent terms.
         * and for every term depth the set of terms with the same depth
         */
        void plugin::compute_scores(expr* e, obj_map<expr, unsigned>& scores) {
            u_map<ptr_vector<expr>> by_depth;
            obj_map<expr, ptr_vector<expr>> parents;
            expr_ref tmp(e, m());
            parents.insert(e, ptr_vector<expr>());
            for (expr* t : subterms::ground(tmp)) {
                if (is_app(t)) {
                    for (expr* arg : *to_app(t)) {
                        parents.insert_if_not_there(arg, ptr_vector<expr>()).push_back(t);        
                    }
                }
                by_depth.insert_if_not_there(get_depth(t), ptr_vector<expr>()).push_back(t);
            }
            unsigned max_depth = get_depth(e);
            scores.insert(e, 0);
            // walk deepest terms first.
            for (unsigned i = max_depth; i > 0; --i) {
                if (!by_depth.contains(i))
                    continue;
                for (expr* t : by_depth[i]) {
                    unsigned score = 0;
                    for (expr* parent : parents[t]) {
                        score += scores[parent];
                    }
                    if (m().is_ite(t)) {
                        score++;
                        TRACEFN("score " << mk_pp(t, m()) << ": " << score);
                    }
                    scores.insert(t, score);
                }
            }
        }

        expr_ref plugin::redirect_ite(replace& subst, unsigned n, var * const* vars, expr * e) {
            expr_ref result(e, m());
            util u(m());
            while (true) {
                obj_map<expr, unsigned> scores;
                compute_scores(result, scores);
                unsigned max_score = 0;
                expr* max_expr = nullptr;
                for (auto const& [k, v] : scores) {
                    if (m().is_ite(k) && v > max_score && u.contains_def(k)) {
                        max_expr = k;
                        max_score = v;
                    }
                }
                if (max_score <= 4) 
                    break;


                ptr_vector<sort> domain;
                ptr_vector<expr> args;
                for (unsigned i = 0; i < n; ++i) {
                    domain.push_back(vars[i]->get_sort());
                    args.push_back(vars[i]);
                }
                                
                symbol fresh_name("fold-rec-" + std::to_string(m().mk_fresh_id())); 
                auto pd = mk_def(fresh_name, n, domain.data(), max_expr->get_sort(), false);
                func_decl* f = pd.get_def()->get_decl();
                expr_ref new_body(m().mk_app(f, n, args.data()), m());
                set_definition(subst, pd, false, n, vars, max_expr);
                subst.reset();
                subst.insert(max_expr, new_body);
                result = subst(result);                
                TRACEFN("substituted\n" << mk_pp(max_expr, m()) << "\n->\n" << new_body << "\n-result->\n" << result);
            }
            return result;
        }
    }

    case_expansion::case_expansion(recfun::util& u, app * n) : 
        m_lhs(n, u.m()), m_def(nullptr), m_args(u.m())  {
        SASSERT(u.is_defined(n));
        func_decl * d = n->get_decl();
        m_def = &u.get_def(d);
        m_args.append(n->get_num_args(), n->get_args());
    }

    std::ostream& case_expansion::display(std::ostream & out) const {
        return out << "case_exp(" << m_lhs << ")";
    }

    std::ostream& body_expansion::display(std::ostream & out) const {
        ast_manager& m = m_pred.m();
        out << "body_exp(" << m_cdef->get_decl()->get_name();
        for (auto* t : m_args) 
            out << " " << mk_pp(t, m);
        return out << ")";
    }

    

}


