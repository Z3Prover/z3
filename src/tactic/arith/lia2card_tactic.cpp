/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    lia2card_tactic.cpp

Abstract:

    Convert 0-1 integer variables cardinality constraints to built-in cardinality operator.

Author:
 
    Nikolaj Bjorner (nbjorner) 2013-11-5

Notes:

--*/
#include"tactical.h"
#include"cooperate.h"
#include"bound_manager.h"
#include"ast_pp.h"
#include"expr_safe_replace.h" // NB: should use proof-producing expr_substitute in polished version.

#include"card_decl_plugin.h"
#include"arith_decl_plugin.h"

class lia2card_tactic : public tactic {

    struct imp {        
        typedef obj_hashtable<expr> expr_set;
        ast_manager &                    m;
        arith_util                       a;
        card_util                        m_card;
        obj_map<expr, ptr_vector<expr> > m_uses;
        obj_map<expr, expr*>             m_converted;
        expr_set                         m_01s;
        
        imp(ast_manager & _m, params_ref const & p):
            m(_m),
            a(m),
            m_card(m) {
        }
        
        void set_cancel(bool f) {
        }
        
        void updt_params(params_ref const & p) {
        }
        
        void operator()(goal_ref const & g, 
                        goal_ref_buffer & result, 
                        model_converter_ref & mc, 
                        proof_converter_ref & pc,
                        expr_dependency_ref & core) {
            SASSERT(g->is_well_sorted());
            mc = 0; pc = 0; core = 0;
            m_01s.reset();
            m_uses.reset();
            m_converted.reset();
            
            tactic_report report("cardinality-intro", *g);
            
            bound_manager bounds(m);
            bounds(*g);

            bound_manager::iterator bit = bounds.begin(), bend = bounds.end();
            for (; bit != bend; ++bit) {
                expr* x = *bit;
                bool s1, s2;
                rational lo, hi;
                if (a.is_int(x) && 
                    bounds.has_lower(x, lo, s1) && !s1 && lo.is_zero() &&
                    bounds.has_upper(x, hi, s2) && !s2 && hi.is_one()) {
                    m_01s.insert(x);
                    TRACE("card", tout << "add bound " << mk_pp(x, m) << "\n";);
                }
            }
            if (m_01s.empty()) {
                result.push_back(g.get());
                return;
            }
            expr_set::iterator it = m_01s.begin(), end = m_01s.end();
            for (; it != end; ++it) {
                m_uses.insert(*it, ptr_vector<expr>());
            }
            for (unsigned j = 0; j < g->size(); ++j) {
                ast_mark mark;
                collect_uses(mark, g->form(j));
            }

            it = m_01s.begin(), end = m_01s.end();
            for (; it != end; ++it) {
                if (!validate_uses(m_uses.find(*it))) {
                    std::cout << "did not validate: " << mk_pp(*it, m) << "\n";
                    m_uses.remove(*it);
                    m_01s.remove(*it);
                    it = m_01s.begin();
                    end = m_01s.end();
                }
            }
            if (m_01s.empty()) {
                result.push_back(g.get());
                return;
            }

            expr_safe_replace sub(m);
            extract_substitution(sub);

            expr_ref   new_curr(m);
            proof_ref  new_pr(m);

            for (unsigned i = 0; i < g->size(); i++) {
                expr * curr = g->form(i);
                sub(curr, new_curr);                
                g->update(i, new_curr, new_pr, g->dep(i));
            }
            g->inc_depth();
            result.push_back(g.get());
            TRACE("card", g->display(tout););
            SASSERT(g->is_well_sorted());

            // TBD: convert models for 0-1 variables.
            // TBD: support proof conversion (or not..)
        }

        void extract_substitution(expr_safe_replace& sub) {
            expr_set::iterator it = m_01s.begin(), end = m_01s.end();
            for (; it != end; ++it) {
                extract_substitution(sub, *it);
            }
        }

        void extract_substitution(expr_safe_replace& sub, expr* x) {
            ptr_vector<expr> const& use_list = m_uses.find(x);
            for (unsigned i = 0; i < use_list.size(); ++i) {
                expr* u = use_list[i];
                convert_01(sub, u);
            }
        }

        expr_ref mk_le(expr* x, rational const& bound) {
            if (bound.is_pos()) {
                return expr_ref(m.mk_true(), m);
            }
            else if (bound.is_zero()) {
                return expr_ref(m.mk_not(mk_01(x)), m);
            }
            else {
                return expr_ref(m.mk_false(), m);
            }
        }

        expr_ref mk_ge(expr* x, rational const& bound) {
            if (bound.is_one()) {
                return expr_ref(mk_01(x), m);
            }
            else if (bound.is_pos()) {
                return expr_ref(m.mk_false(), m);
            }
            else {
                return expr_ref(m.mk_true(), m);
            }
        }

        bool is_01var(expr* x) const {
            return m_01s.contains(x);
        }

        void convert_01(expr_safe_replace& sub, expr* fml) {
            rational n;
            unsigned k;
            expr_ref_vector args(m);
            expr_ref result(m);
            expr* x, *y;
            if (a.is_le(fml, x, y) || a.is_ge(fml, y, x)) {
                if (is_01var(x) && a.is_numeral(y, n)) {
                    sub.insert(fml, mk_le(x, n));
                }
                else if (is_01var(y) && a.is_numeral(x, n)) {
                    sub.insert(fml, mk_ge(y, n));
                }
                else if (is_add(x, args) && is_unsigned(y, k)) { // x <= k
                    sub.insert(fml, m_card.mk_at_most_k(args.size(), args.c_ptr(), k));
                }                
                else if (is_add(y, args) && is_unsigned(x, k)) { // k <= y <=> not (y <= k-1)
                    if (k == 0) 
                        sub.insert(fml, m.mk_true());
                    else 
                        sub.insert(fml, m.mk_not(m_card.mk_at_most_k(args.size(), args.c_ptr(), k-1)));
                }
                else {
                    UNREACHABLE();
                }
            }
            else if (a.is_lt(fml, x, y) || a.is_gt(fml, y, x)) {
                if (is_01var(x) && a.is_numeral(y, n)) {
                    sub.insert(fml, mk_le(x, n-rational(1)));
                }
                else if (is_01var(y) && a.is_numeral(x, n)) {                    
                    sub.insert(fml, mk_ge(y, n+rational(1)));
                }
                else if (is_add(x, args) && is_unsigned(y, k)) { // x < k
                    if (k == 0) 
                        sub.insert(fml, m.mk_false());                
                    else
                        sub.insert(fml, m_card.mk_at_most_k(args.size(), args.c_ptr(), k-1));
                }                    
                else if (is_add(y, args) && is_unsigned(x, k)) { // k < y <=> not (y <= k)
                    sub.insert(fml, m.mk_not(m_card.mk_at_most_k(args.size(), args.c_ptr(), k)));
                }
                else {
                    UNREACHABLE();
                }
            }
            else if (m.is_eq(fml, x, y)) {
                if (!is_01var(x)) {
                    std::swap(x, y);
                }
                else if (is_01var(x) && a.is_numeral(y, n)) {
                    if (n.is_one()) {
                        sub.insert(fml, mk_01(x));
                    }
                    else if (n.is_zero()) {
                        sub.insert(fml, m.mk_not(mk_01(x)));
                    }
                    else {
                        sub.insert(fml, m.mk_false());
                    }
                }
                else {
                    UNREACHABLE();
                }
            }
            else if (is_sum(fml)) {
                SASSERT(m_uses.contains(fml));
                ptr_vector<expr> const& u = m_uses.find(fml);
                for (unsigned i = 0; i < u.size(); ++i) {
                    convert_01(sub, u[i]);
                }
            }
            else {
                UNREACHABLE();
            }
        }

        expr_ref mk_01(expr* x) {
            expr* r;
            SASSERT(is_01var(x));
            if (!m_converted.find(x, r)) {
                symbol name = to_app(x)->get_decl()->get_name();
                r = m.mk_fresh_const(name.str().c_str(), m.mk_bool_sort());
                m_converted.insert(x, r);
            }
            return expr_ref(r, m);
        }

        
        bool is_add(expr* x, expr_ref_vector& args) {
            if (a.is_add(x)) {
                app* ap = to_app(x);                    
                for (unsigned i = 0; i < ap->get_num_args(); ++i) {
                    args.push_back(mk_01(ap->get_arg(i)));
                }
                return true;
            }
            else {
                return false;
            }
        }            

        bool validate_uses(ptr_vector<expr> const& use_list) {
            for (unsigned i = 0; i < use_list.size(); ++i) {
                if (!validate_use(use_list[i])) {
                    return false;
                }
            }
            return true;
        }

        bool validate_use(expr* fml) {
            expr* x, *y;
            if (a.is_le(fml, x, y) ||
                a.is_ge(fml, x, y) ||
                a.is_lt(fml, x, y) ||
                a.is_gt(fml, x, y) ||
                m.is_eq(fml, x, y)) {
                if (a.is_numeral(x)) {
                    std::swap(x,y);
                }
                if ((is_one(y) || a.is_zero(y)) && is_01var(x)) 
                    return true;
                if (a.is_numeral(y) && is_sum(x) && !m.is_eq(fml)) {
                    return true;
                }
            }
            if (is_sum(fml)) {
                SASSERT(m_uses.contains(fml));
                ptr_vector<expr> const& u = m_uses.find(fml);
                for (unsigned i = 0; i < u.size(); ++i) {
                    if (!validate_use(u[i])) {
                        return false;
                    }
                }
                return true;
            }
            TRACE("card", tout << "Use not validated: " << mk_pp(fml, m) << "\n";);

            return false;
        }

        bool is_sum(expr* x) const {
            if (a.is_add(x)) {
                app* ap = to_app(x);
                for (unsigned i = 0; i < ap->get_num_args(); ++i) {
                    if (!is_01var(ap->get_arg(i))) {
                        return false;
                    }
                }
                return true;
            }
            return false;
        }

        bool is_unsigned(expr* x, unsigned& k) {
            rational r;
            if (a.is_numeral(x, r) && r.is_unsigned()) {
                k = r.get_unsigned();
                SASSERT(rational(k) == r);
                return true;
            }
            else {
                return false;
            }
        }

        bool is_one(expr* x) {
            rational r;
            return a.is_numeral(x, r) && r.is_one();
        }

        void collect_uses(ast_mark& mark, expr* f) {
            ptr_vector<expr> todo;
            todo.push_back(f);
            while (!todo.empty()) {
                f = todo.back();
                todo.pop_back();
                if (mark.is_marked(f)) {
                    continue;
                }
                mark.mark(f, true);
                if (is_var(f)) {
                    continue;
                }
                if (is_quantifier(f)) {
                    todo.push_back(to_quantifier(f)->get_expr());
                    continue;
                }
                app* a = to_app(f);
                for (unsigned i = 0; i < a->get_num_args(); ++i) {
                    expr* arg = a->get_arg(i);
                    if (!m_uses.contains(arg)) {
                        m_uses.insert(arg, ptr_vector<expr>());
                    }
                    m_uses.find(arg).push_back(a);
                    todo.push_back(arg);
                }
            }
        }
    };
    
    imp *      m_imp;
    params_ref m_params;
public:
    lia2card_tactic(ast_manager & m, params_ref const & p):
        m_params(p) {
        m_imp = alloc(imp, m, p);
    }

    virtual tactic * translate(ast_manager & m) {
        return alloc(lia2card_tactic, m, m_params);
    }
        
    virtual ~lia2card_tactic() {
        dealloc(m_imp);
    }

    virtual void updt_params(params_ref const & p) {
        m_params = p;
        m_imp->updt_params(p);
    }

    virtual void collect_param_descrs(param_descrs & r) {
    }
    
    virtual void operator()(goal_ref const & in, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc,
                            expr_dependency_ref & core) {
        (*m_imp)(in, result, mc, pc, core);
    }
    
    virtual void cleanup() {
        ast_manager & m = m_imp->m;
        imp * d = m_imp;
        #pragma omp critical (tactic_cancel)
        {
            m_imp = 0;
        }
        dealloc(d);
        d = alloc(imp, m, m_params);
        #pragma omp critical (tactic_cancel)
        {
            m_imp = d;
        }
    }

    virtual void set_cancel(bool f) {
        if (m_imp)
            m_imp->set_cancel(f);
    }
};

tactic * mk_lia2card_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(lia2card_tactic, m, p));
}

