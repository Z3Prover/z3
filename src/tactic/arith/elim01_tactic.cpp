/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    elim01_tactic.cpp

Abstract:

    Replace 0-1 integer variables by Booleans.

Author:
 
    Nikolaj Bjorner (nbjorner) 2013-12-7

Notes:

--*/
#include"tactical.h"
#include"cooperate.h"
#include"bound_manager.h"
#include"ast_pp.h"
#include"expr_safe_replace.h" // NB: should use proof-producing expr_substitute in polished version.
#include"arith_decl_plugin.h"
#include"elim01_tactic.h"
#include"model_smt2_pp.h"
#include"th_rewriter.h"

class bool2int_model_converter : public model_converter {
    ast_manager&                   m;
    arith_util                     a;
    func_decl_ref_vector           m_refs;
    obj_hashtable<func_decl>       m_bools;
    vector<ptr_vector<func_decl> > m_nums_as_bool;
    ptr_vector<func_decl>          m_nums_as_int;
public:

    bool2int_model_converter(ast_manager& m):
        m(m),
        a(m),
        m_refs(m)
    {}

    virtual void operator()(model_ref & old_model, unsigned goal_idx) {
        SASSERT(goal_idx == 0);
        model * new_model = alloc(model, m);
        unsigned num = old_model->get_num_constants();
        for (unsigned i = 0; i < m_nums_as_int.size(); ++i) {
            func_decl* f_old = m_nums_as_int[i];
            rational val(0);
            rational po(1);
            bool is_value = true;
            for (unsigned j = 0; is_value && j < m_nums_as_bool[i].size(); ++j) {
                func_decl* f = m_nums_as_bool[i][j];
                expr* fi = old_model->get_const_interp(f);
                if (!fi) {
                    is_value = false;
                }
                else if (m.is_true(fi)) {
                    val += po;
                }
                else if (!m.is_false(fi)) {
                    is_value = false;
                }
                po *= rational(2);
            }
            if (is_value) {
                expr* fi = a.mk_numeral(val, true);
                new_model->register_decl(f_old, fi);
            }
        }
        for (unsigned i = 0; i < num; ++i) {
            func_decl* f = old_model->get_constant(i);
            expr* fi = old_model->get_const_interp(f);
            if (!m_bools.contains(f)) {
                new_model->register_decl(f, fi);
            }
        }    
        num = old_model->get_num_functions();
        for (unsigned i = 0; i < num; i++) {
            func_decl * f = old_model->get_function(i);
            func_interp * fi = old_model->get_func_interp(f);
            new_model->register_decl(f, fi->copy());
        }
        new_model->copy_usort_interps(*old_model);
        old_model = new_model;        
    }

    void insert(func_decl* x_new, func_decl* x_old) {
        m_refs.push_back(x_new);
        m_refs.push_back(x_old);
        m_bools.insert(x_new);
        m_nums_as_int.push_back(x_old);
        m_nums_as_bool.push_back(ptr_vector<func_decl>());
        m_nums_as_bool.back().push_back(x_new);
    }

    void insert(func_decl* x_old, unsigned sz, func_decl * const* x_new) {
        m_nums_as_int.push_back(x_old);
        m_nums_as_bool.push_back(ptr_vector<func_decl>());
        m_refs.push_back(x_old);
        for (unsigned i = 0; i < sz; ++i) {
            m_refs.push_back(x_new[i]);
            m_nums_as_bool.back().push_back(x_new[i]);
            m_bools.insert(x_new[i]);
        }
    }

    virtual model_converter * translate(ast_translation & translator) {
        bool2int_model_converter* mc = alloc(bool2int_model_converter, translator.to());
        for (unsigned i = 0; i < m_nums_as_int.size(); ++i) {
            mc->insert(m_nums_as_int[i], m_nums_as_bool[i].size(), m_nums_as_bool[i].c_ptr());
        }
        return mc;
    }
};


class elim01_tactic : public tactic {
public:
    typedef obj_hashtable<expr> expr_set;
    ast_manager &                    m;
    arith_util                       a;
    th_rewriter                      m_rewriter;
    params_ref                       m_params;
    unsigned                         m_max_hi_default;
    rational                         m_max_hi;
    
    elim01_tactic(ast_manager & _m, params_ref const & p):
        m(_m),
        a(m),
        m_rewriter(m),
        m_max_hi_default(8),
        m_max_hi(rational(m_max_hi_default)) {
    }

    virtual ~elim01_tactic() {
    }
        
    void set_cancel(bool f) {
    }
        
    virtual void updt_params(params_ref const & p) {
        m_max_hi = rational(p.get_uint("max_coefficient", m_max_hi_default));
        m_params = p;
    }

    virtual void collect_param_descrs(param_descrs & r) {
        r.insert("max_coefficient", CPK_UINT, "(default: 1) maximal upper bound for finite range -> Bool conversion");
    }

    
    virtual void operator()(goal_ref const & g, 
                    goal_ref_buffer & result, 
                    model_converter_ref & mc, 
                    proof_converter_ref & pc,
                    expr_dependency_ref & core) {
        SASSERT(g->is_well_sorted());
        mc = 0; pc = 0; core = 0;
        
        tactic_report report("elim01", *g);
        
        expr_safe_replace sub(m);
        bool2int_model_converter* b2i = alloc(bool2int_model_converter, m);
        mc = b2i;
        bound_manager bounds(m);
        expr_ref_vector axioms(m);
        bounds(*g);
        
        rational zero(0);
        bound_manager::iterator bit = bounds.begin(), bend = bounds.end();
        for (; bit != bend; ++bit) {
            if (!is_app(*bit)) continue;
            app* x = to_app(*bit);
            bool s1, s2;
            rational lo, hi;
            if (a.is_int(x) && 
                bounds.has_lower(x, lo, s1) && !s1 && zero <= lo &&
                bounds.has_upper(x, hi, s2) && !s2 && hi <= m_max_hi && lo <= hi) {
                add_variable(b2i, sub, x, lo.get_unsigned(), hi.get_unsigned(), axioms);
            }
            else if (a.is_int(x)) {
                TRACE("pb", tout << "Not adding variable " << mk_pp(x, m) << " has lower: " 
                      << bounds.has_lower(x, lo, s1) << " " << lo << " has upper: " 
                      << bounds.has_upper(x, hi, s2) << " " << hi << "\n";);
            }
        }

        if (sub.empty()) {
            result.push_back(g.get());
            return;
        }
               
        expr_ref   new_curr(m), tmp_curr(m);
        proof_ref  new_pr(m);
        for (unsigned i = 0; i < g->size(); i++) {
            expr * curr = g->form(i);
            sub(curr, tmp_curr);           
            m_rewriter(tmp_curr, new_curr);
            if (m.proofs_enabled()) {
                new_pr = m.mk_rewrite(curr, new_curr);
                new_pr = m.mk_modus_ponens(g->pr(i), new_pr);
            }
            g->update(i, new_curr, new_pr, g->dep(i));
        }
        for (unsigned i = 0; i < axioms.size(); ++i) {
            g->assert_expr(axioms[i].get());
        }
        g->inc_depth();
        result.push_back(g.get());
        TRACE("pb", g->display(tout););
        SASSERT(g->is_well_sorted());
        
        // TBD: support proof conversion (or not..)
    }
    
    virtual tactic * translate(ast_manager & m) {
        return alloc(elim01_tactic, m, m_params);
    }
                
    virtual void cleanup() {}

    void add_variable(bool2int_model_converter* b2i,
                      expr_safe_replace& sub,
                      app* x,
                      unsigned min_value,
                      unsigned max_value,
                      expr_ref_vector& axioms) {
        std::string name = x->get_decl()->get_name().str();
        unsigned sh = 0;
        app_ref_vector xs(m), ites(m);
        func_decl_ref_vector xfs(m);
        app_ref zero(m), sum(m);
        zero = a.mk_numeral(rational(0), true);
        while (max_value >= (1ul << sh)) {
            xs.push_back(m.mk_fresh_const(name.c_str(), m.mk_bool_sort()));
            xfs.push_back(xs.back()->get_decl());
            ites.push_back(m.mk_ite(xs.back(), a.mk_numeral(rational(1 << sh), true), zero));
            ++sh;
        }
        switch (ites.size()) {
        case 0:
            sum = zero;
            break;
        case 1:
            sum = ites[0].get();
            break;
        default:
            sum = a.mk_add(ites.size(), (expr*const*)ites.c_ptr());
            break;
        }
        TRACE("pb", tout << mk_pp(x, m) << " " << sum << " max: " << max_value << "\n";);

        sub.insert(x, sum);
        b2i->insert(x->get_decl(), xfs.size(), xfs.c_ptr());
        // if max_value+1 is not a power of two:
        if ((max_value & (max_value + 1)) != 0) {
            axioms.push_back(a.mk_le(sum, a.mk_numeral(rational(max_value), true)));
        }
        if (min_value > 0) {
            axioms.push_back(a.mk_ge(sum, a.mk_numeral(rational(min_value), true)));
        }
    }
                      
};

tactic * mk_elim01_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(elim01_tactic, m, p));
}

