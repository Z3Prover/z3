/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    q_model_fixer.cpp

Abstract:

    Model-based quantifier instantiation model-finder plugin

Author:

    Nikolaj Bjorner (nbjorner) 2020-10-02

Notes:
   
    Derives from smt/smt_model_finder.cpp

--*/


#include "ast/for_each_expr.h"
#include "ast/arith_decl_plugin.h"
#include "ast/bv_decl_plugin.h"
#include "model/model_macro_solver.h"
#include "sat/smt/q_model_fixer.h"
#include "sat/smt/q_solver.h"
#include "sat/smt/euf_solver.h"


namespace q {

    template<typename U>
    static bool lt(U const& u, expr* x, expr* y) {
        rational v1, v2;
        if (u.is_numeral(x, v1) && u.is_numeral(y, v2)) 
            return v1 < v2;
        else 
            return x->get_id() < y->get_id();                            
    }

    class arith_projection : public projection_function {
        ast_manager& m;
        arith_util   a;
    public:        
        arith_projection(ast_manager& m): m(m), a(m) {}
        ~arith_projection() override {}
        bool operator()(expr* e1, expr* e2) const override { return lt(a, e1, e2); }
        expr* mk_lt(expr* x, expr* y) override { return a.mk_lt(x, y); }
    };

    class ubv_projection : public projection_function {
        ast_manager& m;
        bv_util bvu;
    public:        
        ubv_projection(ast_manager& m): m(m), bvu(m) {}
        ~ubv_projection() override {}
        bool operator()(expr* e1, expr* e2) const override { return lt(bvu, e1, e2); }
        expr* mk_lt(expr* x, expr* y) override { return m.mk_not(bvu.mk_ule(y, x)); }        
    };

    model_fixer::model_fixer(euf::solver& ctx, q::solver& qs) :
        ctx(ctx), m_qs(qs), m(ctx.get_manager()), m_dependencies(m) {}

    void model_fixer::operator()(model& mdl) {
        ptr_vector<quantifier> univ;
        for (sat::literal lit : m_qs.universal()) {
            quantifier* q = to_quantifier(ctx.bool_var2expr(lit.var()));
            if (ctx.is_relevant(q))
                univ.push_back(q);
        }
        if (univ.empty())
            return;

        m_dependencies.reset();
        m_projection_data.reset();
        m_projection_pinned.reset();
        ptr_vector<quantifier> residue;               
        
        simple_macro_solver sms(m, *this);
        sms(mdl, univ, residue);

        hint_macro_solver hms(m, *this);
        hms(mdl, univ, residue);

        non_auf_macro_solver nas(m, *this, m_dependencies);
        nas.set_mbqi_force_template(ctx.get_config().m_mbqi_force_template);
        nas(mdl, univ, residue);

        univ.append(residue);
        add_projection_functions(mdl, univ);
    }

    quantifier_macro_info* model_fixer::operator()(quantifier* q) {
        quantifier_macro_info* info = nullptr;
        if (!m_q2info.find(q, info)) {
            info = alloc(quantifier_macro_info, m, m_qs.flatten(q));
            m_q2info.insert(q, info);
            ctx.push(new_obj_trail<euf::solver, quantifier_macro_info>(info));
            ctx.push(insert_obj_map<euf::solver, quantifier, quantifier_macro_info*>(m_q2info, q));
        }
        return info;
    }

    void model_fixer::add_projection_functions(model& mdl, ptr_vector<quantifier> const& qs) {
        func_decl_set fns;
        collect_partial_functions(qs, fns);
        for (func_decl* f : fns)
            add_projection_functions(mdl, f);
    }

    void model_fixer::add_projection_functions(model& mdl, func_decl* f) {
        // update interpretation of f so that the graph of f is fully determined by the
        // ground values of its arguments.
        std::cout << mdl << "\n";
        func_interp* fi = mdl.get_func_interp(f);
        if (!fi) 
            return;
        if (fi->is_constant())
            return;
        expr_ref_vector args(m);
        for (unsigned i = 0; i < f->get_arity(); ++i) 
            args.push_back(add_projection_function(mdl, f, i));
        if (!fi->get_else() && fi->num_entries() > 0)
            fi->set_else(fi->get_entry(ctx.s().rand()(fi->num_entries()))->get_result());
        bool has_projection = false;
        for (expr* arg : args)
            has_projection |= !is_var(arg);
        if (!has_projection)
            return;
        func_interp* new_fi = alloc(func_interp, m, f->get_arity());
        func_decl* f_new = m.mk_fresh_func_decl(f->get_name(), symbol("aux"), f->get_arity(), f->get_domain(), f->get_range());
        new_fi->set_else(m.mk_app(f_new, args));
        mdl.update_func_interp(f, new_fi);
        mdl.register_decl(f_new, fi);

        std::cout << mdl << "\n";
    }

    expr_ref model_fixer::add_projection_function(model& mdl, func_decl* f, unsigned idx) {
        sort* srt = f->get_domain(idx);
        projection_function* proj = get_projection(srt);
        if (!proj)
            return expr_ref(m.mk_var(idx, srt), m);
        scoped_ptr<projection_meta_data> md = alloc(projection_meta_data, m);
        expr_ref_vector& values = md->values;
        for (euf::enode* n : ctx.get_egraph().enodes_of(f)) {
            expr* t = n->get_arg(idx)->get_expr();
            values.push_back(mdl(t));
            md->v2t.insert(values.back(), t);
            md->t2v.insert(t, values.back());
        }
        if (values.empty())
            return expr_ref(m.mk_var(idx, srt), m);
        struct lt {
            projection_function* p;
            lt(projection_function* p) : p(p) {}
            bool operator()(expr* a, expr* b) const { return (*p)(a, b); }
        };
        lt _lt(proj);
        std::sort(values.c_ptr(), values.c_ptr() + values.size(), _lt);
        unsigned j = 0;
        for (unsigned i = 0; i < values.size(); ++i) 
            if (i == 0 || values.get(i-1) != values.get(i))
                values[j++] = values.get(i);
        values.shrink(j);
        std::cout << "values: " << values << "\n";

        m_projection_data.insert(indexed_decl(f, idx), md.get());
        m_projection_pinned.push_back(md.detach());

        unsigned sz = values.size();
        expr_ref var(m.mk_var(0, srt), m);
        expr_ref pi(values.get(sz-1), m);
        for (unsigned i = sz - 1; i >= 1; i--) {
            expr* c = proj->mk_lt(var, values.get(i));
            pi = m.mk_ite(c, values.get(i - 1), pi);
        }
        std::cout << "pi " << pi << "\n";
        func_interp* rpi = alloc(func_interp, m, 1);
        rpi->set_else(pi);
        func_decl * p = m.mk_fresh_func_decl(1, &srt, srt);
        mdl.register_decl(p, rpi);       
        return expr_ref(m.mk_app(p, m.mk_var(idx, srt)), m);
    }

    projection_function* model_fixer::get_projection(sort* srt) {
        projection_function* proj = nullptr;
        if (m_projections.find(srt, proj))
            return proj;
        arith_util autil(m);
        bv_util butil(m);
        if (autil.is_real(srt) || autil.is_int(srt))
            proj = alloc(arith_projection, m);
        else if (butil.is_bv_sort(srt))
            proj = alloc(ubv_projection, m);
        // TBD: sbv_projection? FP, ADT projection?
        if (!proj)
            return nullptr;
        m_projections.insert(srt, proj);
        ctx.push(new_obj_trail<euf::solver, projection_function>(proj));
        ctx.push(insert_obj_map<euf::solver, sort, projection_function*>(m_projections, srt));
        return proj;
    }

    void model_fixer::collect_partial_functions(ptr_vector<quantifier> const& qs, func_decl_set& fns) {
        for (quantifier* q : qs) {
            auto* info = (*this)(q);
            quantifier* flat_q = info->get_flat_q();
            expr_ref body(flat_q->get_expr(), m);
            for (expr* t : subterms(body)) 
                if (is_uninterp(t) && !to_app(t)->is_ground())
                    fns.insert(to_app(t)->get_decl());           
        }
    }

    expr* model_fixer::invert_app(app* t, expr* value) { 
        euf::enode* r = nullptr;
        std::cout << "invert-app " << mk_pp(t, m) << " = " << mk_pp(value, m) << "\n";
        if (ctx.values2root().find(value, r))
            std::cout << "inverse " << mk_pp(r->get_expr(), m) << "\n";
        if (ctx.values2root().find(value, r))
            return r->get_expr();
        return value; 
    }

    expr* model_fixer::invert_arg(app* t, unsigned i, expr* value)  { 
        std::cout << "invert-arg " << mk_pp(t, m) << " " << i << " " << mk_pp(value, m) << "\n";
        auto const* md = get_projection_data(t->get_decl(), i);
        if (!md)
            return m.mk_true();
        auto* proj = get_projection(t->get_decl()->get_domain(i));
        if (!proj)
            return m.mk_true();

        if (md->values.size() <= 1) 
            return m.mk_true();
        
        //
        // md->values are sorted
        // 
        unsigned j = 0;
        for (expr* val : md->values) {
            if ((*proj)(value, val))
                ++j;
            else
                break;
        }
        expr* lo = md->values[j];
        expr* arg = t->get_arg(i);
        expr* result = m.mk_not(proj->mk_lt(arg, lo));
        if (j + 1 < md->values.size()) 
            result = m.mk_and(result, proj->mk_lt(arg, md->values[j + 1]));
        std::cout << "invert-art: " << mk_pp(result, m) << "\n";
        return result;
    }
}
