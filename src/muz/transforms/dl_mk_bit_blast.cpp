/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    dl_mk_bit_blast.cpp

Abstract:

    <abstract>

Author:

    Nikolaj Bjorner (nbjorner) 2012-08-30

Revision History:

--*/

#include "dl_mk_bit_blast.h"
#include "bit_blaster_rewriter.h"
#include "rewriter_def.h"
#include "ast_pp.h"
#include "expr_safe_replace.h"
#include "filter_model_converter.h"
#include "dl_mk_interp_tail_simplifier.h"
#include "fixedpoint_params.hpp"
#include "scoped_proof.h"
#include "model_v2_pp.h"

namespace datalog {

    //
    //   P(v) :- Q(extract[1:1]v ++ 0), R(1 ++ extract[0:0]v).
    // -> 
    //   P(bv(x,y)) :- Q(bv(x,0)), R(bv(1,y)) .
    // 
    // Introduce P_bv:
    // P_bv(x,y)  :- Q_bv(x,0), R_bv(1,y)
    // P(bv(x,y)) :- P_bv(x,y)
    // Query

    // this model converter should be composed with a filter converter
    // that gets rid of the new functions.
    class bit_blast_model_converter : public model_converter {
        ast_manager& m;
        bv_util      m_bv;
        func_decl_ref_vector m_old_funcs;
        func_decl_ref_vector m_new_funcs;
    public:
        bit_blast_model_converter(ast_manager& m):
            m(m),
            m_bv(m),
            m_old_funcs(m), 
            m_new_funcs(m) {}

        void insert(func_decl* old_f, func_decl* new_f) {
            m_old_funcs.push_back(old_f);
            m_new_funcs.push_back(new_f);
        }

        virtual model_converter * translate(ast_translation & translator) { 
            return alloc(bit_blast_model_converter, m);
        }

        virtual void operator()(model_ref & model) {
            for (unsigned i = 0; i < m_new_funcs.size(); ++i) {
                func_decl* p = m_new_funcs[i].get();
                func_decl* q = m_old_funcs[i].get();
                func_interp* f = model->get_func_interp(p);
                if (!f) continue;
                expr_ref body(m);                
                unsigned arity_p = p->get_arity();
                unsigned arity_q = q->get_arity();
                TRACE("dl",
                      model_v2_pp(tout, *model);
                      tout << mk_pp(p, m) << "\n";
                      tout << mk_pp(q, m) << "\n";);
                SASSERT(0 < arity_p);
                SASSERT(f);
                model->register_decl(p, f->copy());
                func_interp* g = alloc(func_interp, m, arity_q);

                if (f) {
                    body = f->get_interp();
                    SASSERT(!f->is_partial());
                    SASSERT(body);                    
                }
                else {
                    body = m.mk_false();  
                }
                unsigned idx = 0;
                expr_ref arg(m), proj(m);
                expr_safe_replace sub(m);
                for (unsigned j = 0; j < arity_q; ++j) {
                    sort* s = q->get_domain(j);
                    arg = m.mk_var(j, s);
                    expr* t = arg;
                    if (m_bv.is_bv_sort(s)) {
                        unsigned sz = m_bv.get_bv_size(s);
                        for (unsigned k = 0; k < sz; ++k) {
                            parameter p(k);
                            proj = m.mk_app(m_bv.get_family_id(), OP_BIT2BOOL, 1, &p, 1, &t);
                            sub.insert(m.mk_var(idx++, m.mk_bool_sort()), proj); 
                        }
                    }
                    else {
                        sub.insert(m.mk_var(idx++, s), arg);
                    }
                }
                sub(body);                
                g->set_else(body);
                model->register_decl(q, g);
            }                        
        }        
    };

    class expand_mkbv_cfg : public default_rewriter_cfg {

        context&             m_context;
        ast_manager&         m;
        bv_util              m_util;
        expr_ref_vector      m_args, m_f_vars, m_g_vars;
        func_decl_ref_vector m_old_funcs;
        func_decl_ref_vector m_new_funcs;
        rule_set const*      m_src;
        rule_set*            m_dst;
        obj_map<func_decl,func_decl*> m_pred2blast;


    public:

        expand_mkbv_cfg(context& ctx):
            m_context(ctx), 
            m(ctx.get_manager()),
            m_util(m),
            m_args(m), 
            m_f_vars(m),
            m_g_vars(m),
            m_old_funcs(m),
            m_new_funcs(m),
            m_src(0),
            m_dst(0)
        {}

        ~expand_mkbv_cfg() {}

        void set_src(rule_set const* src) { m_src = src; }
        void set_dst(rule_set* dst) { m_dst = dst; }
        func_decl_ref_vector const& old_funcs() const { return m_old_funcs; }
        func_decl_ref_vector const& new_funcs() const { return m_new_funcs; }
        
        br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) { 
            if (num == 0) {
                if (m_src->is_output_predicate(f))
                    m_dst->set_output_predicate(f);
                return BR_FAILED;
            }

            for (unsigned i = 0; i < num; ++i) {
                if (!m_util.is_mkbv(args[i]))
                    return BR_FAILED;
            }

            // 
            // f(mk_bv(args),...)
            // 
            m_args.reset();
            m_g_vars.reset();
            m_f_vars.reset();
            expr_ref fml(m);
            unsigned idx = 0;
            for (unsigned j = 0; j < num; ++j) {
                expr* arg = args[j];
                if (m_util.is_mkbv(arg)) {
                    app* a = to_app(arg);
                    unsigned sz = a->get_num_args();
                    for (unsigned i = 0; i < sz; ++i) {
                        m_args.push_back(a->get_arg(i));
                        m_g_vars.push_back(m.mk_var(idx++,m.mk_bool_sort()));
                    }
                    m_f_vars.push_back(m_util.mk_bv(sz, m_g_vars.c_ptr()+m_g_vars.size()-sz));
                }
                else {
                    m_args.push_back(arg);
                    m_f_vars.push_back(m.mk_var(idx++, m.get_sort(arg)));
                    m_g_vars.push_back(m_f_vars.back());
                }
            }
            func_decl* g = 0;
            
            if (!m_pred2blast.find(f, g)) {
                
                ptr_vector<sort> domain;
                for (unsigned i = 0; i < m_args.size(); ++i) {
                    domain.push_back(m.get_sort(m_args[i].get()));
                }
                g = m_context.mk_fresh_head_predicate(f->get_name(), symbol("bv"), m_args.size(), domain.c_ptr(), f);
                m_old_funcs.push_back(f);
                m_new_funcs.push_back(g);
                m_pred2blast.insert(f, g);

                m_dst->inherit_predicate(*m_src, f, g);
            }
            result = m.mk_app(g, m_args.size(), m_args.c_ptr());
            result_pr = 0;
            return BR_DONE;
        }
    };

    struct expand_mkbv : public rewriter_tpl<expand_mkbv_cfg> {
        expand_mkbv_cfg m_cfg;
        expand_mkbv(ast_manager& m, context& ctx):
            rewriter_tpl<expand_mkbv_cfg>(m, m.proofs_enabled(), m_cfg),
            m_cfg(ctx) {
        }
    };


    class mk_bit_blast::impl {

        context &         m_context;
        ast_manager &        m;
        params_ref           m_params;
        mk_interp_tail_simplifier m_simplifier;
        bit_blaster_rewriter m_blaster;
        expand_mkbv          m_rewriter;

        bool blast(rule *r, expr_ref& fml) {
            proof_ref pr(m);
            expr_ref fml1(m), fml2(m), fml3(m);
            rule_ref r2(m_context.get_rule_manager());
            // We need to simplify rule before bit-blasting.
            if (!m_simplifier.transform_rule(r, r2)) {
                r2 = r;
            }
            m_context.get_rule_manager().to_formula(*r2.get(), fml1);
            m_blaster(fml1, fml2, pr);
            m_rewriter(fml2, fml3);
            TRACE("dl", tout << mk_pp(fml, m) << " -> " << mk_pp(fml2, m) << " -> " << mk_pp(fml3, m) << "\n";);
            if (fml3 != fml) {
                fml = fml3;
                return true;
            }
            else {
                return false;
            }
        }

    public:
        impl(context& ctx):
            m_context(ctx),
            m(ctx.get_manager()),
            m_params(ctx.get_params().p),
            m_simplifier(ctx),
            m_blaster(ctx.get_manager(), m_params),
            m_rewriter(ctx.get_manager(), ctx) {
            m_params.set_bool("blast_full", true);
            m_params.set_bool("blast_quant", true);
            m_blaster.updt_params(m_params);
        }
        
        rule_set * operator()(rule_set const & source) {
            // TODO pc
            if (!m_context.xform_bit_blast()) {
                return 0;
            }
            rule_manager& rm = m_context.get_rule_manager();
            unsigned sz = source.get_num_rules();
            expr_ref fml(m);            
            rule_set * result = alloc(rule_set, m_context);   
            m_rewriter.m_cfg.set_src(&source);
            m_rewriter.m_cfg.set_dst(result);
            for (unsigned i = 0; !m_context.canceled() && i < sz; ++i) {
                rule * r = source.get_rule(i);
                rm.to_formula(*r, fml);
                if (blast(r, fml)) {
                    proof_ref pr(m);
                    if (r->get_proof()) {
                        scoped_proof _sc(m);
                        pr = m.mk_asserted(fml); // loses original proof of r.
                    }
                    // TODO add logic for pc:
                    // 1. replace fresh predicates by non-bit-blasted predicates
                    // 2. replace pr by the proof of r.
                    rm.mk_rule(fml, pr, *result, r->name());
                }
                else {
                    result->add_rule(r);
                }
            }

            // copy output predicates without any rule (bit-blasting not really needed)
            const func_decl_set& decls = source.get_output_predicates();
            for (func_decl_set::iterator I = decls.begin(), E = decls.end(); I != E; ++I) {
                if (!source.contains(*I))
                    result->set_output_predicate(*I);
            }
            
            if (m_context.get_model_converter()) {               
                filter_model_converter* fmc = alloc(filter_model_converter, m);
                bit_blast_model_converter* bvmc = alloc(bit_blast_model_converter, m);
                func_decl_ref_vector const& old_funcs = m_rewriter.m_cfg.old_funcs();
                func_decl_ref_vector const& new_funcs = m_rewriter.m_cfg.new_funcs();
                for (unsigned i = 0; i < old_funcs.size(); ++i) {
                    fmc->insert(new_funcs[i]);
                    bvmc->insert(old_funcs[i], new_funcs[i]);
                }
                m_context.add_model_converter(concat(bvmc, fmc));
            }
            
            return result;
        }
    };

    mk_bit_blast::mk_bit_blast(context & ctx, unsigned priority) : plugin(priority) {
        m_impl = alloc(impl, ctx);
    }

    mk_bit_blast::~mk_bit_blast() {
        dealloc(m_impl);
    }

    rule_set * mk_bit_blast::operator()(rule_set const & source) {
        return (*m_impl)(source);
    }        

};
