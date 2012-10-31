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


    class expand_mkbv_cfg : public default_rewriter_cfg {

        context&             m_context;
        rule_ref_vector&     m_rules;
        ast_manager&         m;
        bv_util              m_util;
        expr_ref_vector      m_args, m_f_vars, m_g_vars;
        func_decl_ref_vector m_pinned;
        obj_map<func_decl,func_decl*> m_pred2blast;


    public:

        expand_mkbv_cfg(context& ctx, rule_ref_vector& rules): 
            m_context(ctx), 
            m_rules(rules),
            m(ctx.get_manager()),
            m_util(m),
            m_args(m), 
            m_f_vars(m),
            m_g_vars(m),
            m_pinned(m) 
        {}

        ~expand_mkbv_cfg() {}
        
        br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) { 
            rule_manager& rm = m_context.get_rule_manager();
            bool found = false;
            for (unsigned j = 0; !found && j < num; ++j) {
                found = m_util.is_mkbv(args[j]);                
            }
            if (!found) {
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
                m_pinned.push_back(g);
                m_pred2blast.insert(f, g);

                // Create rule f(mk_mkbv(args)) :- g(args)

                fml = m.mk_implies(m.mk_app(g, m_g_vars.size(), m_g_vars.c_ptr()), m.mk_app(f, m_f_vars.size(), m_f_vars.c_ptr()));
                rm.mk_rule(fml, m_rules, g->get_name());
            }
            result = m.mk_app(g, m_args.size(), m_args.c_ptr());
            result_pr = 0;
            return BR_DONE;
        }
    };

    struct expand_mkbv : public rewriter_tpl<expand_mkbv_cfg> {
        expand_mkbv_cfg m_cfg;
        expand_mkbv(ast_manager& m, context& ctx, rule_ref_vector& rules):
            rewriter_tpl<expand_mkbv_cfg>(m, m.proofs_enabled(), m_cfg),
            m_cfg(ctx, rules) {
        }
    };


    class mk_bit_blast::impl {

        context &	     m_context;
        ast_manager &        m;
        params_ref           m_params;
        rule_ref_vector      m_rules;
        bit_blaster_rewriter m_blaster;
        expand_mkbv          m_rewriter;
        

        bool blast(expr_ref& fml) {
            proof_ref pr(m);
            expr_ref fml1(m), fml2(m);
            m_blaster(fml, fml1, pr);
            m_rewriter(fml1, fml2);
            TRACE("dl", tout << mk_pp(fml, m) << " -> " << mk_pp(fml1, m) << " -> " << mk_pp(fml2, m) << "\n";);
            if (fml2 != fml) {
                fml = fml2;
                return true;
            }
            else {
                return false;
            }
        }

        void reset() {
            m_rules.reset();
        }

    public:
        impl(context& ctx):
            m_context(ctx),
            m(ctx.get_manager()),
            m_params(ctx.get_params()),
            m_rules(ctx.get_rule_manager()),
            m_blaster(ctx.get_manager(), m_params),
            m_rewriter(ctx.get_manager(), ctx, m_rules) {
            m_params.set_bool(":blast-full", true);
            m_params.set_bool(":blast-quant", true);
            m_blaster.updt_params(m_params);
        }
        
        rule_set * operator()(rule_set const & source, model_converter_ref& mc, proof_converter_ref& pc) {
            // TODO mc, pc
            if (!m_context.get_params().get_bool(":bit-blast", false)) {
                return 0;
            }
            if (m_context.get_engine() != PDR_ENGINE) {
                return 0;
            }
            rule_manager& rm = m_context.get_rule_manager();
            unsigned sz = source.get_num_rules();
            expr_ref fml(m);            
            reset();
            rule_set * result = alloc(rule_set, m_context);        
            for (unsigned i = 0; i < sz; ++i) {
                rule * r = source.get_rule(i);
                r->to_formula(fml);
                if (blast(fml)) {
                    rm.mk_rule(fml, m_rules, r->name()); 
                }
                else {
                    m_rules.push_back(r);
                }
            }
            
            for (unsigned i = 0; i < m_rules.size(); ++i) {
                result->add_rule(m_rules.get(i));
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

    rule_set * mk_bit_blast::operator()(rule_set const & source, model_converter_ref& mc, proof_converter_ref& pc) {
        return (*m_impl)(source, mc, pc);
    }        

};
