/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    lia2pb_tactic.cpp

Abstract:

    Reduce bounded LIA benchmark into 0-1 LIA benchmark.

Author:

    Leonardo de Moura (leonardo) 2012-02-07.

Revision History:

--*/
#include"tactical.h"
#include"bound_manager.h"
#include"th_rewriter.h"
#include"for_each_expr.h"
#include"extension_model_converter.h"
#include"filter_model_converter.h"
#include"arith_decl_plugin.h"
#include"expr_substitution.h"
#include"ast_smt2_pp.h"

class lia2pb_tactic : public tactic {
    struct imp {
        ast_manager &              m;
        bound_manager              m_bm;
        arith_util                 m_util;
        expr_dependency_ref_vector m_new_deps;
        th_rewriter                m_rw;
        bool                       m_produce_models;
        bool                       m_produce_unsat_cores;
        bool                       m_partial_lia2pb;
        unsigned                   m_max_bits;
        unsigned                   m_total_bits;
        
       
        imp(ast_manager & _m, params_ref const & p):
            m(_m),
            m_bm(m),
            m_util(m),
            m_new_deps(m),
            m_rw(m, p) {
            updt_params(p);
        }
    
        void updt_params_core(params_ref const & p) {
            m_partial_lia2pb = p.get_bool("lia2pb_partial", false);
            m_max_bits       = p.get_uint("lia2pb_max_bits", 32);
            m_total_bits     = p.get_uint("lia2pb_total_bits", 2048);
        }

        void updt_params(params_ref const & p) {
            m_rw.updt_params(p);
            updt_params_core(p);
        }
        
        
        bool is_target_core(expr * n, rational & u) {
            if (!is_uninterp_const(n))
                return false;
            rational l; bool s;
            if (m_bm.has_lower(n, l, s) &&
                m_bm.has_upper(n, u, s) &&  
                l.is_zero() &&
                !u.is_neg() && 
                u.get_num_bits() <= m_max_bits) {
                
                return true;
            }
            return false;
        }
        
        bool is_bounded(expr * n) {
            rational u;
            return is_target_core(n, u);
        }
        
        bool is_target(expr * n) {
            rational u;
            return is_target_core(n, u) && u > rational(1);
        }
        
        struct failed {};

        struct visitor {
            imp & m_owner;
            
            visitor(imp & o):m_owner(o) {}
            
            void throw_failed(expr * n) {
                TRACE("lia2pb", tout << "Failed at:\n" << mk_ismt2_pp(n, m_owner.m) << "\n";);
                throw failed();
            }
            
            void operator()(var * n) { 
                throw_failed(n);
            }
            
            void operator()(app * n) { 
                family_id fid = n->get_family_id();
                if (fid == m_owner.m.get_basic_family_id()) {
                    // all basic family ops are OK
                }
                else if (fid == m_owner.m_util.get_family_id()) {
                    // check if linear
                    switch (n->get_decl_kind()) {
                    case OP_LE:  case OP_GE: case OP_LT: case OP_GT:
                    case OP_ADD: case OP_NUM:
                        return;
                    case OP_MUL:
                        if (n->get_num_args() != 2)
                            throw_failed(n);
                        if (!m_owner.m_util.is_numeral(n->get_arg(0)))
                            throw_failed(n);
                        return;
                    default:
                        throw_failed(n);
                    }
                }
                else if (is_uninterp_const(n)) {
                    if (m_owner.m_util.is_real(n)) {
                        if (!m_owner.m_partial_lia2pb)
                            throw_failed(n);
                    }
                    else if (m_owner.m_util.is_int(n)) {
                        if (!m_owner.m_partial_lia2pb && !m_owner.is_bounded(n))
                            throw_failed(n);
                    }
                }
                else {
                    sort * s = m_owner.m.get_sort(n);
                    if (s->get_family_id() == m_owner.m_util.get_family_id())
                        throw_failed(n);
                }
            }
            
            void operator()(quantifier * n) { 
                throw_failed(n);
            }
        };


        bool check(goal const & g) {
            try {
                expr_fast_mark1 visited;
                visitor proc(*this);
                unsigned sz = g.size();
                for (unsigned i = 0; i < sz; i++) {
                    expr * f = g.form(i);
                    for_each_expr_core<visitor, expr_fast_mark1, true, true>(proc, visited, f);
                }
                return true;
            }
            catch (failed) {
                return false;
            }
        }
        
        bool has_target() {
            bound_manager::iterator it  = m_bm.begin();
            bound_manager::iterator end = m_bm.end();
            for (; it != end; ++it) {
                if (is_target(*it))
                    return true;
            }
            return false;
        }
        
        bool check_num_bits() {
            unsigned num_bits = 0;
            rational u;
            bound_manager::iterator it  = m_bm.begin();
            bound_manager::iterator end = m_bm.end();
            for (; it != end; ++it) {
                expr * x = *it;
                if (is_target_core(x, u) && u > rational(1)) {
                    num_bits += u.get_num_bits();
                    if (num_bits > m_total_bits)
                        return false;
                }
            }
            return true;
        }

        virtual void operator()(goal_ref const & g, 
                                goal_ref_buffer & result, 
                                model_converter_ref & mc, 
                                proof_converter_ref & pc,
                                expr_dependency_ref & core) {
            SASSERT(g->is_well_sorted());
            fail_if_proof_generation("lia2pb", g);
            m_produce_models      = g->models_enabled();
            m_produce_unsat_cores = g->unsat_core_enabled();
            mc = 0; pc = 0; core = 0; result.reset();
            tactic_report report("lia2pb", *g);
            m_bm.reset(); m_rw.reset(); m_new_deps.reset();

            if (g->inconsistent()) {
                result.push_back(g.get());
                return;
            }

            m_bm(*g);
            
            TRACE("lia2pb", m_bm.display(tout););
            
            // check if there is some variable to be converted
            if (!has_target()) {
                // nothing to be done
                g->inc_depth();
                result.push_back(g.get());
                return;
            }
            
            if (!check(*g))
                throw tactic_exception("goal is in a fragment unsupported by lia2pb");
            
            if (!check_num_bits())
                throw tactic_exception("lia2pb failed, number of necessary bits exceeds specified threshold (use option :lia2pb-total-bits to increase threshold)");
            
            extension_model_converter * mc1 = 0;
            filter_model_converter    * mc2 = 0;
            if (m_produce_models) {
                mc1 = alloc(extension_model_converter, m);
                mc2 = alloc(filter_model_converter, m);
                mc  = concat(mc2, mc1);
            }
            
            expr_ref zero(m);
            expr_ref one(m);
            zero = m_util.mk_numeral(rational(0), true);
            one  = m_util.mk_numeral(rational(1), true);
            
            unsigned num_converted = 0;
            expr_substitution subst(m, m_produce_unsat_cores, false);
            rational u;
            ptr_buffer<expr> def_args;
            bound_manager::iterator it  = m_bm.begin();
            bound_manager::iterator end = m_bm.end();
            for (; it != end; ++it) {
                expr * x = *it;
                if (is_target_core(x, u) && u > rational(1)) {
                    num_converted++;
                    def_args.reset();
                    rational a(1);
                    unsigned num_bits = u.get_num_bits();
                    for (unsigned i = 0; i < num_bits; i++) {           
                        app * x_prime = m.mk_fresh_const(0, m_util.mk_int());
                        g->assert_expr(m_util.mk_le(zero, x_prime));
                        g->assert_expr(m_util.mk_le(x_prime, one));
                        if (a.is_one())
                            def_args.push_back(x_prime);
                        else
                            def_args.push_back(m_util.mk_mul(m_util.mk_numeral(a, true), x_prime));
                        if (m_produce_models)
                            mc2->insert(x_prime->get_decl());
                        a *= rational(2);
                    }
                    SASSERT(def_args.size() > 1);
                    expr * def = m_util.mk_add(def_args.size(), def_args.c_ptr());
                    expr_dependency * dep = 0;
                    if (m_produce_unsat_cores) {
                        dep = m.mk_join(m_bm.lower_dep(x), m_bm.upper_dep(x));
                        if (dep != 0)
                            m_new_deps.push_back(dep);
                    }
                    TRACE("lia2pb", tout << mk_ismt2_pp(x, m) << " -> " << dep << "\n";);
                    subst.insert(x, def, 0, dep);
                    if (m_produce_models) {
                        mc1->insert(to_app(x)->get_decl(), def);
                    }
                }
            }
            
            report_tactic_progress(":converted-lia2pb", num_converted);
            
            m_rw.set_substitution(&subst);

            expr_ref   new_curr(m);
            proof_ref  new_pr(m);
            unsigned size = g->size();
            for (unsigned idx = 0; idx < size; idx++) {
                expr * curr = g->form(idx);
                expr_dependency * dep = 0;
                m_rw(curr, new_curr, new_pr);
                if (m_produce_unsat_cores) {
                    dep = m.mk_join(m_rw.get_used_dependencies(), g->dep(idx));
                    m_rw.reset_used_dependencies();                    
                }
                if (m.proofs_enabled()) {
                    new_pr  = m.mk_modus_ponens(g->pr(idx), new_pr);
                }
                g->update(idx, new_curr, new_pr, dep);
            }
            g->inc_depth();
            result.push_back(g.get());
            TRACE("lia2pb", g->display(tout););
            SASSERT(g->is_well_sorted());
        }
    };

    imp *      m_imp;
    params_ref m_params;
public:
    lia2pb_tactic(ast_manager & m, params_ref const & p):
        m_params(p) {
        m_imp = alloc(imp, m, p);
    }

    virtual tactic * translate(ast_manager & m) {
        return alloc(lia2pb_tactic, m, m_params);
    }

    virtual ~lia2pb_tactic() {
        dealloc(m_imp);
    }

    virtual void updt_params(params_ref const & p) {
        m_params = p;
        m_imp->updt_params(p);
    }

    virtual void collect_param_descrs(param_descrs & r) { 
        r.insert("lia2pb_partial", CPK_BOOL, "(default: false) partial lia2pb conversion.");
        r.insert("lia2pb_max_bits", CPK_UINT, "(default: 32) maximum number of bits to be used (per variable) in lia2pb.");
        r.insert("lia2pb_total_bits", CPK_UINT, "(default: 2048) total number of bits to be used (per problem) in lia2pb.");
    }

    virtual void operator()(goal_ref const & in, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc,
                            expr_dependency_ref & core) {
        try {
            (*m_imp)(in, result, mc, pc, core);
        }
        catch (rewriter_exception & ex) {
            throw tactic_exception(ex.msg());
        }
    }
    
    virtual void cleanup() {
        imp * d = alloc(imp, m_imp->m, m_params);
        std::swap(d, m_imp);        
        dealloc(d);
    }

};

tactic * mk_lia2pb_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(lia2pb_tactic, m, p));
}

