/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    card2bv_tactic.cpp

Abstract:

    Tactic for converting Pseudo-Boolean constraints to BV

Author:

    Nikolaj Bjorner (nbjorner) 2014-03-20

Notes:

--*/
#include"tactical.h"
#include"cooperate.h"
#include"rewriter_def.h"
#include"th_rewriter.h"
#include"ast_smt2_pp.h"
#include"expr_substitution.h"
#include"card2bv_tactic.h"
#include"pb_decl_plugin.h"

class card2bv_rewriter {
    ast_manager& m;
    pb_util      pb;
    bv_util      bv;

    unsigned get_num_bits(func_decl* f) {
        rational r(0);
        unsigned sz = f->get_arity();
        for (unsigned i = 0; i < sz; ++i) {
            r += pb.get_coeff(f, i);
        }
        r = r > pb.get_k(f)? r : pb.get_k(f);
        return r.get_num_bits();
    }

public:
    card2bv_rewriter(ast_manager& m):
        m(m),
        pb(m),
        bv(m)
    {}

    br_status mk_app_core(func_decl * f, unsigned sz, expr * const* args, expr_ref & result) {
        if (f->get_family_id() != pb.get_family_id()) {
            return BR_FAILED;
        }
        expr_ref zero(m), a(m), b(m);
        expr_ref_vector es(m);
        unsigned bw = get_num_bits(f);
        zero = bv.mk_numeral(rational(0), bw);
        for (unsigned i = 0; i < sz; ++i) {
            es.push_back(m.mk_ite(args[i], bv.mk_numeral(pb.get_coeff(f, i), bw), zero));
        }
        switch (es.size()) {
        case 0:  a = zero; break;
        case 1:  a = es[0].get(); break;
        default: 
            a = es[0].get();
            for (unsigned i = 1; i < es.size(); ++i) {
                a = bv.mk_bv_add(a, es[i].get());
            }
            break;
        }
        b = bv.mk_numeral(pb.get_k(f), bw);

        switch(f->get_decl_kind()) {
        case OP_AT_MOST_K: 
        case OP_PB_LE: 
            UNREACHABLE();
            result = bv.mk_ule(a, b);
            return BR_DONE; 
        case OP_AT_LEAST_K: 
            UNREACHABLE();
        case OP_PB_GE:
            result = bv.mk_ule(b, a);
            return BR_DONE;
        case OP_PB_EQ: 
            result = m.mk_eq(a, b);
            return BR_DONE;
        default:
            UNREACHABLE();
        }
        return BR_FAILED;
    }
};

struct card2bv_rewriter_cfg : public default_rewriter_cfg {
    card2bv_rewriter m_r;
    bool rewrite_patterns() const { return false; }
    bool flat_assoc(func_decl * f) const { return false; }
    br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
        result_pr = 0;
        return m_r.mk_app_core(f, num, args, result);
    }
    card2bv_rewriter_cfg(ast_manager & m):m_r(m) {}
};

template class rewriter_tpl<card2bv_rewriter_cfg>;

class pb_rewriter : public rewriter_tpl<card2bv_rewriter_cfg> {
    card2bv_rewriter_cfg m_cfg;
public:
    pb_rewriter(ast_manager & m):
        rewriter_tpl<card2bv_rewriter_cfg>(m, false, m_cfg),
        m_cfg(m) {}
};

class card2bv_tactic : public tactic {
    ast_manager &              m;
    params_ref                 m_params;
    th_rewriter                m_rw1;
    pb_rewriter                m_rw2;
    
public:

    card2bv_tactic(ast_manager & m, params_ref const & p):
        m(m),
        m_params(p),
        m_rw1(m),
        m_rw2(m) {
    }

    virtual tactic * translate(ast_manager & m) {
        return alloc(card2bv_tactic, m, m_params);
    }

    virtual ~card2bv_tactic() {
    }

    virtual void updt_params(params_ref const & p) {
        m_params = p;
    }

    virtual void collect_param_descrs(param_descrs & r) {  
    }

    void set_cancel(bool f) {
        m_rw1.set_cancel(f);
        m_rw2.set_cancel(f);
    }
    
    virtual void operator()(goal_ref const & g, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc,
                            expr_dependency_ref & core) {
        TRACE("pb2bv", g->display(tout););
        SASSERT(g->is_well_sorted());
        fail_if_proof_generation("card2bv", g);
        mc = 0; pc = 0; core = 0; result.reset();
        tactic_report report("card2bv", *g);
        m_rw1.reset(); 
        m_rw2.reset(); 
        
        if (g->inconsistent()) {
            result.push_back(g.get());
            return;
        }
                
        unsigned size = g->size();
        expr_ref new_f1(m), new_f2(m);
        for (unsigned idx = 0; idx < size; idx++) {
            m_rw1(g->form(idx), new_f1);
            m_rw2(new_f1, new_f2);
            g->update(idx, new_f2);
        }

        g->inc_depth();
        result.push_back(g.get());
        TRACE("card2bv", g->display(tout););
        SASSERT(g->is_well_sorted());
    }
    
    virtual void cleanup() {
    }
};

tactic * mk_card2bv_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(card2bv_tactic, m, p));
}

