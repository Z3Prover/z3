/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    bv1_blaster_tactic.cpp

Abstract:

    Rewriter for "blasting" bit-vectors of size n into bit-vectors of size 1.
    This rewriter only supports concat and extract operators.
    This transformation is useful for handling benchmarks that contain
    many BV equalities. 

    Remark: other operators can be mapped into concat/extract by using
    the simplifiers.

Author:

    Leonardo (leonardo) 2011-10-25

Notes:

--*/
#include"tactical.h"
#include"bit_blaster_model_converter.h"
#include"bv_decl_plugin.h"
#include"rewriter_def.h"
#include"for_each_expr.h"
#include"cooperate.h"
#include"bv_rewriter.h"

class bv1_blaster_tactic : public tactic {

    struct rw_cfg : public default_rewriter_cfg {
        ast_manager &                      m_manager;
        bv_util                            m_util;
        obj_map<func_decl, expr*>          m_const2bits;
        expr_ref_vector                    m_saved;
        expr_ref                           m_bit1;
        expr_ref                           m_bit0;

        unsigned long long                 m_max_memory; // in bytes
        unsigned                           m_max_steps;
        bool                               m_produce_models;

        ast_manager & m() const { return m_manager; }
        bv_util & butil() { return m_util; }
        bv_util const & butil() const { return m_util; }
        
        void cleanup_buffers() {
            m_saved.finalize();
        }
        
        rw_cfg(ast_manager & m, params_ref const & p):
            m_manager(m),
            m_util(m),
            m_saved(m),
            m_bit1(m),
            m_bit0(m) {
            m_bit1 = butil().mk_numeral(rational(1), 1);
            m_bit0 = butil().mk_numeral(rational(0), 1);
            updt_params(p);
        }

        void updt_params(params_ref const & p) {
            m_max_memory     = megabytes_to_bytes(p.get_uint("max_memory", UINT_MAX));
            m_max_steps      = p.get_uint("max_steps", UINT_MAX);
            m_produce_models = p.get_bool("produce_models", false);
        }
        
        bool rewrite_patterns() const { UNREACHABLE(); return false; }
        
        bool max_steps_exceeded(unsigned num_steps) const { 
            cooperate("bv1 blaster");
            if (memory::get_allocation_size() > m_max_memory)
                throw tactic_exception(TACTIC_MAX_MEMORY_MSG);
            return num_steps > m_max_steps;
        }
        
        typedef ptr_buffer<expr, 128> bit_buffer;

        void get_bits(expr * arg, bit_buffer & bits) {
            SASSERT(butil().is_concat(arg) || butil().get_bv_size(arg) == 1);
            if (butil().is_concat(arg))
                bits.append(to_app(arg)->get_num_args(), to_app(arg)->get_args());
            else
                bits.push_back(arg);
        }
        
        void mk_const(func_decl * f, expr_ref & result) {
            SASSERT(f->get_family_id() == null_family_id);
            SASSERT(f->get_arity() == 0);
            expr * r;
            if (m_const2bits.find(f, r)) {
                result = r;
                return;
            }
            sort * s = f->get_range();
            SASSERT(butil().is_bv_sort(s));
            unsigned bv_size = butil().get_bv_size(s);
            if (bv_size == 1) {
                result = m().mk_const(f);
                return;
            }
            sort * b = butil().mk_sort(1);
            ptr_buffer<expr> bits;
            for (unsigned i = 0; i < bv_size; i++) {
                bits.push_back(m().mk_fresh_const(0, b));
            }
            r = butil().mk_concat(bits.size(), bits.c_ptr());
            m_saved.push_back(r);
            m_const2bits.insert(f, r);
            result = r;
        }
        
        void blast_bv_term(expr * t, expr_ref & result) {
            bit_buffer bits;
            unsigned bv_size = butil().get_bv_size(t);
            if (bv_size == 1) {
                result = t;
                return;
            } 
            unsigned i = bv_size;
            while (i > 0) {
                --i;
                bits.push_back(butil().mk_extract(i, i, t));
            }
            result = butil().mk_concat(bits.size(), bits.c_ptr());
        }
        
        void reduce_eq(expr * arg1, expr * arg2, expr_ref & result) {
            bit_buffer bits1;
            bit_buffer bits2;
            get_bits(arg1, bits1);
            get_bits(arg2, bits2);
            SASSERT(bits1.size() == bits2.size());
            bit_buffer new_eqs;
            unsigned i = bits1.size();
            while (i > 0) {
                --i;
                new_eqs.push_back(m().mk_eq(bits1[i], bits2[i]));
            }
            result = m().mk_and(new_eqs.size(), new_eqs.c_ptr());
        }
        
        void reduce_ite(expr * c, expr * t, expr * e, expr_ref & result) {
            bit_buffer t_bits;
            bit_buffer e_bits;
            get_bits(t, t_bits);
            get_bits(e, e_bits);
            SASSERT(t_bits.size() == e_bits.size());
            bit_buffer new_ites;
            unsigned num = t_bits.size();
            for (unsigned i = 0; i < num; i++)
                new_ites.push_back(m().mk_ite(c, t_bits[i], e_bits[i]));
            result = butil().mk_concat(new_ites.size(), new_ites.c_ptr());
        }
        
        void reduce_num(func_decl * f, expr_ref & result) {
            SASSERT(f->get_num_parameters() == 2);
            SASSERT(f->get_parameter(0).is_rational());
            SASSERT(f->get_parameter(1).is_int());
            bit_buffer bits;
            rational v  = f->get_parameter(0).get_rational();
            rational two(2);
            unsigned sz = f->get_parameter(1).get_int();
            for (unsigned i = 0; i < sz; i++) {
                if ((v % two).is_zero())
                    bits.push_back(m_bit0);
                else
                    bits.push_back(m_bit1);
                v = div(v, two);
            }
            std::reverse(bits.begin(), bits.end());
            result = butil().mk_concat(bits.size(), bits.c_ptr());
        }
        
        void reduce_extract(func_decl * f, expr * arg, expr_ref & result) {
            bit_buffer arg_bits;
            get_bits(arg, arg_bits);
            SASSERT(arg_bits.size() == butil().get_bv_size(arg));
            unsigned high  = butil().get_extract_high(f);
            unsigned low   = butil().get_extract_low(f);
            unsigned sz    = arg_bits.size();
            unsigned start = sz - 1 - high;
            unsigned end   = sz - 1 - low;
            bit_buffer bits;
            for (unsigned i = start; i <= end; i++) {
                bits.push_back(arg_bits[i]);
            }
            result = butil().mk_concat(bits.size(), bits.c_ptr());
        }
        
        void reduce_concat(unsigned num, expr * const * args, expr_ref & result) {
            bit_buffer bits;
            bit_buffer arg_bits;
            for (unsigned i = 0; i < num; i++) {
                expr * arg = args[i];
                arg_bits.reset();
                get_bits(arg, arg_bits);
                bits.append(arg_bits.size(), arg_bits.c_ptr());
            }
            result = butil().mk_concat(bits.size(), bits.c_ptr());
        }

        void reduce_bin_xor(expr * arg1, expr * arg2, expr_ref & result) {
            bit_buffer bits1;
            bit_buffer bits2;
            get_bits(arg1, bits1);
            get_bits(arg2, bits2);
            SASSERT(bits1.size() == bits2.size());
            bit_buffer new_bits;
            unsigned num = bits1.size();
            for (unsigned i = 0; i < num; i++) {
                new_bits.push_back(m().mk_ite(m().mk_eq(bits1[i], bits2[i]), m_bit0, m_bit1));
            }
            result = butil().mk_concat(new_bits.size(), new_bits.c_ptr());
        }

        void reduce_xor(unsigned num_args, expr * const * args, expr_ref & result) {
            SASSERT(num_args > 0);
#if 1
            if (num_args == 1) {
                result = args[0];
                return;
            }
            reduce_bin_xor(args[0], args[1], result);
            for (unsigned i = 2; i < num_args; i++) {
                reduce_bin_xor(result, args[i], result);
            }
#else
            ptr_buffer<bit_buffer> args_bits;
            for (unsigned i = 0; i < num_args; i++) {
                bit_buffer * buff_i = alloc(bit_buffer);
                get_bits(args[i], *buff_i);
                args_bits.push_back(buff_i);
            }
            bit_buffer new_bits;
            unsigned sz = butil().get_bv_size(args[0]);
            for (unsigned i = 0; i < sz; i++) {
                ptr_buffer<expr> eqs;
                for (unsigned j = 0; j < num_args; j++) {
                    bit_buffer * buff_j = args_bits[j];
                    eqs.push_back(m().mk_eq(buff_j->get(i), m_bit1));
                }
                expr * cond = m().mk_xor(eqs.size(), eqs.c_ptr());
                new_bits.push_back(m().mk_ite(cond, m_bit1, m_bit0));
            }
            result = butil().mk_concat(new_bits.size(), new_bits.c_ptr());
            std::for_each(args_bits.begin(), args_bits.end(), delete_proc<bit_buffer>());
#endif
        }
        
        br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
            result_pr = 0;
            if (num == 0 && f->get_family_id() == null_family_id && butil().is_bv_sort(f->get_range())) {
                mk_const(f, result);
                return BR_DONE;
            }
            
            if (m().is_eq(f)) {
                SASSERT(num == 2);
                if (butil().is_bv(args[0])) {
                    reduce_eq(args[0], args[1], result);
                    return BR_DONE;
                }
                return BR_FAILED;
            }
            
            if (m().is_ite(f)) {
                SASSERT(num == 3);
                if (butil().is_bv(args[1])) {
                    reduce_ite(args[0], args[1], args[2], result);
                    return BR_DONE;
                }
                return BR_FAILED;
            }
            
            if (f->get_family_id() == butil().get_family_id()) {
                switch (f->get_decl_kind()) {
                case OP_BV_NUM:
                    reduce_num(f, result);
                    return BR_DONE;
                case OP_EXTRACT:
                    SASSERT(num == 1);
                    reduce_extract(f, args[0], result);
                    return BR_DONE;
                case OP_CONCAT:
                    reduce_concat(num, args, result);
                    return BR_DONE;
                case OP_BXOR:
                    reduce_xor(num, args, result);
                    return BR_DONE;
                default:
                    UNREACHABLE();
                    return BR_FAILED;
                }
            }
            
            if (butil().is_bv_sort(f->get_range())) {
                blast_bv_term(m().mk_app(f, num, args), result);
                return BR_DONE;
            }
            
            return BR_FAILED;
        }
        
        bool reduce_quantifier(quantifier * old_q, 
                               expr * new_body, 
                               expr * const * new_patterns, 
                               expr * const * new_no_patterns,
                               expr_ref & result,
                               proof_ref & result_pr) {
            UNREACHABLE();
            return false;
        }
    };

    struct rw : public rewriter_tpl<rw_cfg> {
        rw_cfg m_cfg;

        rw(ast_manager & m, params_ref const & p):
            rewriter_tpl<rw_cfg>(m, m.proofs_enabled(), m_cfg),
            m_cfg(m, p) {
        }
    };


    struct imp {
        rw                m_rw;
        unsigned          m_num_steps;
        
        imp(ast_manager & m, params_ref const & p):
            m_rw(m, p) {
        }

        struct not_target {};
        
        struct visitor {
            family_id m_bv_fid;
            visitor(family_id bv_fid):m_bv_fid(bv_fid) {}
            void operator()(var const * n) { throw not_target(); }
            void operator()(app const * n) { 
                if (n->get_family_id() == m_bv_fid) {
                    switch (n->get_decl_kind()) {
                    case OP_BV_NUM:
                    case OP_EXTRACT:
                    case OP_CONCAT:
                        return;
                    case OP_BXOR:
                        // it doesn't payoff to do the reduction in this case.
                        throw not_target();
                    default:
                        throw not_target();
                    }
                }
            }
            void operator()(quantifier const * n) { throw not_target(); }
        };
        
        bool is_target(goal const & g) const {
            expr_fast_mark1 visited;
            unsigned sz = g.size();
            visitor proc(m_rw.cfg().butil().get_family_id());
            try {
                for (unsigned i = 0; i < sz; i++) {
                    expr * f = g.form(i);
                    for_each_expr_core<visitor, expr_fast_mark1, false, true>(proc, visited, f);
                }
            }
            catch (not_target) {
                return false;
            }
            return true;
        }
        
        ast_manager & m() const { return m_rw.m(); }
        
        
        void operator()(goal_ref const & g, 
                        goal_ref_buffer & result, 
                        model_converter_ref & mc, 
                        proof_converter_ref & pc,
                        expr_dependency_ref & core) {
            mc = 0; pc = 0; core = 0;
            
            if (!is_target(*g))
                throw tactic_exception("bv1 blaster cannot be applied to goal");
            
            tactic_report report("bv1-blaster", *g);
            m_num_steps = 0;
            
            bool proofs_enabled = g->proofs_enabled();
            expr_ref   new_curr(m());
            proof_ref  new_pr(m());
            unsigned   size = g->size();
            for (unsigned idx = 0; idx < size; idx++) {
                if (g->inconsistent())
                    break;
                expr * curr = g->form(idx);
                m_rw(curr, new_curr, new_pr);
                m_num_steps += m_rw.get_num_steps();
                if (proofs_enabled) {
                    proof * pr = g->pr(idx);
                    new_pr     = m().mk_modus_ponens(pr, new_pr);
                }
                g->update(idx, new_curr, new_pr, g->dep(idx));
            }
            
            if (g->models_enabled())
                mc = mk_bv1_blaster_model_converter(m(), m_rw.cfg().m_const2bits);
            g->inc_depth();
            result.push_back(g.get());
            m_rw.cfg().cleanup();
        }
        
        unsigned get_num_steps() const { return m_num_steps; }
    };

    imp *      m_imp;
    params_ref m_params;
public:
    bv1_blaster_tactic(ast_manager & m, params_ref const & p = params_ref()):
        m_params(p) {
        m_imp = alloc(imp, m, p);
    }

    virtual tactic * translate(ast_manager & m) {
        return alloc(bv1_blaster_tactic, m, m_params);
    }

    virtual ~bv1_blaster_tactic() {
        dealloc(m_imp);
    }

    virtual void updt_params(params_ref const & p) {
        m_params = p;
        m_imp->m_rw.cfg().updt_params(p);
    }

    virtual void collect_param_descrs(param_descrs & r) { 
        insert_max_memory(r);
        insert_max_steps(r);
    }

    bool is_target(goal const & g) const {
        return m_imp->is_target(g);
    }
    
    /**
       \brief "Blast" bit-vectors of size n in s into bit-vectors of size 1.
       If s contains other bit-vectors operators different from concat/extract, then this is method is a NO-OP.
       It also does not support quantifiers.
       Return a model_converter that converts any model for the updated set into a model for the old set.
    */
    virtual void operator()(goal_ref const & g, 
                            goal_ref_buffer & result, 
                            model_converter_ref & mc, 
                            proof_converter_ref & pc,
                            expr_dependency_ref & core) {
        (*m_imp)(g, result, mc, pc, core);
    }
    
    virtual void cleanup() {
        imp * d = alloc(imp, m_imp->m(), m_params);
        std::swap(d, m_imp);        
        dealloc(d);
    }
    
    unsigned get_num_steps() const {
        return m_imp->get_num_steps();
    }
    
};

tactic * mk_bv1_blaster_tactic(ast_manager & m, params_ref const & p) {
    return clean(alloc(bv1_blaster_tactic, m, p));
}

class is_qfbv_eq_probe : public probe {
public:
    virtual result operator()(goal const & g) {
        bv1_blaster_tactic t(g.m());
        return t.is_target(g);

    }
};

probe * mk_is_qfbv_eq_probe() {
    return alloc(is_qfbv_eq_probe);
}
