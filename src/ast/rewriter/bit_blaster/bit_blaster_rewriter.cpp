/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    bit_blaster_rewriter.cpp

Abstract:

    Bit-blasting rewriter

Author:

    Leonardo (leonardo) 2012-10-04

Notes:

--*/
#include"bit_blaster_rewriter.h"
#include"bv_decl_plugin.h"
#include"bit_blaster_tpl_def.h"
#include"rewriter_def.h"
#include"bool_rewriter.h"
#include"ref_util.h"
#include"ast_smt2_pp.h"

struct blaster_cfg {
    typedef rational numeral;

    bool_rewriter & m_rewriter;
    bv_util &       m_util;
    blaster_cfg(bool_rewriter & r, bv_util & u):m_rewriter(r), m_util(u) {}
    
    ast_manager & m() const { return m_util.get_manager(); }
    numeral power(unsigned n) const { return rational::power_of_two(n); }
    void mk_xor(expr * a, expr * b, expr_ref & r) { m_rewriter.mk_xor(a, b, r); }
    void mk_xor3(expr * a, expr * b, expr * c, expr_ref & r) {
        expr_ref tmp(m());
        mk_xor(b, c, tmp);
        mk_xor(a, tmp, r);
    }
    void mk_iff(expr * a, expr * b, expr_ref & r) { m_rewriter.mk_iff(a, b, r); }
    void mk_and(expr * a, expr * b, expr_ref & r) { m_rewriter.mk_and(a, b, r); }
    void mk_and(expr * a, expr * b, expr * c, expr_ref & r) { m_rewriter.mk_and(a, b, c, r); }
    void mk_and(unsigned sz, expr * const * args, expr_ref & r) { m_rewriter.mk_and(sz, args, r); }
    void mk_or(expr * a, expr * b, expr_ref & r) { m_rewriter.mk_or(a, b, r); }
    void mk_or(expr * a, expr * b, expr * c, expr_ref & r) { m_rewriter.mk_or(a, b, c, r); }
    void mk_or(unsigned sz, expr * const * args, expr_ref & r) { m_rewriter.mk_or(sz, args, r); }
    void mk_not(expr * a, expr_ref & r) { m_rewriter.mk_not(a, r); }
    void mk_carry(expr * a, expr * b, expr * c, expr_ref & r) {
        expr_ref t1(m()), t2(m()), t3(m());
#if 1
        mk_and(a, b, t1);
        mk_and(a, c, t2);
        mk_and(b, c, t3);
        mk_or(t1, t2, t3, r);
#else
        mk_or(a, b, t1);
        mk_or(a, c, t2);
        mk_or(b, c, t3);
        mk_and(t1, t2, t3, r);
#endif 
    }
    void mk_ite(expr * c, expr * t, expr * e, expr_ref & r) { m_rewriter.mk_ite(c, t, e, r); }
    void mk_nand(expr * a, expr * b, expr_ref & r) { m_rewriter.mk_nand(a, b, r); }
    void mk_nor(expr * a, expr * b, expr_ref & r) { m_rewriter.mk_nor(a, b, r); }
};

// CMW: GCC/LLVM do not like this definition because a symbol of the same name exists in assert_set_bit_blaster.o
// template class bit_blaster_tpl<blaster_cfg>;

class blaster : public bit_blaster_tpl<blaster_cfg> {
    bool_rewriter           m_rewriter;
    bv_util                 m_util;
public:
    blaster(ast_manager & m):
        bit_blaster_tpl<blaster_cfg>(blaster_cfg(m_rewriter, m_util)),
        m_rewriter(m),
        m_util(m) {
        m_rewriter.set_flat(false);
        m_rewriter.set_elim_and(true);
    }

    bv_util & butil() { return m_util; }
};

struct blaster_rewriter_cfg : public default_rewriter_cfg {
    ast_manager &                            m_manager;
    blaster &                                m_blaster;
    expr_ref_vector                          m_in1;
    expr_ref_vector                          m_in2;
    expr_ref_vector                          m_out;
    obj_map<func_decl, expr*>                m_const2bits;
    expr_ref_vector                          m_bindings;
    func_decl_ref_vector                     m_keys;
    expr_ref_vector                          m_values;
    unsigned_vector                          m_keyval_lim;

    bool                                     m_blast_mul;
    bool                                     m_blast_add;
    bool                                     m_blast_quant;
    bool                                     m_blast_full;
    unsigned long long                       m_max_memory;
    unsigned                                 m_max_steps;

    ast_manager & m() const { return m_manager; }
    bv_util & butil() { return m_blaster.butil(); }

    void cleanup_buffers() {
        m_in1.finalize();
        m_in2.finalize();
        m_out.finalize();
        m_bindings.finalize();
    }
    
    blaster_rewriter_cfg(ast_manager & m, blaster & b, params_ref const & p):
        m_manager(m),
        m_blaster(b),
        m_in1(m),
        m_in2(m),
        m_out(m),
        m_bindings(m),
        m_keys(m), 
        m_values(m) {
        updt_params(p);
    }

    ~blaster_rewriter_cfg() {
    }

    void updt_params(params_ref const & p) {
        m_max_memory     = megabytes_to_bytes(p.get_uint("max_memory", UINT_MAX));
        m_max_steps      = p.get_uint("max_steps", UINT_MAX);
        m_blast_add      = p.get_bool("blast_add", true);
        m_blast_mul      = p.get_bool("blast_mul", true);
        m_blast_full     = p.get_bool("blast_full", false);
        m_blast_quant    = p.get_bool("blast_quant", false);
        m_blaster.set_max_memory(m_max_memory);
    }

    bool rewrite_patterns() const { return true; }

    bool max_steps_exceeded(unsigned num_steps) const { 
        cooperate("bit blaster");
        if (memory::get_allocation_size() > m_max_memory)
            throw rewriter_exception(Z3_MAX_MEMORY_MSG);
        return num_steps > m_max_steps;
    }

    void get_bits(expr * t, expr_ref_vector & out_bits) {
        if (butil().is_mkbv(t)) {
            out_bits.append(to_app(t)->get_num_args(), to_app(t)->get_args());
        }
        else {
            unsigned bv_size = butil().get_bv_size(t);
            for (unsigned i = 0; i < bv_size; i++) {
                parameter p(i);
                out_bits.push_back(m().mk_app(butil().get_family_id(), OP_BIT2BOOL, 1, &p, 1, &t));
            }
            SASSERT(bv_size == out_bits.size());
        }
    }

    void push() {
        m_keyval_lim.push_back(m_keys.size());
    }

    void pop(unsigned num_scopes) {
        if (num_scopes > 0) {
            unsigned new_sz = m_keyval_lim.size() - num_scopes;
            unsigned lim = m_keyval_lim[new_sz];
            for (unsigned i = m_keys.size(); i > lim; ) {
                --i;
                m_const2bits.remove(m_keys[i].get());
            }
            m_keys.resize(lim);
            m_values.resize(lim);
            m_keyval_lim.resize(new_sz);
        }
    }

    template<typename V>
    app * mk_mkbv(V const & bits) {
        return m().mk_app(butil().get_family_id(), OP_MKBV, bits.size(), bits.c_ptr());
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
        sort * b = m().mk_bool_sort();
        m_out.reset();
        for (unsigned i = 0; i < bv_size; i++) {
            m_out.push_back(m().mk_fresh_const(0, b));
        }
        r = mk_mkbv(m_out);
        m_const2bits.insert(f, r);
        m_keys.push_back(f);
        m_values.push_back(r);
        result = r;
    }

#define MK_UNARY_REDUCE(OP, BB_OP)                              \
void OP(expr * arg, expr_ref & result) {                        \
    m_in1.reset();                                              \
    get_bits(arg, m_in1);                                       \
    m_out.reset();                                              \
    m_blaster.BB_OP(m_in1.size(), m_in1.c_ptr(), m_out);        \
    result = mk_mkbv(m_out);                                    \
}

    MK_UNARY_REDUCE(reduce_not, mk_not);
    MK_UNARY_REDUCE(reduce_redor, mk_redor);
    MK_UNARY_REDUCE(reduce_redand, mk_redand);
    
#define MK_BIN_REDUCE(OP, BB_OP)                                        \
void OP(expr * arg1, expr * arg2, expr_ref & result) {                  \
    m_in1.reset(); m_in2.reset();                                       \
    get_bits(arg1, m_in1);                                              \
    get_bits(arg2, m_in2);                                              \
    m_out.reset();                                                      \
    m_blaster.BB_OP(m_in1.size(), m_in1.c_ptr(), m_in2.c_ptr(), m_out); \
    result = mk_mkbv(m_out);                                            \
}

    MK_BIN_REDUCE(reduce_shl, mk_shl);
    MK_BIN_REDUCE(reduce_ashr, mk_ashr);
    MK_BIN_REDUCE(reduce_lshr, mk_lshr);
    MK_BIN_REDUCE(reduce_udiv, mk_udiv);
    MK_BIN_REDUCE(reduce_urem, mk_urem);
    MK_BIN_REDUCE(reduce_sdiv, mk_sdiv);
    MK_BIN_REDUCE(reduce_srem, mk_srem);
    MK_BIN_REDUCE(reduce_smod, mk_smod);
    MK_BIN_REDUCE(reduce_ext_rotate_left, mk_ext_rotate_left);
    MK_BIN_REDUCE(reduce_ext_rotate_right, mk_ext_rotate_right);

#define MK_BIN_AC_REDUCE(OP, BIN_OP, BB_OP)                             \
MK_BIN_REDUCE(BIN_OP, BB_OP);                                           \
void OP(unsigned num_args, expr * const * args, expr_ref & result) {    \
    SASSERT(num_args > 0);                                              \
    result = args[0];                                                   \
    expr_ref new_result(m_manager);                                     \
    for (unsigned i = 1; i < num_args; i++) {                           \
        BIN_OP(result.get(), args[i], new_result);                      \
        result = new_result;                                            \
    }                                                                   \
}

    MK_BIN_AC_REDUCE(reduce_add, reduce_bin_add, mk_adder);
    MK_BIN_AC_REDUCE(reduce_mul, reduce_bin_mul, mk_multiplier);

    MK_BIN_AC_REDUCE(reduce_or, reduce_bin_or, mk_or);
    MK_BIN_AC_REDUCE(reduce_xor, reduce_bin_xor, mk_xor);


#define MK_BIN_PRED_REDUCE(OP, BB_OP)                                           \
void OP(expr * arg1, expr * arg2, expr_ref & result) {                          \
    m_in1.reset(); m_in2.reset();                                               \
    get_bits(arg1, m_in1);                                                      \
    get_bits(arg2, m_in2);                                                      \
    m_blaster.BB_OP(m_in1.size(), m_in1.c_ptr(), m_in2.c_ptr(), result);        \
}

    MK_BIN_PRED_REDUCE(reduce_eq,  mk_eq);
    MK_BIN_PRED_REDUCE(reduce_sle, mk_sle);
    MK_BIN_PRED_REDUCE(reduce_ule, mk_ule);
    MK_BIN_PRED_REDUCE(reduce_umul_no_overflow, mk_umul_no_overflow);
    MK_BIN_PRED_REDUCE(reduce_smul_no_overflow, mk_smul_no_overflow);
    MK_BIN_PRED_REDUCE(reduce_smul_no_underflow, mk_smul_no_underflow);

#define MK_PARAMETRIC_UNARY_REDUCE(OP, BB_OP)                   \
void OP(expr * arg, unsigned n, expr_ref & result) {            \
    m_in1.reset();                                              \
    get_bits(arg, m_in1);                                       \
    m_out.reset();                                              \
    m_blaster.BB_OP(m_in1.size(), m_in1.c_ptr(), n, m_out);     \
    result = mk_mkbv(m_out);                                    \
}

MK_PARAMETRIC_UNARY_REDUCE(reduce_sign_extend, mk_sign_extend);

    void reduce_ite(expr * arg1, expr * arg2, expr * arg3, expr_ref & result) {
        m_in1.reset();
        m_in2.reset();
        get_bits(arg2, m_in1);                                                     
        get_bits(arg3, m_in2);                                                     
        m_out.reset();
        m_blaster.mk_multiplexer(arg1, m_in1.size(), m_in1.c_ptr(), m_in2.c_ptr(), m_out);
        result = mk_mkbv(m_out);                                                
    }

    void reduce_concat(unsigned num_args, expr * const * args, expr_ref & result) {
        m_out.reset();
        unsigned i = num_args;
        while (i > 0) {
            i--;
            m_in1.reset();
            get_bits(args[i], m_in1);
            m_out.append(m_in1.size(), m_in1.c_ptr());
        }
        result = mk_mkbv(m_out);
    }

    void reduce_extract(unsigned start, unsigned end, expr * arg, expr_ref & result) {
        m_in1.reset();
        get_bits(arg, m_in1);
        m_out.reset();
        for (unsigned i = start; i <= end; ++i)
            m_out.push_back(m_in1.get(i));
        result = mk_mkbv(m_out);
    }

    void reduce_num(func_decl * f, expr_ref & result) {
        SASSERT(f->get_num_parameters() == 2);
        SASSERT(f->get_parameter(0).is_rational());
        SASSERT(f->get_parameter(1).is_int());
        rational v     = f->get_parameter(0).get_rational();
        unsigned bv_sz = f->get_parameter(1).get_int();
        m_out.reset();
        m_blaster.num2bits(v, bv_sz, m_out);
        result = mk_mkbv(m_out);
    }

    void throw_unsupported() {
        throw rewriter_exception("operator is not supported, you must simplify the goal before applying bit-blasting");
    }

    void blast_bv_term(expr * t, expr_ref & result, proof_ref & result_pr) {
        ptr_buffer<expr> bits;
        unsigned bv_size = butil().get_bv_size(t);
        for (unsigned i = 0; i < bv_size; i++) {
            parameter p(i);
            bits.push_back(m().mk_app(butil().get_family_id(), OP_BIT2BOOL, 1, &p, 1, &t));
        }
        result    = mk_mkbv(bits);
        result_pr = 0;
    }
    
    br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
        result_pr = 0;
        TRACE("bit_blaster", tout << f->get_name() << " ";
              for (unsigned i = 0; i < num; ++i) tout << mk_pp(args[i], m()) << " ";
              tout << "\n";);
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
                SASSERT(num == 0);
                reduce_num(f, result);
                return BR_DONE;
            case OP_BADD:
                if (!m_blast_add)
                    return BR_FAILED;
                reduce_add(num, args, result);
                return BR_DONE;
            case OP_BMUL:
                if (!m_blast_mul)
                    return BR_FAILED;
                reduce_mul(num, args, result);
                return BR_DONE;

            case OP_BSDIV:
            case OP_BUDIV:
            case OP_BSREM:
            case OP_BUREM:
            case OP_BSMOD:
                if (m_blast_mul)
                    throw_unsupported(); // must simplify to DIV_I AND DIV0
                return BR_FAILED; // keep them

            case OP_BSDIV0:
            case OP_BUDIV0:
            case OP_BSREM0:
            case OP_BUREM0:
            case OP_BSMOD0:
                return BR_FAILED;

            case OP_BSDIV_I:
                if (!m_blast_mul)
                    return BR_FAILED;
                SASSERT(num == 2);
                reduce_sdiv(args[0], args[1], result);
                return BR_DONE;
            case OP_BUDIV_I:
                if (!m_blast_mul)
                    return BR_FAILED;
                SASSERT(num == 2);
                reduce_udiv(args[0], args[1], result);
                return BR_DONE;
            case OP_BSREM_I:
                if (!m_blast_mul)
                    return BR_FAILED;
                SASSERT(num == 2);
                reduce_srem(args[0], args[1], result);
                return BR_DONE;
            case OP_BUREM_I:
                if (!m_blast_mul)
                    return BR_FAILED;
                SASSERT(num == 2);
                reduce_urem(args[0], args[1], result);
                return BR_DONE;
            case OP_BSMOD_I:
                if (!m_blast_mul)
                    return BR_FAILED;
                SASSERT(num == 2);
                reduce_smod(args[0], args[1], result);
                return BR_DONE;
            case OP_ULEQ:
                SASSERT(num == 2);
                reduce_ule(args[0], args[1], result);
                return BR_DONE;
            case OP_SLEQ:
                SASSERT(num == 2);
                reduce_sle(args[0], args[1], result);
                return BR_DONE;
            case OP_BOR:
                reduce_or(num, args, result);
                return BR_DONE;
            case OP_BNOT:
                SASSERT(num == 1);
                reduce_not(args[0], result);
                return BR_DONE;
            case OP_BXOR:
                reduce_xor(num, args, result);
                return BR_DONE;
                
            case OP_CONCAT:
                reduce_concat(num, args, result);
                return BR_DONE;
            case OP_SIGN_EXT:
                SASSERT(num == 1);
                reduce_sign_extend(args[0], f->get_parameter(0).get_int(), result);
                return BR_DONE;
            case OP_EXTRACT:
                SASSERT(num == 1);
                reduce_extract(f->get_parameter(1).get_int(), f->get_parameter(0).get_int(), args[0], result);
                return BR_DONE;

            case OP_BREDOR:
                SASSERT(num == 1);
                reduce_redor(args[0], result);
                return BR_DONE;
            case OP_BREDAND:
                SASSERT(num == 1);
                reduce_redand(args[0], result);
                return BR_DONE;
            case OP_BSHL:
                SASSERT(num == 2);
                reduce_shl(args[0], args[1], result);
                return BR_DONE;
            case OP_BLSHR:
                SASSERT(num == 2);
                reduce_lshr(args[0], args[1], result);
                return BR_DONE;
            case OP_BASHR:
                SASSERT(num == 2);
                reduce_ashr(args[0], args[1], result);
                return BR_DONE;
            case OP_EXT_ROTATE_LEFT:
                SASSERT(num == 2);
                reduce_ext_rotate_left(args[0], args[1], result);
                return BR_DONE;
            case OP_EXT_ROTATE_RIGHT:
                SASSERT(num == 2);
                reduce_ext_rotate_right(args[0], args[1], result);
                return BR_DONE;

            case OP_BUMUL_NO_OVFL:
                SASSERT(num == 2);
                reduce_umul_no_overflow(args[0], args[1], result);
                return BR_DONE;
            case OP_BSMUL_NO_OVFL:
                SASSERT(num == 2);
                reduce_smul_no_overflow(args[0], args[1], result);
                return BR_DONE;
            case OP_BSMUL_NO_UDFL:
                SASSERT(num == 2);
                reduce_smul_no_underflow(args[0], args[1], result);
                return BR_DONE;
                
            case OP_BIT2BOOL:
            case OP_MKBV:
            case OP_INT2BV:
            case OP_BV2INT:
                return BR_FAILED;
            default:
                TRACE("bit_blaster", tout << "non-supported operator: " << f->get_name() << "\n";
                      for (unsigned i = 0; i < num; i++) tout << mk_ismt2_pp(args[i], m()) << std::endl;);
                throw_unsupported();
            }
        }

        if (m_blast_full && butil().is_bv_sort(f->get_range())) {
            blast_bv_term(m().mk_app(f, num, args), result, result_pr);
            return BR_DONE;
        }
        
        return BR_FAILED;
    }

    bool pre_visit(expr * t) {
        if (m_blast_quant && is_quantifier(t)) {
            quantifier * q = to_quantifier(t);
            ptr_buffer<expr> new_bindings;
            ptr_buffer<expr> new_args;
            unsigned i = q->get_num_decls();
            unsigned j = 0;
            while (i > 0) {
                --i;
                sort * s = q->get_decl_sort(i);
                if (butil().is_bv_sort(s)) {
                    unsigned bv_size = butil().get_bv_size(s);
                    new_args.reset();
                    for (unsigned k = 0; k < bv_size; k++) {
                        new_args.push_back(m().mk_var(j, m().mk_bool_sort()));
                        j++;
                    }
                    new_bindings.push_back(mk_mkbv(new_args));
                }
                else {
                    new_bindings.push_back(m().mk_var(j, s));
                    j++;
                }
            }
            SASSERT(new_bindings.size() == q->get_num_decls());
            i = q->get_num_decls();
            while (i > 0) {
                i--;
                m_bindings.push_back(new_bindings[i]);
            }
        }
        return true;
    }

    bool reduce_var(var * t, expr_ref & result, proof_ref & result_pr) {
        if (m_blast_quant) {
            if (t->get_idx() >= m_bindings.size())
                return false;
            result = m_bindings.get(m_bindings.size() - t->get_idx() - 1);
            result_pr = 0;
            return true;
        }
        
        if (m_blast_full && butil().is_bv(t)) {
            blast_bv_term(t, result, result_pr);
            return true;
        }
        
        return false;
    }

    bool reduce_quantifier(quantifier * old_q, 
                           expr * new_body, 
                           expr * const * new_patterns, 
                           expr * const * new_no_patterns,
                           expr_ref & result,
                           proof_ref & result_pr) {
        if (!m_blast_quant)
            return false;
        unsigned curr_sz   = m_bindings.size();
        SASSERT(old_q->get_num_decls() <= curr_sz);
        unsigned num_decls = old_q->get_num_decls();
        unsigned old_sz    = curr_sz - num_decls;
        string_buffer<> name_buffer;
        ptr_buffer<sort> new_decl_sorts;
        sbuffer<symbol>  new_decl_names;
        for (unsigned i = 0; i < num_decls; i++) {
            symbol const & n = old_q->get_decl_name(i);
            sort * s         = old_q->get_decl_sort(i);
            if (butil().is_bv_sort(s)) {
                unsigned bv_size = butil().get_bv_size(s);
                for (unsigned j = 0; j < bv_size; j++) {
                    name_buffer.reset();
                    name_buffer << n << "." << j;
                    new_decl_names.push_back(symbol(name_buffer.c_str()));
                    new_decl_sorts.push_back(m().mk_bool_sort());
                }
            }
            else {
                new_decl_sorts.push_back(s);
                new_decl_names.push_back(n);
            }
        }
        result = m().mk_quantifier(old_q->is_forall(), new_decl_sorts.size(), new_decl_sorts.c_ptr(), new_decl_names.c_ptr(),
                                   new_body, old_q->get_weight(), old_q->get_qid(), old_q->get_skid(),
                                   old_q->get_num_patterns(), new_patterns, old_q->get_num_no_patterns(), new_no_patterns);
        result_pr = 0;
        m_bindings.shrink(old_sz);
        return true;
    }
};

// CMW: GCC/LLVM do not like this definition because a symbol of the same name exists in assert_set_bit_blaster.o
// template class rewriter_tpl<blaster_rewriter_cfg>;

struct bit_blaster_rewriter::imp : public rewriter_tpl<blaster_rewriter_cfg> {
    blaster              m_blaster;
    blaster_rewriter_cfg m_cfg;
    imp(ast_manager & m, params_ref const & p):
        rewriter_tpl<blaster_rewriter_cfg>(m, 
                                           m.proofs_enabled(), 
                                           m_cfg),
        m_blaster(m),
        m_cfg(m, m_blaster, p) {
        SASSERT(m_blaster.butil().get_family_id() == m.get_family_id("bv"));
    }
    void push() { m_cfg.push(); }
    void pop(unsigned s) { m_cfg.pop(s); }
};

bit_blaster_rewriter::bit_blaster_rewriter(ast_manager & m, params_ref const & p):
    m_imp(alloc(imp, m, p)) {
}

bit_blaster_rewriter::~bit_blaster_rewriter() {
    dealloc(m_imp);
}

void bit_blaster_rewriter::updt_params(params_ref const& p) {
    m_imp->m_cfg.updt_params(p);
}


void bit_blaster_rewriter::push() {
    m_imp->push();
}

void bit_blaster_rewriter::pop(unsigned num_scopes) {
    m_imp->pop(num_scopes);
}

ast_manager & bit_blaster_rewriter::m() const {
    return m_imp->m();
}

unsigned bit_blaster_rewriter::get_num_steps() const {
    return m_imp->get_num_steps();
}

void bit_blaster_rewriter::cleanup() {
    m_imp->cleanup();
}

obj_map<func_decl, expr*> const & bit_blaster_rewriter::const2bits() const {
    return m_imp->m_cfg.m_const2bits;
}

void bit_blaster_rewriter::operator()(expr * e, expr_ref & result, proof_ref & result_proof) {
    m_imp->operator()(e, result, result_proof);
}

