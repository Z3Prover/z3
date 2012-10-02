/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    gl_tactic.cpp

Abstract:

    A T-function
    and perhaps Goldreich Levin-based heuristic.

Author:

    Nikolaj (nbjorner) 2011-12-18

Notes:

  This module experiments with T-function bit-vector operations.
 
  TBD: 
  1. convert to tactic.
  2. implement using fewer y bits based on satisfying assignment.
  3. try out code-generation.
  4. better lemma learning?
  5. Incremental refinement into SAT.



--*/

#include"gl_tactic.h"
#include"assertion_set_strategy.h"
#include"bv_decl_plugin.h"
#include"shallow_context_simplifier.h"
#include"elim_uncnstr_vars.h"
#include"max_bv_sharing.h"
#include"max_bool_sharing.h"
#include"bv_size_reduction.h"
#include"context_simplifier.h"
#include"nnf.h"
#include"cooperate.h"
#include"ast_smt2_pp.h"
#include"elim_var_model_converter.h"
#include"smt_context.h"
#include"ast_pp.h"

using namespace gl;


typedef svector<uint64> assignment;

static void gl_unsupported(ast_manager& m, expr* e) {
    TRACE("gl_st", if (e) tout << "unsupported: " << mk_ismt2_pp(e, m) << "\n";);
    throw gl_exception("");
}        

class expr_evaluator {
    typedef unsigned char uint8;
    typedef unsigned short uint16;
    typedef unsigned uint32;
    typedef signed char int8;
    typedef signed short int16;
    typedef signed int int32;

    enum code {
        ADD,
        SUB,
        MUL,
        ITE,
        BAND,
        BOR,
        BXOR,
        BNOT,
        ULT,
        SLT,
        SHL,
        ASHR,
        LSHR,
        LOADC,
        LOADV,
        EQ,      
        UREM,
        SREM,
        SMOD,
        UDIV,
        SDIV
    };

    struct oper {
        code      m_code;
        unsigned  dst;
        unsigned  src1;
        unsigned  src2;
        unsigned  src3;
        uint64    data;
        unsigned  bw;

        static oper mk_binary(code c, unsigned bw, unsigned dst, unsigned src1, unsigned src2) {
            return oper(c, bw, dst, src1, src2, 0, 0);            
        }
        static oper mk_ite(unsigned bw, unsigned dst, unsigned src1, unsigned src2, unsigned src3) {
            return oper(ITE, bw, dst, src1, src2, src3, 0);
        }
        static oper mk_loadc(unsigned bw, unsigned dst, uint64 data) {
            return oper(LOADC, bw, dst, 0, 0, 0, data);
        }

    private:
        oper(code c, unsigned bw, unsigned dst, unsigned src1, unsigned src2, unsigned src3, uint64 data): 
            m_code(c), bw(bw), dst(dst), src1(src1), src2(src2), src3(src3), data(data) { }
    };

    ast_manager&      m;
    bv_util           m_bv;
    svector<uint64>   m_regs;
    svector<oper>     m_ops;
    unsigned          m_dst;
    obj_map<expr, unsigned> m_cache;
    assignment const*        m_vals_tmp;
    obj_map<app, unsigned>* m_vars_tmp;

    unsigned mk_oper(code c, expr* e, unsigned src1, unsigned src2) {
        return mk_oper(c, get_bitwidth(e), src1, src2);
    }

    unsigned get_bitwidth(expr* e) {
        unsigned bw = 0;
        if (m.is_bool(e)) {
            bw = 1;
        }
        else if (m_bv.is_bv(e)) {
            bw= m_bv.get_bv_size(e);
            if (bw > 64) {
                unsupported(e);
            }
        }
        else {
            unsupported(e);
        }
        return bw;
    }

    unsigned mk_oper(code c, unsigned bw, unsigned src1, unsigned src2) {
        unsigned dst = m_regs.size();
        m_regs.push_back(0);
        m_ops.push_back(oper::mk_binary(c, bw, dst, src1, src2));
        return dst;
    }

    unsigned mk_const(expr* e, uint64 c) {
        return mk_const(get_bitwidth(e), c);
    }

    unsigned mk_const(unsigned bw, uint64 c) {
        unsigned dst = m_regs.size();
        m_regs.push_back(0);
        m_ops.push_back(oper::mk_loadc(bw, dst, c));
        return dst;
    }


    unsigned mk_ite(expr* e, unsigned src1, unsigned src2, unsigned src3) {
        unsigned dst = m_regs.size();
        unsigned bw = get_bitwidth(e);
        m_regs.push_back(0);
        m_ops.push_back(oper::mk_ite(bw, dst, src1, src2, src3));
        return dst;        
    }

    unsigned mk_oper(code c, unsigned num_args, expr* const* args, uint64 def) {
        if (num_args == 0) {
            unsupported(0);
            return mk_const(static_cast<unsigned>(0), def);
        }
        unsigned dst = compile(args[0]);        
        for (unsigned i = 1; i < num_args; ++i) {
            dst = mk_oper(c, args[i], dst, compile(args[i]));
        }
        return dst;                                
    }

    unsigned compile(app* a) {               
        unsigned src1 = 0, src2 = 0, src3 = 0, dst = 0;
        uint64 src0 = 0;
        unsigned num_args = a->get_num_args();
        expr* const* args = a->get_args();
        unsigned var_id = 0;

        if (num_args >= 1) {
            src1 = compile(a->get_arg(0));
        }
        if (num_args >= 2) {
            src2 = compile(a->get_arg(1));
        }
        if (num_args >= 3) {
            src3 = compile(a->get_arg(2));
        }
        if (m_bv.is_bv(a) && m_bv.get_bv_size(a) > 64) {
            unsupported(a);
        }
        if (m_vars_tmp->find(a, var_id)) {
            return mk_oper(LOADV, a, var_id, 0);
        }
        if (a->get_family_id() == m.get_basic_family_id()) {
            switch(a->get_decl_kind()) {
            case OP_AND:
                return mk_oper(BAND, num_args, args, 1);
            case OP_OR:
                return mk_oper(BOR, num_args, args, 0);
            case OP_NOT:
                return mk_oper(BNOT, a, src1, 0);
            case OP_EQ:
                return mk_oper(EQ, a, src1, src2);
            case OP_ITE:
                return mk_ite(a, src1, src2, src3);
            case OP_DISTINCT:
                unsupported(a);
            case OP_TRUE:
                return mk_const(a, 1);
            case OP_FALSE:
                return mk_const(a, 0);
            case OP_XOR:
                return mk_oper(BNOT, a, mk_oper(EQ, a, src1, src2), 0);
            case OP_IFF:
                return mk_oper(EQ, a, src1, src2); // mask?
            default:
                UNREACHABLE();
            }
        }
        if (a->get_family_id() == m_bv.get_family_id()) {
            unsigned bv_size;
            rational val;
            switch(a->get_decl_kind()) {
            case OP_BV_NUM: 
                VERIFY(m_bv.is_numeral(a, val, bv_size));
                if (bv_size > 64) {
                    unsupported(a);
                }
                src0 = val.get_uint64();
                return mk_const(a, src0);
            case OP_BIT1:
                return mk_const(a, 1);
            case OP_BIT0:
                return mk_const(a, 0);
            case OP_BNEG:
                SASSERT(num_args == 1);
                return mk_oper(SUB, a, 0, src1);
            case OP_BADD:
                return mk_oper(ADD, num_args, args, 0);
            case OP_BSUB:
                SASSERT(num_args == 2);
                return mk_oper(SUB, a, src1, src2);                
            case OP_BMUL:
                return mk_oper(MUL, num_args, args, 1);     
            case OP_BSDIV:
            case OP_BSDIV0: 
            case OP_BSDIV_I: 
                return mk_oper(SDIV, a, src1, src2);
            case OP_BUDIV:
            case OP_BUDIV0:
            case OP_BUDIV_I:
                return mk_oper(UDIV, a, src1, src2);
            case OP_BSREM:
            case OP_BSREM0:
            case OP_BSREM_I:
                return mk_oper(SREM, a, src1, src2);
            case OP_BUREM:
            case OP_BUREM0:
            case OP_BUREM_I:
                return mk_oper(UREM, a, src1, src2);
            case OP_BSMOD:                
            case OP_BSMOD0:                
            case OP_BSMOD_I:
                return mk_oper(SMOD, a, src1, src2);
            case OP_ULEQ:
                return mk_oper(BOR, a, mk_oper(ULT, a, src1, src2), mk_oper(EQ, a, src1, src2));
            case OP_SLEQ:
                return mk_oper(BOR, a, mk_oper(SLT, a, src1, src2), mk_oper(EQ, a, src1, src2));
            case OP_UGEQ:
                return mk_oper(BOR, a, mk_oper(ULT, a, src2, src1), mk_oper(EQ, a, src1, src2));
            case OP_SGEQ:
                return mk_oper(BOR, a, mk_oper(SLT, a, src2, src1), mk_oper(EQ, a, src1, src2));
            case OP_ULT:
                return mk_oper(ULT, a, src1, src2);
            case OP_SLT:
                return mk_oper(SLT, a, src1, src2);
            case OP_UGT:
                return mk_oper(ULT, a, src2, src1);
            case OP_SGT:                
                return mk_oper(SLT, a, src2, src1);
            case OP_BAND:
                return mk_oper(BAND, num_args, args, ~((uint64)0));
            case OP_BOR:
                return mk_oper(BOR, num_args, args, 0);
            case OP_BNOT:
                return mk_oper(BNOT, a, src1, 0);
            case OP_BXOR:
                SASSERT(num_args == 2);
                return mk_oper(BXOR, a, src1, src2);
            case OP_BNAND:
                return mk_oper(BNOT, a, mk_oper(BAND, num_args, args, ~((uint64)0)), 0);
            case OP_BNOR:
                return mk_oper(BNOT, a, mk_oper(BOR,  num_args, args, 0), 0);
            case OP_BXNOR:
                SASSERT(num_args == 2);
                return mk_oper(BNOT, a, mk_oper(BXOR, a, src1, src2), 0);                
            case OP_CONCAT: {
                SASSERT(num_args > 0);
                expr* last = args[num_args-1];
                src1 = compile(last);
                unsigned offset = m_bv.get_bv_size(last);
                for (unsigned i = num_args-1; i > 0; ) {
                    --i;
                    unsigned bv_size = m_bv.get_bv_size(args[i]);
                    uint64 mask = (1ull << offset)-1;
                    offset += bv_size;
                    src2 = compile(args[i]);
                    src2 = mk_oper(SHL, args[i], src2, offset);                    
                    src1 = mk_oper(BAND, offset, src1, mk_const(offset, mask));
                    src1 = mk_oper(BOR, offset, src1, src2);

                }
                return src1;
            }                
            case OP_SIGN_EXT:
                unsupported(a);
            case OP_ZERO_EXT:
                unsupported(a);
            case OP_EXTRACT: {
                unsigned lo = m_bv.get_extract_low(a);
                unsigned hi = m_bv.get_extract_high(a);
                if (lo > 0) {
                    dst = mk_oper(SHL, a, src1, lo);
                }
                else {
                    dst = src1;
                }
                return dst;
            }
            case OP_REPEAT:                
            case OP_BREDOR:
            case OP_BREDAND:
            case OP_BCOMP:         
                unsupported(a);
            case OP_BSHL:
                SASSERT(num_args == 2);
                return mk_oper(SHL, a, src1, src2);
            case OP_BLSHR:
                SASSERT(num_args == 2);
                return mk_oper(LSHR, a, src1, src2);
            case OP_BASHR:
                SASSERT(num_args == 2);
                return mk_oper(ASHR, a, src1, src2);
            case OP_ROTATE_LEFT:
            case OP_ROTATE_RIGHT:
            case OP_EXT_ROTATE_LEFT:
            case OP_EXT_ROTATE_RIGHT:                
            case OP_BUMUL_NO_OVFL: // no unsigned multiplication overflow predicate
            case OP_BSMUL_NO_OVFL: // no signed multiplication overflow predicate
            case OP_BSMUL_NO_UDFL: // no signed multiplication underflow predicate                
            case OP_BIT2BOOL: // predicate
                unsupported(a);
            case OP_MKBV:     // bools to bv 
                return src1;
            case OP_INT2BV:
            case OP_BV2INT:
            case OP_CARRY:
            case OP_XOR3:
                unsupported(a);
            }
        }
        unsupported(a);
        UNREACHABLE();
        return 0;
    }

    uint64 to_bool(bool b) { return b?0x1:0x0; }

    void interpret(oper oper) {
        unsigned mask = 0;
        switch(oper.m_code) {
        case LOADC:
            m_regs[oper.dst] = oper.data;
            break;
        case LOADV:
            m_regs[oper.dst] = (*m_vals_tmp)[oper.src1];
            break;
        case ADD:
            m_regs[oper.dst] = m_regs[oper.src1] + m_regs[oper.src2];
            break;
        case SUB:
            switch(oper.bw) 
            {
            case 8: m_regs[oper.dst] = (uint8)m_regs[oper.src1] - (uint8)m_regs[oper.src2]; break;
            case 16: m_regs[oper.dst] = (uint16)m_regs[oper.src1] - (uint16)m_regs[oper.src2]; break;
            case 32: m_regs[oper.dst] = (uint32)m_regs[oper.src1] - (uint32)m_regs[oper.src2]; break;
            case 64: m_regs[oper.dst] = m_regs[oper.src1] - m_regs[oper.src2]; break;
            default: unsupported(0);
            }
            break;
        case MUL:
            m_regs[oper.dst] = m_regs[oper.src1] * m_regs[oper.src2];
            break;
        case SDIV:
            switch(oper.bw) 
            {
            case 8: m_regs[oper.dst] = (int8)m_regs[oper.src1] / (int8)m_regs[oper.src2]; break;
            case 16: m_regs[oper.dst] = (int16)m_regs[oper.src1] / (int16)m_regs[oper.src2]; break;
            case 32: m_regs[oper.dst] = (int32)m_regs[oper.src1] / (int32)m_regs[oper.src2]; break;
            case 64: m_regs[oper.dst] = (int64)m_regs[oper.src1] / (int64)m_regs[oper.src2]; break;
            default: unsupported(0);
            }
            break;
        case UDIV:
            switch(oper.bw) 
            {
            case 8: m_regs[oper.dst] = (uint8)m_regs[oper.src1] / (uint8)m_regs[oper.src2]; break;
            case 16: m_regs[oper.dst] = (uint16)m_regs[oper.src1] / (uint16)m_regs[oper.src2]; break;
            case 32: m_regs[oper.dst] = (uint32)m_regs[oper.src1] / (uint32)m_regs[oper.src2]; break;
            case 64: m_regs[oper.dst] = m_regs[oper.src1] / m_regs[oper.src2]; break;
            default: unsupported(0);
            }
            break;
        case SMOD:
        case SREM:
        case UREM:
            unsupported(0);
        case BAND:
            m_regs[oper.dst] = m_regs[oper.src1] & m_regs[oper.src2];
            break;
        case BOR:
            m_regs[oper.dst] = m_regs[oper.src1] | m_regs[oper.src2];
            break;
        case BXOR:
            m_regs[oper.dst] = m_regs[oper.src1] ^ m_regs[oper.src2];
            break;
        case BNOT:
            m_regs[oper.dst] = ~m_regs[oper.src1];
            break;
        case SHL:
            mask = (1ull << oper.bw) - 1;
            m_regs[oper.dst] = m_regs[oper.src1] << (mask & m_regs[oper.src2]);
            break;
        case LSHR:
            m_regs[oper.dst] = m_regs[oper.src1] >> (mask & m_regs[oper.src2]);
            break;
        case ASHR:
            switch(oper.bw) 
            {
            case 8: m_regs[oper.dst] = (int8)m_regs[oper.src1] >> (int8)m_regs[oper.src2]; break;
            case 16: m_regs[oper.dst] = (int16)m_regs[oper.src1] >> (int16)m_regs[oper.src2]; break;
            case 32: m_regs[oper.dst] = (int32)m_regs[oper.src1] >> (int32)m_regs[oper.src2]; break;
            case 64: m_regs[oper.dst] = (int64)m_regs[oper.src1] >> (int64)m_regs[oper.src2]; break;
            default: unsupported(0);
            }
            break;
        case ULT:
            switch(oper.bw) 
            {
            case 8: m_regs[oper.dst] = to_bool((uint8)m_regs[oper.src1] < (uint8)m_regs[oper.src2]); break;
            case 16: m_regs[oper.dst] = to_bool((uint16)m_regs[oper.src1] < (uint16)m_regs[oper.src2]); break;
            case 32: m_regs[oper.dst] = to_bool((uint32)m_regs[oper.src1] < (uint32)m_regs[oper.src2]); break;
            case 64: m_regs[oper.dst] = to_bool(m_regs[oper.src1] < m_regs[oper.src2]); break;
            default: unsupported(0);
            }
            break;
        case SLT:
            switch(oper.bw) 
            {
            case 8: m_regs[oper.dst] = to_bool((int8)m_regs[oper.src1] < (int8)m_regs[oper.src2]); break;
            case 16: m_regs[oper.dst] = to_bool((int16)m_regs[oper.src1] < (int16)m_regs[oper.src2]); break;
            case 32: m_regs[oper.dst] = to_bool((int32)m_regs[oper.src1] < (int32)m_regs[oper.src2]); break;
            case 64: m_regs[oper.dst] = to_bool((int64)m_regs[oper.src1] < (int64)m_regs[oper.src2]); break;
            default: unsupported(0);
            }
            break;
        case ITE:
            m_regs[oper.dst] = (0x1&m_regs[oper.src1])?m_regs[oper.src2]:m_regs[oper.src3];
            break;
        case EQ: 
            mask = (1ull << oper.bw) - 1;
            m_regs[oper.dst] = to_bool((mask & m_regs[oper.src1]) == (mask & m_regs[oper.src2]));
            break;        
        default:
            UNREACHABLE();
            break;
        }
    }

    unsigned compile(expr* e) {
        unsigned val;
        TRACE("gl_st", tout << mk_ismt2_pp(e, m) << "\n";);
        if (!is_app(e)) {
            unsupported(e);
        }
        app* a = to_app(e);
        if (!m_cache.find(a, val)) {
            val = compile(a);
            m_cache.insert(a, val);
        }
        return val;
    }

    void interpret() {
        for (unsigned i = 0; i < m_ops.size(); ++i) {
            interpret(m_ops[i]);
        }
    }

    void unsupported(expr* e) {
        gl_unsupported(m, e);
    }

public:

    expr_evaluator(ast_manager& m): m(m), m_bv(m), m_vals_tmp(0)
    {}

    void compile(obj_map<app,unsigned>& vars, expr* e) {
        m_vars_tmp = &vars;
        m_dst = compile(e);
    }

    uint64 evaluate(assignment const& assign) {
        m_vals_tmp = &assign;
        interpret();
        return m_regs[m_dst];
    }

};

// compile a formula by abstracting T-functions (of certain size) 
// to propositional abstrations.
class t_function_abstractor {
    ast_manager&           m;
    bv_util                m_bv;
    family_id              m_bv_fid;
    app_ref_vector*        m_t_funs, *m_t_proxies;
    obj_map<app,unsigned>* m_t_vars;
    obj_map<app,app*>      m_cache;

    void unsupported(expr* e) { gl_unsupported(m, e); }

    void unsupported() { gl_unsupported(m, 0); }

    bool is_bv(app* t) const {
        return m_bv_fid == t->get_family_id();
    }

    // t is a T function. Extract constraints on inputs.
    void absT(expr* _t, app_ref& result) {
        app* c;
        if (!is_app(_t)) {
            unsupported(_t);
        }
        app* t = to_app(_t);
        if (m_cache.find(t, c)) {
            result = c;
        }
        else {
            absT(t, result);
            m_cache.insert(t, result);
        }
    }

    void absT(app* t, app_ref& result) {        
        if (is_bv(t)) {
            absTBv(t, result);
        }
        else {
            absTVar(t, result);
        }
    }

    void absT(unsigned num_args, expr* const* args, expr_ref_vector& rs) {        
        app_ref result(m);
        for (unsigned i = 0; i < num_args; ++i) {
            absT(args[i], result);
            rs.push_back(result);
        }
    }

    void absTVar(app* t, app_ref& result) {
        absF(t, result);
        m_t_vars->insert(result, m_t_vars->size());
    }

    void absTBv(app* t, app_ref& result) {
        SASSERT(is_bv(t));
        expr_ref_vector results(m);
        switch(t->get_decl_kind()) {
        case OP_BV_NUM: 
        case OP_BIT1:
        case OP_BIT0:
        case OP_BADD:
        case OP_BSUB:
        case OP_BNEG:
        case OP_BMUL:
        case OP_BAND:
        case OP_BOR:
        case OP_BNOT:
        case OP_BXOR:
        case OP_BNAND:
        case OP_BNOR:
        case OP_BXNOR:
        case OP_CONCAT:
        case OP_SIGN_EXT:
        case OP_ZERO_EXT:
        case OP_EXTRACT:
        case OP_BSHL:
            absT(t->get_num_args(), t->get_args(), results);
            result = m.mk_app(t->get_decl(), results.size(), results.c_ptr());
            break;
        default:
            absTVar(t, result);
            break;
        }
    }

    // f is a formula/non-T function. Extract T functions.
    void absF(expr* _f, app_ref& result) {
        app* c;
        if (!is_app(_f)) {
            unsupported(_f);
        }
        app* f = to_app(_f);
        if (m_cache.find(f, c)) {
            result = c;
        }
        else {
            absF(f, result);
            m_cache.insert(f, result);
        }
    }

    void absF(app* a, app_ref& result) {
        if (a->get_family_id() == m.get_basic_family_id()) {
            absFBasic(a, result);
        }
        else if (is_bv(a)) {
            absFBv(a, result);
        }
        else {
            expr_ref_vector rs(m);
            absF(a->get_num_args(), a->get_args(), rs);
            result = m.mk_app(a->get_decl(), rs.size(), rs.c_ptr());
        }
    }

    void absF(unsigned num_args, expr*const* args, expr_ref_vector& rs) {
        app_ref result(m);
        for (unsigned i = 0; i < num_args; ++i) {
            absF(args[i], result);
            rs.push_back(result);
        }
    }

    void absFBasic(app* f, app_ref& result) {
        expr_ref_vector results(m);
        expr* e1, *e2;
        if (m.is_eq(f, e1, e2) && m_bv.is_bv(e1)) {
            app_ref r1(m), r2(m);
            r1 = to_app(m_bv.mk_bv_xor(2, f->get_args()));
            absFBv(r1, r2);
            e1 = m_bv.mk_numeral(rational(0), m_bv.get_bv_size(e1));
            result = m.mk_eq(e1, r2);
        }
        else {
            absF(f->get_num_args(), f->get_args(), results);
            result = m.mk_app(f->get_decl(), results.size(), results.c_ptr());
        }
    }

    void absFBv(app* a, app_ref& result) {
        expr_ref_vector results(m);
        switch(a->get_decl_kind()) {
        case OP_BADD:
        case OP_BSUB:
        case OP_BNEG:
        case OP_BMUL:
        case OP_BAND:
        case OP_BOR:
        case OP_BNOT:
        case OP_BXOR:
        case OP_BNAND:
        case OP_BNOR:
        case OP_BXNOR:
        case OP_CONCAT:
        case OP_SIGN_EXT:
        case OP_ZERO_EXT:
        case OP_EXTRACT:
        case OP_BSHL: {
            app_ref tmp(m);
            absT(a, tmp);
            result = m.mk_fresh_const("T",m.get_sort(a));
            m_t_funs->push_back(tmp);
            m_t_proxies->push_back(result);
            return;
        }
        default:
            absF(a->get_num_args(), a->get_args(), results);
            result = m.mk_app(a->get_decl(), results.size(), results.c_ptr());
            return;
        }
    }

public:
    t_function_abstractor(ast_manager& m): m(m), m_bv(m), m_bv_fid(m.get_family_id("bv")) {}

    void operator()(expr* e, app_ref& result, app_ref_vector& t_funs, app_ref_vector& t_proxies, obj_map<app, unsigned>& t_vars) {
        m_cache.reset();
        m_t_funs = &t_funs;
        m_t_proxies = &t_proxies;
        m_t_vars = &t_vars;
        absF(e, result);
    }

};

class gl_eval {
    ast_manager&   m;
    expr_evaluator m_eval;
    app_ref        m_proxy;
    expr_ref       m_proxy_val;
    uint64         m_expected;
    bool           m_expected_valid;
public:
    gl_eval(ast_manager& m): m(m), m_eval(m), m_proxy(m), m_proxy_val(m), m_expected(0) {}
    
    void set_model(model_ref& mdl) { 
        m_proxy_val = 0;
        if (mdl->eval(m_proxy, m_proxy_val, false) && m_proxy_val.get()) {
            rational r;
            bv_util bv(m);
            unsigned bv_size;
            m_expected_valid = true;
            VERIFY(bv.is_numeral(m_proxy_val, r, bv_size));
            m_expected = r.get_uint64();
            TRACE("gl_st", tout << mk_pp(m_proxy, m) << " |-> " << r << "\n";);
        }
        else {
            m_expected_valid = false;
        }
    }
    
    void set_proxy(app* e) { m_proxy = e; }

    expr* get_proxy() { return m_proxy; }

    expr* get_proxy_val() { return m_proxy_val; }
    
    bool operator()(assignment const& assign, unsigned num_bits) {
        if (!m_expected_valid) {
            TRACE("gl_st", tout << mk_pp(m_proxy, m) << " not valid\n";);
            return true;
        }
        else {
            uint64 val = m_eval.evaluate(assign);
            uint64 mask = (1ULL << num_bits) - 1ULL;
            TRACE("gl_st", tout << mk_pp(m_proxy, m) << " " << val << " expected: " << m_expected << " num_bits: " << num_bits << "\n";);
            return (val & mask) == (m_expected & mask);
        }
    }    

    void compile(obj_map<app, unsigned>& var2index, expr* e) {
        m_eval.compile(var2index, e);
    }
};


class gl_st : public assertion_set_strategy {

    ast_manager&           m;
    front_end_params       m_params;

    // variables and their assignments.    obj_map<app, unsigned> m_var2index;
    ptr_vector<app>        m_index2var;
    svector<uint64>        m_vals;

    // t-functions
    vector<gl_eval*>       m_evals;
    
    // external search state.
    smt::context      m_ctx;

    // internal search state.
    unsigned_vector   m_search_stack;
    unsigned          m_max_bitwidth;
    unsigned          m_max_search_depth;
    
    
    bv_util           m_bv;
    volatile bool     m_cancel;

public:

    gl_st(ast_manager& m, params_ref const& p): 
        m(m), m_ctx(m, m_params),
        m_bv(m), m_cancel(false),
        m_max_search_depth(0) {
        m_params.m_model = true;
        }

    virtual ~gl_st() {
        for (unsigned i = 0; i < m_evals.size(); ++i) dealloc(m_evals[i]); 
    }

    struct nonsat_by_gl { };

    struct unsupported_by_gl { };

    virtual void operator()(assertion_set & s, model_converter_ref & mc) {
        ptr_vector<expr> conjs;
        for (unsigned i = 0; i < s.size(); ++i) {
            conjs.push_back(s.form(i));
        }
        app_ref fml1(m.mk_and(conjs.size(), conjs.c_ptr()), m);
        app_ref fml2(m);
        t_function_abstractor TAbs(m);
        app_ref_vector t_funs(m), t_proxies(m);
        TAbs(fml1, fml2, t_funs, t_proxies, m_var2index);
        TRACE("gl_st", 
              tout << mk_pp(fml1, m) << "\n";
              tout << mk_pp(fml2, m) << "\n";);

        m_index2var.resize(m_var2index.size());
        m_vals.resize(m_var2index.size());
        obj_map<app, unsigned>::iterator it = m_var2index.begin(), end = m_var2index.end();
        for (; it != end; ++it) {
            m_index2var[it->m_value] = it->m_key;
        }

        m_max_bitwidth = 0;
        
        for (unsigned i = 0; i < t_funs.size(); ++i) {
            gl_eval* eval = alloc(gl_eval, m);
            eval->compile(m_var2index, t_funs[i].get());
            eval->set_proxy(t_proxies[i].get());
            m_evals.push_back(eval);
            m_max_bitwidth = std::max(m_max_bitwidth, m_bv.get_bv_size(t_proxies[i].get()));
        }

        m_ctx.assert_expr(fml2);

        if (search()) {
            elim_var_model_converter* emc = alloc(elim_var_model_converter, m);
            mc = emc;
            for (unsigned i = 0; i < m_index2var.size(); ++i) {
                expr_ref vl(m);
                if (m.is_bool(m_index2var[i])) {
                    vl = m_vals[i]? m.mk_true():m.mk_false();
                }
                else if (m_bv.is_bv(m_index2var[i])) {
                    vl = m_bv.mk_numeral(m_vals[i], m_bv.get_bv_size(m_index2var[i]));
                }
                emc->insert(m_index2var[i]->get_decl(), vl);
            }
            // TBD: other variables.
            s.reset();
        }
        else {
            throw nonsat_by_gl();
        }
    }
    
    virtual void cleanup() {

    }
        
    virtual void collect_statistics(statistics & st) const {

    }

    virtual void reset_statistics() {

    }
protected:
    virtual void set_cancel(bool f) {
    }
private:

    void checkpoint() { 
        if (m_cancel)
            throw gl_exception(STE_CANCELED_MSG);
        cooperate("gl");
    }    

    bool search() {
        while (true) {
            lbool res = m_ctx.check();
            if (res == l_false) {
                return false;
            }
            model_ref mdl;
            m_ctx.get_model(mdl);
            for (unsigned i = 0; i < m_evals.size(); ++i) {
                m_evals[i]->set_model(mdl);
            }
            m_max_search_depth = 0;
            if (t_search()) {
                return true;
            }
            expr_ref_vector eqs(m);
            for (unsigned i = 0; i < m_evals.size(); ++i) {
                expr* v = m_evals[i]->get_proxy_val();
                expr* p = m_evals[i]->get_proxy();
                if (v && p) {
                    if (m_bv.is_bv(v) && m_bv.get_bv_size(v) > m_max_search_depth) {
                        v = m_bv.mk_extract(m_max_search_depth-1,0,v);
                        p = m_bv.mk_extract(m_max_search_depth-1,0,p);
                    }
                    eqs.push_back(m.mk_eq(v, p));
                }
            }
            expr_ref fml(m);
            fml = m.mk_and(eqs.size(), eqs.c_ptr());
            TRACE("gl_st", tout << "block " << mk_pp(fml, m) << "\n";);
            m_ctx.assert_expr(m.mk_not(fml));
        }
        return false;
    }


    bool t_search() {
        if (!decide()) {
            return false;
        }
        while (true) {
            while (!propagate()) {
                if (!backtrack()) {
                    return false;
                }
            }
            if (!decide()) {
                return true;
            }
        }
    }

    bool propagate() {
        // update the assignment.
        for (unsigned i = 0; i < m_index2var.size(); ++i) {
            m_vals[i] = 0;
            for (unsigned j = 0; j < m_search_stack.size(); ++j) {
                if (m_search_stack[j] & (1 << i)) {
                    m_vals[i] |= (1ULL << j);
                }
            }
        }
        // evaluate under assignment
        for (unsigned i = 0; i < m_evals.size(); ++i) {
            if (!(*m_evals[i])(m_vals, m_search_stack.size())) {
                return false;
            }
        }
        return true;
    }

    // backtrack to previous level.        
    bool backtrack() {
        while (!next()) {
            TRACE("gl_st", tout << "level: " << m_search_stack.size() << "\n";);
            m_search_stack.pop_back();
            if (m_search_stack.empty()) {
                return false;
            }
        }
        return true;
    }

    bool next() {        
        SASSERT(!m_search_stack.empty());
        m_search_stack.back()++;
        TRACE("gl_st", tout << "next " << m_search_stack.back() << "\n";);
        return !(m_search_stack.back() & (1 << m_index2var.size()));
    }

    // choose the next assignment.
    bool decide() {
        if (m_search_stack.size() == m_max_bitwidth) {
            return false;
        }
        else {
            m_search_stack.push_back(0);
            m_max_search_depth = std::max(m_max_search_depth,  m_search_stack.size());
            return true;
        }
    }

    std::ostream& display(std::ostream& out) {
        out << "gl";
        return out;
    }

};

MK_FAIL_IF(fail_if_not_bv, !is_qfbv(s), "failed: GL supports only pure QF_BV for now.");

static as_st * mk_gl_preamble(ast_manager & m, params_ref const & p) {
    params_ref main_p;
    main_p.set_bool(":elim-and", true);
    main_p.set_bool(":push-ite-bv", true);
    main_p.set_bool(":blast-distinct", true);
    main_p.set_bool(":hi-div0", true);

    params_ref simp2_p = p;
    simp2_p.set_bool(":som", true);
    simp2_p.set_bool(":pull-cheap-ite", true);
    simp2_p.set_bool(":push-ite-bv", false);
    simp2_p.set_bool(":local-ctx", true);
    simp2_p.set_uint(":local-ctx-limit", 10000000);

    params_ref hoist_p;
    hoist_p.set_bool(":hoist-mul", true);
    hoist_p.set_bool(":som", false);

    params_ref gaussian_p;
    // conservative guassian elimination. 
    gaussian_p.set_uint(":gaussian-max-occs", 2); 

    return and_then(and_then(mk_simplifier(m),
                             mk_shallow_simplifier(m),
                             using_params(mk_gaussian(m), gaussian_p),
                             mk_elim_uncnstr_vars(m),
                             mk_bv_size_reduction(m),
                             using_params(mk_simplifier(m), simp2_p)),
                    using_params(mk_simplifier(m), hoist_p),
                        mk_max_bv_sharing(m),
                        mk_nnf(p));
}

as_st * mk_gl(ast_manager & m, params_ref const& p) {
    return alloc(gl_st, m, p);
}

as_st * mk_qfbv_gl_strategy(ast_manager & m, params_ref const & p) {
    params_ref gl_p(p);

    as_st * st = and_then(mk_gl_preamble(m, p),
                          fail_if_not_bv(), 
                          mk_gl(m, gl_p));
    
    st->updt_params(p);
    return st;
}

