
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

#include "bv_simplifier_plugin.h"
#include "arith_decl_plugin.h"
#include "ast_pp.h"
#include "reg_decl_plugins.h"

class tst_bv_simplifier_plugin_cls {
    class mgr {
    public:
        mgr(ast_manager& m) {
            reg_decl_plugins(m);
        }
    };
    ast_manager m_manager;
    mgr         m_mgr;
    bv_simplifier_params m_bv_params;
    basic_simplifier_plugin m_bsimp;
    arith_util m_arith;
    bv_simplifier_plugin m_simp;
    bv_util     m_bv_util;
    family_id   m_fid;

    void get_num(expr* e, unsigned bv_size, rational& r) {
        unsigned bv_size0;
        if (!m_bv_util.is_numeral(e, r, bv_size0)) {
            UNREACHABLE();
        }
        SASSERT(bv_size == bv_size0);
    }

    unsigned u32(expr* e) {
        rational r;
		std::cout << mk_pp(e,m_manager) << "\n";
        get_num(e, 32, r);
        return r.get_unsigned();
    }

    unsigned char u8(expr* e) {
        rational r;
        get_num(e, 8, r);
        return static_cast<unsigned char>(r.get_unsigned());
    }
	int i32(expr* e) {
        return static_cast<int>(u32(e));
    }

    uint64 u64(expr* e) {
        rational r;
        get_num(e, 64, r);
        return r.get_uint64();
    }

    int64 i64(expr* e) {
        rational r;
        get_num(e, 64, r);
        if (r >= power(rational(2), 63)) {
            r -= power(rational(2), 64);
        }
        return r.get_int64();
    }

    bool ast2bool(expr* e) {
        if (m_manager.is_true(e)) {
            return true;
        }
        if (m_manager.is_false(e)) {
            return false;
        }
        UNREACHABLE();
        return false;        
    }

    bool bit2bool(expr* e) {
        rational r;
        get_num(e, 1, r);
        return 0 != r.get_unsigned();
    }

    expr* mk_int(unsigned i) {
        return m_arith.mk_numeral(rational(i), true);
    }

public:

    tst_bv_simplifier_plugin_cls() : 
        m_mgr(m_manager),
        m_bsimp(m_manager),
        m_arith(m_manager),
        m_simp(m_manager, m_bsimp, m_bv_params), 
        m_bv_util(m_manager), 
        m_fid(0) {
        m_fid = m_manager.mk_family_id("bv");
    }

    ~tst_bv_simplifier_plugin_cls() {}

    void test_num(unsigned a) {
        expr_ref e(m_manager), e1(m_manager);
        app_ref ar(m_manager);
        uint64 a64 = static_cast<uint64>(a);

        e1 = m_bv_util.mk_numeral(rational(a), 32);
        expr* const es[1] = { e1.get() };

        ar = m_manager.mk_app(m_fid, OP_BNEG, e1.get());
        m_simp.reduce(ar->get_decl(), ar->get_num_args(), ar->get_args(), e);
        SASSERT((0-a) == u32(e.get()));

        ar = m_manager.mk_app(m_fid, OP_BNOT, e1.get());
        m_simp.reduce(ar->get_decl(), ar->get_num_args(), ar->get_args(), e);
        SASSERT((~a) == u32(e.get()));

        parameter params[2] = { parameter(32), parameter(32) };
        ar = m_manager.mk_app(m_fid, OP_SIGN_EXT, 1, params, 1, es);
        m_simp.reduce(ar->get_decl(), ar->get_num_args(), ar->get_args(), e);
        SASSERT(((int64)(int)a) == i64(e.get()));

        ar = m_manager.mk_app(m_fid, OP_ZERO_EXT, 1, params, 1, es);
        m_simp.reduce(ar->get_decl(), ar->get_num_args(), ar->get_args(), e);
        SASSERT(((uint64)a) == u64(e.get()));

        params[0] = parameter(7);
        params[1] = parameter(0);
        ar = m_manager.mk_app(m_fid, OP_EXTRACT, 2, params, 1, es);
        m_simp.reduce(ar->get_decl(), ar->get_num_args(), ar->get_args(), e);
        SASSERT(((unsigned char)a) == u8(e.get()));

        params[0] = parameter(2);
        ar = m_manager.mk_app(m_fid, OP_REPEAT, 1, params, 1, es);
        m_simp.reduce(ar->get_decl(), ar->get_num_args(), ar->get_args(), e);
        SASSERT(((a64 << 32) | a64) == u64(e.get()));

        ar = m_manager.mk_app(m_fid, OP_BREDOR, e1.get());
        m_simp.reduce(ar->get_decl(), ar->get_num_args(), ar->get_args(), e);
        SASSERT((a != 0) == bit2bool(e.get()));

        ar = m_manager.mk_app(m_fid, OP_BREDAND, e1.get());
        m_simp.reduce(ar->get_decl(), ar->get_num_args(), ar->get_args(), e);
        SASSERT((a == 0xFFFFFFFF) == bit2bool(e.get()));

        params[0] = parameter(8);

        ar = m_manager.mk_app(m_fid, OP_ROTATE_LEFT, 1, params, 1, es);
        m_simp.reduce(ar->get_decl(), ar->get_num_args(), ar->get_args(), e);
        SASSERT(((a << 8) | (a >> 24)) == u32(e.get()));

        ar = m_manager.mk_app(m_fid, OP_ROTATE_RIGHT, 1, params, 1, es);
        m_simp.reduce(ar->get_decl(), ar->get_num_args(), ar->get_args(), e);
        SASSERT(((a >> 8) | (a << 24)) == u32(e.get()));

        params[0] = parameter(m_manager.mk_sort(m_manager.mk_family_id("arith"), INT_SORT));
        ar = m_manager.mk_app(m_fid, OP_BV2INT, 1, params, 1, es);
		expr* es2[1] = { ar.get() };
		params[0] = parameter(32);
        ar = m_manager.mk_app(m_fid, OP_INT2BV, 1, params, 1, es2);
		m_simp.reduce(ar->get_decl(), ar->get_num_args(), ar->get_args(), e);
        SASSERT(a == u32(e.get()));

        ar = m_manager.mk_app(m_fid, OP_BIT0);
        m_simp.reduce(ar->get_decl(), ar->get_num_args(), ar->get_args(), e);        
        SASSERT(!bit2bool(e.get()));

        ar = m_manager.mk_app(m_fid, OP_BIT1);
        m_simp.reduce(ar->get_decl(), ar->get_num_args(), ar->get_args(), e);        
        SASSERT(bit2bool(e.get()));

    }

    void test_pair(unsigned a, unsigned b) {
     
        expr_ref e(m_manager), e1(m_manager), e2(m_manager);
        app_ref ar(m_manager);
        int sa = static_cast<int>(a);
        int sb = static_cast<int>(b);
        uint64 a64 = static_cast<uint64>(a);
        uint64 b64 = static_cast<uint64>(b);
        
        e1 = m_bv_util.mk_numeral(rational(a), 32);
        e2 = m_bv_util.mk_numeral(rational(b), 32);
        expr* const e1e2[] = { e1.get(), e2.get() };
        
        
        ar = m_manager.mk_app(m_fid, OP_BADD, 2, e1e2);
        m_simp.reduce(ar->get_decl(), ar->get_num_args(), ar->get_args(), e);
        SASSERT((a + b) == u32(e.get()));
        
        ar = m_manager.mk_app(m_fid, OP_BSUB, 2, e1e2);
        m_simp.reduce(ar->get_decl(), ar->get_num_args(), ar->get_args(), e);
        SASSERT((a - b) == u32(e.get()));

        ar = m_manager.mk_app(m_fid, OP_BMUL, 2, e1e2);
        m_simp.reduce(ar->get_decl(), ar->get_num_args(), ar->get_args(), e);
        SASSERT((a * b) == u32(e.get()));

        ar = m_manager.mk_app(m_fid, OP_BAND, 2, e1e2);
        m_simp.reduce(ar->get_decl(), ar->get_num_args(), ar->get_args(), e);
        SASSERT((a & b) == u32(e.get()));

        ar = m_manager.mk_app(m_fid, OP_BOR, 2, e1e2);
        m_simp.reduce(ar->get_decl(), ar->get_num_args(), ar->get_args(), e);
        SASSERT((a | b) == u32(e.get()));

        ar = m_manager.mk_app(m_fid, OP_BNOR, 2, e1e2);
        m_simp.reduce(ar->get_decl(), ar->get_num_args(), ar->get_args(), e);
        SASSERT(~(a | b) == u32(e.get()));

        ar = m_manager.mk_app(m_fid, OP_BXOR, 2, e1e2);
        m_simp.reduce(ar->get_decl(), ar->get_num_args(), ar->get_args(), e);
        SASSERT((a ^ b) == u32(e.get()));

        ar = m_manager.mk_app(m_fid, OP_BXNOR, 2, e1e2);
        m_simp.reduce(ar->get_decl(), ar->get_num_args(), ar->get_args(), e);
        SASSERT((~(a ^ b)) == u32(e.get()));
        
        ar = m_manager.mk_app(m_fid, OP_BNAND, 2, e1e2);
        m_simp.reduce(ar->get_decl(), ar->get_num_args(), ar->get_args(), e);
        SASSERT((~(a & b)) == u32(e.get()));
        
        ar = m_manager.mk_app(m_fid, OP_ULEQ, 2, e1e2);
        m_simp.reduce(ar->get_decl(), ar->get_num_args(), ar->get_args(), e);
        SASSERT((a <= b) == ast2bool(e.get()));

        ar = m_manager.mk_app(m_fid, OP_UGEQ, 2, e1e2);
        m_simp.reduce(ar->get_decl(), ar->get_num_args(), ar->get_args(), e);
        SASSERT((a >= b) == ast2bool(e.get()));

        ar = m_manager.mk_app(m_fid, OP_ULT, 2, e1e2);
        m_simp.reduce(ar->get_decl(), ar->get_num_args(), ar->get_args(), e);
        SASSERT((a < b) == ast2bool(e.get()));

        ar = m_manager.mk_app(m_fid, OP_UGT, 2, e1e2);
        m_simp.reduce(ar->get_decl(), ar->get_num_args(), ar->get_args(), e);
        SASSERT((a > b) == ast2bool(e.get()));

        ar = m_manager.mk_app(m_fid, OP_SLEQ, 2, e1e2);
        m_simp.reduce(ar->get_decl(), ar->get_num_args(), ar->get_args(), e);
        SASSERT((sa <= sb) == ast2bool(e.get()));

        ar = m_manager.mk_app(m_fid, OP_SGEQ, 2, e1e2);
        m_simp.reduce(ar->get_decl(), ar->get_num_args(), ar->get_args(), e);
        SASSERT((sa >= sb) == ast2bool(e.get()));

        ar = m_manager.mk_app(m_fid, OP_SLT, 2, e1e2);
        m_simp.reduce(ar->get_decl(), ar->get_num_args(), ar->get_args(), e);
        SASSERT((sa < sb) == ast2bool(e.get()));

        ar = m_manager.mk_app(m_fid, OP_SGT, 2, e1e2);
        m_simp.reduce(ar->get_decl(), ar->get_num_args(), ar->get_args(), e);
        SASSERT((sa > sb) == ast2bool(e.get()));

        ar = m_manager.mk_app(m_fid, OP_BSHL, 2, e1e2);
        m_simp.reduce(ar->get_decl(), ar->get_num_args(), ar->get_args(), e);
        SASSERT(((b>=32)?0:(a << b)) == u32(e.get()));

        ar = m_manager.mk_app(m_fid, OP_BLSHR, 2, e1e2);
        m_simp.reduce(ar->get_decl(), ar->get_num_args(), ar->get_args(), e);
        SASSERT(((b>=32)?0:(a >> b)) == u32(e.get()));

        ar = m_manager.mk_app(m_fid, OP_BASHR, 2, e1e2);
        m_simp.reduce(ar->get_decl(), ar->get_num_args(), ar->get_args(), e);

        std::cout << "compare: " << sa << " >> " << b << " = " << (sa >> b) << " with " << i32(e.get()) << "\n";
        SASSERT(b >= 32 || ((sa >> b) == i32(e.get())));

        if (b != 0) {
            ar = m_manager.mk_app(m_fid, OP_BSDIV, 2, e1e2);
            m_simp.reduce(ar->get_decl(), ar->get_num_args(), ar->get_args(), e);
            SASSERT((sa / sb) == i32(e.get()));

            ar = m_manager.mk_app(m_fid, OP_BUDIV, 2, e1e2);
            m_simp.reduce(ar->get_decl(), ar->get_num_args(), ar->get_args(), e);
            SASSERT((a / b) == u32(e.get()));

            ar = m_manager.mk_app(m_fid, OP_BSREM, 2, e1e2);
            m_simp.reduce(ar->get_decl(), ar->get_num_args(), ar->get_args(), e);
            //SASSERT((sa % sb) == i32(e.get()));

            ar = m_manager.mk_app(m_fid, OP_BUREM, 2, e1e2);
            m_simp.reduce(ar->get_decl(), ar->get_num_args(), ar->get_args(), e);
            SASSERT((a % b) == u32(e.get()));

            // TBD: BSMOD.
        }

        ar = m_manager.mk_app(m_fid, OP_CONCAT, 2, e1e2);
        m_simp.reduce(ar->get_decl(), ar->get_num_args(), ar->get_args(), e);
        SASSERT(((a64 << 32) | b64) == u64(e.get()));

        ar = m_manager.mk_app(m_fid, OP_BCOMP, 2, e1e2);
        m_simp.reduce(ar->get_decl(), ar->get_num_args(), ar->get_args(), e);
        SASSERT((a == b) == bit2bool(e.get()));
    }

    void test() {
        unsigned_vector nums;
        nums.push_back(0);
        nums.push_back(1);
        nums.push_back(-1);
        nums.push_back(2);
        nums.push_back(31);
        nums.push_back(32);
        nums.push_back(33);
        nums.push_back(435562);
        nums.push_back(-43556211);
        // TBD add some random numbers.


        for (unsigned i = 0; i < nums.size(); ++i) {
            test_num(nums[i]);
            for (unsigned j = 0; j < nums.size(); ++j) {
                test_pair(nums[i], nums[j]);
            }
        }
    }
};


void tst_bv_simplifier_plugin() {
    tst_bv_simplifier_plugin_cls tst_cls;
    tst_cls.test();
}
