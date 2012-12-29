#include "expr_rand.h"
#include "bv_decl_plugin.h"
#include "array_decl_plugin.h"
#include "arith_decl_plugin.h"
#include "ast_pp.h"


expr_rand::expr_rand(ast_manager& m):
    m_manager(m),
    m_num_vars(0),
    m_num_apps(0),
    m_num_nodes(0),
    m_max_steps(10),
    m_funcs(m)
{}

expr_rand::~expr_rand() {
    map_t::iterator it = m_nodes.begin(); 
    map_t::iterator end = m_nodes.end(); 
    for (; it != end; ++it) {
        dealloc(it->m_value);
    }
}

void expr_rand::add_var(sort* s) {
    add_expr(m_manager.mk_fresh_const("x", s));
}

void expr_rand::add_func_decl(func_decl* f) {
    m_funcs.push_back(f);
}

void expr_rand::add_expr(expr* t) {
    sort* s = m_manager.get_sort(t);
    expr_ref_vector* vals = 0;
    if (!m_nodes.find(s, vals)) {
        vals = alloc(expr_ref_vector, m_manager);
        m_nodes.insert(s, vals);
    }
    vals->push_back(t);    
}

void expr_rand::get_next(sort* s, expr_ref& e) {
    walk(m_max_steps);
    e = choose_expr(s);
}

void expr_rand::walk() {
    func_decl* f = choose_func_decl();
    unsigned arity = f->get_arity();
    expr_ref_vector args(m_manager);
    for (unsigned i = 0; i < arity; ++i) {
        args.push_back(choose_expr(f->get_domain(i)));
    }
    expr* r = m_manager.mk_app(f, args.size(), args.c_ptr());
    add_expr(r);
}

void expr_rand::walk(unsigned n) {
    for (unsigned i = 0; i < n; ++i) {
        walk();
    }
}
    
func_decl* expr_rand::choose_func_decl() {
    unsigned idx = m_random(m_funcs.size());
    return m_funcs[idx].get();
}

expr* expr_rand::choose_expr(sort* s) {
    expr_ref_vector* vals = 0;
    if (!m_nodes.find(s, vals)) {
        add_var(s);
        if (!m_nodes.find(s, vals)) {
            UNREACHABLE();
        }
        SASSERT(vals);
    }
    unsigned idx = m_random(vals->size());
    return (*vals)[idx].get();
}

void expr_rand::initialize_arith(unsigned num_vars) {
    arith_util u(m_manager);
    family_id afid = m_manager.mk_family_id("arith");
    sort* i_ty = m_manager.mk_sort(afid, INT_SORT, 0, 0);
    for(unsigned i = 0; i < num_vars; ++i) {
        add_var(i_ty);
    }
    sort* is[2] = { i_ty, i_ty };
    decl_kind kinds[7] = {OP_ADD, OP_MUL, OP_SUB, OP_LE, OP_LT, OP_GE, OP_GT };
    for (unsigned i = 0; i < 7; ++i) {
        add_func_decl(m_manager.mk_func_decl(afid, kinds[i], 0, 0, 2, is));
    }

    add_expr(u.mk_numeral(rational(0), true));
    add_expr(u.mk_numeral(rational(1), true));
    add_expr(u.mk_numeral(rational(2), true));
    add_expr(u.mk_numeral(rational(3), true));
    add_expr(u.mk_numeral(rational(6), true));
    add_expr(u.mk_numeral(rational(7), true));
    add_expr(u.mk_numeral(rational(-1), true));
    add_expr(u.mk_numeral(rational(-2), true));
}

void expr_rand::initialize_bv(unsigned num_vars) {
    bv_util u(m_manager);
    family_id bfid = m_manager.get_basic_family_id();
    family_id bvfid = m_manager.mk_family_id("bv");
    

    const unsigned num_sizes = 6;
    unsigned sizes[num_sizes] = { 1, 2, 8, 16, 24, 32 };
    parameter p1(1), p2(2), p3(3), p4(4), p8(8), p16(16), p24(24), p32(32);

    for (unsigned i = 0; i < num_sizes; ++i) {
        add_expr(u.mk_numeral(rational(0), sizes[i]));        
        add_expr(u.mk_numeral(rational(1), sizes[i]));        
    }
    add_expr(u.mk_numeral(rational(2), 2));
    add_expr(u.mk_numeral(rational(3), 2));
    add_expr(u.mk_numeral(rational(6), 8));
    add_expr(u.mk_numeral(rational(7), 8));
    add_expr(u.mk_numeral(rational(static_cast<unsigned>(-2)), 32));
    add_expr(u.mk_numeral(rational(static_cast<unsigned>(-1)), 32));

    for (unsigned i = 0; num_vars > 0; ++i, --num_vars) {
        i = i % num_sizes;
        parameter param(sizes[i]);
        add_var(m_manager.mk_sort(bvfid, BV_SORT, 1, &param));
    }
    for (unsigned i = 0; i < num_sizes; ++i) {
        parameter param(sizes[i]);
        sort* s = m_manager.mk_sort(bvfid, BV_SORT, 1, &param);
        
        sort* ss[3] = { s, s, s };
        add_func_decl(m_manager.mk_func_decl(bvfid, OP_BNEG, 0, 0, 1, ss));
        add_func_decl(m_manager.mk_func_decl(bvfid, OP_BADD, 0, 0, 2, ss));
        add_func_decl(m_manager.mk_func_decl(bvfid, OP_BSUB, 0, 0, 2, ss));
        add_func_decl(m_manager.mk_func_decl(bvfid, OP_BMUL, 0, 0, 2, ss));
        add_func_decl(m_manager.mk_func_decl(bvfid, OP_BSDIV, 0, 0, 2, ss));
        add_func_decl(m_manager.mk_func_decl(bvfid, OP_BUDIV, 0, 0, 2, ss));
        add_func_decl(m_manager.mk_func_decl(bvfid, OP_BSREM, 0, 0, 2, ss));
        add_func_decl(m_manager.mk_func_decl(bvfid, OP_BUREM, 0, 0, 2, ss));
        add_func_decl(m_manager.mk_func_decl(bvfid, OP_BSMOD, 0, 0, 2, ss));
        add_func_decl(m_manager.mk_func_decl(bvfid, OP_ULEQ, 0, 0, 2, ss));
        add_func_decl(m_manager.mk_func_decl(bvfid, OP_SLEQ, 0, 0, 2, ss));
        add_func_decl(m_manager.mk_func_decl(bvfid, OP_UGEQ, 0, 0, 2, ss));
        add_func_decl(m_manager.mk_func_decl(bvfid, OP_SGEQ, 0, 0, 2, ss));
        add_func_decl(m_manager.mk_func_decl(bvfid, OP_ULT, 0, 0, 2, ss));
        add_func_decl(m_manager.mk_func_decl(bvfid, OP_SLT, 0, 0, 2, ss));
        add_func_decl(m_manager.mk_func_decl(bvfid, OP_UGT, 0, 0, 2, ss));
        add_func_decl(m_manager.mk_func_decl(bvfid, OP_SGT, 0, 0, 2, ss));
        add_func_decl(m_manager.mk_func_decl(bvfid, OP_BAND, 0, 0, 2, ss));
        add_func_decl(m_manager.mk_func_decl(bvfid, OP_BOR, 0, 0, 2, ss));
        add_func_decl(m_manager.mk_func_decl(bvfid, OP_BNOT, 0, 0, 1, ss));
        add_func_decl(m_manager.mk_func_decl(bvfid, OP_BXOR, 0, 0, 2, ss));
        add_func_decl(m_manager.mk_func_decl(bvfid, OP_BXNOR, 0, 0, 2, ss));
        add_func_decl(m_manager.mk_func_decl(bvfid, OP_BNAND, 0, 0, 2, ss));
        add_func_decl(m_manager.mk_func_decl(bvfid, OP_BCOMP, 0, 0, 2, ss));
        add_func_decl(m_manager.mk_func_decl(bvfid, OP_BREDAND, 0, 0, 1, ss));
        add_func_decl(m_manager.mk_func_decl(bvfid, OP_BREDOR, 0, 0, 1, ss));
        add_func_decl(m_manager.mk_func_decl(bvfid, OP_BSHL, 0, 0, 2, ss));
        add_func_decl(m_manager.mk_func_decl(bvfid, OP_BLSHR, 0, 0, 2, ss));
        add_func_decl(m_manager.mk_func_decl(bvfid, OP_BASHR, 0, 0, 2, ss));

        add_func_decl(m_manager.mk_func_decl(bfid,  OP_EQ, 0, 0, 2, ss));

        add_func_decl(m_manager.mk_func_decl(bvfid, OP_ROTATE_LEFT, 1, &p1, 1, ss));
        add_func_decl(m_manager.mk_func_decl(bvfid, OP_ROTATE_RIGHT, 1, &p1, 1, ss));

    }

    sort* b8  = m_manager.mk_sort(bvfid, BV_SORT, 1, &p8);
    sort* b16 = m_manager.mk_sort(bvfid, BV_SORT, 1, &p16);
    sort* b24 = m_manager.mk_sort(bvfid, BV_SORT, 1, &p24);
    sort* b32 = m_manager.mk_sort(bvfid, BV_SORT, 1, &p32);

    // OP_CONCAT:
    {
        sort* ss[2] = { b8, b8 };
        add_func_decl(m_manager.mk_func_decl(bvfid, OP_CONCAT, 0, 0, 2, ss));
        ss[0] = b16;
        ss[1] = b8;
        add_func_decl(m_manager.mk_func_decl(bvfid, OP_CONCAT, 0, 0, 2, ss));
        ss[0] = b8;
        ss[1] = b16;
        add_func_decl(m_manager.mk_func_decl(bvfid, OP_CONCAT, 0, 0, 2, ss));
        ss[0] = b16;
        ss[1] = b16;
        add_func_decl(m_manager.mk_func_decl(bvfid, OP_CONCAT, 0, 0, 2, ss));
        ss[0] = b24;
        ss[1] = b8;
        add_func_decl(m_manager.mk_func_decl(bvfid, OP_CONCAT, 0, 0, 2, ss));
        ss[0] = b8;
        ss[1] = b24;
        add_func_decl(m_manager.mk_func_decl(bvfid, OP_CONCAT, 0, 0, 2, ss));
    }

    
    add_func_decl(m_manager.mk_func_decl(bvfid, OP_SIGN_EXT, 1, &p8, 1, &b8));
    add_func_decl(m_manager.mk_func_decl(bvfid, OP_SIGN_EXT, 1, &p8, 1, &b16));
    add_func_decl(m_manager.mk_func_decl(bvfid, OP_SIGN_EXT, 1, &p16, 1, &b8));
    add_func_decl(m_manager.mk_func_decl(bvfid, OP_SIGN_EXT, 1, &p16, 1, &b16));
    add_func_decl(m_manager.mk_func_decl(bvfid, OP_SIGN_EXT, 1, &p8, 1, &b16));
    add_func_decl(m_manager.mk_func_decl(bvfid, OP_SIGN_EXT, 1, &p16, 1, &b8));
    add_func_decl(m_manager.mk_func_decl(bvfid, OP_SIGN_EXT, 1, &p8, 1, &b24));

    add_func_decl(m_manager.mk_func_decl(bvfid, OP_ZERO_EXT, 1, &p8, 1, &b8));
    add_func_decl(m_manager.mk_func_decl(bvfid, OP_ZERO_EXT, 1, &p8, 1, &b16));
    add_func_decl(m_manager.mk_func_decl(bvfid, OP_ZERO_EXT, 1, &p16, 1, &b8));
    add_func_decl(m_manager.mk_func_decl(bvfid, OP_ZERO_EXT, 1, &p16, 1, &b16));
    add_func_decl(m_manager.mk_func_decl(bvfid, OP_ZERO_EXT, 1, &p8, 1, &b16));
    add_func_decl(m_manager.mk_func_decl(bvfid, OP_ZERO_EXT, 1, &p16, 1, &b8));
    add_func_decl(m_manager.mk_func_decl(bvfid, OP_ZERO_EXT, 1, &p8, 1, &b24));

    parameter bounds[2] = { parameter(7), parameter(0) };
    add_func_decl(m_manager.mk_func_decl(bvfid, OP_EXTRACT, 2, bounds, 1, &b32));
    bounds[0] = parameter(15);
    add_func_decl(m_manager.mk_func_decl(bvfid, OP_EXTRACT, 2, bounds, 1, &b32));
    bounds[0] = parameter(23);
    add_func_decl(m_manager.mk_func_decl(bvfid, OP_EXTRACT, 2, bounds, 1, &b32));
    bounds[1] = parameter(8);
    add_func_decl(m_manager.mk_func_decl(bvfid, OP_EXTRACT, 2, bounds, 1, &b32));
    bounds[1] = parameter(16);
    add_func_decl(m_manager.mk_func_decl(bvfid, OP_EXTRACT, 2, bounds, 1, &b32));

    add_func_decl(m_manager.mk_func_decl(bvfid, OP_REPEAT, 1, &p4, 1, &b8));
    add_func_decl(m_manager.mk_func_decl(bvfid, OP_REPEAT, 1, &p3, 1, &b8));
    add_func_decl(m_manager.mk_func_decl(bvfid, OP_REPEAT, 1, &p2, 1, &b8));
    add_func_decl(m_manager.mk_func_decl(bvfid, OP_REPEAT, 1, &p1, 1, &b8));

    /*
    OP_ROTATE_LEFT,
    OP_ROTATE_RIGHT,
    */
}

void expr_rand::initialize_array(unsigned num_vars, sort* dom, sort* rng) {
    family_id afid = m_manager.mk_family_id("array");
    parameter p1(dom), p2(rng);
    parameter ps[2] = { p1, p2 };
    sort* a = m_manager.mk_sort(afid, ARRAY_SORT, 2, ps);
    sort* ss[3] = { a, dom, rng };
    
    add_func_decl(m_manager.mk_func_decl(afid, OP_STORE, 0, 0, 3, ss));
    add_func_decl(m_manager.mk_func_decl(afid, OP_SELECT, 0, 0, 2, ss));

    for (unsigned i = 0; i < num_vars; ++i) {
        add_var(a);
    }
}

void expr_rand::initialize_basic(unsigned amplification) {
    family_id bfid = m_manager.get_basic_family_id();
    sort* bools[2] = { m_manager.mk_bool_sort(), m_manager.mk_bool_sort() };
    for (unsigned i = 0; i < amplification; ++i) {
        add_func_decl(m_manager.mk_func_decl(bfid, OP_OR, 0, 0, 2, bools));
        add_func_decl(m_manager.mk_func_decl(bfid, OP_NOT, 0, 0, 1, bools));         
    }
    map_t::iterator it  = m_nodes.begin(); 
    map_t::iterator end = m_nodes.end(); 
    for (; it != end; ++it) {
        sort* s = it->m_key;
        sort* ites[3] = { bools[0], s, s };
        add_func_decl(m_manager.mk_func_decl(bfid, OP_ITE, 0, 0, 3, ites));
    }
}
