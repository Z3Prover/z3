/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    bit_blaster_model_convert.cpp

Abstract:

    Model converter for bit-blasting tactics.

Author:

    Leonardo (leonardo) 2011-05-09

Notes:

--*/
#include "model/model.h"
#include "model/model_pp.h"
#include "tactic/model_converter.h"
#include "ast/bv_decl_plugin.h"
#include "ast/ast_smt2_pp.h"
#include "ast/ast_util.h"

/**
   If TO_BOOL == true, then bit-vectors of size n were blasted into n-tuples of Booleans.
   If TO_BOOL == false, then bit-vectors of size n were blasted into n-tuples of bit-vectors of size 1.
*/
template<bool TO_BOOL>
struct bit_blaster_model_converter : public model_converter {
    func_decl_ref_vector      m_vars;
    expr_ref_vector           m_bits;
    func_decl_ref_vector      m_newbits;

    ast_manager & m() const { return m_vars.get_manager(); }
    
    bit_blaster_model_converter(
        ast_manager & m, 
        obj_map<func_decl, expr*> const & const2bits, 
        ptr_vector<func_decl> const& newbits):
        m_vars(m), m_bits(m), m_newbits(m) {
        for (auto const& kv : const2bits) {
            func_decl * v = kv.m_key;
            expr * bits   = kv.m_value;
            SASSERT(!TO_BOOL || is_app_of(bits, m.get_family_id("bv"), OP_MKBV));
            SASSERT(TO_BOOL  || is_app_of(bits, m.get_family_id("bv"), OP_CONCAT));
            m_vars.push_back(v);
            m_bits.push_back(bits);
        }
        for (func_decl* f : newbits) 
            m_newbits.push_back(f);
    }
    
    ~bit_blaster_model_converter() override {
    }
    
    void collect_bits(obj_hashtable<func_decl> & bits) {
        unsigned sz = m_bits.size();
        for (unsigned i = 0; i < sz; i++) {
            expr * bs = m_bits.get(i);
            SASSERT(!TO_BOOL || is_app_of(bs, m().get_family_id("bv"), OP_MKBV));
            SASSERT(TO_BOOL  || is_app_of(bs, m().get_family_id("bv"), OP_CONCAT));
            unsigned num_args = to_app(bs)->get_num_args();
            for (unsigned j = 0; j < num_args; j++) {
                expr * bit = to_app(bs)->get_arg(j);
                SASSERT(!TO_BOOL || m().is_bool(bit)); 
                SASSERT(TO_BOOL ||  is_sort_of(m().get_sort(bit), m().get_family_id("bv"), BV_SORT));
                SASSERT(is_uninterp_const(bit));
                bits.insert(to_app(bit)->get_decl());
            }
        }
        TRACE("blaster_mc",
              tout << "bits that should not be included in the model:\n";
              obj_hashtable<func_decl>::iterator it  = bits.begin();
              obj_hashtable<func_decl>::iterator end = bits.end();
              for (; it != end; ++it) {
                  tout << (*it)->get_name() << " ";
              }
              tout << "\n";);

    }
    
    void copy_non_bits(obj_hashtable<func_decl> & bits, model * old_model, model * new_model) {
        unsigned num = old_model->get_num_constants();
        for (unsigned i = 0; i < num; i++) {
            func_decl * f = old_model->get_constant(i);
            if (bits.contains(f))
                continue;
            TRACE("blaster_mc", tout << "non-bit: " << f->get_name() << "\n";);
            expr * fi     = old_model->get_const_interp(f);
            new_model->register_decl(f, fi);
        }
        TRACE("blaster_mc", tout << "after copy non bits:\n"; model_pp(tout, *new_model););
        new_model->copy_func_interps(*old_model);
        new_model->copy_usort_interps(*old_model);
        TRACE("blaster_mc", tout << "after copying functions and sorts:\n"; model_pp(tout, *new_model););
    }
    
    void mk_bvs(model * old_model, model * new_model) {
        bv_util util(m());
        rational val;
        rational two(2);
        SASSERT(m_vars.size() == m_bits.size());
        unsigned sz = m_vars.size();
        for (unsigned i = 0; i < sz; i++) {
            expr* new_val = old_model->get_const_interp(m_vars.get(i));
            if (new_val) {
                new_model->register_decl(m_vars.get(i), new_val);
                continue;
            }
            expr * bs = m_bits.get(i);
            val.reset();
            unsigned bv_sz = to_app(bs)->get_num_args();
            if (TO_BOOL) {
                SASSERT(is_app_of(bs, m().get_family_id("bv"), OP_MKBV));
                unsigned j = bv_sz;
                while (j > 0) {
                    --j;
                    val *= two;
                    expr * bit = to_app(bs)->get_arg(j);
                    SASSERT(m().is_bool(bit));
                    SASSERT(is_uninterp_const(bit));
                    func_decl * bit_decl = to_app(bit)->get_decl();
                    expr * bit_val = old_model->get_const_interp(bit_decl);
                    if (bit_val != nullptr && m().is_true(bit_val))
                        val++;
                }
            }
            else {
                SASSERT(is_app_of(bs, m().get_family_id("bv"), OP_CONCAT));
                for (unsigned j = 0; j < bv_sz; j++) {
                    val *= two;
                    expr * bit = to_app(bs)->get_arg(j);
                    SASSERT(util.is_bv(bit));
                    SASSERT(util.get_bv_size(bit) == 1);
                    SASSERT(is_uninterp_const(bit));
                    func_decl * bit_decl = to_app(bit)->get_decl();
                    expr * bit_val = old_model->get_const_interp(bit_decl);
                    // remark: if old_model does not assign bit_val, then assume it is false.
                    if (bit_val != nullptr && !util.is_zero(bit_val))
                        val++;
                }
            }
            new_val = util.mk_numeral(val, bv_sz);
            new_model->register_decl(m_vars.get(i), new_val);
        }
    }

    app_ref mk_bv(expr* bs, model& old_model) {
        bv_util util(m());
        unsigned bv_sz = to_app(bs)->get_num_args();
        expr_ref_vector args(m());
        app_ref result(m());
        for (expr * bit : *to_app(bs)) {
            SASSERT(is_uninterp_const(bit));
            func_decl * bit_decl = to_app(bit)->get_decl();
            expr * bit_val = old_model.get_const_interp(bit_decl);
            args.push_back(bit_val ? bit_val : bit);
        }

        if (TO_BOOL) {
            SASSERT(is_app_of(bs, m().get_family_id("bv"), OP_MKBV));
            result = util.mk_bv(bv_sz, args.c_ptr());
        }
        else {
            SASSERT(is_app_of(bs, m().get_family_id("bv"), OP_CONCAT));
            result = util.mk_concat(bv_sz, args.c_ptr());
        }
        return result;
    }

    void operator()(model_ref & md) override {
        model * new_model = alloc(model, m());
        obj_hashtable<func_decl> bits;
        collect_bits(bits);
        copy_non_bits(bits, md.get(), new_model);
        mk_bvs(md.get(), new_model);
        md = new_model;
    }

    /**
       \brief simplisic expansion operator for formulas.
       It just adds back bit-vector definitions to the formula whether they are used or not.

     */
    void operator()(expr_ref& fml) override {
        unsigned sz = m_vars.size();
        if (sz == 0) return;
        expr_ref_vector fmls(m());
        fmls.push_back(fml);
        for (unsigned i = 0; i < sz; i++) {
            fmls.push_back(m().mk_eq(m().mk_const(m_vars.get(i)), m_bits.get(i)));
        }        
        m_vars.reset();
        m_bits.reset();
        fml = mk_and(fmls);
    }
    
    void display(std::ostream & out) override {
        for (func_decl * f : m_newbits) 
            display_del(out, f);
        unsigned sz = m_vars.size();
        for (unsigned i = 0; i < sz; i++) 
            display_add(out, m(), m_vars.get(i), m_bits.get(i));
    }

    void get_units(obj_map<expr, bool>& units) override {
        // no-op
    }

protected:
    bit_blaster_model_converter(ast_manager & m):m_vars(m), m_bits(m), m_newbits(m) { }
public:

    model_converter * translate(ast_translation & translator) override {
        bit_blaster_model_converter * res = alloc(bit_blaster_model_converter, translator.to());
        for (func_decl * v : m_vars) 
            res->m_vars.push_back(translator(v));
        for (expr* b : m_bits)
            res->m_bits.push_back(translator(b));
        for (func_decl* f : m_newbits)
            res->m_newbits.push_back(translator(f));
        return res;
    }
};

model_converter * mk_bit_blaster_model_converter(ast_manager & m, obj_map<func_decl, expr*> const & const2bits, ptr_vector<func_decl> const& newbits) {
    return const2bits.empty() ? nullptr : alloc(bit_blaster_model_converter<true>, m, const2bits, newbits);
}

model_converter * mk_bv1_blaster_model_converter(ast_manager & m, obj_map<func_decl, expr*> const & const2bits, ptr_vector<func_decl> const& newbits) {
    return const2bits.empty() ? nullptr : alloc(bit_blaster_model_converter<false>, m, const2bits, newbits);
}


