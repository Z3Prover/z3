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
#include"model.h"
#include"model_pp.h"
#include"model_converter.h"
#include"bv_decl_plugin.h"
#include"ast_smt2_pp.h"

/**
   If TO_BOOL == true, then bit-vectors of size n were blasted into n-tuples of Booleans.
   If TO_BOOL == false, then bit-vectors of size n were blasted into n-tuples of bit-vectors of size 1.
*/
template<bool TO_BOOL>
struct bit_blaster_model_converter : public model_converter {
    func_decl_ref_vector      m_vars;
    expr_ref_vector           m_bits;

    ast_manager & m() const { return m_vars.get_manager(); }
    
    bit_blaster_model_converter(ast_manager & m, obj_map<func_decl, expr*> const & const2bits):m_vars(m), m_bits(m) {
        obj_map<func_decl, expr*>::iterator it  = const2bits.begin();
        obj_map<func_decl, expr*>::iterator end = const2bits.end();
        for (; it != end; ++it) {
            func_decl * v = it->m_key;
            expr * bits   = it->m_value;
            SASSERT(!TO_BOOL || is_app_of(bits, m.get_family_id("bv"), OP_MKBV));
            SASSERT(TO_BOOL  || is_app_of(bits, m.get_family_id("bv"), OP_CONCAT));
            m_vars.push_back(v);
            m_bits.push_back(bits);
        }
    }
    
    virtual ~bit_blaster_model_converter() {
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
                    // remark: if old_model does not assign bit_val, then assume it is false.
                    if (bit_val != 0 && m().is_true(bit_val))
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
                    if (bit_val != 0 && !util.is_zero(bit_val))
                        val++;
                }
            }
            expr * new_val = util.mk_numeral(val, bv_sz);
            new_model->register_decl(m_vars.get(i), new_val);
        }
    }

    virtual void operator()(model_ref & md, unsigned goal_idx) {
        SASSERT(goal_idx == 0);
        model * new_model = alloc(model, m());
        obj_hashtable<func_decl> bits;
        collect_bits(bits);
        copy_non_bits(bits, md.get(), new_model);
        mk_bvs(md.get(), new_model);
        md = new_model;
    }

    virtual void operator()(model_ref & md) {
        operator()(md, 0);
    }
    
    virtual void display(std::ostream & out) {
        out << "(bit-blaster-model-converter";
        unsigned sz = m_vars.size();
        for (unsigned i = 0; i < sz; i++) {
            out << "\n  (" << m_vars.get(i)->get_name() << " ";
            unsigned indent = m_vars.get(i)->get_name().size() + 4;
            out << mk_ismt2_pp(m_bits.get(i), m(), indent) << ")";
        }   
        out << ")" << std::endl;
    }

protected:
    bit_blaster_model_converter(ast_manager & m):m_vars(m), m_bits(m) { }
public:

    virtual model_converter * translate(ast_translation & translator) {
        bit_blaster_model_converter * res = alloc(bit_blaster_model_converter, translator.to());
        for (unsigned i = 0; i < m_vars.size(); i++)
            res->m_vars.push_back(translator(m_vars[i].get()));
        for (unsigned i = 0; i < m_bits.size(); i++)
            res->m_bits.push_back(translator(m_bits[i].get()));
        return res;
    }
};

model_converter * mk_bit_blaster_model_converter(ast_manager & m, obj_map<func_decl, expr*> const & const2bits) {
    return alloc(bit_blaster_model_converter<true>, m, const2bits);
}

model_converter * mk_bv1_blaster_model_converter(ast_manager & m, obj_map<func_decl, expr*> const & const2bits) {
    return alloc(bit_blaster_model_converter<false>, m, const2bits);
}


