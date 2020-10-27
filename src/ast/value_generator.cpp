/*++
  Copyright (c) 2020 Microsoft Corporation

  Module Name:

   value_generatorr.cpp

  Abstract:
   
    Generate mostly different values using index as seed.

  Author:

    Nikolaj Bjorner 2020-04-25

--*/

#include "ast/value_generator.h"
#include "ast/datatype_decl_plugin.h"
#include "ast/array_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/bv_decl_plugin.h"
#include "ast/seq_decl_plugin.h"
#include <cmath>



/*
  \brief inverse of the Cantor function.
  It converts an unsigned into a pair of unsigned numbers that are not
  bigger (and only equal for values 0, 1).
*/
static void inverse_cantor(unsigned z, unsigned& x, unsigned& y) {
    unsigned w = ((unsigned)sqrt(static_cast<double>(8*z + 1)) - 1)/2;
    unsigned t = (unsigned)(w*w + w)/2;
    y = z - t;
    x = w - y;
}

static bool is_small_size(sort_size const& sz) {
    return sz.is_finite() && sz.size() < (UINT_MAX >> 12);
}

class datatype_value_generator : public value_generator_core {
    ast_manager&     m;
    value_generator& g;
    datatype_util    dt;
    sort_ref_vector  m_sorts;
    obj_map<sort, expr_ref_vector*> m_values;
    obj_map<func_decl, unsigned> m_constr2seen;
    random_gen       m_rand;
        
    unsigned_vector inf;
    void index2vector(unsigned z, func_decl* c, unsigned_vector& v) {
        unsigned arity = c->get_arity();
        v.resize(arity);
        inf.reset();
        for (unsigned i = 0; i < arity; ++i) {
            sort* s = c->get_domain(i);
            sort_size const& sz = s->get_num_elements();
            if (is_small_size(sz)) {
                v[i] = z % sz.size();
                z = z/((unsigned)sz.size());
            }
            else {
                inf.push_back(i);
            }
        }
        // fill in values for large domains
        for (unsigned i = 0; i + 1 < inf.size(); ++i) {
            inverse_cantor(z, v[inf[i]], z);        
        }
        if (!inf.empty()) {
            v[inf.back()] = z;   
        } 
    }

    bool domain_size_exhausted(unsigned j, func_decl* c) {
        unsigned arity = c->get_arity();
        uint64_t dsz = 1;
        for (unsigned i = 0; i < arity; ++i) {
            sort* s = c->get_domain(i);
            sort_size const& sz = s->get_num_elements();
            if (is_small_size(sz)) {
                dsz *= sz.size();
            }
            else {
                return false;
            }
            if (dsz > j) {
                return false;
            }
        }
        return j >= dsz;
    }


public:
    datatype_value_generator(value_generator& g, ast_manager& m):
        m(m), g(g), dt(m), m_sorts(m) {}
   
    ~datatype_value_generator() {
        for (auto& kv : m_values) dealloc(kv.m_value);
    }

    family_id get_fid() const override { 
        return dt.get_family_id(); 
    }

    /*
      In the off chance that a recursive datatype constructor is left recursive and has no base case on its own
      we iterate over constructors in a random order to make sure to hit the base cases eventually.
      In such cases m_constr2seen might not get updated accurately and we admit repetitions. 
      
     */
    unsigned_vector indices;
    expr_ref get_value(sort* s, unsigned index) override {
        expr_ref_vector* vp = nullptr;
        if (!m_values.find(s, vp)) {
            vp = alloc(expr_ref_vector, m);
            for (auto* c : *dt.get_datatype_constructors(s)) {
                if (c->get_arity() == 0)
                    vp->push_back(m.mk_const(c));
            }
            m_values.insert(s, vp);
            m_sorts.push_back(s);
        }
        auto& v = *vp;
        expr_ref_vector args(m);
        bool some_valid = true;
        while (v.size() <= index && some_valid) {
            some_valid = false;
            auto const& decls = *dt.get_datatype_constructors(s);
            int start = m_rand();
            for (unsigned i = 0; i < decls.size(); ++i) { 
                func_decl* c = decls[(i + start) % decls.size()];
                unsigned arity = c->get_arity();
                if (arity == 0)
                    continue;
                args.resize(c->get_arity());
                unsigned j = 0;
                m_constr2seen.find(c, j);
                if (domain_size_exhausted(j, c))
                    continue;
                m_constr2seen.insert(c, j + 1);
                index2vector(j, c, indices);
                bool valid = true;
                for (unsigned i = 0; valid && i < args.size(); ++i) {
                    args[i] = g.get_value(c->get_domain(i), indices[i]);
                    valid &= args.get(i) != nullptr;
                }
                if (valid) {
                    v.push_back(m.mk_app(c, args));
                    some_valid = true;
                }
            }
        }
        return expr_ref(v.get(index, nullptr), m);
    }
};


class arith_value_generator : public value_generator_core {
    ast_manager&     m;
    arith_util       a;
    int u2i(unsigned u) {
        if (0 == (u % 2))
            return u/2;
        else
            return -(int)((u+1)/2);
    }

    void calkin_wilf(unsigned i, unsigned& x, unsigned& y) {
        while (i > 1) {
            if (i % 2 == 0) {
                x += y;                
            }
            else {
                y += x;
            }
            i /= 2;
        }
    }

public:
    arith_value_generator(ast_manager& m): m(m), a(m) {}

    family_id get_fid() const override { 
        return a.get_family_id(); 
    }

    expr_ref get_value(sort* s, unsigned index) override {
        if (a.is_int(s)) {
            return expr_ref(a.mk_int(u2i(index)), m);
        }
        if (index == 0) 
            return expr_ref(a.mk_real(rational(0)), m);
        unsigned x = 1, y = 1;
        calkin_wilf((index/2) + 1, x, y);
        if ((index % 2) == 0) x = -(int)x;
        return expr_ref(a.mk_real(rational(x, y)), m);
    }    
};

class seq_value_generator : public value_generator_core {
    ast_manager&  m;
    value_generator& g;
    seq_util      seq;
public:
    seq_value_generator(value_generator& g, ast_manager& m): m(m), g(g), seq(m) {}

    family_id get_fid() const override { 
        return seq.get_family_id(); 
    }

    expr_ref get_value(sort* s, unsigned index) override {
        sort* elem_sort = nullptr;
        if (!seq.is_seq(s, elem_sort)) {
            return expr_ref(m.mk_fresh_const("re", s), m);
        }
        if (index == 0) {
            return expr_ref(seq.str.mk_empty(s), m);
        }
        --index;
        sort_size const& sz = elem_sort->get_num_elements();
        expr_ref_vector es(m);
        unsigned idx = 0;
        if (is_small_size(sz)) {
            // TBD: could also use a Gray-code version
            // TBD: could also prefer longer sequences
            unsigned esz = (unsigned)sz.size();
            index += esz;
            do {
                idx = index % esz; 
                expr_ref elem = g.get_value(elem_sort, idx);
                es.push_back(seq.str.mk_unit(elem));
                index /= esz;
            }
            while (index >= esz);
        }
        else {
            do {
                inverse_cantor(index, idx, index);
                expr_ref elem = g.get_value(elem_sort, idx);
                es.push_back(seq.str.mk_unit(elem));
            }
            while (index > 0);
        }
        return expr_ref(seq.str.mk_concat(es, s), m);
    }    
};


class array_value_generator : public value_generator_core {
    ast_manager&     m;
    value_generator& g;
    array_util       a;
public:
    array_value_generator(value_generator& g, ast_manager& m): m(m), g(g), a(m) {}

    family_id get_fid() const override { 
        return a.get_family_id(); 
    }

    // if both domain and range are finite, this will create repetitions.
    // overall, finite domain arrays can be handled separately
    // repetitions also happen when the same set of indices are updated twice

    expr_ref get_value(sort* s, unsigned index) override {
        unsigned arity = get_array_arity(s);
        sort* r = get_array_range(s);
        sort_size const& sz = r->get_num_elements();
        if (sz.is_finite() && sz.size() == 1) {
            return expr_ref(a.mk_const_array(s, g.get_value(r, 0)), m);           
        }
        
        unsigned z = 0;
        if (is_small_size(sz)) {
            z = index % sz.size();
            index = index / (unsigned)sz.size();
        }
        else {
            inverse_cantor(index, z, index);
        }
        expr_ref result(a.mk_const_array(s, g.get_value(r, z)), m);
        unsigned default_index = z;
        expr_ref_vector args(m);
        unsigned_vector inf;
        args.resize(arity+2);
        while (index > 0) {            
            args[0] = result;
            for (unsigned i = 0; i < arity; ++i) {
                sort* d = get_array_domain(s, i);
                sort_size const& dsz = d->get_num_elements();
                if (is_small_size(dsz)) {
                    args[1 + i] = g.get_value(d, index % dsz.size());
                    index = index / ((unsigned)dsz.size());
                }
                else {
                    inf.push_back(i);
                }
            }
            for (unsigned i : inf) {
                inverse_cantor(index, z, index);
                args[1 + i] = g.get_value(get_array_domain(s, i), z);
            }

            // ensure z is different from default_index.
            if (is_small_size(sz)) {
                z = index % (sz.size() - 1);
                index = index / (unsigned)sz.size();
            }
            else {
                inverse_cantor(index, z, index);
            }
            if (z >= default_index) z++;
            args[arity+1] = g.get_value(r, z);
            result = a.mk_store(args);
        }
        
        return result;
    }    
};

class bv_value_generator : public value_generator_core {
    ast_manager& m;
    bv_util bv;
public:
    bv_value_generator(ast_manager& m): m(m), bv(m) {}

    family_id get_fid() const override { 
        return bv.get_family_id(); 
    }

    expr_ref get_value(sort* s, unsigned index) override {
        index %= bv.get_bv_size(s);
        return expr_ref(bv.mk_numeral(rational(index), s), m);
    }
};

class bool_value_generator : public value_generator_core {
    ast_manager& m;
public:
    bool_value_generator(ast_manager& m): m(m) {}

    family_id get_fid() const override { 
        return m.get_basic_family_id(); 
    }

    expr_ref get_value(sort* s, unsigned index) override {
        if (!m.is_bool(s))
            return expr_ref(m.mk_fresh_const("basic", s), m);
        if (index % 2 == 0)
            return expr_ref(m.mk_false(), m);
        return expr_ref(m.mk_true(), m);
    }
};

    
value_generator::value_generator(ast_manager& m): m(m) {
}

void value_generator::init() {
    if (!m_plugins.empty())
        return;
    add_plugin(alloc(datatype_value_generator, *this, m));
    add_plugin(alloc(arith_value_generator, m));
    add_plugin(alloc(bv_value_generator, m));
    add_plugin(alloc(bool_value_generator, m));
    add_plugin(alloc(seq_value_generator, *this, m));
    add_plugin(alloc(array_value_generator, *this, m));
    // fp_value_generator
    // uninterp_sort_value_generator
}

void value_generator::add_plugin(value_generator_core* v) {
    m_plugins.reserve(v->get_fid() + 1);
    m_plugins.set(v->get_fid(), v);
}

expr_ref value_generator::get_value(sort* s, unsigned index) {
    init();
    auto fid = s->get_family_id();
    auto* p = m_plugins.get(fid, nullptr);
    return p ? p->get_value(s, index) : expr_ref(m.mk_fresh_const(s->get_name(), s), m);
}
