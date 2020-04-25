#include "smt/value_generator.h"
#include <math>


class datatype_value_generator : public value_generator_core {
    ast_manager&     m;
    value_generator& g;
    datatype_util    dt;
    sort_ref_vector  m_sorts;
    obj_map<sort, expr_ref_vector*> m_values;
    obj_map<func_decl, unsigned> m_constr2seen;

    /*
      \brief inverse of the Cantor function.
      It converts an unsigned into a pair of unsigned numbers that are not
      bigger (and only equal for values 0, 1).
     */
    void inverse_cantor(unsigned z, unsigned& x, unsigned& y) {
        unsigned w = (sqrt(8*z + 1) - 1)/2;
        unsigned t = (w*w + 2)/2;
        y = z - t;
        x = w - y;
    }

    unsigned_vector inf;
    void index2vector(unsigned z, func_decl* c, unsigned_vector& v) {
        unsigned arity = c->get_arity();
        v.resize(arity);
        inf.reset();
        for (unsigned i = 0; i < arity; ++i) {
            sort* s = c->get_domain(i);
            sort_size const& sz = s->get_num_elements();
            if (sz.is_finite() && sz.size() < (UINT_MAX >> 12)) {
                v[i] = z % sz.size();
                z /= sz.size();
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

public:
    datatype_value_generator(value_generator& g, ast_manager& m):
        m(m), g(g), dt(m), m_values(m) {}
   
    ~datatype_value_generator() {
        for (auto& kv : m_values) dealloc(kv.m_value);
    }

    family_id get_fid() const override { 
        return dt.get_family_id(); 
    }

    expr* get_value(sort* s, unsigned index) override {
        expr_ref_vector* vp = nullptr;
        if (!m_values.contains(s, vp)) {
            vp = allocate(expr_ref_vector, m);
            for (auto* c : *dt.get_datatype_constructors(s)) {
                if (c->get_arity() == 0)
                    vp->push_back(m.mk_app(c));
            }
            m_values.insert(s, vp);
        }
        auto& v = *vp;
        expr_ref_vector args(m);
        bool some_valid = true;
        while (v.size() <= index && some_valid) {
            some_valid = false;
            for (auto* c : *dt.get_datatype_constructors(s)) {
                unsigned arity = c->get_arity();
                if (arity == 0)
                    continue;
                args.resize(c->get_arity());
                unsigned j = 0;
                m_constr2seen.find(c, j);
                m_constr2seen.insert(c, j+1);
                if (beyond_domain_size(j, c))
                    continue;
                index2vector(j, c, indices);
                bool valid = true;
                // still does not ensure non-termination when 
                // 0 is used on a left-recursive datatype constructor
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
        return v.get(index, nullptr);
    }
};


class arith_value_generator : public value_generator_core {
    ast_manager&     m;
    arith_util       a;
    int u2i(unsigned u) {
        if (0 == (u % 2))
            return u/2;
        else
            return -((u+1)/2);
    }
public:
    arith_value_generator(ast_manager& m): m(m), a(m) {}

    family_id get_fid() const override { 
        return a.get_family_id(); 
    }

    expr* get_value(sort* s, unsigned index) override {
        if (a.is_int(s)) {
            return a.mk_int(u2i(index));
        }
        if (index == 0) 
            return a.mk_real(rational(0));
        unsigned x, y;
        // still imperfect as y could divide x
        inverse_cantor(index/2, x, y);
        x++; 
        y++;
        if (index % 2 == 0) x = -x;
        return a.mk_real(rational(x, y));               
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

    expr* get_value(sort* s, unsigned index) override {
        unsigned sz = 0;
        bv.get_bv_size(s, sz);
        if (sz < 30 && index >= (1 << sz))
            return nullptr;
        return bv.mk_numeral(index, s);
    }
};

class bool_value_generator : public value_generator_core {
    ast_manager& m;
public:
    bool_value_generator(ast_manager& m): m(m) {}

    family_id get_fid() const override { 
        return m.get_family_id(); 
    }

    expr* get_value(sort* s, unsigned index) override {
        if (!m.is_bool(s))
            return nullptr;
        if (index == 0)
            return m.mk_false();
        if (index == 1)
            return m.mk_true();
        return nullptr;
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
    // seq_value_generator
    // fp_value_generator
    // array_value_generator
    // uninterp_sort_value_generator
}

void value_generator::add_plugin(value_generator_core* v) {
    m_plugins.reserve(v->get_fid() + 1);
    m_plugins.set(v->get_fid(), v);
}

expr* value_generator::get_value(sort* s, unsigned index) {
    init();
    famiily_id fid = s->get_family_id();
    auto* p = m_plugins.get(fid, nullptr);
    return p ? p->get_value(s, index) : nullptr;
}
