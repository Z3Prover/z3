/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    model_converter.h

Abstract:

    Abstract interface for converting models.

Author:

    Leonardo (leonardo) 2011-04-21

Notes:

--*/
#include"model_converter.h"
#include"model_v2_pp.h"

class concat_model_converter : public concat_converter<model_converter> {
public:
    concat_model_converter(model_converter * mc1, model_converter * mc2):concat_converter<model_converter>(mc1, mc2) {}

    virtual void operator()(model_ref & m) {
        this->m_c2->operator()(m);
        this->m_c1->operator()(m);
    }

    virtual void operator()(model_ref & m, unsigned goal_idx) {
        this->m_c2->operator()(m, goal_idx);
        this->m_c1->operator()(m, 0);
    }

    virtual void operator()(labels_vec & r, unsigned goal_idx) {
        this->m_c2->operator()(r, goal_idx);
        this->m_c1->operator()(r, 0);
    }

  
    virtual char const * get_name() const { return "concat-model-converter"; }

    virtual model_converter * translate(ast_translation & translator) {
        return this->translate_core<concat_model_converter>(translator);
    }
};

model_converter * concat(model_converter * mc1, model_converter * mc2) {
    if (mc1 == 0)
        return mc2;
    if (mc2 == 0)
        return mc1;
    return alloc(concat_model_converter, mc1, mc2);
}

class concat_star_model_converter : public concat_star_converter<model_converter> {
public:
    concat_star_model_converter(model_converter * mc1, unsigned num, model_converter * const * mc2s, unsigned * szs):
        concat_star_converter<model_converter>(mc1, num, mc2s, szs) {
    }

    virtual void operator()(model_ref & m) {
        // TODO: delete method after conversion is complete
        UNREACHABLE();
    }

    virtual void operator()(model_ref & m, unsigned goal_idx) {
        unsigned num = this->m_c2s.size();
        for (unsigned i = 0; i < num; i++) {
            if (goal_idx < this->m_szs[i]) {
                // found the model converter that should be used
                model_converter * c2 = this->m_c2s[i];
                if (c2)
                    c2->operator()(m, goal_idx);
                if (m_c1)
                    this->m_c1->operator()(m, i);
                return;
            }
            // invalid goal
            goal_idx -= this->m_szs[i];
        }
        UNREACHABLE();
    }

    virtual void operator()(labels_vec & r, unsigned goal_idx) {
        unsigned num = this->m_c2s.size();
        for (unsigned i = 0; i < num; i++) {
            if (goal_idx < this->m_szs[i]) {
                // found the model converter that should be used
                model_converter * c2 = this->m_c2s[i];
                if (c2)
                  c2->operator()(r, goal_idx);
                if (m_c1)
                  this->m_c1->operator()(r, i);
                return;
            }
            // invalid goal
            goal_idx -= this->m_szs[i];
        }
        UNREACHABLE();
    }
    
    virtual char const * get_name() const { return "concat-star-model-converter"; }

    virtual model_converter * translate(ast_translation & translator) {
        return this->translate_core<concat_star_model_converter>(translator);
    }
};

model_converter * concat(model_converter * mc1, unsigned num, model_converter * const * mc2s, unsigned * szs) {
    SASSERT(num > 0);
    if (num == 1)
        return concat(mc1, mc2s[0]);
    unsigned i;
    for (i = 0; i < num; i++) {
        if (mc2s[i] != 0)
            break;
    }
    if (i == num) {
        // all mc2s are 0
        return mc1;
    }
    return alloc(concat_star_model_converter, mc1, num, mc2s, szs);
}

class model2mc : public model_converter {
    model_ref m_model;
    buffer<symbol> m_labels;
public:
    model2mc(model * m):m_model(m) {}

    model2mc(model * m, buffer<symbol> const & r):m_model(m), m_labels(r) {}

    virtual ~model2mc() {}

    virtual void operator()(model_ref & m) {
        m = m_model;
    }

    virtual void operator()(model_ref & m, unsigned goal_idx) {
        m = m_model;
    }

    virtual void operator()(labels_vec & r, unsigned goal_idx) {
      r.append(m_labels.size(), m_labels.c_ptr());
    }

  virtual void cancel() {
    }
    
    virtual void display(std::ostream & out) {
        out << "(model->model-converter-wrapper\n";
        model_v2_pp(out, *m_model);
        out << ")\n";
    }    
    
    virtual model_converter * translate(ast_translation & translator) {
        model * m = m_model->translate(translator);
        return alloc(model2mc, m);
    }
};

model_converter * model2model_converter(model * m) {
    if (m == 0)
        return 0;
    return alloc(model2mc, m);
}

model_converter * model_and_labels2model_converter(model * m, buffer<symbol> & r) {
    if (m == 0)
        return 0;
    return alloc(model2mc, m, r);
}

void model_converter2model(ast_manager & mng, model_converter * mc, model_ref & m) {
    if (mc) {
        m = alloc(model, mng);
        (*mc)(m, 0);
    }
}

void apply(model_converter_ref & mc, model_ref & m, unsigned gidx) {
    if (mc) {
        (*mc)(m, gidx);
    }
}

