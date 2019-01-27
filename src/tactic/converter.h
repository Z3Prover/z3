/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    converter.h

Abstract:

    Abstract class and templates for proof and model converters.

Author:

    Leonardo (leonardo) 2011-11-14

Notes:

--*/
#ifndef CONVERTER_H_
#define CONVERTER_H_

#include "util/vector.h"
#include "util/ref.h"
#include "ast/ast_translation.h"

class converter {
    unsigned m_ref_count;
public:
    converter():m_ref_count(0) {}
    virtual ~converter() {}

    void inc_ref() { ++m_ref_count;  }

    void dec_ref() { 
        --m_ref_count;
        if (m_ref_count == 0) {
            dealloc(this);
        }
    }

    virtual void cancel() {}
    
    virtual void display(std::ostream & out) = 0;
};

template<typename T>
class concat_converter : public T {
protected:
    ref<T> m_c1;
    ref<T> m_c2;

    template<typename T2>
    T * translate_core(ast_translation & translator) {
        T * t1 = m_c1->translate(translator);
        T * t2 = m_c2->translate(translator);
        return alloc(T2, t1, t2);
    }

public:
    concat_converter(T * c1, T * c2):m_c1(c1), m_c2(c2) {}
    
    ~concat_converter() override {}

    void cancel() override {
        m_c2->cancel();
        m_c1->cancel();
    }

    virtual char const * get_name() const = 0;
    
    void display(std::ostream & out) override {
        m_c1->display(out);
        m_c2->display(out);
    }
};

template<typename T>
class concat_star_converter : public T {
protected:
    ref<T>          m_c1;
    ptr_vector<T>   m_c2s;
    unsigned_vector m_szs;

    template<typename T2>
    T * translate_core(ast_translation & translator) {
        T * t1 = m_c1 ? m_c1->translate(translator) : nullptr;
        ptr_buffer<T> t2s;
        for (T* c : m_c2s)
            t2s.push_back(c ? c->translate(translator) : nullptr);
        return alloc(T2, t1, m_c2s.size(), t2s.c_ptr(), m_szs.c_ptr());
    }

public:
    concat_star_converter(T * c1, unsigned num, T * const * c2s, unsigned * szs):
        m_c1(c1) {
        for (unsigned i = 0; i < num; i++) {
            T * c2 = c2s[i];
            if (c2)
                c2->inc_ref();
            m_c2s.push_back(c2);
            m_szs.push_back(szs[i]);
        }
    }

    ~concat_star_converter() override {
        for (T* c : m_c2s)
            if (c) c->dec_ref();
    }

    void cancel() override {
        if (m_c1)
            m_c1->cancel();
        for (T* c : m_c2s)
            if (c) c->cancel();
    }

    virtual char const * get_name() const = 0;
    
    void display(std::ostream & out) override {
        if (m_c1)
            m_c1->display(out);
        for (T* c : m_c2s) 
            if (c) c->display(out);
    }
};

#endif

