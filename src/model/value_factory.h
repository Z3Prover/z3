/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    value_factory.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-10-28.

Revision History:

--*/
#pragma once

#include "ast/ast.h"
#include "util/obj_hashtable.h"

/**
   \brief Auxiliary object used during model construction.
*/
class value_factory {
protected:
    ast_manager & m_manager;
    family_id     m_fid;
public:
    value_factory(ast_manager & m, family_id fid);

    virtual ~value_factory();

    /**
       \brief Return some value of the given sort. The result is always different from zero.
    */
    virtual expr * get_some_value(sort * s) = 0;

    /**
       \brief Return two distinct values of the given sort. The results are stored in v1 and v2.
       Return false if the intended interpretation of the given sort has only one element. 
    */
    virtual bool get_some_values(sort * s, expr_ref & v1, expr_ref & v2) = 0;
    
    /**
       \brief Return a fresh value of the given sort. 
       Return 0 if it is not possible to do that (e.g., the sort is finite).
    */
    virtual expr * get_fresh_value(sort * s) = 0;

    /**
       \brief Used to register that the given value was used in model construction.
       So, get_fresh_value cannot return this value anymore.
    */
    virtual void register_value(expr * n) = 0;

    family_id get_family_id() const { return m_fid; }
};

class basic_factory : public value_factory {
public:
    basic_factory(ast_manager & m);
    
    expr * get_some_value(sort * s) override;

    bool get_some_values(sort * s, expr_ref & v1, expr_ref & v2) override;
    
    expr * get_fresh_value(sort * s) override;

    void register_value(expr * n) override { }
};

/**
   \brief Template for value factories for numeric (and enumeration-like) sorts
*/
template<typename Number>
class simple_factory : public value_factory {
protected:
    struct value_set {
        obj_hashtable<expr> m_values;
        Number              m_next;
        value_set():
            m_next(0) {
        }
    };
    
    typedef obj_map<sort, value_set *> sort2value_set;
    
    sort2value_set         m_sort2value_set;
    expr_ref_vector        m_values;
    sort_ref_vector        m_sorts;
    ptr_vector<value_set>  m_sets;

    value_set * get_value_set(sort * s) {
        value_set * set = nullptr;
        if (!m_sort2value_set.find(s, set)) {
            set = alloc(value_set);
            m_sort2value_set.insert(s, set);
            m_sorts.push_back(s);
            m_sets.push_back(set);
        }
        SASSERT(set != 0);
        DEBUG_CODE({
            value_set * set2 = 0;
            SASSERT(m_sort2value_set.find(s, set2));
            SASSERT(set == set2);
        });
        return set;
    }

    virtual app * mk_value_core(Number const & val, sort * s) = 0;

    app * mk_value(Number const & val, sort * s, bool & is_new) {
        value_set * set = get_value_set(s);
        app * new_val   = mk_value_core(val, s);
        is_new          = false;
        if (!set->m_values.contains(new_val)) {
            m_values.push_back(new_val);
            set->m_values.insert(new_val);
            is_new = true;
        }
        SASSERT(set->m_values.contains(new_val));
        return new_val;
    }

public:
    simple_factory(ast_manager & m, family_id fid):
        value_factory(m, fid),
        m_values(m),
        m_sorts(m) {
    }

    ~simple_factory() override {
        std::for_each(m_sets.begin(), m_sets.end(), delete_proc<value_set>());
    }
    
    expr * get_some_value(sort * s) override {
        value_set * set = nullptr;
        expr * result = nullptr;
        if (m_sort2value_set.find(s, set) && !set->m_values.empty()) 
            result = *(set->m_values.begin());
        else
            result = mk_value(Number(0), s);
        return result;
    }

    bool get_some_values(sort * s, expr_ref & v1, expr_ref & v2) override {
        value_set * set = nullptr;
        if (m_sort2value_set.find(s, set)) {
            switch (set->m_values.size()) {
            case 0:
                v1 = mk_value(Number(0), s);
                v2 = mk_value(Number(1), s);
                break;
            case 1:
                v1 = *(set->m_values.begin());
                v2 = mk_value(Number(0), s);
                if (v1 == v2)
                    v2 = mk_value(Number(1), s);
                break;
            default:
                obj_hashtable<expr>::iterator it = set->m_values.begin();
                v1 = *it;
                ++it;
                v2 = *it;
                break;
            }
            SASSERT(v1 != v2);
            return true;
        }
        v1 = mk_value(Number(0), s);
        v2 = mk_value(Number(1), s);
        return true;
    }

    expr * get_fresh_value(sort * s) override {
        value_set * set  = get_value_set(s);
        bool is_new      = false;
        expr * result    = nullptr;
        sort_info* s_info = s->get_info();
        sort_size const* sz = s_info?&s_info->get_num_elements():nullptr;
        bool has_max = false;
        Number max_size(0);
        if (sz && sz->is_finite() && sz->size() < UINT_MAX) {
            unsigned usz = static_cast<unsigned>(sz->size());
            max_size = Number(usz);
            has_max = true;
        }
        Number start = set->m_next;
        Number & next    = set->m_next;
        while (!is_new) {
            result = mk_value(next, s, is_new);
            next++;
            if (has_max && next > max_size + start) {
                return nullptr;
            }
        }
        SASSERT(result != 0);
        return result;
    }

    void register_value(expr * n) override {
        sort * s = n->get_sort();
        value_set * set  = get_value_set(s);
        if (!set->m_values.contains(n)) {
            m_values.push_back(n);
            set->m_values.insert(n);
        }
    }
        
    virtual app * mk_value(Number const & val, sort * s) {
        bool is_new;
        return mk_value(val, s, is_new);
    }

    unsigned get_num_sorts() const { return m_sorts.size(); }

    sort * get_sort(unsigned idx) const { return m_sorts.get(idx); }
};

/**
   \brief Factory for creating values for uninterpreted sorts and user
   declared (uninterpreted) sorts.
*/
class user_sort_factory : public simple_factory<unsigned> {
    obj_hashtable<sort>  m_finite;   //!< set of sorts that are marked as finite.
    obj_hashtable<expr>  m_empty_universe;
    app * mk_value_core(unsigned const & val, sort * s) override;
public:
    user_sort_factory(ast_manager & m);
    ~user_sort_factory() override {}

    /**
       \brief Make the universe of \c s finite, by preventing new
       elements to be added to its universe.
    */
    void freeze_universe(sort * s);

    /**
       \brief Return true if the universe of \c s is frozen and finite.
    */
    bool is_finite(sort * s) const {
        return m_finite.contains(s);
    }

    /**
       \brief Return the "known" universe of \c s. It doesn't matter whether
       s is finite or not. If \c s is finite, then it is the whole universe.
    */
    obj_hashtable<expr> const & get_known_universe(sort * s) const;

    /**
       \brief Return sorts with finite interpretations.
    */
    obj_hashtable<sort> const & get_finite_sorts() const { return m_finite; }

    expr * get_some_value(sort * s) override;

    bool get_some_values(sort * s, expr_ref & v1, expr_ref & v2) override;

    expr * get_fresh_value(sort * s) override;
    
    void register_value(expr * n) override;
};


