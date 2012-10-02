/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    value.h

Abstract:

    Abstract class used to represent values in a model.

Author:

    Leonardo de Moura (leonardo) 2007-08-14.

Revision History:

--*/
#ifndef _VALUE_H_
#define _VALUE_H_

#include"core_model.h"
#include"ast.h"
#include"ref.h"

class model;

class value {
    partition_id m_partition_id;
    unsigned     m_ref_count;
    type_ast *   m_type;

    friend class model;

    void set_partition_id(partition_id id) { 
        m_partition_id = id;
    }

public:
    value(type_ast * ty):
        m_partition_id(null_partition_id),
        m_ref_count(0),
        m_type(ty) {
    }

    virtual ~value() {}

    void inc_ref() { m_ref_count ++; }
    
    void dec_ref() { 
        SASSERT(m_ref_count > 0);
        m_ref_count--;
        if (m_ref_count == 0) {
            dealloc(this);
        }
    }

    partition_id get_partition_id() { return m_partition_id; }

    type_ast * get_type() const { return m_type; }

    virtual void display(std::ostream & out) const = 0;

    virtual unsigned hash() const = 0;

    virtual bool operator==(const value & other) const = 0;

    virtual void infer_types(ast_vector<type_ast> & result) { /* default: do nothing */ }
    
    virtual void collect_used_partitions(svector<bool> & result) { /* default: do nothing */ }
};

inline std::ostream & operator<<(std::ostream & target, const value & v) {
    v.display(target);
    return target;
}

class value_factory {
    family_id     m_fid;
public:
    value_factory(symbol fname, ast_manager & m):
        m_fid(m.get_family_id(fname)) {
    }
    
    virtual ~value_factory() {}
    
    // Return some value of the given type
    virtual value * get_some_value(type_ast * ty) = 0; 

    // Return two distinct values of the given type
    virtual bool get_some_values(type_ast * ty, ref<value> & v1, ref<value> & v2) = 0;
    
    // Return a fresh value of the given type
    virtual value * get_fresh_value(type_ast * ty) = 0;

    virtual value * update_value(value * source, const svector<partition_id> & pid2pid) {
        return source;
    }

    family_id get_family_id() const { return m_fid; }
};

class bool_value : public value {
    friend class basic_factory;
    bool m_value;

    bool_value(bool v, type_ast * ty):
        value(ty),
        m_value(v) {
    }

public:
   
    bool get_value() const { 
        return m_value;
    }

    virtual void display(std::ostream & out) const;

    virtual unsigned hash() const;

    virtual bool operator==(const value & other) const;
};

class basic_factory : public value_factory {
    ast_ref<type_ast> m_bool;
    ref<bool_value> m_true;
    ref<bool_value> m_false;
public:
    basic_factory(ast_manager & m);

    virtual ~basic_factory() {}

    bool_value * get_true() const { 
        return m_true.get();
    }

    bool_value * get_false() const {
        return m_false.get();
    }

    // Return some value of the given type
    virtual value * get_some_value(type_ast * ty) {
        return get_false();
    }

    // Return two distinct values of the given type
    virtual bool get_some_values(type_ast * ty, ref<value> & v1, ref<value> & v2) {
        v1 = get_false();
        v2 = get_true();
        return true;
    }
    
    // Return a fresh value of the given type
    virtual value * get_fresh_value(type_ast * ty) {
        // it is not possible to create new fresh values... 
        return 0;
    }
};

#endif /* _VALUE_H_ */

