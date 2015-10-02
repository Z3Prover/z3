/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    resource_limit.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2007-04-18.

Revision History:

--*/
#ifndef RESOURCE_LIMIT_H_
#define RESOURCE_LIMIT_H_

//
// This object is used to limit the availability of "resources" during a search.
// The main applications:
//
// - limiting the number of conflicts.
//
// - limiting the number of branching&bound steps in the ILP
//
// - limiting the number of quantifier instantiations.
//
// - etc.
//
// The idea is that when the resources are exhausted, the bounded_search terminates with
// the undefined result.
//
// Then, the search can restart with bigger limits.
class resource_limit {
public:
    virtual ~resource_limit() {
    }

    virtual const char * get_description() const = 0;

    // - Reset counters associated with the limit.
    virtual void reset_counters() = 0;

    // - The limit was exhausted.
    virtual bool exhausted() const = 0;

    // - Return true if the limit is incremented.
    virtual bool inc_limit() = 0;
    
    virtual int get_limit() const = 0;

    virtual void reset() = 0;
};

class base_resource_limit : public resource_limit {
protected:
    int          m_counter;
    int          m_curr_limit;
    int          m_init_limit;
    int          m_max_limit;  // <0 if unbounded
    const char * m_description;
public:

    base_resource_limit(int init_limit, int max_limit, const char * desc):
        m_counter(0),
        m_curr_limit(init_limit),
        m_init_limit(init_limit),
        m_max_limit(max_limit),
        m_description(desc) {
    }

    virtual ~base_resource_limit() {
    }

    int get_counter() const {
        return m_counter;
    }

    bool inc_counter() {
        m_counter++;
        return m_counter <= m_curr_limit;
    }
    
    void set_init_limit(int l) {
        m_init_limit = l;
        m_curr_limit = l;
    }
    
    void set_max_limit(int l) {
        m_max_limit = l;
    }

    virtual const char * get_description() const {
        return m_description;
    }
    
    virtual void reset_counters() {
        m_counter = 0;
    }

    virtual bool exhausted() const {
        return m_counter >= m_curr_limit;
    }

    virtual int get_limit() const {
        return m_curr_limit;
    }

    virtual void reset() {
        m_counter    = 0;
        m_curr_limit = m_init_limit;
    }
};

class li_resource_limit : public base_resource_limit {
    int m_increment;
public:

    li_resource_limit(int init_limit, int max_limit, int inc, const char * desc):
        base_resource_limit(init_limit, max_limit, desc),
        m_increment(inc) {
    }

    virtual ~li_resource_limit() {
    }

    virtual bool inc_limit() {
        int new_limit = m_curr_limit + m_increment;
        if (m_max_limit < 0 || new_limit <= m_max_limit) {
            m_curr_limit = new_limit;
            return true;
        }
        TRACE("resource_limit", tout << new_limit << " exhausts " << m_max_limit << "\n";);
        return false;
    }

};

class ei_resource_limit : public base_resource_limit {
    double m_increment_ratio;
public:

    ei_resource_limit(int init_limit, int max_limit, double inc, const char * desc):
        base_resource_limit(init_limit, max_limit, desc),
        m_increment_ratio(inc) {
    }

    virtual ~ei_resource_limit() {
    }

    virtual bool inc_limit() {
        int new_limit = static_cast<int>(m_curr_limit * m_increment_ratio);
        if (m_max_limit < 0 || new_limit <= m_max_limit) {
            m_curr_limit = new_limit;
            return true;
        }
        TRACE("resource_limit", tout << new_limit << " exhausts " << m_max_limit << "\n";);
        return false;
    }
};
    

#endif /* RESOURCE_LIMIT_H_ */

