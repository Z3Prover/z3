/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    probe.cpp

Abstract:

    Evaluates/Probes a goal.
    
    A probe is used to build tactics (aka strategies) that
    makes decisions based on the structure of a goal.
    
Author:

    Leonardo de Moura (leonardo) 2011-10-13.

Revision History:

--*/
#include"probe.h"
#include"arith_decl_plugin.h"
#include"bv_decl_plugin.h"
#include"goal_util.h"

class memory_probe : public probe {
public:
    virtual result operator()(goal const & g) {
        return result(static_cast<double>(memory::get_allocation_size())/static_cast<double>(1024*1024));
    }
};

probe * mk_memory_probe() {
    return alloc(memory_probe);
}

class depth_probe : public probe {
public:
    virtual result operator()(goal const & g) {
        return result(g.depth());
    }
};

class size_probe : public probe {
public:
    virtual result operator()(goal const & g) {
        return result(g.size());
    }
};

class num_exprs_probe : public probe {
public:
    virtual result operator()(goal const & g) {
        return result(g.num_exprs());
    }
};

probe * mk_depth_probe() {
    return alloc(depth_probe);
}

probe * mk_size_probe() {
    return alloc(size_probe);
}

probe * mk_num_exprs_probe() {
    return alloc(num_exprs_probe);
}

class unary_probe : public probe {
protected:
    probe * m_p;
public:
    unary_probe(probe * p):
        m_p(p) {
        SASSERT(p); 
        p->inc_ref(); 
    }
    
    ~unary_probe() { 
        m_p->dec_ref(); 
    }

};

class bin_probe : public probe {
protected:
    probe * m_p1;
    probe * m_p2;
public:
    bin_probe(probe * p1, probe * p2):
        m_p1(p1), 
        m_p2(p2) { 
        SASSERT(p1); 
        SASSERT(p2);
        p1->inc_ref(); 
        p2->inc_ref(); 
    }
    
    ~bin_probe() { 
        m_p1->dec_ref(); 
        m_p2->dec_ref(); 
    }
};

class not_probe : public unary_probe {
public:
    not_probe(probe * p):unary_probe(p) {}
    virtual result operator()(goal const & g) {
        return result(!m_p->operator()(g).is_true());
    }    
};

class and_probe : public bin_probe {
public:
    and_probe(probe * p1, probe * p2):bin_probe(p1, p2) {}
    virtual result operator()(goal const & g) {
        return result(m_p1->operator()(g).is_true() && m_p2->operator()(g).is_true());
    }
};

class or_probe : public bin_probe {
public:
    or_probe(probe * p1, probe * p2):bin_probe(p1, p2) {}
    virtual result operator()(goal const & g) {
        return result(m_p1->operator()(g).is_true() || m_p2->operator()(g).is_true());
    }
};

class eq_probe : public bin_probe {
public:
    eq_probe(probe * p1, probe * p2):bin_probe(p1, p2) {}
    virtual result operator()(goal const & g) {
        return result(m_p1->operator()(g).get_value() == m_p2->operator()(g).get_value());
    }
};

class le_probe : public bin_probe {
public:
    le_probe(probe * p1, probe * p2):bin_probe(p1, p2) {}
    virtual result operator()(goal const & g) {
        return result(m_p1->operator()(g).get_value() <= m_p2->operator()(g).get_value());
    }
};

class add_probe : public bin_probe {
public:
    add_probe(probe * p1, probe * p2):bin_probe(p1, p2) {}
    virtual result operator()(goal const & g) {
        return result(m_p1->operator()(g).get_value() + m_p2->operator()(g).get_value());
    }
};

class sub_probe : public bin_probe {
public:
    sub_probe(probe * p1, probe * p2):bin_probe(p1, p2) {}
    virtual result operator()(goal const & g) {
        return result(m_p1->operator()(g).get_value() - m_p2->operator()(g).get_value());
    }
};

class mul_probe : public bin_probe {
public:
    mul_probe(probe * p1, probe * p2):bin_probe(p1, p2) {}
    virtual result operator()(goal const & g) {
        return result(m_p1->operator()(g).get_value() * m_p2->operator()(g).get_value());
    }
};

class div_probe : public bin_probe {
public:
    div_probe(probe * p1, probe * p2):bin_probe(p1, p2) {}
    virtual result operator()(goal const & g) {
        return result(m_p1->operator()(g).get_value() / m_p2->operator()(g).get_value());
    }
};

class const_probe : public probe {
    double m_val;
public:
    const_probe(double v):m_val(v) {}
    
    virtual result operator()(goal const & g) {
        return result(m_val); 
    }
};

probe * mk_const_probe(double v) {
    return alloc(const_probe, v);
}

probe * mk_not(probe * p) {
    return alloc(not_probe, p);
}

probe * mk_and(probe * p1, probe * p2) {
    return alloc(and_probe, p1, p2);
}

probe * mk_or(probe * p1, probe * p2) {
    return alloc(or_probe, p1, p2);
}

probe * mk_implies(probe * p1, probe * p2) {
    return mk_or(mk_not(p1), p2);
}

probe * mk_eq(probe * p1, probe * p2) {
    return alloc(eq_probe, p1, p2);
}

probe * mk_neq(probe * p1, probe * p2) {
    return mk_not(mk_eq(p1, p2));
}

probe * mk_le(probe * p1, probe * p2) {
    return alloc(le_probe, p1, p2);
}

probe * mk_ge(probe * p1, probe * p2) {
    return mk_le(p2, p1);
}

probe * mk_lt(probe * p1, probe * p2) {
    return mk_not(mk_ge(p1, p2));
}

probe * mk_gt(probe * p1, probe * p2) {
    return mk_lt(p2, p1);
}

probe * mk_add(probe * p1, probe * p2) {
    return alloc(add_probe, p1, p2);
}

probe * mk_mul(probe * p1, probe * p2) {
    return alloc(mul_probe, p1, p2);
}

probe * mk_sub(probe * p1, probe * p2) {
    return alloc(sub_probe, p1, p2);
}

probe * mk_div(probe * p1, probe * p2) {
    return alloc(div_probe, p1, p2);
}

struct is_non_propositional_predicate {
    struct found {};
    ast_manager & m;

    is_non_propositional_predicate(ast_manager & _m):m(_m) {}
    void operator()(var *) { throw found();  }
    void operator()(quantifier *) { throw found(); }
    void operator()(app * n) {
        if (!m.is_bool(n))
            throw found();
        
        family_id fid = n->get_family_id();
        if (fid == m.get_basic_family_id())
            return; 
        
        if (is_uninterp_const(n))
            return;

        throw found();
    }
};

struct is_non_qfbv_predicate {
    struct found {};
    ast_manager & m;
    bv_util       u;

    is_non_qfbv_predicate(ast_manager & _m):m(_m), u(m) {}

    void operator()(var *) { throw found();  }
    
    void operator()(quantifier *) { throw found(); }
    
    void operator()(app * n) {
        if (!m.is_bool(n) && !u.is_bv(n))
            throw found();
        family_id fid = n->get_family_id();
        if (fid == m.get_basic_family_id()) 
            return; 
        if (fid == u.get_family_id())
            return;
        if (is_uninterp_const(n))
            return;
        throw found();
    }
};

class is_propositional_probe : public probe {
public:
    virtual result operator()(goal const & g) {
        return !test<is_non_propositional_predicate>(g);
    }
};

class is_qfbv_probe : public probe {
public:
    virtual result operator()(goal const & g) {
        return !test<is_non_qfbv_predicate>(g);
    }
};

probe * mk_is_propositional_probe() {
    return alloc(is_propositional_probe);
}

probe * mk_is_qfbv_probe() {
    return alloc(is_qfbv_probe); 
}

struct is_non_qfaufbv_predicate {
    struct found {};
    ast_manager & m;
    bv_util       m_bv_util;
    array_util    m_array_util;

    is_non_qfaufbv_predicate(ast_manager & _m) : m(_m), m_bv_util(_m), m_array_util(_m) {}

    void operator()(var *) { throw found(); }

    void operator()(quantifier *) { throw found(); }

    void operator()(app * n) {        
        if (!m.is_bool(n) && !m_bv_util.is_bv(n) && !m_array_util.is_array(n))
            throw found();
        family_id fid = n->get_family_id();
        if (fid == m.get_basic_family_id())
            return;
        if (fid == m_bv_util.get_family_id() || fid == m_array_util.get_family_id())
            return;
        if (is_uninterp(n))
            return;

        throw found();
    }
};

class is_qfaufbv_probe : public probe {
public:
    virtual result operator()(goal const & g) {
        return !test<is_non_qfaufbv_predicate>(g);
    }
};

probe * mk_is_qfaufbv_probe() {
    return alloc(is_qfaufbv_probe);
}

class num_consts_probe : public probe {
    bool         m_bool;   // If true, track only boolean constants. Otherwise, track only non boolean constants.
    char const * m_family; // (Ignored if m_bool == true), if != 0 and m_bool == true, then track only constants of the given family.
    struct proc {
        ast_manager & m;
        bool          m_bool;
        family_id     m_fid;
        unsigned      m_counter;
        proc(ast_manager & _m, bool b, char const * family):m(_m), m_bool(b), m_counter(0) {
            if (family != 0)
                m_fid = m.mk_family_id(family);
            else
                m_fid = null_family_id;
        }
        void operator()(quantifier *) {}
        void operator()(var *) {}
        void operator()(app * n) { 
            if (n->get_num_args() == 0 && !m.is_value(n)) {
                if (m_bool) {
                    if (m.is_bool(n))
                        m_counter++;
                }
                else {
                    if (m_fid == null_family_id) {
                        if (!m.is_bool(n))
                            m_counter++;
                    }
                    else {
                        if (m.get_sort(n)->get_family_id() == m_fid)
                            m_counter++;
                    }
                }
            }
        }
    };

public:
    num_consts_probe(bool b, char const * f):
        m_bool(b), m_family(f) {
    }
    virtual result operator()(goal const & g) {
        proc p(g.m(), m_bool, m_family);
        unsigned sz = g.size();
        expr_fast_mark1 visited;
        for (unsigned i = 0; i < sz; i++) {
            for_each_expr_core<proc, expr_fast_mark1, true, true>(p, visited, g.form(i));        
        }
        return result(p.m_counter);
    }
};

probe * mk_num_consts_probe() {
    return alloc(num_consts_probe, false, 0);
}

probe * mk_num_bool_consts_probe() {
    return alloc(num_consts_probe, true, 0);
}

probe * mk_num_arith_consts_probe() {
    return alloc(num_consts_probe, false, "arith");
}

probe * mk_num_bv_consts_probe() {
    return alloc(num_consts_probe, false, "bv");
}

class produce_proofs_probe : public probe {
public:
    virtual result operator()(goal const & g) {
        return g.proofs_enabled();
    }
};

class produce_models_probe : public probe {
public:
    virtual result operator()(goal const & g) {
        return g.models_enabled();
    }
};

class produce_unsat_cores_probe : public probe {
public:
    virtual result operator()(goal const & g) {
        return g.unsat_core_enabled();
    }
};

probe * mk_produce_proofs_probe() {
    return alloc(produce_proofs_probe);
}

probe * mk_produce_models_probe() {
    return alloc(produce_models_probe);
}

probe * mk_produce_unsat_cores_probe() {
    return alloc(produce_unsat_cores_probe);
}

struct has_pattern_probe : public probe {
    struct found {};

    struct proc {
        void operator()(var * n) {}
        void operator()(app * n) {}
        void operator()(quantifier * n) { 
            if (n->get_num_patterns() > 0 || n->get_num_no_patterns() > 0)
                throw found();
        }
    };
public:
    virtual result operator()(goal const & g) {
        try {
            expr_fast_mark1 visited;
            proc p;
            unsigned sz = g.size();
            for (unsigned i = 0; i < sz; i++) {
                quick_for_each_expr(p, visited, g.form(i));
            }
            return false;
        }
        catch (found) {
            return true;
        }
    }
};

probe * mk_has_pattern_probe() {
    return alloc(has_pattern_probe);
}
