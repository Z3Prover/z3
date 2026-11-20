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
#include <cstring>
#include <cmath>
#include <cstdint>
#include "tactic/probe.h"
#include "tactic/tactic.h"
#include "ast/arith_decl_plugin.h"
#include "ast/bv_decl_plugin.h"
#include "tactic/goal_util.h"
#include "ast/rewriter/bv_rewriter.h"

class memory_probe : public probe {
public:
    char const* name() const override { return "memory"; }
    result operator()(goal const & g) override {
        return result(static_cast<double>(memory::get_allocation_size())/static_cast<double>(1024*1024));
    }
};

probe * mk_memory_probe() {
    return alloc(memory_probe);
}

class depth_probe : public probe {
public:
    char const* name() const override { return "depth"; }
    result operator()(goal const & g) override {
        return result(g.depth());
    }
};

class size_probe : public probe {
public:
    char const* name() const override { return "size"; }
    result operator()(goal const & g) override {
        return result(g.size());
    }
};

class num_exprs_probe : public probe {
public:
    char const* name() const override { return "num-exprs"; }
    result operator()(goal const & g) override {
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

    ~unary_probe() override {
        m_p->dec_ref();
    }

    bool has_syntax() const override { return m_p->has_syntax(); }

    void updt_params(params_ref const & p) override { m_p->updt_params(p); }

    // a probe of the same class with the argument a
    virtual probe * clone1(probe * a) const = 0;

    probe * clone() override {
        probe * a = m_p->clone();
        return a == m_p ? this : clone1(a);
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

    ~bin_probe() override {
        m_p1->dec_ref();
        m_p2->dec_ref();
    }

    probe const* arg1() const { return m_p1; }
    probe const* arg2() const { return m_p2; }

    bool has_syntax() const override { return m_p1->has_syntax() && m_p2->has_syntax(); }

    std::ostream& display_sexpr(std::ostream& out) const override {
        m_p1->display_sexpr(out << "(" << name() << " ");
        return m_p2->display_sexpr(out << " ") << ")";
    }

    std::ostream& display_with(std::ostream& out, params_ref const & p, std::string * notes, std::string & problems) const override {
        m_p1->display_with(out << "(" << name() << " ", p, notes, problems);
        return m_p2->display_with(out << " ", p, notes, problems) << ")";
    }

    void updt_params(params_ref const & p) override {
        m_p1->updt_params(p);
        m_p2->updt_params(p);
    }

    // a probe of the same class with the arguments a and b
    virtual probe * clone2(probe * a, probe * b) const = 0;

    probe * clone() override {
        probe * a = m_p1->clone();
        probe * b = m_p2->clone();
        if (a == m_p1 && b == m_p2)
            return this;
        // a or b may be new: hold them while the copy takes its references
        probe_ref ra(a), rb(b);
        return clone2(a, b);
    }
};

class not_probe : public unary_probe {
public:
    not_probe(probe * p):unary_probe(p) {}
    probe * clone1(probe * a) const override { return alloc(not_probe, a); }
    result operator()(goal const & g) override {
        return result(!m_p->operator()(g).is_true());
    }
    std::ostream& display_sexpr(std::ostream& out) const override;
    std::ostream& display_with(std::ostream& out, params_ref const & p, std::string * notes, std::string & problems) const override;
};

class and_probe : public bin_probe {
public:
    and_probe(probe * p1, probe * p2):bin_probe(p1, p2) {}
    probe * clone2(probe * a, probe * b) const override { return alloc(and_probe, a, b); }
    char const* name() const override { return "and"; }
    result operator()(goal const & g) override {
        return result(m_p1->operator()(g).is_true() && m_p2->operator()(g).is_true());
    }
};

class or_probe : public bin_probe {
public:
    or_probe(probe * p1, probe * p2):bin_probe(p1, p2) {}
    probe * clone2(probe * a, probe * b) const override { return alloc(or_probe, a, b); }
    char const* name() const override { return "or"; }
    result operator()(goal const & g) override {
        return result(m_p1->operator()(g).is_true() || m_p2->operator()(g).is_true());
    }
};

class eq_probe : public bin_probe {
public:
    eq_probe(probe * p1, probe * p2):bin_probe(p1, p2) {}
    probe * clone2(probe * a, probe * b) const override { return alloc(eq_probe, a, b); }
    char const* name() const override { return "="; }
    result operator()(goal const & g) override {
        return result(m_p1->operator()(g).get_value() == m_p2->operator()(g).get_value());
    }
};

class le_probe : public bin_probe {
public:
    le_probe(probe * p1, probe * p2):bin_probe(p1, p2) {}
    probe * clone2(probe * a, probe * b) const override { return alloc(le_probe, a, b); }
    char const* name() const override { return "<="; }
    result operator()(goal const & g) override {
        return result(m_p1->operator()(g).get_value() <= m_p2->operator()(g).get_value());
    }
};

class add_probe : public bin_probe {
public:
    add_probe(probe * p1, probe * p2):bin_probe(p1, p2) {}
    probe * clone2(probe * a, probe * b) const override { return alloc(add_probe, a, b); }
    char const* name() const override { return "+"; }
    result operator()(goal const & g) override {
        return result(m_p1->operator()(g).get_value() + m_p2->operator()(g).get_value());
    }
};

class sub_probe : public bin_probe {
public:
    sub_probe(probe * p1, probe * p2):bin_probe(p1, p2) {}
    probe * clone2(probe * a, probe * b) const override { return alloc(sub_probe, a, b); }
    char const* name() const override { return "-"; }
    result operator()(goal const & g) override {
        return result(m_p1->operator()(g).get_value() - m_p2->operator()(g).get_value());
    }
};

class mul_probe : public bin_probe {
public:
    mul_probe(probe * p1, probe * p2):bin_probe(p1, p2) {}
    probe * clone2(probe * a, probe * b) const override { return alloc(mul_probe, a, b); }
    char const* name() const override { return "*"; }
    result operator()(goal const & g) override {
        return result(m_p1->operator()(g).get_value() * m_p2->operator()(g).get_value());
    }
};

class div_probe : public bin_probe {
public:
    div_probe(probe * p1, probe * p2):bin_probe(p1, p2) {}
    probe * clone2(probe * a, probe * b) const override { return alloc(div_probe, a, b); }
    char const* name() const override { return "/"; }
    result operator()(goal const & g) override {
        return result(m_p1->operator()(g).get_value() / m_p2->operator()(g).get_value());
    }
};

class const_probe : public probe {
    double m_val;
public:
    const_probe(double v):m_val(v) {}

    std::ostream& display_sexpr(std::ostream& out) const override {
        if (m_val == std::floor(m_val) && std::fabs(m_val) < 1e15)
            return out << static_cast<int64_t>(m_val);
        return out << m_val;
    }

    // the parser reads a constant as a 32-bit integer
    bool has_syntax() const override {
        return m_val == std::floor(m_val) && std::fabs(m_val) <= INT32_MAX;
    }

    std::ostream& display_with(std::ostream& out, params_ref const & p, std::string * notes, std::string & problems) const override {
        if (!has_syntax())
            add_problem(problems, m_val == std::floor(m_val) ? "constant too big" : "constant not an integer");
        return display_sexpr(out);
    }

    result operator()(goal const & g) override {
        return result(m_val);
    }
};

// mk_lt and mk_gt are encoded with not_probe; display them as (< a b).
std::ostream& not_probe::display_sexpr(std::ostream& out) const {
    auto* b = dynamic_cast<bin_probe const*>(m_p);
    if (b && dynamic_cast<le_probe const*>(m_p)) {
        // mk_lt(p1, p2) is (not (<= p2 p1)); print it as (< p1 p2)
        b->arg2()->display_sexpr(out << "(< ");
        return b->arg1()->display_sexpr(out << " ") << ")";
    }
    return m_p->display_sexpr(out << "(not ") << ")";
}

std::ostream& not_probe::display_with(std::ostream& out, params_ref const & p, std::string * notes, std::string & problems) const {
    auto* b = dynamic_cast<bin_probe const*>(m_p);
    if (b && dynamic_cast<le_probe const*>(m_p)) {
        b->arg2()->display_with(out << "(< ", p, notes, problems);
        return b->arg1()->display_with(out << " ", p, notes, problems) << ")";
    }
    return m_p->display_with(out << "(not ", p, notes, problems) << ")";
}

// See mk_param_probe. The value is set by updt_params; clone copies the probe.
class param_probe : public probe {
    symbol   m_key;
    unsigned m_default;
    unsigned m_value;
public:
    param_probe(symbol const & key, unsigned d, unsigned v) : m_key(key), m_default(d), m_value(v) {}

    void updt_params(params_ref const & p) override { m_value = p.get_uint(m_key, m_default); }

    probe * clone() override { return alloc(param_probe, m_key, m_default, m_value); }

    result operator()(goal const & g) override { return result(m_value); }

    // the constant it evaluates to: the tactic language has no parameter probes
    std::ostream& display_sexpr(std::ostream& out) const override { return out << m_value; }

    bool has_syntax() const override { return m_value <= INT32_MAX; }

    std::ostream& display_with(std::ostream& out, params_ref const & p, std::string * notes, std::string & problems) const override {
        unsigned v = p.get_uint(m_key, m_default);
        // the parser reads a constant as a 32-bit integer
        if (v > INT32_MAX)
            add_problem(problems, "constant too big");
        if (notes) {
            *notes += (notes->empty() ? "" : ", ") + std::string(m_key.str()) + " " + std::to_string(v);
            if (!p.contains(m_key))
                *notes += " (default)";
            else if (p.contains(scope_global_mark(m_key)))
                *notes += " (global)";
        }
        return out << v;
    }
};

probe * mk_param_probe(char const * key, unsigned _default) {
    return alloc(param_probe, symbol(key), _default, _default);
}

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
    struct found : public std::exception {};
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
    struct found : public std::exception {};
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
        if (fid == u.get_family_id()) {
            if (n->get_decl_kind() == OP_BSDIV0 ||
                n->get_decl_kind() == OP_BUDIV0 ||
                n->get_decl_kind() == OP_BSREM0 ||
                n->get_decl_kind() == OP_BUREM0 ||
                n->get_decl_kind() == OP_BSMOD0)
                throw found();
            return;
        }
        if (is_uninterp_const(n))
            return;
        throw found();
    }
};

class is_propositional_probe : public probe {
public:
    char const* name() const override { return "is-propositional"; }
    result operator()(goal const & g) override {
        return !test<is_non_propositional_predicate>(g);
    }
};


class is_qfbv_probe : public probe {
public:
    char const* name() const override { return "is-qfbv"; }
    result operator()(goal const & g) override {
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
    struct found : public std::exception {};
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
    char const* name() const override { return "is-qfaufbv"; }
    result operator()(goal const & g) override {
        return !test<is_non_qfaufbv_predicate>(g);
    }
};

probe * mk_is_qfaufbv_probe() {
    return alloc(is_qfaufbv_probe);
}


struct is_non_qfufbv_predicate {
    struct found : public std::exception {};
    ast_manager & m;
    bv_util       m_bv_util;

    is_non_qfufbv_predicate(ast_manager & _m) : m(_m), m_bv_util(_m) {}

    void operator()(var *) { throw found(); }

    void operator()(quantifier *) { throw found(); }

    void operator()(app * n) {
        if (!m.is_bool(n) && !m_bv_util.is_bv(n))
            throw found();
        family_id fid = n->get_family_id();
        if (fid == m.get_basic_family_id())
            return;
        if (fid == m_bv_util.get_family_id())
            return;
        if (is_uninterp(n))
            return;

        throw found();
    }
};

class is_qfufbv_probe : public probe {
public:
    char const* name() const override { return "is-qfufbv"; }
    bool has_syntax() const override { return false; } // not registered
    result operator()(goal const & g) override {
        return !test<is_non_qfufbv_predicate>(g);
    }
};

probe * mk_is_qfufbv_probe() {
    return alloc(is_qfufbv_probe);
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
            if (family != nullptr)
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
                        if (n->get_sort()->get_family_id() == m_fid)
                            m_counter++;
                    }
                }
            }
        }
    };

public:
    char const* name() const override {
        if (m_bool)
            return "num-bool-consts";
        if (m_family == nullptr)
            return "num-consts";
        return strcmp(m_family, "arith") == 0 ? "num-arith-consts" : "num-bv-consts";
    }

    num_consts_probe(bool b, char const * f):
        m_bool(b), m_family(f) {
    }
    result operator()(goal const & g) override {
        proc p(g.m(), m_bool, m_family);
        unsigned sz = g.size();
        expr_fast_mark1 visited;
        for (unsigned i = 0; i < sz; ++i) {
            for_each_expr_core<proc, expr_fast_mark1, true, true>(p, visited, g.form(i));
        }
        return result(p.m_counter);
    }
};

probe * mk_num_consts_probe() {
    return alloc(num_consts_probe, false, nullptr);
}

probe * mk_num_bool_consts_probe() {
    return alloc(num_consts_probe, true, nullptr);
}

probe * mk_num_arith_consts_probe() {
    return alloc(num_consts_probe, false, "arith");
}

probe * mk_num_bv_consts_probe() {
    return alloc(num_consts_probe, false, "bv");
}

class produce_proofs_probe : public probe {
public:
    char const* name() const override { return "produce-proofs"; }
    result operator()(goal const & g) override {
        return g.proofs_enabled();
    }
};

class produce_models_probe : public probe {
public:
    char const* name() const override { return "produce-model"; }
    result operator()(goal const & g) override {
        return g.models_enabled();
    }
};

class produce_unsat_cores_probe : public probe {
public:
    char const* name() const override { return "produce-unsat-cores"; }
    result operator()(goal const & g) override {
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
    char const* name() const override { return "has-patterns"; }
    struct found : public std::exception {};

    struct proc {
        void operator()(var * n) {}
        void operator()(app * n) {}
        void operator()(quantifier * n) {
            if (n->get_num_patterns() > 0 || n->get_num_no_patterns() > 0)
                throw found();
        }
    };
public:
    result operator()(goal const & g) override {
        try {
            expr_fast_mark1 visited;
            proc p;
            unsigned sz = g.size();
            for (unsigned i = 0; i < sz; ++i) {
                quick_for_each_expr(p, visited, g.form(i));
            }
            return false;
        }
        catch (const found &) {
            return true;
        }
    }
};

probe * mk_has_pattern_probe() {
    return alloc(has_pattern_probe);
}


struct has_quantifier_probe : public probe {
    char const* name() const override { return "has-quantifiers"; }
    struct found : public std::exception {};

    struct proc {
        void operator()(var * n) {}
        void operator()(app * n) {}
        void operator()(quantifier * n) { throw found(); }
    };
public:
    result operator()(goal const & g) override {
        try {
            expr_fast_mark1 visited;
            proc p;
            unsigned sz = g.size();
            for (unsigned i = 0; i < sz; ++i) {
                quick_for_each_expr(p, visited, g.form(i));
            }
            return false;
        }
        catch (const found &) {
            return true;
        }
    }
};

probe * mk_has_quantifier_probe() {
    return alloc(has_quantifier_probe);
}



