/*++
Copyright (c) 2006 Microsoft Corporation

Abstract:

    Macro solving utilities

Author:

    Leonardo de Moura (leonardo) 2010-12-17.

--*/

#pragma once

class evaluator {
public:
    virtual expr* eval(expr* n, bool model_completion) = 0;
};

// -----------------------------------
//
// Instantiation sets
//
// -----------------------------------

/**
   \brief Instantiation sets are the S_{k,j} sets in the Complete quantifier instantiation paper.
*/
class model_instantiation_set {
    ast_manager& m;
    obj_map<expr, unsigned> m_elems; // and the associated generation
    obj_map<expr, expr*>   m_inv;
    expr_mark               m_visited;
public:
    model_instantiation_set(ast_manager& m) :m(m) {}

    ~model_instantiation_set() {
        for (auto const& kv : m_elems) {
            m.dec_ref(kv.m_key);
        }
        m_elems.reset();
    }

    obj_map<expr, unsigned> const& get_elems() const { return m_elems; }

    void insert(expr* n, unsigned generation) {
        if (m_elems.contains(n) || contains_model_value(n)) {
            return;
        }
        TRACE("model_finder", tout << mk_pp(n, m) << "\n";);
        m.inc_ref(n);
        m_elems.insert(n, generation);
        SASSERT(!m.is_model_value(n));
    }

    void remove(expr* n) {
        // We can only remove n if it is in m_elems, AND m_inv was not initialized yet.
        SASSERT(m_elems.contains(n));
        SASSERT(m_inv.empty());
        m_elems.erase(n);
        TRACE("model_finder", tout << mk_pp(n, m) << "\n";);
        m.dec_ref(n);
    }

    void display(std::ostream& out) const {
        for (auto const& kv : m_elems) {
            out << mk_bounded_pp(kv.m_key, m) << " [" << kv.m_value << "]\n";
        }
        out << "inverse:\n";
        for (auto const& kv : m_inv) {
            out << mk_bounded_pp(kv.m_key, m) << " -> " << mk_bounded_pp(kv.m_value, m) << "\n";
        }
    }

    expr* get_inv(expr* v) const {
        expr* t = nullptr;
        m_inv.find(v, t);
        return t;
    }

    unsigned get_generation(expr* t) const {
        unsigned gen = 0;
        m_elems.find(t, gen);
        return gen;
    }

    void mk_inverse(evaluator& ev) {
        for (auto const& kv : m_elems) {
            expr* t = kv.m_key;
            SASSERT(!contains_model_value(t));
            unsigned gen = kv.m_value;
            expr* t_val = ev.eval(t, true);
            if (!t_val) break;
            TRACE("model_finder", tout << mk_pp(t, m) << " " << mk_pp(t_val, m) << "\n";);

            expr* old_t = nullptr;
            if (m_inv.find(t_val, old_t)) {
                unsigned old_t_gen = 0;
                SASSERT(m_elems.contains(old_t));
                m_elems.find(old_t, old_t_gen);
                if (gen < old_t_gen) {
                    m_inv.insert(t_val, t);
                }
            }
            else {
                m_inv.insert(t_val, t);
            }
        }
    }

    obj_map<expr, expr*> const& get_inv_map() const {
        return m_inv;
    }

    struct is_model_value {};
    void operator()(expr* n) {
        if (m.is_model_value(n)) {
            throw is_model_value();
        }
    }

    bool contains_model_value(expr* n) {
        if (m.is_model_value(n)) {
            return true;
        }
        if (is_app(n) && to_app(n)->get_num_args() == 0) {
            return false;
        }
        m_visited.reset();
        try {
            for_each_expr(*this, m_visited, n);
        }
        catch (const is_model_value&) {
            return true;
        }
        return false;
    }
};
