/*++
Copyright (c) 2006 Microsoft Corporation

Abstract:

    Macro solving utilities

Author:

    Leonardo de Moura (leonardo) 2010-12-17.

--*/

#pragma once

/**
   During model construction time,
   we solve several constraints that impose restrictions
   on how the model for the ground formulas may be extended to
   a model to the relevant universal quantifiers.

   The class node and its subclasses are used to solve
   these constraints.
*/

/**
   \brief Base class used to solve model construction constraints.
*/
class model_node {
    unsigned            m_id;
    model_node*         m_find{ nullptr };
    unsigned            m_eqc_size{ 1 };

    sort* m_sort; // sort of the elements in the instantiation set.

    bool                m_mono_proj{ false };     // relevant for integers & reals & bit-vectors
    bool                m_signed_proj{ false };   // relevant for bit-vectors.
    ptr_vector<model_node>    m_avoid_set;
    ptr_vector<expr>    m_exceptions;

    scoped_ptr<model_instantiation_set> m_set;
    expr* m_else      { nullptr };
    func_decl* m_proj { nullptr };

    // Append the new elements of v2 into v1. v2 should not be used after this operation, since it may suffer destructive updates.
    template<typename T>
    void dappend(ptr_vector<T>& v1, ptr_vector<T>& v2) {
        if (v2.empty())
            return;
        if (v1.empty()) {
            v1.swap(v2);
            return;
        }
        for (T* t : v2) {
            if (!v1.contains(t))
                v1.push_back(t);
        }
        v2.finalize();
    }
public:
    model_node(unsigned id, sort* s) :
        m_id(id),
        m_sort(s) {
    }

    ~model_node() {}

    unsigned get_id() const { return m_id; }

    sort* get_sort() const { return m_sort; }

    bool is_root() const { return m_find == nullptr; }

    model_node* get_root() const {
        model_node* curr = const_cast<model_node*>(this);
        while (!curr->is_root()) {
            curr = curr->m_find;
        }
        SASSERT(curr->is_root());
        return curr;
    }

    void merge(model_node* other) {
        model_node* r1 = get_root();
        model_node* r2 = other->get_root();
        SASSERT(!r1->m_set);
        SASSERT(!r2->m_set);
        SASSERT(r1->get_sort() == r2->get_sort());
        if (r1 == r2)
            return;
        if (r1->m_eqc_size > r2->m_eqc_size)
            std::swap(r1, r2);
        r1->m_find = r2;
        r2->m_eqc_size += r1->m_eqc_size;
        if (r1->m_mono_proj)
            r2->m_mono_proj = true;
        if (r1->m_signed_proj)
            r2->m_signed_proj = true;
        dappend(r2->m_avoid_set, r1->m_avoid_set);
        dappend(r2->m_exceptions, r1->m_exceptions);
    }

    void insert_avoid(model_node* n) {
        ptr_vector<model_node>& as = get_root()->m_avoid_set;
        if (!as.contains(n))
            as.push_back(n);
    }

    void insert_exception(expr* n) {
        ptr_vector<expr>& ex = get_root()->m_exceptions;
        if (!ex.contains(n))
            ex.push_back(n);
    }

    void set_mono_proj() {
        get_root()->m_mono_proj = true;
    }

    bool is_mono_proj() const {
        return get_root()->m_mono_proj;
    }

    void set_signed_proj() {
        get_root()->m_signed_proj = true;
    }

    bool is_signed_proj() const {
        return get_root()->m_signed_proj;
    }

    void mk_instantiation_set(ast_manager& m) {
        SASSERT(is_root());
        SASSERT(!m_set);
        m_set = alloc(model_instantiation_set, m);
    }

    void insert(expr* n, unsigned generation) {
        SASSERT(is_ground(n));
        get_root()->m_set->insert(n, generation);
    }

    void display(std::ostream& out, ast_manager& m) const {
        if (is_root()) {
            out << "root node ------\n";
            out << "@" << m_id << " mono: " << m_mono_proj << " signed: " << m_signed_proj << ", sort: " << mk_pp(m_sort, m) << "\n";
            out << "avoid-set: ";
            for (model_node* n : m_avoid_set) {
                out << "@" << n->get_root()->get_id() << " ";
            }
            out << "\n";
            out << "exceptions: ";
            for (expr* e : m_exceptions) {
                out << mk_bounded_pp(e, m) << " ";
            }
            out << "\n";
            if (m_else)
                out << "else: " << mk_pp(m_else, m, 6) << "\n";
            if (m_proj)
                out << "projection: " << m_proj->get_name() << "\n";
            if (m_set) {
                out << "instantiation-set:\n";
                m_set->display(out);
            }
            out << "----------------\n";
        }
        else {
            out << "@" << m_id << " -> @" << get_root()->get_id() << "\n";
        }
    }

    model_instantiation_set const* get_instantiation_set() const { return get_root()->m_set.get(); }

    model_instantiation_set* get_instantiation_set() { return get_root()->m_set.get(); }

    ptr_vector<expr> const& get_exceptions() const { return get_root()->m_exceptions; }

    ptr_vector<model_node> const& get_avoid_set() const { return get_root()->m_avoid_set; }

    // return true if m_avoid_set.contains(this)
    bool must_avoid_itself() const {
        model_node* r = get_root();
        for (model_node* n : m_avoid_set) {
            if (r == n->get_root())
                return true;
        }
        return false;
    }

    void set_else(expr* e) {
        SASSERT(!is_mono_proj());
        SASSERT(get_root()->m_else == nullptr);
        get_root()->m_else = e;
    }

    expr* get_else() const {
        return get_root()->m_else;
    }

    void set_proj(func_decl* f) {
        SASSERT(get_root()->m_proj == nullptr);
        get_root()->m_proj = f;
    }

    func_decl* get_proj() const {
        return get_root()->m_proj;
    }
};
