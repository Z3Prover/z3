/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    <name>

Abstract:

    <abstract>

Author:
    Nikolaj Bjorner (nbjorner)
    Lev Nachmanson (levnach)

Revision History:


--*/

#pragma once
namespace lp {
class constraint; // forward definition
struct constraint_hash {
    size_t operator() (const constraint* c) const;
};

struct constraint_equal {
    bool operator() (const constraint * a, const constraint * b) const;
};

class constraint { // we only have less or equal for the inequality sign, which is enough for integral variables
    int                                              m_id;  
    bool                                             m_is_ineq;
    polynomial                                       m_poly;
    mpq                                              m_d; // the divider for the case of a divisibility constraint
    std::unordered_set<constraint_index>             m_assert_origins; // these indices come from the client and get collected during tightening
    bool                                             m_active;
public :
    void set_active_flag() {m_active = true;}
    void remove_active_flag() { m_active = false; }
    bool is_active() const { return m_active; }
    unsigned id() const { return m_id; }
    const polynomial & poly() const { return m_poly; }
    polynomial & poly() { return m_poly; }
    std::unordered_set<constraint_index> & assert_origins() { return m_assert_origins;}
    const std::unordered_set<constraint_index> & assert_origins() const { return m_assert_origins;}
    bool is_lemma() const { return !is_assert(); }
    bool is_assert() const { return m_assert_origins.size() == 1; }
    bool is_ineq() const { return m_is_ineq; }
    const mpq & divider() const { return m_d; }
    static constraint * make_ineq_assert(
        int id,
        const vector<monomial>& term,
        const mpq& a,
        constraint_index  origin) {
        return new constraint(id, origin, polynomial(term, a), true);
    }

    static constraint * make_ineq_constraint(
        int id,
        const polynomial & p,
        std::unordered_set<constraint_index> origins) {
        return new constraint(id, origins,p ,true);
    }

    static constraint * make_ineq_lemma(unsigned id, const polynomial &p) {
        return new constraint(id, p, true);
    }

    // static constraint make_div_lemma(unsigned id, const polynomial &p, const mpq & div) {
    //     lp_assert(false); // not implemented
    //     // constraint * c = new constraint(id, p, true);
    //     // c->m_d = div;
    //     return nullptr;
    // }
private:
    constraint(
        unsigned id,
        constraint_index assert_origin,
        const polynomial & p,
        bool is_ineq):
        m_id(id),
        m_is_ineq(is_ineq),
        m_poly(p),
        m_active(false)
    { // creates an assert
        m_assert_origins.insert(assert_origin);
    }
    constraint(
        unsigned id,
        const std::unordered_set<constraint_index>& origins,
        const polynomial & p,
        bool is_ineq):
        m_id(id),
        m_is_ineq(is_ineq),
        m_poly(p),
        m_assert_origins(origins),
        m_active(false) {}


    
    constraint(
        unsigned id,
        const polynomial & p,
        bool is_ineq):
        m_id(id),
        m_is_ineq(is_ineq),
        m_poly(p),
        m_active(false) { // creates a lemma
    }
        
public:
    constraint() {}

    const mpq & coeff(var_index j) const {
        return m_poly.coeff(j);
    }
    const vector<monomial>& coeffs() const { return m_poly.m_coeffs;}

    bool is_tight(unsigned j) const {
        const mpq & a = m_poly.coeff(j);
        return a == 1 || a == -1;
    }
    void add_predecessor(const constraint* p) {
        lp_assert(p != nullptr);
        for (auto m : p->assert_origins())
            m_assert_origins.insert(m); }
};
}
