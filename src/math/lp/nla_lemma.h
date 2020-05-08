/*++
  Copyright (c) 2017 Microsoft Corporation

  Module Name:

  nla_core.h

  Author:
  Nikolaj Bjorner (nbjorner)
  Lev Nachmanson (levnach)

--*/
#pragma once
namespace nla {
struct ineq {
    lp::lconstraint_kind m_cmp;
    lp::lar_term         m_term;
    rational             m_rs;
    ineq(lp::lconstraint_kind cmp, const lp::lar_term& term, const rational& rs) : m_cmp(cmp), m_term(term), m_rs(rs) {}
    bool operator==(const ineq& a) const {
        return m_cmp == a.m_cmp && m_term == a.m_term && m_rs == a.m_rs;
    }
    const lp::lar_term& term() const { return m_term; };
    lp::lconstraint_kind cmp() const { return m_cmp;  };
    const rational& rs() const { return m_rs; };
};

class lemma {
    vector<ineq>     m_ineqs;
    lp::explanation  m_expl;
public:
    void push_back(const ineq& i) { m_ineqs.push_back(i);}
    size_t size() const { return m_ineqs.size() + m_expl.size(); }
    const vector<ineq>& ineqs() const { return m_ineqs; }
    vector<ineq>& ineqs() { return m_ineqs; }
    lp::explanation& expl() { return m_expl; }
    const lp::explanation& expl() const { return m_expl; }
    bool is_conflict() const { return m_ineqs.empty() && !m_expl.empty(); }
};
}
