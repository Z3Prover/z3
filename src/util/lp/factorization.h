
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
namespace nla {

class factorization {
    svector<lpvar>         m_vars;
    rational               m_sign;
    std::function<void (expl_set&)> m_explain;
public:
    void explain(expl_set& s) const { m_explain(s); }
    bool is_empty() const { return m_vars.empty(); }
    svector<lpvar> & vars() { return m_vars; }
    const svector<lpvar> & vars() const { return m_vars; }
    rational const& sign() const { return m_sign; }
    rational& sign() { return m_sign; } // the setter
    unsigned operator[](unsigned k) const { return m_vars[k]; }
    size_t size() const { return m_vars.size(); }
    const lpvar* begin() const { return m_vars.begin(); }
    const lpvar* end() const { return m_vars.end(); }
    factorization(std::function<void (expl_set&)> explain) : m_explain(explain) {}
};
}
