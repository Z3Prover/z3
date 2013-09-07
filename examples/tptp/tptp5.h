#ifndef TPTP5_H_
#define TPTP5_H_


class TreeNode;

#if 0
class named_formulas {
    expr_ref_vector m_fmls;
    svector<symbol> m_names;
    bool m_has_conjecture;
    unsigned m_conjecture_index;
public:
    named_formulas(ast_manager& m) : 
        m_fmls(m), 
        m_has_conjecture(false),
        m_conjecture_index(0)
        {}
    void push_back(expr* fml, char const* name) {
        m_fmls.push_back(fml);
        m_names.push_back(symbol(name));
    }
    unsigned size() const { return m_fmls.size(); }
    expr*const* c_ptr() const { return m_fmls.c_ptr(); }
    expr* operator[](unsigned i) { return m_fmls[i].get(); }
    symbol const& name(unsigned i) { return m_names[i]; }
    void set_has_conjecture() { 
        m_has_conjecture = true;
        m_conjecture_index = m_fmls.size();
    }
    bool has_conjecture() const { return m_has_conjecture; }
    unsigned conjecture_index() const { return m_conjecture_index; }
};

bool tptp5_parse(ast_manager& m, char const* filename, named_formulas& fmls);
#endif

#endif
