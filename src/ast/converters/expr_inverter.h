/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    expr_inverter.h

Abstract:

    inverter interface and instance

Author:

    Nikolaj Bjorner (nbjorner) 2022-10-11


--*/
#pragma once

#include "ast/converters/generic_model_converter.h"

class iexpr_inverter {
protected:
    ast_manager&                m;
    std::function<bool(expr*)>  m_is_var;
    generic_model_converter_ref m_mc;
    bool                        m_produce_proofs = false;

    bool uncnstr(expr* e) const { return m_is_var(e); }
    bool uncnstr(unsigned num, expr * const * args) const;
    void mk_fresh_uncnstr_var_for(sort* s, expr_ref& v);
    void mk_fresh_uncnstr_var_for(func_decl* f, expr_ref& v) { mk_fresh_uncnstr_var_for(f->get_range(), v); }
    void add_def(expr * v, expr * def);
    void add_defs(unsigned num, expr * const * args, expr * u, expr * identity);

public:
    iexpr_inverter(ast_manager& m): m(m) {}
    virtual ~iexpr_inverter() {}
    virtual void set_is_var(std::function<bool(expr*)>& is_var) { m_is_var = is_var; }
    virtual void set_model_converter(generic_model_converter* mc) { m_mc = mc; }
    virtual void set_produce_proofs(bool p) { m_produce_proofs = true; }
    
    virtual bool operator()(func_decl* f, unsigned n, expr* const* args, expr_ref& new_expr) = 0;
    virtual bool mk_diff(expr* t, expr_ref& r) = 0;
    virtual family_id get_fid() const = 0;
};

class expr_inverter : public iexpr_inverter {
    ptr_vector<iexpr_inverter> m_inverters;

public:
    expr_inverter(ast_manager& m);
    ~expr_inverter() override;
    bool operator()(func_decl* f, unsigned n, expr* const* args, expr_ref& new_expr) override;
    bool mk_diff(expr* t, expr_ref& r) override;
    void set_is_var(std::function<bool(expr*)>& is_var) override; 
    void set_model_converter(generic_model_converter* mc) override;
    void set_produce_proofs(bool p) override;
    family_id get_fid() const override { return null_family_id;  }
};
