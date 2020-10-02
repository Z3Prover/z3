/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    fpa_factory.h

Abstract:

    Floating-Point Theory Plugin

Author:

    Christoph (cwinter) 2014-04-23

--*/
#pragma once

#include "ast/seq_decl_plugin.h"
#include "model/model_core.h"
#include "model/value_factory.h"

class fpa_value_factory : public value_factory {
    fpa_util          m_util;
    
    virtual app * mk_value_core(mpf const & val, sort * s) {
        SASSERT(m_util.get_ebits(s) == val.get_ebits());
        SASSERT(m_util.get_sbits(s) == val.get_sbits());
        return m_util.mk_value(val);
    }
    
 public:
    fpa_value_factory(ast_manager & m, family_id fid) :
        value_factory(m, fid),
        m_util(m) {}
    
    ~fpa_value_factory() override {}
    
    expr * get_some_value(sort * s) override {
        mpf_manager & mpfm = m_util.fm();
        
        if (m_util.is_rm(s))
            return m_util.mk_round_toward_zero();
        else {
            scoped_mpf q(mpfm);
            mpfm.set(q, m_util.get_ebits(s), m_util.get_sbits(s), 0);
            return m_util.mk_value(q);
        }
    }
    
    bool get_some_values(sort * s, expr_ref & v1, expr_ref & v2) override {
        mpf_manager & mpfm = m_util.fm();
        
        if (m_util.is_rm(s))
            v1 = v2 = m_util.mk_round_toward_zero();
        else {
            scoped_mpf q(mpfm);
            mpfm.set(q, m_util.get_ebits(s), m_util.get_sbits(s), 0);
            v1 = m_util.mk_value(q);
            mpfm.set(q, m_util.get_ebits(s), m_util.get_sbits(s), 1);
            v2 = m_util.mk_value(q);
        }
        return true;
    }
    
    expr * get_fresh_value(sort * s) override { return get_some_value(s); }
    void register_value(expr * n) override { /* Ignore */ }
    
    app * mk_value(mpf const & x) {
        return m_util.mk_value(x);
    }
};


