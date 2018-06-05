/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    <name>

Abstract:

    <abstract>

Author:
    Lev Nachmanson (levnach)

Revision History:


--*/
#pragma once
namespace lp  {
class var_register {
    svector<unsigned> m_local_vars_to_external;
    std::unordered_map<unsigned, unsigned> m_external_vars_to_local;
public:
    unsigned add_var(unsigned user_var) {
        auto t = m_external_vars_to_local.find(user_var);
        if (t != m_external_vars_to_local.end()) {
            return t->second;
        }

        unsigned ret = size();
        m_external_vars_to_local[user_var] = ret;
        m_local_vars_to_external.push_back(user_var);
        return ret;
    }

    const svector<unsigned> & vars() const { return m_local_vars_to_external; }
    
    unsigned local_var_to_user_var(unsigned local_var) const {
        return m_local_vars_to_external[local_var];
    }
    unsigned size() const {
        return m_local_vars_to_external.size();
    }
    void clear() {
        m_local_vars_to_external.clear();
        m_external_vars_to_local.clear();
    }
};
}
