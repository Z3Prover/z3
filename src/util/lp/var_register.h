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
class ext_var_info {
    unsigned m_internal_j; // the internal index
    bool m_is_integer;
public:
    ext_var_info() {}
    ext_var_info(unsigned j): ext_var_info(j, true) {}
    ext_var_info(unsigned j , bool is_int) : m_internal_j(j), m_is_integer(is_int) {}
    unsigned internal_j() const { return m_internal_j;}
    bool is_integer() const {return m_is_integer;}
};

class var_register {
    svector<unsigned> m_local_to_external;
    std::unordered_map<unsigned, ext_var_info> m_external_to_local;
public:
    unsigned add_var(unsigned user_var) {
        return add_var(user_var, true);
    }    
    unsigned add_var(unsigned user_var, bool is_int) {
        auto t = m_external_to_local.find(user_var);
        if (t != m_external_to_local.end()) {
            return t->second.internal_j();
        }

        unsigned j = size();
        m_external_to_local[user_var] = ext_var_info(j, is_int);
        m_local_to_external.push_back(user_var);
        return j;
    }

    const svector<unsigned> & vars() const { return m_local_to_external; }
    
    unsigned local_to_external(unsigned local_var) const {
        return m_local_to_external[local_var];
    }
    unsigned size() const {
        return m_local_to_external.size();
    }
    void clear() {
        m_local_to_external.clear();
        m_external_to_local.clear();
    }

    unsigned external_to_local(unsigned j) const {
        auto it = m_external_to_local.find(j);
        lp_assert(it != m_external_to_local.end());
        return it->second.internal_j();
    }

    bool external_is_int(unsigned j) const {
        auto it = m_external_to_local.find(j);
        lp_assert(it != m_external_to_local.end());
        return it->second.is_integer();
    }

    bool external_is_used(unsigned ext_j) const {
        auto it = m_external_to_local.find(ext_j);
        return it != m_external_to_local.end();
    }

    bool external_is_used(unsigned ext_j, unsigned & local_j ) const {
        auto it = m_external_to_local.find(ext_j);
        if ( it == m_external_to_local.end())
            return false;
        local_j = it->second.internal_j();
        return true;
    }

    bool external_is_used(unsigned ext_j, unsigned & local_j, bool & is_int ) const {
        auto it = m_external_to_local.find(ext_j);
        if ( it == m_external_to_local.end())
            return false;
        local_j = it->second.internal_j();
        is_int = it->second.is_integer();
        return true;
    }

    
    bool local_is_int(unsigned j) const {
        return external_is_int(m_local_to_external[j]);
    }

    void shrink(unsigned shrunk_size) {
        for (unsigned j = size(); j-- > shrunk_size;) {
            m_external_to_local.erase(m_local_to_external[j]);
        }
        m_local_to_external.resize(shrunk_size);
    }
    
};
}
