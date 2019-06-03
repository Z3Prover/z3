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
    unsigned m_external_j;
    bool m_is_integer;
    std::string m_name;
public:
    ext_var_info() {}
    ext_var_info(unsigned j): ext_var_info(j, true) {}
    ext_var_info(unsigned j , bool is_int) : m_external_j(j), m_is_integer(is_int) {}
    ext_var_info(unsigned j , bool is_int, std::string name) : m_external_j(j), m_is_integer(is_int), m_name(name) {}
    
    unsigned external_j() const { return m_external_j;}
    bool is_integer() const {return m_is_integer;}
    void set_name(std::string name) { m_name = name; }
    std::string get_name() const { return m_name; }
};

class var_register {
    svector<ext_var_info> m_local_to_external;
    std::unordered_map<unsigned, unsigned> m_external_to_local;
    unsigned m_local_offset;
public:
    var_register(unsigned offset) : m_local_offset(offset) {}
    
    unsigned add_var(unsigned user_var) {
        return add_var(user_var, true);
    }    

    void set_name(unsigned j, std::string name) {
        m_local_to_external[j].set_name(name);
    }

    std::string get_name(unsigned j) const {
        return m_local_to_external[j].get_name();
    }

    unsigned add_var(unsigned user_var, bool is_int) {
        auto t = m_external_to_local.find(user_var);
        if (t != m_external_to_local.end()) {
            return t->second;
        }

        m_local_to_external.push_back(ext_var_info(user_var, is_int));
        return m_external_to_local[user_var] = size() - 1 + m_local_offset;
    }

    svector<unsigned> vars() const {
        svector<unsigned> ret;
        for (const auto& p : m_local_to_external) {
            ret.push_back(p.external_j());
        }
        return ret;
    }
    
    unsigned local_to_external(unsigned local_var) const {
        SASSERT(local_var >= m_local_offset);
        return m_local_to_external[local_var - m_local_offset].external_j();
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
        return it->second;
    }

    bool external_is_used(unsigned ext_j) const {
        auto it = m_external_to_local.find(ext_j);
        return it != m_external_to_local.end();
    }

    bool external_is_used(unsigned ext_j, unsigned & local_j ) const {
        auto it = m_external_to_local.find(ext_j);
        if ( it == m_external_to_local.end()) {
            local_j = -1;
            return false;
        }
        local_j = it->second;
        return true;
    }

    bool external_is_used(unsigned ext_j, unsigned & local_j, bool & is_int ) const {
        auto it = m_external_to_local.find(ext_j);
        if ( it == m_external_to_local.end()){
            local_j = -1;
            return false;
        }
        local_j = it->second;
        SASSERT(local_j >= m_local_offset);
        is_int = m_local_to_external[local_j - m_local_offset].is_integer();
        return true;
    }

    
    bool local_is_int(unsigned j) const {
        SASSERT(j >= m_local_offset);
        return m_local_to_external[j - m_local_offset].is_integer();
    }

    void shrink(unsigned shrunk_size) {
        for (unsigned j = size(); j-- > shrunk_size;) {
            m_external_to_local.erase(m_local_to_external[j].external_j());
        }
        m_local_to_external.resize(shrunk_size);
    }
    
};
}
