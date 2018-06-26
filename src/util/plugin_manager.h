/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    plugin_manager.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2007-09-18.

Revision History:

--*/
#ifndef PLUGIN_MANAGER_H_
#define PLUGIN_MANAGER_H_

#include "util/util.h"

template<typename Plugin>
class plugin_manager {
    ptr_vector<Plugin>   m_fid2plugins;
    ptr_vector<Plugin>   m_plugins;
public:
    ~plugin_manager() {
        reset();
    }

    void reset() {
        std::for_each(m_plugins.begin(), m_plugins.end(), delete_proc<Plugin>());
        release();
    }

    /**
       \brief Release ownership of the plugins.
    */
    void release() {
        m_fid2plugins.reset();
        m_plugins.reset();
    }
    
    void register_plugin(Plugin * p) {
        SASSERT(p);
        family_id fid = p->get_family_id();
        SASSERT(m_fid2plugins.get(fid, 0) == 0);
        m_fid2plugins.setx(fid, p, 0);
        m_plugins.push_back(p);
    }
    
    Plugin * get_plugin(family_id fid) const {
        if (fid == null_family_id) {
            return nullptr;
        }
        return m_fid2plugins.get(fid, 0);
    }

    ptr_vector<Plugin> const& plugins() const { return m_plugins; }

    typename ptr_vector<Plugin>::const_iterator begin() const { 
        return m_plugins.begin(); 
    }

    typename ptr_vector<Plugin>::const_iterator end() const { 
        return m_plugins.end(); 
    }
};

#endif /* PLUGIN_MANAGER_H_ */

