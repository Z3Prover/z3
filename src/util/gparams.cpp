/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    gparams.cpp

Abstract:

    Global parameter management.

Author:

    Leonardo (leonardo) 2012-11-29

Notes:

--*/
#include"gparams.h"
#include"dictionary.h"

extern void gparams_register_modules();

struct gparams::imp {
    dictionary<param_descrs*> m_module_param_descrs;
    param_descrs              m_param_descrs;
    dictionary<params_ref *>  m_module_params;
    params_ref                m_params;
    params_ref                m_empty;
public:
    imp() {
    }

    ~imp() {
        {
            dictionary<param_descrs*>::iterator it  = m_module_param_descrs.begin();
            dictionary<param_descrs*>::iterator end = m_module_param_descrs.end();
            for (; it != end; ++it) {
                dealloc(it->m_value);
            }
        }
        {
            dictionary<params_ref*>::iterator it  = m_module_params.begin();
            dictionary<params_ref*>::iterator end = m_module_params.end();
            for (; it != end; ++it) {
                dealloc(it->m_value);
            }
        }
    }

    void register_global(param_descrs & d) {
        m_param_descrs.copy(d);
    }

    void register_module(char const * module_name, param_descrs * d) {
        symbol s(module_name);
        param_descrs * old_d;
        if (m_module_param_descrs.find(s, old_d)) {
            old_d->copy(*d);
            dealloc(d);
        }
        else {
            m_module_param_descrs.insert(s, d);
        }
    }

    void display(std::ostream & out, unsigned indent, bool smt2_style) {
        m_param_descrs.display(out, indent, smt2_style);
        dictionary<param_descrs*>::iterator it  = m_module_param_descrs.begin();
        dictionary<param_descrs*>::iterator end = m_module_param_descrs.end();
        for (; it != end; ++it) {
            out << "[module] " << it->m_key << "\n";
            it->m_value->display(out, indent + 4, smt2_style);
        }
    }

    void normalize(char const * name, /* out */ symbol & mod_name, /* out */ symbol & param_name) {
        if (*name == ':')
            name++;
        std::string tmp = name;
        unsigned n = tmp.size();
        for (unsigned i = 0; i < n; i++) {
            if (tmp[i] >= 'A' && tmp[i] <= 'Z')
                tmp[i] = tmp[i] - 'A' + 'a';
            else if (tmp[i] == '-')
                tmp[i] = '_';
        }
        for (unsigned i = 0; i < n; i++) {
            if (tmp[i] == '.') {
                param_name = tmp.substr(i+1).c_str();
                tmp.resize(i);
                mod_name   = tmp.c_str();
                return;
            }
        }
        param_name = tmp.c_str();
        mod_name   = symbol::null;
    }

    params_ref & get_params(symbol const & mod_name) {
        if (mod_name == symbol::null) {
            return m_params;
        }
        else {
            params_ref * p;
            if (m_module_params.find(mod_name, p)) {
                return *p;
            }
            else {
                p = alloc(params_ref);
                m_module_params.insert(mod_name, p);
                return *p;
            }
        }
    }

    void set(param_descrs const & d, symbol const & param_name, char const * value, symbol const & mod_name) {
        param_kind k = d.get_kind(param_name);
        params_ref & ps = get_params(mod_name);
        if (k == CPK_INVALID) {
            if (mod_name == symbol::null)
                throw default_exception("unknown parameter '%s'", param_name.bare_str());
            else
                throw default_exception("unknown parameter '%s' at module '%s'", param_name.bare_str(), mod_name.bare_str());
        }
        else if (k == CPK_UINT) {
            long val = strtol(value, 0, 10);
            ps.set_uint(param_name, static_cast<unsigned>(val));
        }
        else if (k == CPK_BOOL) {
            if (strcmp(value, "true") == 0) {
                ps.set_bool(param_name, true);
            }
            else if (strcmp(value, "false") == 0) {
                ps.set_bool(param_name, false);
            }
            else {
                if (mod_name == symbol::null)
                    throw default_exception("invalid value '%s' for Boolean parameter '%s'", value, param_name.bare_str());
                else
                    throw default_exception("invalid value '%s' for Boolean parameter '%s' at module '%s'", value, param_name.bare_str(), mod_name.bare_str());
            }
        }
        else if (k == CPK_SYMBOL) {
            ps.set_sym(param_name, symbol(value));
        }
        else if (k == CPK_STRING) {
            ps.set_str(param_name, value);
        }
        else {
            if (mod_name == symbol::null)
                throw default_exception("unsupported parameter type '%s'", param_name.bare_str());
            else
                throw default_exception("unsupported parameter type '%s' at module '%s'", param_name.bare_str(), mod_name.bare_str());
        }
    }

    void set(char const * name, char const * value) {
        symbol m, p;
        normalize(name, m, p);
        if (m == symbol::null) {
            set(m_param_descrs, p, value, m);
        }
        else {
            param_descrs * d;
            if (m_module_param_descrs.find(m, d)) {
                set(*d, p, value, m);
            }
            else {
                throw default_exception("invalid parameter, unknown module '%s'", m.bare_str());
            }
        }
    }

    std::string get_value(char const * name) {
        
    }


    params_ref const & get_module(symbol const & module_name) {
        params_ref * ps = 0;
        if (m_module_params.find(module_name, ps)) {
            return *ps;
        }
        else {
            return m_empty;
        }
    }
    
    params_ref const & get() { 
        return m_params;
    }

};

gparams::imp * gparams::g_imp = 0;

void gparams::set(char const * name, char const * value) {
    SASSERT(g_imp != 0);
    g_imp->set(name, value);
}

std::string gparams::get_value(char const * name) {
    SASSERT(g_imp != 0);
    g_imp->get_value(name);
}

void gparams::register_global(param_descrs & d) {
    SASSERT(g_imp != 0);
    g_imp->register_global(d);
}

void gparams::register_module(char const * module_name, param_descrs * d) {
    SASSERT(g_imp != 0);
    g_imp->register_module(module_name, d);
}

params_ref const & gparams::get_module(char const * module_name) {
    return get_module(symbol(module_name));
}

params_ref const & gparams::get_module(symbol const & module_name) {
    SASSERT(g_imp != 0);
    return g_imp->get_module(module_name);
}

params_ref const & gparams::get() {
    SASSERT(g_imp != 0);
    return g_imp->get();
}

void gparams::display(std::ostream & out, unsigned indent, bool smt2_style) {
    SASSERT(g_imp != 0);
    g_imp->display(out, indent, smt2_style);
}

void gparams::init() {
    g_imp = alloc(imp);
    gparams_register_modules();
}

void gparams::finalize() {
    if (g_imp != 0) {
        dealloc(g_imp);
        g_imp = 0;
    }
}


