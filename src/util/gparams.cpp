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
        #pragma omp critical (gparams)
        {
           m_param_descrs.copy(d);
        }
    }

    void register_module(char const * module_name, param_descrs * d) {
        #pragma omp critical (gparams)
        {
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
    }

    void display(std::ostream & out, unsigned indent, bool smt2_style) {
        #pragma omp critical (gparams)
        {
            m_param_descrs.display(out, indent, smt2_style);
            dictionary<param_descrs*>::iterator it  = m_module_param_descrs.begin();
            dictionary<param_descrs*>::iterator end = m_module_param_descrs.end();
            for (; it != end; ++it) {
                out << "[module] " << it->m_key << "\n";
                it->m_value->display(out, indent + 4, smt2_style);
            }
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
            params_ref * p = 0;
            if (!m_module_params.find(mod_name, p)) {
                p = alloc(params_ref);
                m_module_params.insert(mod_name, p);
            }
            SASSERT(p != 0);
            return *p;
        }
    }

    void set(param_descrs const & d, symbol const & param_name, char const * value, symbol const & mod_name) {
        param_kind k = d.get_kind(param_name);
        params_ref & ps = get_params(mod_name);
        if (k == CPK_INVALID) {
            if (mod_name == symbol::null)
                throw exception("unknown parameter '%s'", param_name.bare_str());
            else
                throw exception("unknown parameter '%s' at module '%s'", param_name.bare_str(), mod_name.bare_str());
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
                    throw exception("invalid value '%s' for Boolean parameter '%s'", value, param_name.bare_str());
                else
                    throw exception("invalid value '%s' for Boolean parameter '%s' at module '%s'", value, param_name.bare_str(), mod_name.bare_str());
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
                throw exception("unsupported parameter type '%s'", param_name.bare_str());
            else
                throw exception("unsupported parameter type '%s' at module '%s'", param_name.bare_str(), mod_name.bare_str());
        }
    }

    void set(char const * name, char const * value) {
        bool error = false;
        std::string error_msg;
        #pragma omp critical (gparams)
        {
            try {
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
                        throw exception("invalid parameter, unknown module '%s'", m.bare_str());
                    }
                }
            }
            catch (exception & ex) {
                // Exception cannot cross critical section boundaries.
                error = true;
                error_msg = ex.msg();
            }
        }
        if (error)
            throw exception(error_msg);
    }

    std::string get_value(params_ref const & ps, symbol const & p) {
        std::ostringstream buffer;
        ps.display(buffer, p);
        return buffer.str();
    }

    std::string get_default(param_descrs const & d, symbol const & p, symbol const & m) {
        if (!d.contains(p)) {
            if (m == symbol::null)
                throw exception("unknown parameter '%s'", p.bare_str());
            else
                throw exception("unknown parameter '%s' at module '%s'", p.bare_str(), m.bare_str());
        }
        char const * r = d.get_default(p);
        if (r == 0) 
            return "default";
        return r;
    }

    std::string get_value(char const * name) {
        std::string r;
        bool error = false;
        std::string error_msg;
        #pragma omp critical (gparams)
        {
            try {
                symbol m, p;
                normalize(name, m, p);
                if (m == symbol::null) {
                    if (m_params.contains(p)) {
                        r = get_value(m_params, p);
                    }
                    else {
                        r = get_default(m_param_descrs, p, m);
                    }
                }
                else {
                    params_ref * ps = 0;
                    if (m_module_params.find(m, ps) && ps->contains(p)) {
                        r = get_value(*ps, p);
                    }
                    else {
                        param_descrs * d;
                        if (m_module_param_descrs.find(m, d)) {
                            r = get_default(*d, p, m);
                        }
                        else {
                            throw exception("unknown module '%s'", m.bare_str());
                        }
                    }
                }
            }
            catch (exception & ex) {
                // Exception cannot cross critical section boundaries.
                error = true;
                error_msg = ex.msg();
            }
        }
        if (error)
            throw exception(error_msg);
        return r;
    }

    params_ref get_module(symbol const & module_name) {
        params_ref result;
        params_ref * ps = 0;
        #pragma omp critical (gparams)
        {
            if (m_module_params.find(module_name, ps)) {
                result = *ps;
            }
        }
        return result;
    }
    
    params_ref get() { 
        params_ref result;
        #pragma omp critical (gparams)
        {
            result = m_params;
        }
        return result;
    }

};

gparams::imp * gparams::g_imp = 0;

void gparams::set(char const * name, char const * value) {
    SASSERT(g_imp != 0);
    g_imp->set(name, value);
}

void gparams::set(symbol const & name, char const * value) {
    SASSERT(g_imp != 0);
    g_imp->set(name.bare_str(), value);
}

std::string gparams::get_value(char const * name) {
    SASSERT(g_imp != 0);
    return g_imp->get_value(name);
}

std::string gparams::get_value(symbol const & name) {
    SASSERT(g_imp != 0);
    return g_imp->get_value(name.bare_str());
}

void gparams::register_global(param_descrs & d) {
    SASSERT(g_imp != 0);
    g_imp->register_global(d);
}

void gparams::register_module(char const * module_name, param_descrs * d) {
    SASSERT(g_imp != 0);
    g_imp->register_module(module_name, d);
}

params_ref gparams::get_module(char const * module_name) {
    return get_module(symbol(module_name));
}

params_ref gparams::get_module(symbol const & module_name) {
    SASSERT(g_imp != 0);
    return g_imp->get_module(module_name);
}

params_ref gparams::get() {
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


