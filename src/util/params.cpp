/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    params.cpp

Abstract:

    Parameters

Author:

    Leonardo (leonardo) 2011-05-09

Notes:

--*/
#include "util/params.h"
#include "util/rational.h"
#include "util/symbol.h"
#include "util/dictionary.h"

params_ref params_ref::g_empty_params_ref;

std::string norm_param_name(char const * n) {
    if (n == nullptr)
        return "_";
    if (*n == ':')
        n++;
    std::string r = n;
    unsigned sz = static_cast<unsigned>(r.size());
    if (sz == 0)
        return "_";
    for (unsigned i = 0; i < sz; i++) {
        char curr = r[i];
        if ('A' <= curr && curr <= 'Z')
            r[i] = curr - 'A' + 'a';
        else if (curr == '-' || curr == ':')
            r[i] = '_';
    }
    return r;
}

std::string norm_param_name(symbol const & n) {
    return norm_param_name(n.bare_str());
}

struct param_descrs::imp {
    struct info {
        param_kind   m_kind;
        char const * m_descr;
        char const * m_default;
        char const * m_module;

        info(param_kind k, char const * descr, char const * def, char const* module):
            m_kind(k),
            m_descr(descr),
            m_default(def),
            m_module(module) {
        }

        info():
            m_kind(CPK_INVALID), 
            m_descr(nullptr),
            m_default(nullptr),
            m_module(nullptr) {
        }
    };

    dictionary<info> m_info;
    svector<symbol> m_names;

    void insert(symbol const & name, param_kind k, char const * descr, char const * def, char const* module) {
        SASSERT(!name.is_numerical());
        info i;
        if (m_info.find(name, i)) {
            SASSERT(i.m_kind == k);
            return;
        }
        m_info.insert(name, info(k, descr, def, module));
        m_names.push_back(name);
    }

    void erase(symbol const & name) {
        m_info.erase(name);
    }

    bool contains(symbol const & name) const {
        return m_info.contains(name);
    }
                                    
    param_kind get_kind(symbol const & name) const {
        info i;
        if (m_info.find(name, i))
            return i.m_kind;
        return CPK_INVALID;
    }

    bool split_name(symbol const& name, symbol & prefix, symbol & suffix) const {
        if (name.is_numerical()) return false;
        char const* str = name.bare_str();
        char const* period = strchr(str,'.');
        if (!period) return false;
        svector<char> prefix_((unsigned)(period-str), str);
        prefix_.push_back(0);
        prefix = symbol(prefix_.c_ptr());
        suffix = symbol(period + 1);
        return true;
    }

    param_kind get_kind_in_module(symbol & name) const {
        param_kind k = get_kind(name);
        symbol prefix, suffix;
        if (k == CPK_INVALID && split_name(name, prefix, suffix)) {   
            k = get_kind(suffix);
            if (k != CPK_INVALID) {
                if (symbol(get_module(suffix)) == prefix) {
                    name = suffix;
                }
                else {
                    k = CPK_INVALID;
                }
            }
        }
        return k;
    }

    char const* get_module(symbol const& name) const {
        info i;
        if (m_info.find(name, i)) 
            return i.m_module;
        return nullptr;
    }

    char const * get_descr(symbol const & name) const {
        info i;
        if (m_info.find(name, i))
            return i.m_descr;
        return nullptr;
    }

    char const * get_default(symbol const & name) const {
        info i;
        if (m_info.find(name, i))
            return i.m_default;
        return nullptr;
    }

    unsigned size() const {
        return m_names.size();
    }
    
    symbol get_param_name(unsigned idx) const {
        return m_names[idx];
    }

    struct lt {
        bool operator()(symbol const & s1, symbol const & s2) const { return strcmp(s1.bare_str(), s2.bare_str()) < 0; }
    };

    void display(std::ostream & out, unsigned indent, bool smt2_style, bool include_descr) const {
        svector<symbol> names;
        dictionary<info>::iterator it  = m_info.begin();
        dictionary<info>::iterator end = m_info.end();
        for (; it != end; ++it) {
            names.push_back(it->m_key);
        }
        std::sort(names.begin(), names.end(), lt());
        svector<symbol>::iterator it2  = names.begin();
        svector<symbol>::iterator end2 = names.end();
        for (; it2 != end2; ++it2) {
            for (unsigned i = 0; i < indent; i++) out << " ";
            if (smt2_style)
                out << ':';
            char const * s = it2->bare_str();
            unsigned n = static_cast<unsigned>(strlen(s));
            for (unsigned i = 0; i < n; i++) {
                if (smt2_style && s[i] == '_')
                    out << '-';
                else if (!smt2_style && s[i] == '-')
                    out << '_';
                else if (s[i] >= 'A' && s[i] <= 'Z')
                    out << (s[i] - 'A' + 'a');
                else 
                    out << s[i];
            }
            info d;
            m_info.find(*it2, d);
            SASSERT(d.m_descr);
            out << " (" << d.m_kind << ")";
            if (include_descr)
                out << " " << d.m_descr;
            if (d.m_default != nullptr)
                out << " (default: " << d.m_default << ")";
            out << "\n";
        }
    }

    void copy(param_descrs & other) {
        dictionary<info>::iterator it  = other.m_imp->m_info.begin();
        dictionary<info>::iterator end = other.m_imp->m_info.end();
        for (; it != end; ++it) {
            insert(it->m_key, it->m_value.m_kind, it->m_value.m_descr, it->m_value.m_default, it->m_value.m_module);
        }
    }

};

param_descrs::param_descrs() {
    m_imp = alloc(imp);
}

param_descrs::~param_descrs() {
    dealloc(m_imp);
}

void param_descrs::copy(param_descrs & other) {
    m_imp->copy(other);
}

void param_descrs::insert(symbol const & name, param_kind k, char const * descr, char const * def, char const* module) {
    m_imp->insert(name, k, descr, def, module);
}

void param_descrs::insert(char const * name, param_kind k, char const * descr, char const * def, char const* module) {
    insert(symbol(name), k, descr, def, module);
}

bool param_descrs::contains(char const * name) const {
    return contains(symbol(name));
}

bool param_descrs::contains(symbol const & name) const {
    return m_imp->contains(name);
}

char const * param_descrs::get_descr(char const * name) const {
    return get_descr(symbol(name));
}

char const * param_descrs::get_descr(symbol const & name) const {
    return m_imp->get_descr(name);
}

char const * param_descrs::get_default(char const * name) const {
    return get_default(symbol(name));
}

char const * param_descrs::get_default(symbol const & name) const {
    return m_imp->get_default(name);
}

void param_descrs::erase(symbol const & name) {
    m_imp->erase(name);
}

void param_descrs::erase(char const * name) {
    erase(symbol(name));
}

param_kind param_descrs::get_kind_in_module(symbol & name) const {
    return m_imp->get_kind_in_module(name);
}

param_kind param_descrs::get_kind(symbol const & name) const {
    return m_imp->get_kind(name);
}

param_kind param_descrs::get_kind(char const * name) const {
    return get_kind(symbol(name));
}

unsigned param_descrs::size() const {
    return m_imp->size();
}

symbol param_descrs::get_param_name(unsigned i) const {
    return m_imp->get_param_name(i);
}

char const* param_descrs::get_module(symbol const& name) const {
    return m_imp->get_module(name);
}

void param_descrs::display(std::ostream & out, unsigned indent, bool smt2_style, bool include_descr) const {
    return m_imp->display(out, indent, smt2_style, include_descr);
}

void insert_max_memory(param_descrs & r) {
    r.insert("max_memory", CPK_UINT, "(default: infty) maximum amount of memory in megabytes.");
}

void insert_max_steps(param_descrs & r) {
    r.insert("max_steps", CPK_UINT, "(default: infty) maximum number of steps.");
}

void insert_produce_models(param_descrs & r) {
    r.insert("produce_models", CPK_BOOL, "(default: false) model generation.");
}

void insert_produce_proofs(param_descrs & r) {
    r.insert("produce_proofs", CPK_BOOL, "(default: false) proof generation.");
}

void insert_timeout(param_descrs & r) {
    r.insert("timeout", CPK_UINT, "(default: infty) timeout in milliseconds.");
}

class params {
    friend class params_ref;
    struct value {
        param_kind m_kind;
        union {
            bool          m_bool_value;
            unsigned      m_uint_value;
            double        m_double_value;
            char const *  m_str_value;
            char const *  m_sym_value;
            rational *    m_rat_value;
        };
    };
    typedef std::pair<symbol, value> entry;
    svector<entry> m_entries;
    unsigned       m_ref_count;
    void del_value(entry & e);
    void del_values();

public:
    params():m_ref_count(0) {}
    ~params() {
        reset();
    }

    void inc_ref() { m_ref_count++; }
    void dec_ref() { 
        SASSERT(m_ref_count > 0); 
        if (--m_ref_count == 0) dealloc(this); 
    }

    bool empty() const { return m_entries.empty(); }
    bool contains(symbol const & k) const;
    bool contains(char const * k) const;

    void reset();
    void reset(symbol const & k);
    void reset(char const * k);

    void validate(param_descrs const & p) {
        svector<params::entry>::iterator it  = m_entries.begin();  
        svector<params::entry>::iterator end = m_entries.end();
        symbol suffix, prefix;
        for (; it != end; ++it) {                                
            param_kind expected = p.get_kind_in_module(it->first);
            if (expected == CPK_INVALID) {
                std::stringstream strm;
                strm << "unknown parameter '" << it->first.str() << "'\n";    
                strm << "Legal parameters are:\n";
                p.display(strm, 2, false, false);
                throw default_exception(strm.str());
            }
            if (it->second.m_kind != expected && 
                !(it->second.m_kind == CPK_UINT && expected == CPK_NUMERAL)) {
                std::stringstream strm;
                strm << "Parameter " << it->first.str() << " was given argument of type ";
                strm << it->second.m_kind << ", expected " << expected;                
                throw default_exception(strm.str());
            }
        }
    }
    
    // getters
    bool get_bool(symbol const & k, bool _default) const;
    bool get_bool(char const * k, bool _default) const;
    unsigned get_uint(symbol const & k, unsigned _default) const;
    unsigned get_uint(char const * k, unsigned _default) const;
    double get_double(symbol const & k, double _default) const;
    double get_double(char const * k, double _default) const;
    char const * get_str(symbol const & k, char const * _default) const;
    char const * get_str(char const * k, char const * _default) const;
    rational get_rat(symbol const & k, rational const & _default) const;
    rational get_rat(char const * k, rational const & _default) const; 
    symbol get_sym(symbol const & k, symbol const & _default) const;
    symbol get_sym(char const * k, symbol const & _default) const;

    bool get_bool(char const * k, params_ref const & fallback, bool _default) const;
    unsigned get_uint(char const * k, params_ref const & fallback, unsigned _default) const;
    double get_double(char const * k, params_ref const & fallback, double _default) const;
    char const * get_str(char const * k, params_ref const & fallback, char const * _default) const;
    symbol get_sym(char const * k, params_ref const & fallback, symbol const & _default) const;

    // setters
    void set_bool(symbol const & k, bool v);
    void set_bool(char const * k, bool  v);
    void set_uint(symbol const & k, unsigned v);
    void set_uint(char const * k, unsigned v);
    void set_double(symbol const & k, double v);
    void set_double(char const * k, double v);
    void set_str(symbol const & k, char const * v);
    void set_str(char const * k, char const * v);
    void set_rat(symbol const & k, rational const & v);
    void set_rat(char const * k, rational const & v); 
    void set_sym(symbol const & k, symbol const & v);
    void set_sym(char const * k, symbol const & v);

    void display(std::ostream & out) const {
        out << "(params";
        svector<params::entry>::const_iterator it  = m_entries.begin();  
        svector<params::entry>::const_iterator end = m_entries.end();
        for (; it != end; ++it) {
            out << " " << it->first;            
            switch (it->second.m_kind) {
            case CPK_BOOL:
                out << " " << (it->second.m_bool_value?"true":"false");
                break;
            case CPK_UINT:
                out << " " <<it->second.m_uint_value;
                break;
            case CPK_DOUBLE:
                out << " " << it->second.m_double_value;
                break;
            case CPK_NUMERAL:
                out << " " << *(it->second.m_rat_value);
                break;
            case CPK_SYMBOL:
                out << " " << symbol::mk_symbol_from_c_ptr(it->second.m_sym_value);
                break;
            case CPK_STRING:
                out << " " << it->second.m_str_value;
                break;
            default:
                UNREACHABLE();
                break;
            }
        }
        out << ")";
    }

    void display_smt2(std::ostream & out, char const* module, param_descrs& descrs) const {
        svector<params::entry>::const_iterator it  = m_entries.begin();  
        svector<params::entry>::const_iterator end = m_entries.end();
        for (; it != end; ++it) {
            if (!descrs.contains(it->first)) continue;
            out << "(set-option :";
            out << module << ".";        
            out << it->first;
            switch (it->second.m_kind) {
            case CPK_BOOL:
                out << " " << (it->second.m_bool_value?"true":"false");
                break;
            case CPK_UINT:
                out << " " <<it->second.m_uint_value;
                break;
            case CPK_DOUBLE:
                out << " " << it->second.m_double_value;
                break;
            case CPK_NUMERAL:
                out << " " << *(it->second.m_rat_value);
                break;
            case CPK_SYMBOL:
                out << " " << symbol::mk_symbol_from_c_ptr(it->second.m_sym_value);
                break;
            case CPK_STRING:
                out << " " << it->second.m_str_value;
                break;
            default:
                UNREACHABLE();
                break;
            }
            out << ")\n";
        }
    }

    void display(std::ostream & out, symbol const & k) const {
        svector<params::entry>::const_iterator it  = m_entries.begin();  
        svector<params::entry>::const_iterator end = m_entries.end();
        for (; it != end; ++it) {                                
            if (it->first != k)
                continue;
            switch (it->second.m_kind) {
            case CPK_BOOL:
                out << (it->second.m_bool_value?"true":"false");
                return;
            case CPK_UINT:
                out << it->second.m_uint_value;
                return;
            case CPK_DOUBLE:
                out << it->second.m_double_value;
                return;
            case CPK_NUMERAL:
                out << *(it->second.m_rat_value);
                return;
            case CPK_SYMBOL:
                out << symbol::mk_symbol_from_c_ptr(it->second.m_sym_value);
                return;
            case CPK_STRING:
                out << it->second.m_str_value;
                return;
            default:
                out << "internal";
                return;
            }
        }
        out << "default";
    }
};

params_ref::~params_ref() {
    if (m_params)
        m_params->dec_ref();
}

params_ref::params_ref(params_ref const & p):
    m_params(nullptr) {
    operator=(p);
}

void params_ref::display(std::ostream & out) const {
    if (m_params)
        m_params->display(out);
    else 
        out << "(params)";
}

void params_ref::display_smt2(std::ostream& out, char const* module, param_descrs& descrs) const {
    if (m_params)
        m_params->display_smt2(out, module, descrs);

}


void params_ref::display(std::ostream & out, char const * k) const {
    display(out, symbol(k));
}

void params_ref::display(std::ostream & out, symbol const & k) const {
    if (m_params)
        m_params->display(out, k);
    else
        out << "default";
}

void params_ref::validate(param_descrs const & p) {
    if (m_params)
        m_params->validate(p);
}

params_ref & params_ref::operator=(params_ref const & p) {
    if (p.m_params)
        p.m_params->inc_ref();
    if (m_params)
        m_params->dec_ref();
    m_params = p.m_params;
    return *this;
}

void params_ref::copy(params_ref const & src) {
    if (m_params == nullptr)
        operator=(src);
    else {
        init();
        copy_core(src.m_params);
    }
}

void params_ref::copy_core(params const * src) {
    if (src == nullptr)
        return;
    for (auto const& p : src->m_entries) {
        switch (p.second.m_kind) {
        case CPK_BOOL:
            m_params->set_bool(p.first, p.second.m_bool_value);
            break;
        case CPK_UINT:
            m_params->set_uint(p.first, p.second.m_uint_value);
            break;
        case CPK_DOUBLE:
            m_params->set_double(p.first, p.second.m_double_value);
            break;
        case CPK_NUMERAL:
            m_params->set_rat(p.first, *(p.second.m_rat_value));
            break;
        case CPK_SYMBOL:
            m_params->set_sym(p.first, symbol::mk_symbol_from_c_ptr(p.second.m_sym_value));
            break;
        case CPK_STRING:
            m_params->set_str(p.first, p.second.m_str_value);
            break;
        default:
            UNREACHABLE();
            break;
        }
    }
}

void params_ref::init() {
    if (!m_params) {
        m_params = alloc(params);
        m_params->inc_ref();
    }
    else if (m_params->m_ref_count > 1) {
        params * old = m_params;
        m_params = alloc(params);
        m_params->inc_ref();
        copy_core(old);
        old->dec_ref();
    }
    
    SASSERT(m_params->m_ref_count == 1);
}

bool params_ref::get_bool(symbol const & k, bool _default) const { return m_params ? m_params->get_bool(k, _default) : _default; }
bool params_ref::get_bool(char const * k, bool _default) const { return m_params ? m_params->get_bool(k, _default) : _default; }
unsigned params_ref::get_uint(symbol const & k, unsigned _default) const { return m_params ? m_params->get_uint(k, _default) : _default; }
unsigned params_ref::get_uint(char const * k, unsigned _default) const { return m_params ? m_params->get_uint(k, _default) : _default; }
double params_ref::get_double(symbol const & k, double _default) const { return m_params ? m_params->get_double(k, _default) : _default; }
double params_ref::get_double(char const * k, double _default) const { return m_params ? m_params->get_double(k, _default) : _default; }
char const * params_ref::get_str(symbol const & k, char const * _default) const { return m_params ? m_params->get_str(k, _default) : _default; }
char const * params_ref::get_str(char const * k, char const * _default) const { return m_params ? m_params->get_str(k, _default) : _default; }

rational params_ref::get_rat(symbol const & k, rational const & _default) const { 
    return m_params ? m_params->get_rat(k, _default) : _default; 
}

rational params_ref::get_rat(char const * k, rational const & _default) const { 
    return m_params ? m_params->get_rat(k, _default) : _default; 
}

symbol params_ref::get_sym(symbol const & k, symbol const & _default) const { 
    return m_params ? m_params->get_sym(k, _default) : _default; 
}

symbol params_ref::get_sym(char const * k, symbol const & _default) const { 
    return m_params ? m_params->get_sym(k, _default) : _default; 
}

bool params_ref::get_bool(char const * k, params_ref const & fallback, bool _default) const {
    return m_params ? m_params->get_bool(k, fallback, _default) : fallback.get_bool(k, _default);
}

unsigned params_ref::get_uint(char const * k, params_ref const & fallback, unsigned _default) const {
    return m_params ? m_params->get_uint(k, fallback, _default) : fallback.get_uint(k, _default);
}

double params_ref::get_double(char const * k, params_ref const & fallback, double _default) const {
    return m_params ? m_params->get_double(k, fallback, _default) : fallback.get_double(k, _default);
}

char const * params_ref::get_str(char const * k, params_ref const & fallback, char const * _default) const {
    return m_params ? m_params->get_str(k, fallback, _default) : fallback.get_str(k, _default);
}

symbol params_ref::get_sym(char const * k, params_ref const & fallback, symbol const & _default) const {
    return m_params ? m_params->get_sym(k, fallback, _default) : fallback.get_sym(k, _default);
}

bool params_ref::empty() const {
    if (!m_params)
        return true;
    return m_params->empty();
}

bool params_ref::contains(symbol const & k) const {
    if (!m_params)
        return false;
    return m_params->contains(k);
}

bool params_ref::contains(char const * k) const {
    if (!m_params)
        return false;
    return m_params->contains(k);
}

void params_ref::reset() {
    if (m_params)
        m_params->reset();
}

void params_ref::reset(symbol const & k) {
    if (m_params)
        m_params->reset(k);
}

void params_ref::reset(char const * k) {
    if (m_params)
        m_params->reset(k);
}

void params_ref::set_bool(symbol const & k, bool v) {
    init();
    m_params->set_bool(k, v);
}

void params_ref::set_bool(char const * k, bool  v) {
    init();
    m_params->set_bool(k, v);
}

void params_ref::set_uint(symbol const & k, unsigned v) {
    init();
    m_params->set_uint(k, v);
}

void params_ref::set_uint(char const * k, unsigned v) {
    init();
    m_params->set_uint(k, v);
}

void params_ref::set_double(symbol const & k, double v) {
    init();
    m_params->set_double(k, v);
}

void params_ref::set_double(char const * k, double v) {
    init();
    m_params->set_double(k, v);
}

void params_ref::set_str(symbol const & k, char const * v) {
    init();
    m_params->set_str(k, v);
}

void params_ref::set_str(char const * k, char const * v) {
    init();
    m_params->set_str(k, v);
}

void params_ref::set_rat(symbol const & k, rational const & v) {
    init();
    m_params->set_rat(k, v);
}

void params_ref::set_rat(char const * k, rational const & v) {
    init();
    m_params->set_rat(k, v);
}

void params_ref::set_sym(symbol const & k, symbol const & v) {
    init();
    m_params->set_sym(k, v);
}

void params_ref::set_sym(char const * k, symbol const & v) {
    init();
    m_params->set_sym(k, v);
}


void params::del_value(entry & e) {
    switch (e.second.m_kind) {
    case CPK_NUMERAL:
        if (e.second.m_kind == CPK_NUMERAL)
            dealloc(e.second.m_rat_value);
        break;
    default:
        return;
    }
}

#define TRAVERSE_ENTRIES(CODE) {                        \
    svector<entry>::iterator it  = m_entries.begin();   \
    svector<entry>::iterator end = m_entries.end();     \
    for (; it != end; ++it) {                           \
        CODE                                            \
    }                                                   \
}

#define TRAVERSE_CONST_ENTRIES(CODE) {                          \
    svector<entry>::const_iterator it  = m_entries.begin();     \
    svector<entry>::const_iterator end = m_entries.end();       \
    for (; it != end; ++it) {                                   \
        CODE                                                    \
    }                                                           \
}

void params::del_values() {
    TRAVERSE_ENTRIES(del_value(*it););
}

#define CONTAINS(k) {                                           \
    if (empty())                                                \
        return false;                                           \
    TRAVERSE_CONST_ENTRIES(if (it->first == k) return true;);   \
    return false;                                               \
}

bool params::contains(symbol const & k) const {
    CONTAINS(k);
}
 
bool params::contains(char const * k) const {
    CONTAINS(k);
}

void params::reset() {
    del_values();
    m_entries.finalize();
    SASSERT(empty());
}

#define RESET(k) {                              \
    if (empty()) return;                        \
    TRAVERSE_ENTRIES(if (it->first == k) {      \
        svector<entry>::iterator it2 = it;      \
        del_value(*it2);                        \
        ++it;                                   \
        for (; it != end; ++it, ++it2) {        \
            *it2 = *it;                         \
        }                                       \
        m_entries.pop_back();                   \
        return;                                 \
    });                                         \
}

void params::reset(symbol const & k) {
    RESET(k);
}

void params::reset(char const * k) {
    RESET(k);
}

#define GET_VALUE(MATCH_CODE, KIND) {                                           \
    if (empty()) return _default;                                                \
    TRAVERSE_CONST_ENTRIES(if (it->first == k && it->second.m_kind == KIND) {   \
        MATCH_CODE                                                              \
    });                                                                         \
    return _default;                                                             \
}
    
#define GET_SIMPLE_VALUE(FIELD_NAME, KIND) GET_VALUE(return it->second.FIELD_NAME;, KIND)

bool params::get_bool(symbol const & k, bool _default) const {
    GET_SIMPLE_VALUE(m_bool_value, CPK_BOOL);
}

bool params::get_bool(char const * k, bool _default) const {
    GET_SIMPLE_VALUE(m_bool_value, CPK_BOOL);
}

unsigned params::get_uint(symbol const & k, unsigned _default) const {
    GET_SIMPLE_VALUE(m_uint_value, CPK_UINT);
}

unsigned params::get_uint(char const * k, unsigned _default) const {
    GET_SIMPLE_VALUE(m_uint_value, CPK_UINT);
}

double params::get_double(symbol const & k, double _default) const {
    GET_SIMPLE_VALUE(m_double_value, CPK_DOUBLE);
}

double params::get_double(char const * k, double _default) const {
    GET_SIMPLE_VALUE(m_double_value, CPK_DOUBLE);
}

char const * params::get_str(symbol const & k, char const * _default) const {
    GET_SIMPLE_VALUE(m_str_value, CPK_STRING);
}

char const * params::get_str(char const * k, char const * _default) const {
    GET_SIMPLE_VALUE(m_str_value, CPK_STRING);
}

rational params::get_rat(symbol const & k, rational const & _default) const {
    if (empty()) return _default;                                               
    TRAVERSE_CONST_ENTRIES(if (it->first == k) {
            if (it->second.m_kind == CPK_NUMERAL) {   
                return *(it->second.m_rat_value);
            }
            if (it->second.m_kind == CPK_UINT) {
                return rational(static_cast<int>(it->second.m_uint_value));
            }
        });
    return _default;                                                            
}

rational params::get_rat(char const * k, rational const & _default) const {
    if (empty()) return _default;                                               
    TRAVERSE_CONST_ENTRIES(if (it->first == k) {
            if (it->second.m_kind == CPK_NUMERAL) {   
                return *(it->second.m_rat_value);
            }
            if (it->second.m_kind == CPK_UINT) {
                return rational(static_cast<int>(it->second.m_uint_value));
            }
        });
    return _default;                                                            
}

symbol params::get_sym(symbol const & k, symbol const & _default) const {
    GET_VALUE(return symbol::mk_symbol_from_c_ptr(it->second.m_sym_value);, CPK_SYMBOL);
}

symbol params::get_sym(char const * k, symbol const & _default) const {
    GET_VALUE(return symbol::mk_symbol_from_c_ptr(it->second.m_sym_value);, CPK_SYMBOL);
}

#define GET_VALUE2(MATCH_CODE, KIND) {                                  \
    if (!empty()) {                                                     \
        TRAVERSE_CONST_ENTRIES(if (it->first == k && it->second.m_kind == KIND) { \
                MATCH_CODE                                              \
        });                                                             \
    }                                                                   \
}

#define GET_SIMPLE_VALUE2(FIELD_NAME, KIND) GET_VALUE2(return it->second.FIELD_NAME;, KIND)

bool params::get_bool(char const * k, params_ref const & fallback, bool _default) const {
    GET_SIMPLE_VALUE2(m_bool_value, CPK_BOOL);
    return fallback.get_bool(k, _default);
}

unsigned params::get_uint(char const * k, params_ref const & fallback, unsigned _default) const {
    GET_SIMPLE_VALUE2(m_uint_value, CPK_UINT);
    return fallback.get_uint(k, _default);
}

double params::get_double(char const * k, params_ref const & fallback, double _default) const {
    GET_SIMPLE_VALUE2(m_double_value, CPK_DOUBLE);
    return fallback.get_double(k, _default);
}

char const * params::get_str(char const * k, params_ref const & fallback, char const * _default) const {
    GET_SIMPLE_VALUE2(m_str_value, CPK_STRING);
    return fallback.get_str(k, _default);
}

symbol params::get_sym(char const * k, params_ref const & fallback, symbol const & _default) const {
    GET_VALUE2(return symbol::mk_symbol_from_c_ptr(it->second.m_sym_value);, CPK_SYMBOL);
    return fallback.get_sym(k, _default);
}

#define SET_VALUE(MATCH_CODE, ADD_CODE) {       \
    TRAVERSE_ENTRIES(if (it->first == k) {      \
        MATCH_CODE                              \
        return;                                 \
    });                                         \
    ADD_CODE                                    \
}

#define SET_SIMPLE_VALUE(FIELD_NAME, KIND) SET_VALUE({  \
    del_value(*it);                                     \
    it->second.m_kind = KIND;                           \
    it->second.FIELD_NAME = v;                          \
},                                                      \
{                                                       \
    entry new_entry;                                    \
    new_entry.first  = symbol(k);                       \
    new_entry.second.m_kind = KIND;                     \
    new_entry.second.FIELD_NAME = v;                    \
    m_entries.push_back(new_entry);                     \
})

// setters
void params::set_bool(symbol const & k, bool v) {
    SET_SIMPLE_VALUE(m_bool_value, CPK_BOOL);
}

void params::set_bool(char const * k, bool  v) {
    SET_SIMPLE_VALUE(m_bool_value, CPK_BOOL);
}
 
void params::set_uint(symbol const & k, unsigned v) {
    SET_SIMPLE_VALUE(m_uint_value, CPK_UINT);
}

void params::set_uint(char const * k, unsigned v) {
    SET_SIMPLE_VALUE(m_uint_value, CPK_UINT);
}

void params::set_double(symbol const & k, double v) {
    SET_SIMPLE_VALUE(m_double_value, CPK_DOUBLE);
}

void params::set_double(char const * k, double v) {
    SET_SIMPLE_VALUE(m_double_value, CPK_DOUBLE);
}

void params::set_str(symbol const & k, char const * v) {
    SET_SIMPLE_VALUE(m_str_value, CPK_STRING);
}

void params::set_str(char const * k, char const * v) {
    SET_SIMPLE_VALUE(m_str_value, CPK_STRING);
}

#define SET_RAT_VALUE() SET_VALUE({                             \
    if (it->second.m_kind != CPK_NUMERAL) {                     \
        del_value(*it);                                         \
        it->second.m_kind = CPK_NUMERAL;                        \
        it->second.m_rat_value = alloc(rational);               \
    }                                                           \
    *(it->second.m_rat_value) = v;                              \
},                                                              \
{                                                               \
    entry new_entry;                                            \
    new_entry.first  = symbol(k);                               \
    new_entry.second.m_kind = CPK_NUMERAL;                      \
    new_entry.second.m_rat_value = alloc(rational);             \
    *(new_entry.second.m_rat_value) = v;                        \
    m_entries.push_back(new_entry);                             \
})

void params::set_rat(symbol const & k, rational const & v) {
    SET_RAT_VALUE();
}

void params::set_rat(char const * k, rational const & v) {
    SET_RAT_VALUE();
}

#define SET_SYM_VALUE() SET_VALUE({                     \
    del_value(*it);                                     \
    it->second.m_kind = CPK_SYMBOL;                     \
    it->second.m_sym_value = v.bare_str();              \
},                                                      \
{                                                       \
    entry new_entry;                                    \
    new_entry.first  = symbol(k);                       \
    new_entry.second.m_kind = CPK_SYMBOL;               \
    new_entry.second.m_sym_value = v.bare_str();        \
    m_entries.push_back(new_entry);                     \
})

void params::set_sym(symbol const & k, symbol const & v) {
    SET_SYM_VALUE();
}

void params::set_sym(char const * k, symbol const & v) {
    SET_SYM_VALUE();
}

#ifdef Z3DEBUG
void pp(params_ref const & p) {
    std::cout << p << std::endl;
}
#endif
