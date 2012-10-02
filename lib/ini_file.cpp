/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    ini_file.cpp

Abstract:

    Configuration file support.

Author:

    Leonardo de Moura (leonardo) 2007-05-10.

Revision History:

--*/
#include"ini_file.h"
#include"util.h"
#include"trace.h"
#include"str_hashtable.h"
#include"map.h"
#include"string_buffer.h"
#include"symbol_table.h"
#include"error_codes.h"
#include<sstream>

template<typename T>
class value_vector_map {
    void *                                          m_owner;
    map<T *, vector<T> *, ptr_hash<T>, ptr_eq<T> >  m_mapping;
    ptr_vector<T>                                   m_domain;
    ptr_vector<vector<T> >                          m_range;
    unsigned                                        m_max_size;
public:
    value_vector_map(void * owner):m_owner(owner), m_max_size(0) {}

    ~value_vector_map() {
        std::for_each(m_range.begin(), m_range.end(), delete_proc<vector<T> >());
    }
    
    void insert(T * ptr, T const & value) {
        SASSERT(reinterpret_cast<size_t>(ptr) >= reinterpret_cast<size_t>(m_owner));
        vector<T> * vect;
        if (m_mapping.find(ptr, vect)) {
            vect->push_back(value);
            if (vect->size() > m_max_size)
                m_max_size = vect->size();
            return;
        }
        vect = alloc(vector<T>);
        m_range.push_back(vect);
        m_domain.push_back(ptr);
        vect->push_back(value);
        if (m_max_size == 0)
            m_max_size = 1;
        m_mapping.insert(ptr, vect);
    }
    
    void copy_params(void * curr_owner, unsigned idx) {
        typename ptr_vector<T>::iterator it  = m_domain.begin();
        typename ptr_vector<T>::iterator end = m_domain.end();
        for (; it != end; ++it) {
            T * ptr = *it;
            vector<T> * vect = 0;
            m_mapping.find(ptr, vect);
            SASSERT(vect != 0);
            if (idx < vect->size()) {
                // BIG HACK
                SASSERT(reinterpret_cast<size_t>(ptr) >= reinterpret_cast<size_t>(m_owner));
                size_t offset = reinterpret_cast<size_t>(ptr) - reinterpret_cast<size_t>(m_owner);
                T * curr_ptr  = reinterpret_cast<T *>(reinterpret_cast<char *>(curr_owner) + offset);
                *curr_ptr = vect->operator[](idx);
            }
        }
    }

    unsigned size(void) const { return m_max_size; }
};

struct param_vector_imp {
    value_vector_map<bool>                      m_bool_params;
    value_vector_map<unsigned>                  m_unsigned_params;
    value_vector_map<int>                       m_int_params;
    value_vector_map<double>                    m_double_params;
    value_vector_map<std::string>               m_string_params;
    value_vector_map<symbol>                    m_symbol_params;
    value_vector_map<svector<symbol> >          m_symbol_list_params;
    value_vector_map<svector<symbol_nat_pair> > m_symbol_nat_list_params;
    
    param_vector_imp(void * owner):
        m_bool_params(owner),
        m_unsigned_params(owner),
        m_int_params(owner),
        m_double_params(owner),
        m_string_params(owner),
        m_symbol_params(owner),
        m_symbol_list_params(owner),
        m_symbol_nat_list_params(owner) {
    }

    void insert_bool_param(bool * value_ptr, bool value) {
        TRACE("param_vector", tout << "insert: " << value_ptr << " -> " << value << "\n";);
        m_bool_params.insert(value_ptr, value);
    }

    void insert_unsigned_param(unsigned * value_ptr, unsigned value) {
        TRACE("param_vector", tout << "insert: " << value_ptr << " -> " << value << "\n";);
        m_unsigned_params.insert(value_ptr, value);
    }

    void insert_int_param(int * value_ptr, int value) {
        TRACE("param_vector", tout << "insert: " << value_ptr << " -> " << value << "\n";);
        m_int_params.insert(value_ptr, value);
    }

    void insert_double_param(double * value_ptr, double value) {
        TRACE("param_vector", tout << "insert: " << value_ptr << " -> " << value << "\n";);
        m_double_params.insert(value_ptr, value);
    }

    void insert_string_param(std::string * value_ptr, std::string const & value) {
        TRACE("param_vector", tout << "insert: " << value_ptr << " -> " << value << "\n";);
        m_string_params.insert(value_ptr, value);
    }

    void insert_symbol_param(symbol * value_ptr, symbol const & value) {
        TRACE("param_vector", tout << "insert: " << value_ptr << " -> " << value << "\n";);
        m_symbol_params.insert(value_ptr, value);
    }

    void insert_symbol_list_param(svector<symbol> * value_ptr, svector<symbol> const & value) {
        TRACE("param_vector", tout << "insert: " << value_ptr << " -> "; display(tout, value.begin(), value.end()); tout << "\n";);
        m_symbol_list_params.insert(value_ptr, value);
    }

    void insert_symbol_nat_list_param(svector<symbol_nat_pair> * value_ptr, svector<symbol_nat_pair> const & value) {
        TRACE("param_vector", tout << "insert: " << value_ptr << " -> "; display(tout, value.begin(), value.end()); tout << "\n";);
        m_symbol_nat_list_params.insert(value_ptr, value);
    }

    void copy_params(void * curr_owner, unsigned idx) {
        m_bool_params.copy_params(curr_owner, idx);
        m_unsigned_params.copy_params(curr_owner, idx);
        m_int_params.copy_params(curr_owner, idx);
        m_double_params.copy_params(curr_owner, idx);
        m_string_params.copy_params(curr_owner, idx);
        m_symbol_params.copy_params(curr_owner, idx);
        m_symbol_list_params.copy_params(curr_owner, idx);
        m_symbol_nat_list_params.copy_params(curr_owner, idx);
    }

    unsigned size(void) const {
        unsigned ret = 0;
        ret = std::max(ret, m_bool_params.size());
        ret = std::max(ret, m_unsigned_params.size());
        ret = std::max(ret, m_int_params.size());
        ret = std::max(ret, m_double_params.size());
        ret = std::max(ret, m_string_params.size());
        ret = std::max(ret, m_symbol_params.size());
        ret = std::max(ret, m_symbol_list_params.size());
        ret = std::max(ret, m_symbol_nat_list_params.size());
        return ret;
    }
};


param_vector::param_vector(void * owner):
    m_ref_count(0) {
    m_imp = alloc(param_vector_imp, owner);
}

param_vector::~param_vector() {
    dealloc(m_imp);
}

void param_vector::inc_ref() {
    m_ref_count++;
}

void param_vector::dec_ref() {
    SASSERT(m_ref_count > 0);
    m_ref_count--;
    if (m_ref_count == 0)
        dealloc(this);
}

void param_vector::copy_params(void * curr_owner, unsigned idx) {
    m_imp->copy_params(curr_owner, idx);
}

unsigned param_vector::size(void) const
{
    return m_imp->size();
}

enum itoken {
    ITK_NULL, ITK_ID, ITK_NUM, ITK_DOUBLE, ITK_STRING, ITK_BAD_STRING, ITK_TRUE, ITK_FALSE, ITK_COMMA, ITK_LP, ITK_RP, ITK_LCB, ITK_RCB, ITK_CLN, ITK_EQ, ITK_BAD_ID, ITK_EOS, ITK_LAST
};

class ini_reserved_symbols {
    typedef map<char const *, itoken, str_hash_proc, str_eq_proc> str2token;
    str2token m_str2token;

public:
    ini_reserved_symbols() {
        m_str2token.insert("true",  ITK_TRUE);
        m_str2token.insert("false", ITK_FALSE);
    }

    itoken string2itoken(char const * str) {
        str2token::entry * e = m_str2token.find_core(const_cast<char *>(str));
        if (e)
            return e->get_data().m_value;
        else
            return ITK_ID;
    }
};

static char const * g_itoken2string[] = {
    "<null>", 
    "<id>", 
    "<num>", 
    "<num-double>", 
    "<string>", 
    "<invalid-string>", 
    "true", 
    "false", 
    ",",
    "(",
    ")",
    "{",
    "}",
    ":",
    "=", 
    "<invalid-id>", 
    "<end-of-stream>"
};

COMPILE_TIME_ASSERT(sizeof(g_itoken2string)/sizeof(char const*) == ITK_LAST);

inline static const char * itoken2string(itoken t) {
    return g_itoken2string[t];
}

inline itoken string2itoken(ini_reserved_symbols& reserved, char const * str) {
    itoken r = reserved.string2itoken(str);
    TRACE("token", tout << str << " -> " << itoken2string(r) << "\n";);
    return r;
}

class ini_lexer {
    std::istream  & m_input;
    char            m_curr_char;
    int             m_line;
    int             m_pos;
    int             m_tok_pos;
    string_buffer<> m_buffer;
    ini_reserved_symbols m_ini_reserved;
public:
    bool eos() const {
        return m_curr_char == EOF;
    }
    
    void next() {
        m_curr_char = m_input.get();
        m_pos++;
    }
    
    void save_and_next() {
        m_buffer << m_curr_char;
        next();
    }

    ini_lexer(std::istream & input):
        m_input(input),
        m_line(1),
        m_pos(0),
        m_tok_pos(0),
        m_ini_reserved() {
        next();
    }

    itoken read_num() {
        while (isdigit(m_curr_char)) {
            save_and_next();
        }
        if (m_curr_char == '.') {
            save_and_next();
            while (isdigit(m_curr_char)) {
                save_and_next();
            }
            if (m_curr_char == 'e' || m_curr_char == 'E' || m_curr_char == 'd' || m_curr_char == 'D') {
                save_and_next();
                if (m_curr_char == '-') {
                    save_and_next();
                }
                while (isdigit(m_curr_char)) {
                    save_and_next();
                }
            }
            return ITK_DOUBLE;
        }
        return ITK_NUM;
    }

    itoken read_id() {
        while (!eos() && (isalpha(m_curr_char) || isdigit(m_curr_char) || m_curr_char == '_')) {
            save_and_next();
        }
        return string2itoken(m_ini_reserved, m_buffer.c_str());
    }
    
    itoken read_string() { 
        m_tok_pos = m_pos; 
        next(); 
        while (m_curr_char != '"' && m_curr_char != '\'') { 
            if (m_input.eof()) {
                return ITK_BAD_STRING;
            }
            if (m_curr_char == '\n') {
                return ITK_BAD_STRING;
            }
            if (m_curr_char == '\\') { 
                next(); // do not save the '\' 
                switch (m_curr_char) { 
                case 't': 
                    m_buffer << '\t'; 
                    next(); 
                    break; 
                case 'n': 
                    m_buffer << '\n'; 
                    next(); 
                    break; 
                case '\n': 
                    m_buffer << '\n'; 
                    next();
                    break;
                default: 
                    if (!isdigit(m_curr_char)) {
                        save_and_next();  /* handles \\, \", \', and \? */ 
                    }
                    else {  /* \xxx */ 
                        int c = 0; 
                        int i = 0; 
                        do { 
                            c = 10*c + (m_curr_char-'0'); 
                            next(); 
                        } 
                        while (++i<3 && isdigit(m_curr_char)); 
                        if (c > UCHAR_MAX) {
                            return ITK_BAD_STRING;
                        }
                        m_buffer << static_cast<char>(c); 
                    } 
                } 
            } 
            else {
                save_and_next(); 
            }
        } 
        next(); 
        return ITK_STRING;
    } 

    itoken next_token() {
        for(;;) {
            if (eos()) {
                return ITK_EOS;
            }
            
            m_buffer.reset();
            switch (m_curr_char) {
            case ';': // comment
                while (m_curr_char != '\n' && !eos()) {
                    next();
                }
                break;
            case '\n':
                next();
                m_line++;
                break;
            case '=':
                m_tok_pos = m_pos;
                next();
                return ITK_EQ;
            case '\'':
            case '\"':
                return read_string();
            case '{':
                m_tok_pos = m_pos;
                next();
                return ITK_LCB;
            case '}':
                m_tok_pos = m_pos;
                next();
                return ITK_RCB;
            case '(':
                m_tok_pos = m_pos;
                next();
                return ITK_LP;
            case ')':
                m_tok_pos = m_pos;
                next();
                return ITK_RP;
            case ',':
                m_tok_pos = m_pos;
                next();
                return ITK_COMMA;
            case ':':
                m_tok_pos = m_pos;
                next();
                return ITK_CLN;
            default:
                if (isspace(m_curr_char)) {
                    next();
                    break;
                }
                else if (isdigit(m_curr_char)) {
                    m_tok_pos = m_pos;
                    save_and_next();
                    return read_num();
                }
                else {
                    char old = m_curr_char;
                    m_tok_pos = m_pos;
                    save_and_next();
                    TRACE("ini_lexer", tout << "old: " << static_cast<unsigned>(old) << " " << old << "\n";);
                    if (old == '-' && isdigit(m_curr_char)) {
                        return read_num();
                    }
                    else if (old == '_' || isalpha(old)) {
                        return read_id();
                    }
                    else {
                        return ITK_BAD_ID;
                    }
                }
            }
        }
    }

    char const * get_token_data() const {
        return m_buffer.c_str();
    }

    unsigned get_token_pos() const {
        return m_tok_pos;
    }
};


enum ini_param_kind {
    IPK_BOOL,
    IPK_INT,
    IPK_UNSIGNED,
    IPK_DOUBLE,
    IPK_PERCENTAGE,
    IPK_STRING,
    IPK_SYMBOL,
    IPK_SYMBOL_LIST,
    IPK_SYMBOL_NAT_LIST
};


struct ini_param_info {
    ini_param_kind m_kind;
    bool           m_is_mutable;
    
    char const *   m_description;
    union {
        struct {
            int m_int_min;
            int m_int_max;
            int * m_int_val;
        };
        struct {
            unsigned m_uint_min;
            unsigned m_uint_max;
            unsigned * m_uint_val;
        };
        bool *                     m_bool_val;
        double *                   m_double_val;
        double *                   m_perc_val;
        symbol *                   m_sym_val;
        std::string *              m_str_val;
        svector<symbol> *          m_sym_list_val;
        svector<symbol_nat_pair> * m_sym_nat_list_val;
    };

    ini_param_info(char const * descr = 0):
        m_kind(IPK_BOOL),
        m_is_mutable(false),
        m_description(descr),
        m_bool_val(0) {
    }
    
    ini_param_info(int min, int max, int * val, char const * descr, bool is_mutable):
        m_kind(IPK_INT),
        m_is_mutable(is_mutable),
        m_description(descr),
        m_int_min(min),
        m_int_max(max),
        m_int_val(val) {
    }

    ini_param_info(unsigned min, unsigned max, unsigned * val, char const * descr, bool is_mutable):
        m_kind(IPK_UNSIGNED),
        m_is_mutable(is_mutable),
        m_description(descr),
        m_uint_min(min),
        m_uint_max(max),
        m_uint_val(val) {
    }

    ini_param_info(bool * val, char const * descr, bool is_mutable):
        m_kind(IPK_BOOL),
        m_is_mutable(is_mutable),
        m_description(descr),
        m_bool_val(val) {
    }

    ini_param_info(bool perc, double * val, char const * descr, bool is_mutable):
        m_kind(perc ? IPK_PERCENTAGE : IPK_DOUBLE),
        m_is_mutable(is_mutable),
        m_description(descr),
        m_perc_val(val) {
    }

    ini_param_info(svector<symbol> * val, char const * descr, bool is_mutable):
        m_kind(IPK_SYMBOL_LIST),
        m_is_mutable(is_mutable),
        m_description(descr),
        m_sym_list_val(val) {
    }

    ini_param_info(svector<symbol_nat_pair> * val, char const * descr, bool is_mutable):
        m_kind(IPK_SYMBOL_NAT_LIST),
        m_is_mutable(is_mutable),
        m_description(descr),
        m_sym_nat_list_val(val) {
    }

    ini_param_info(symbol * s, char const * descr, bool is_mutable):
        m_kind(IPK_SYMBOL),
        m_is_mutable(is_mutable),
        m_description(descr),
        m_sym_val(s) {
    }

    ini_param_info(std::string * str, char const * descr, bool is_mutable):
        m_kind(IPK_STRING),
        m_is_mutable(is_mutable),
        m_description(descr),
        m_str_val(str) {
    }

};

struct ini_params_imp {
    bool                         m_abort_on_error;
    ini_reserved_symbols         m_ini_reserved;
    ref<param_vector>            m_param_vector;
    symbol_table<ini_param_info> m_param_info;
    bool                         m_is_frozen;

    ini_params_imp(bool abort_on_error): m_abort_on_error(abort_on_error), m_is_frozen(false) {}

    void freeze(bool f) { m_is_frozen = f; }

    void register_param_vector(param_vector * pv) {
        m_param_vector = pv;
    }

    void register_bool_param(symbol param_name, bool & value, char const * descr, bool is_mutable) {
        SASSERT(!m_param_info.contains(param_name));
        m_param_info.insert(param_name, ini_param_info(&value, descr, is_mutable));
    }

    void register_unsigned_param(symbol param_name, unsigned min, unsigned max, unsigned & value, char const * descr, bool is_mutable) {
        SASSERT(!m_param_info.contains(param_name));
        m_param_info.insert(param_name, ini_param_info(min, max, &value, descr, is_mutable));
    }

    void register_int_param(symbol param_name, int min, int max, int & value, char const * descr, bool is_mutable) {
        SASSERT(!m_param_info.contains(param_name));
        m_param_info.insert(param_name, ini_param_info(min, max, &value, descr, is_mutable));
    }

    void register_percentage_param(symbol param_name, double & value, char const * descr, bool is_mutable) {
        SASSERT(!m_param_info.contains(param_name));
        m_param_info.insert(param_name, ini_param_info(true, &value, descr, is_mutable));
    }

    void register_double_param(symbol param_name, double & value, char const * descr, bool is_mutable) {
        SASSERT(!m_param_info.contains(param_name));
        m_param_info.insert(param_name, ini_param_info(false, &value, descr, is_mutable));
    }

    void register_string_param(symbol param_name, std::string & value, char const * descr, bool is_mutable) {
        SASSERT(!m_param_info.contains(param_name));
        m_param_info.insert(param_name, ini_param_info(&value, descr, is_mutable));
    }

    void register_symbol_param(symbol param_name, symbol & value, char const * descr, bool is_mutable) {
        SASSERT(!m_param_info.contains(param_name));
        m_param_info.insert(param_name, ini_param_info(&value, descr, is_mutable));
    }

    void register_symbol_list_param(symbol param_name, svector<symbol> & value, char const * descr, bool is_mutable) {
        SASSERT(!m_param_info.contains(param_name));
        m_param_info.insert(param_name, ini_param_info(&value, descr, is_mutable));
    }

    void register_symbol_nat_list_param(symbol param_name, svector<symbol_nat_pair> & value, char const * descr, bool is_mutable) {
        SASSERT(!m_param_info.contains(param_name));
        m_param_info.insert(param_name, ini_param_info(&value, descr, is_mutable));
    }

    struct symbol_lt_proc {
        bool operator()(const symbol & s1, const symbol & s2) const {
            return strcmp(s1.bare_str(), s2.bare_str()) < 0;
        }
    };

    void display_param_help(char const* param_id, std::ostream& out) const {
        ini_param_info info;
        if (m_param_info.find(symbol(param_id), info)) {
            display_param_info(out, info);
        }
        else {
            out << "option " << param_id << " does not exist";
        }
    }

    void display_param_info(std::ostream& out, ini_param_info& info) const {
        switch (info.m_kind) {
        case IPK_BOOL:
            out << " boolean"; 
            out << ", default: " << (*info.m_bool_val ? "true" : "false");
            break;
        case IPK_INT:
            out << " integer"; 
            if (info.m_int_min > INT_MIN) {
                out << ", min: " << info.m_int_min;
            }
            if (info.m_int_max < INT_MAX) {
                out << ", max: " << info.m_int_max;
            }
            out << ", default: " << *info.m_int_val;
            break;
        case IPK_UNSIGNED:
            out << " unsigned integer";
            if (info.m_uint_min > 0) {
                out << ", min: " << info.m_uint_min;
            }
            if (info.m_uint_max < INT_MAX) {
                out << ", max: " << info.m_uint_max;
            }
            out << ", default: " << *info.m_uint_val;
            break;
        case IPK_DOUBLE:
            out << " double"; 
            out << ", default: " << *info.m_double_val;
            break;
        case IPK_PERCENTAGE:
            out << " percentage"; 
            out << ", default: " << *info.m_perc_val;
            break;
        case IPK_SYMBOL:
            out << " symbol";
            out << ", default: " << *info.m_sym_val;
            break;
        case IPK_STRING:
            out << " string";
            out << ", default: " << *info.m_str_val;
            break;
        case IPK_SYMBOL_LIST:
            out << " list of symbols (strings)";
            break;
        case IPK_SYMBOL_NAT_LIST:
            out << " list of pairs: symbols(strings) x unsigned";
            break;
        }
        if (info.m_description) {
            out << ", " << info.m_description << ".";
        }
        out << "\n";
    }

    void display_params(std::ostream & out) const {
        svector<symbol> params;
        m_param_info.get_dom(params);
        std::sort(params.begin(), params.end(), symbol_lt_proc());
        svector<symbol>::iterator it  = params.begin();
        svector<symbol>::iterator end = params.end();
        for (; it != end; ++it) {
            out << *it << ":";
            ini_param_info info;
            m_param_info.find(*it, info);
            display_param_info(out, info);
        }
    }

    void display_params_documentation(std::ostream & out) const {
        out << "// AUTOMATICALLY GENERATED FILE - DO NOT EDIT\n\n"
            << "/**\n"
            << "  \\page config INI parameters\n\n";
        svector<symbol> params;
        m_param_info.get_dom(params);
        std::sort(params.begin(), params.end(), symbol_lt_proc());
        svector<symbol>::iterator it  = params.begin();
        svector<symbol>::iterator end = params.end();
        for (; it != end; ++it) {
            out << "- \\c " << *it << ":";
            ini_param_info info;
            m_param_info.find(*it, info);
            switch (info.m_kind) {
            case IPK_BOOL:
                out << " \\em boolean"; 
                out << ", default: " << (*info.m_bool_val ? "\\c true" : "\\c false");
                break;
            case IPK_INT:
                out << " \\em integer"; 
                if (info.m_int_min > INT_MIN) {
                    out << ", min: \\c " << info.m_int_min;
                }
                if (info.m_int_max < INT_MAX) {
                    out << ", max: \\c " << info.m_int_max;
                }
                out << ", default: \\c " << *info.m_int_val;
                break;
            case IPK_UNSIGNED:
                out << " \\em unsigned \\em integer";
                if (info.m_uint_min > 0) {
                    out << ", min: \\c " << info.m_uint_min;
                }
                if (info.m_uint_max < INT_MAX) {
                    out << ", max: \\c " << info.m_uint_max;
                }
                out << ", default: \\c " << *info.m_uint_val;
                break;
            case IPK_DOUBLE:
                out << " \\em double"; 
                out << ", default: \\c " << *info.m_double_val;
                break;
            case IPK_PERCENTAGE:
                out << " \\em percentage"; 
                out << ", default: \\c " << *info.m_perc_val;
                break;
            case IPK_STRING:
                out << " \\em string";
                out << ", default: " << *info.m_str_val;
                break;
            case IPK_SYMBOL:
                out << " \\em symbol";
                out << ", default: " << *info.m_sym_val;
                break;
            case IPK_SYMBOL_LIST:
                out << " \\em list \\em of \\em symbols \\em (strings)";
                break;
            case IPK_SYMBOL_NAT_LIST:
                out << " \\em list \\em of \\em pairs: \\em symbols(strings) \\em x \\em unsigned";
                break;
            }
            if (info.m_description) {
                out << ", " << info.m_description << ".";
            }
            out << "\n\n";
        }
        out << "*/\n";
    }

    void error(char const * param_id, char const * msg) {
        if (m_abort_on_error) {
            verbose_stream() << "Error setting '" << param_id << "', reason: " << msg << "\n";
            throw z3_error(ERR_INI_FILE);
        }
        else {
            throw set_get_param_exception(param_id, msg);
        }
    }

    symbol trim(char const * param_id) {
        string_buffer<> m_buffer;
        while (*param_id != 0 && !isspace(*param_id)) {
            m_buffer.append(*param_id);
            param_id++;
        }
        return symbol(m_buffer.c_str());
    }

    void set_param_value(char const * param_id, char const * param_value) {
        TRACE("param_value", tout << param_id << " " << param_value << "\n";);
        if (param_value == 0) {
            error(param_id, "invalid (null) option");
        }
        symbol s(param_id);
        ini_param_info info;
        if (!m_param_info.find(s, info)) {
            s = trim(param_id);
            if (!m_param_info.find(s, info))
                error(param_id, "unknown option.");
        }
        if (!info.m_is_mutable && m_is_frozen) {
            error(param_id, "option value cannot be modified after initialization");
        }
        switch (info.m_kind) {
        case IPK_BOOL:
            parse_bool_param(param_id, info, param_value);
            break;
        case IPK_INT:
            parse_int_param(param_id, info, param_value);
            break;
        case IPK_UNSIGNED:
            parse_uint_param(param_id, info, param_value);
            break;
        case IPK_DOUBLE:
            parse_double_param(param_id, info, param_value);
            break;
        case IPK_PERCENTAGE: 
            parse_perc_param(param_id, info, param_value);
            break;
        case IPK_STRING:
            parse_string_param(param_id, info, param_value);
            break;
        case IPK_SYMBOL:
            // TODO: not used so far
            *info.m_sym_val = param_value;
            break;
        case IPK_SYMBOL_LIST:
            error(param_id, "this option can only be set in an INI file");
            break;
        case IPK_SYMBOL_NAT_LIST:
            error(param_id, "this option can only be set in an INI file");
            break;
        default:
            UNREACHABLE();
        }
    }


    bool get_param_value(char const * param_id, std::string& param_value) {
        TRACE("param_value", tout << param_id << "\n";);
        std::ostringstream buffer;
        symbol s(param_id);
        ini_param_info info;
        if (!m_param_info.find(s, info)) {
            s = trim(param_id);
            if (!m_param_info.find(s, info)) {
                return false;
            }
        }
        switch (info.m_kind) {
        case IPK_BOOL:
            buffer << ((*info.m_bool_val)?"true":"false");
            break;
        case IPK_INT:
            buffer << (*info.m_int_val);
            break;
        case IPK_UNSIGNED:
            buffer << (*info.m_uint_val);
            break;
        case IPK_DOUBLE:
            buffer << (*info.m_double_val);
            break;
        case IPK_PERCENTAGE: 
            buffer << (*info.m_perc_val);
            break;
        case IPK_STRING:
            buffer << (*info.m_str_val);
            break;
        case IPK_SYMBOL:
            buffer << (info.m_sym_val->str());
            break;
        case IPK_SYMBOL_LIST:
            error(param_id, "this option cannot be retrieved");
            break;
        case IPK_SYMBOL_NAT_LIST:
            error(param_id, "this option cannot be retrieved");
            break;
        default:
            UNREACHABLE();
        }
        param_value = buffer.str();
        return true;
    }

    string_buffer<> m_buffer;
    
    char const * get_token_data() const {
        return m_buffer.c_str();
    }
    
    void save_and_next(char const * & in) {
        m_buffer.append(*in);
        ++in;
    }        

    itoken read_num(char const * & in) {
        while (isdigit(*in)) {
            save_and_next(in);
        }
        TRACE("read_num", tout << "1. read_num: " << m_buffer.c_str() << ", *in: " << *in << "\n";);
        if (*in == '.') {
            save_and_next(in);
            while (isdigit(*in)) {
                save_and_next(in);
            }
            TRACE("read_num", tout << "2. read_num: " << m_buffer.c_str() << ", *in: " << *in << "\n";);
            if (*in == 'e' || *in == 'E' || *in == 'd' || *in == 'D') {
                save_and_next(in);
                if (*in == '-') {
                    save_and_next(in);
                }
                while (isdigit(*in)) {
                    save_and_next(in);
                }
            }
            return ITK_DOUBLE;
        }
        return ITK_NUM;
    }

    itoken read_id(char const * & in) {
        while (!*in == 0 && (isalpha(*in) || isdigit(*in) || *in == '_')) {
            save_and_next(in);
        }
        return string2itoken(m_ini_reserved, m_buffer.c_str());
    }

    itoken read_string(char const * & in) {
        ++in;
        while (*in != '"' && *in != '\'') { 
            TRACE("read_string", tout << *in << "\n";);
            if (*in == 0) 
                return ITK_BAD_STRING;
            if (*in == '\n') 
                return ITK_BAD_STRING;
            if (*in == '\\') { 
                ++in;
                switch (*in) {
                case 't': 
                    m_buffer << '\t'; 
                    ++in;
                    break; 
                case 'n': 
                    m_buffer << '\n'; 
                    ++in;
                    break; 
                case '\n': 
                    m_buffer << '\n'; 
                    ++in;
                    break;
                default: 
                    if (!isdigit(*in)) {
                        save_and_next(in);  /* handles \\, \", \', and \? */ 
                    }
                    else {  /* \xxx */ 
                        int c = 0; 
                        int i = 0; 
                        do { 
                            c = 10*c + (*in-'0'); 
                            ++in;
                        } 
                        while (++i<3 && isdigit(*in)); 
                        if (c > UCHAR_MAX)
                            return ITK_BAD_STRING;
                        m_buffer << static_cast<char>(c); 
                    } 
                } 
            } 
            else {
                save_and_next(in); 
            }
        }
        ++in;
        return ITK_STRING;
    }
    
    itoken next_token(char const * & in) {
        for(;;) {
            if (*in == 0) 
                return ITK_EOS;
            m_buffer.reset();
            switch (*in) {
            case '{':
                in++;
                return ITK_LCB;
            case '}':
                in++;
                return ITK_RCB;
            case ',':
                in++;
                return ITK_COMMA;
            case '"':
            case '\'':
                TRACE("read_string", tout << "found \"\n";);
                return read_string(in);
            default:
                if (isspace(*in)) {
                    in++;
                    break;
                }
                else if (isdigit(*in)) {
                    TRACE("read_num", tout << "found is_digit\n";);
                    return read_num(in);
                }
                else {
                    char old = *in;
                    save_and_next(in);
                    if (old == '-' && isdigit(*in)) {
                        return read_num(in);
                    }
                    else if (old == '_' || isalpha(old)) {
                        return read_id(in);
                    }
                    else {
                        return ITK_BAD_ID;
                    }
                }
            }
        }
    }

    bool end_of_list(char const * param_id, char const * & param_value) {
        switch (next_token(param_value)) {
        case ITK_COMMA:
            return false;
        case ITK_RCB:
            return true;
        default:
            error(param_id, "boolean value (true/false) expected");
        }
        return false;
    }
    
    void parse_bool_param(char const * param_id, ini_param_info & info, char const * param_value) {
        switch (next_token(param_value)) {
        case ITK_TRUE:
            *info.m_bool_val = true;
            break;
        case ITK_FALSE:
            *info.m_bool_val = false;
            break;
        default:
            error(param_id, "boolean value (true/false) expected");
        }
        if (m_param_vector.get() && next_token(param_value) == ITK_LCB) {
            for (;;) {
                switch (next_token(param_value)) {
                case ITK_TRUE:
                    m_param_vector->m_imp->insert_bool_param(info.m_bool_val, true);
                    break;
                case ITK_FALSE:
                    m_param_vector->m_imp->insert_bool_param(info.m_bool_val, false);
                    break;
                default:
                    error(param_id, "boolean value (true/false) expected");
                }
                if (end_of_list(param_id, param_value))
                    return;
            }
        }
    }

    void parse_int_param(char const * param_id, ini_param_info & info, char const * param_value) {
        if (next_token(param_value) != ITK_NUM)
            error(param_id, "integer expected");
        int val = strtol(get_token_data(), 0, 10);
        if (val < info.m_int_min || val > info.m_int_max)
            error(param_id, "integer out of bounds");
        *info.m_int_val = val;
        if (m_param_vector.get() && next_token(param_value) == ITK_LCB) {
            for (;;) {
                if (next_token(param_value) != ITK_NUM)
                    error(param_id, "integer expected");
                int val = strtol(get_token_data(), 0, 10);
                if (val < info.m_int_min || val > info.m_int_max)
                    error(param_id, "integer out of bounds");
                m_param_vector->m_imp->insert_int_param(info.m_int_val, val);
                if (end_of_list(param_id, param_value))
                    return;
            }
        }
    }

    void parse_uint_param(char const * param_id, ini_param_info & info, char const * param_value) {
        if (next_token(param_value) != ITK_NUM)
            error(param_id, "integer expected");
        unsigned val = static_cast<unsigned>(strtol(get_token_data(), 0, 10));
        
        if (val < info.m_uint_min || val > info.m_uint_max)
            error(param_id, "unsigned out of bounds");
        *info.m_uint_val = val;
        if (m_param_vector.get() && next_token(param_value) == ITK_LCB) {
            for (;;) {
                if (next_token(param_value) != ITK_NUM)
                    error(param_id, "integer expected");
                unsigned val = static_cast<unsigned>(strtol(get_token_data(), 0, 10));
                if (val < info.m_uint_min || val > info.m_uint_max)
                    error(param_id, "unsigned out of bounds");
                m_param_vector->m_imp->insert_unsigned_param(info.m_uint_val, val);
                if (end_of_list(param_id, param_value))
                    return;
            }
        }
    }

    void parse_double_param(char const * param_id, ini_param_info & info, char const * param_value) {
        itoken k = next_token(param_value);
        if (k != ITK_NUM && k != ITK_DOUBLE)
            error(param_id, "float expected");
        char * aux;
        *info.m_double_val = strtod(get_token_data(), &aux);
        if (m_param_vector.get() && next_token(param_value) == ITK_LCB) {
            for (;;) {
                k = next_token(param_value);
                if (k != ITK_NUM && k != ITK_DOUBLE)
                    error(param_id, "float expected");
                m_param_vector->m_imp->insert_double_param(info.m_double_val, strtod(get_token_data(), &aux));
                if (end_of_list(param_id, param_value))
                    return;
            }
        }
    }

    void parse_perc_param(char const * param_id, ini_param_info & info, char const * param_value) {
        if (next_token(param_value) != ITK_NUM)
            error(param_id, "integer expected");
        int val = strtol(get_token_data(), 0, 10);
        if (val < 0 || val > 100)
            error(param_id, "integer between 0 and 100 expected");
        *info.m_perc_val = static_cast<double>(val)/100.0;
        if (m_param_vector.get() && next_token(param_value) == ITK_LCB) {
            for (;;) {
                if (next_token(param_value) != ITK_NUM)
                    error(param_id, "integer expected");
                int val = strtol(get_token_data(), 0, 10);
                if (val < 0 || val > 100)
                    error(param_id, "integer between 0 and 100 expected");
                m_param_vector->m_imp->insert_double_param(info.m_perc_val, static_cast<double>(val)/100.0);
                if (end_of_list(param_id, param_value))
                    return;
            }
        }
    }

    void parse_string_param(char const * param_id, ini_param_info & info, char const * param_value) {
        if (next_token(param_value) != ITK_STRING)
            error(param_id, "string expected");
        *info.m_str_val = get_token_data();
        if (m_param_vector.get() && next_token(param_value) == ITK_LCB) {
            for (;;) {
                if (next_token(param_value) != ITK_STRING)
                    error(param_id, "string expected");
                m_param_vector->m_imp->insert_string_param(info.m_str_val, get_token_data());
                if (end_of_list(param_id, param_value))
                    return;
            }
        }
    }
};

class ini_parser {
    ini_lexer           m_lexer;
    ini_params_imp *    m_params;
    itoken              m_curr_token;

    void error(unsigned pos, char const * msg) {
        if (m_params->m_abort_on_error) {
            verbose_stream() << "Error INI file [position: " << pos << "]: " << msg << "\n";
            throw z3_error(ERR_INI_FILE);
        }
        else {
            throw ini_parser_exception(pos, msg);
        }
    }
        
    void error(char const * msg) {
        error(m_lexer.get_token_pos(), msg);
    }

    itoken get_curr_token() {
        if (m_curr_token == ITK_NULL) {
            m_curr_token = m_lexer.next_token(); 
        }
        SASSERT(m_curr_token != ITK_NULL);
        return m_curr_token;
    }

    void next() {
        if (m_curr_token == ITK_NULL) {
            m_lexer.next_token(); 
        }
        else {
            m_curr_token = ITK_NULL;
        }
    }

    char const * get_token_data() {
        if (m_curr_token == ITK_NULL) {
            get_curr_token();
        }
        SASSERT(m_curr_token != ITK_NULL);
        return m_lexer.get_token_data();
    }

    bool test_next(itoken expected) {
        if (get_curr_token() == expected) {
            next();
            return true;
        }
        else {
            return false;
        }
    }

    void check(itoken expected) {
        if (!test_next(expected)) {
            string_buffer<> msg;
            msg << "unexpected token '" << itoken2string(get_curr_token()) 
                << "', '" << itoken2string(expected) << "' expected.";
            error(msg.c_str());
        }
    }

public:
    ini_parser(std::istream & in, ini_params_imp * p):
        m_lexer(in),
        m_params(p),
        m_curr_token(ITK_NULL) {
    }

    void parse_param() {
        symbol s(get_token_data());
        check(ITK_ID);
        ini_param_info info;
        if (!m_params->m_param_info.find(s, info)) {
            error("unknown option.");
        }
        check(ITK_EQ);
        switch (info.m_kind) {
        case IPK_BOOL:
            parse_bool_param(info);
            break;
        case IPK_INT:
            parse_int_param(info);
            break;
        case IPK_UNSIGNED:
            parse_uint_param(info);
            break;
        case IPK_DOUBLE:
            parse_double_param(info);
            break;
        case IPK_PERCENTAGE:
            parse_perc_param(info);
            break;
        case IPK_STRING:
            parse_string_param(info);
            break;
        case IPK_SYMBOL:
            // TODO: add support for VAL{VAL,...,VAL}
            *info.m_sym_val = get_token_data();
            check(ITK_STRING);
            break;
        case IPK_SYMBOL_NAT_LIST:
            parse_symbol_nat_list(info);
            break;
        case IPK_SYMBOL_LIST:
            parse_symbol_list(info);
            break;
        default:
            UNREACHABLE();
        }
    }
    
    bool end_of_list() {
        switch (get_curr_token()) {
        case ITK_COMMA:
            next();
            return false;
        case ITK_RCB:
            next();
            return true;
        default:
            error("boolean value expected");
        }
        return false;
    }

    void parse_bool_param(ini_param_info & info) {
        if (get_curr_token() != ITK_TRUE && get_curr_token() != ITK_FALSE)
            error("boolean value expected");
        *info.m_bool_val = get_curr_token() == ITK_TRUE;
        next();
        if (m_params->m_param_vector.get() && get_curr_token() == ITK_LCB) {
            next();
            for (;;) {
                if (get_curr_token() != ITK_TRUE && get_curr_token() != ITK_FALSE)
                    error("boolean value expected");
                m_params->m_param_vector->m_imp->insert_bool_param(info.m_bool_val, get_curr_token() == ITK_TRUE);
                next();
                if (end_of_list())
                    return;
            }
        }
    }

    void parse_int_param(ini_param_info & info) {
        if (get_curr_token() != ITK_NUM)
            error("integer expected");
        int val = strtol(get_token_data(), 0, 10);
        if (val < info.m_int_min || val > info.m_int_max)
            error("integer out of bounds");
        *info.m_int_val = val;
        next();
        TRACE("int_param", tout << "val: " << val << "\n";);
        if (m_params->m_param_vector.get() && get_curr_token() == ITK_LCB) {
            next();
            for (;;) {
                if (get_curr_token() != ITK_NUM)
                    error("integer expected");
                int val = strtol(get_token_data(), 0, 10);
                if (val < info.m_int_min || val > info.m_int_max)
                    error("integer out of bounds");
                m_params->m_param_vector->m_imp->insert_int_param(info.m_int_val, val);
                next();
                if (end_of_list())
                    return;
            }
        }
    }

    void parse_uint_param(ini_param_info & info) {
        if (get_curr_token() != ITK_NUM)
            error("integer expected");
        long val = strtol(get_token_data(), 0, 10);
        if (val < static_cast<long>(info.m_uint_min) || val > static_cast<long>(info.m_uint_max))
            error("integer out of bounds");
        *info.m_uint_val = val;
        next();
        if (m_params->m_param_vector.get() && get_curr_token() == ITK_LCB) {
            next();
            for (;;) {
                if (get_curr_token() != ITK_NUM)
                    error("integer expected");
                long val = strtol(get_token_data(), 0, 10);
                if (val < static_cast<long>(info.m_uint_min) || val > static_cast<long>(info.m_uint_max))
                    error("integer out of bounds");
                m_params->m_param_vector->m_imp->insert_unsigned_param(info.m_uint_val, val);
                next();
                if (end_of_list())
                    return;
            }
        }
    }

    void parse_double_param(ini_param_info & info) {
        if (get_curr_token() != ITK_NUM && get_curr_token() != ITK_DOUBLE)
            error("float expected");
        char * aux;
        *info.m_double_val = strtod(get_token_data(), &aux);
        next();
        if (m_params->m_param_vector.get() && get_curr_token() == ITK_LCB) {
            next();
            for (;;) {
                if (get_curr_token() != ITK_NUM && get_curr_token() != ITK_DOUBLE)
                    error("float expected");
                m_params->m_param_vector->m_imp->insert_double_param(info.m_double_val, strtod(get_token_data(), &aux));
                next();
                if (end_of_list())
                    return;
            }
        }
    }

    void parse_perc_param(ini_param_info & info) {
        if (get_curr_token() != ITK_NUM)
            error("integer expected");
        int val = strtol(get_token_data(), 0, 10);
        if (val < 0 || val > 100)
            error("integer between 0 and 100 expected");
        *info.m_perc_val = static_cast<double>(val)/100.0;
        next();
        if (m_params->m_param_vector.get() && get_curr_token() == ITK_LCB) {
            next();
            for (;;) {
                if (get_curr_token() != ITK_NUM)
                    error("integer expected");
                int val = strtol(get_token_data(), 0, 10);
                if (val < 0 || val > 100)
                    error("integer between 0 and 100 expected");
                m_params->m_param_vector->m_imp->insert_double_param(info.m_perc_val, static_cast<double>(val)/100.0);
                next();
                if (end_of_list())
                    return;
            }
        }
    }

    void parse_string_param(ini_param_info & info) {
        if (get_curr_token() != ITK_STRING)
            error("string expected");
        *info.m_str_val = get_token_data();
        next();
        if (m_params->m_param_vector.get() && get_curr_token() == ITK_LCB) {
            next();
            for (;;) {
                if (get_curr_token() != ITK_STRING)
                    error("string expected");
                m_params->m_param_vector->m_imp->insert_string_param(info.m_str_val, get_token_data());
                next();
                if (end_of_list())
                    return;
            }
        }
    }

    void parse_s_list(svector<symbol> & result) {
        check(ITK_LP);
        for (;;) {
            symbol s(get_token_data());
            result.push_back(s);
            check(ITK_ID);
            if (!test_next(ITK_COMMA)) {
                check(ITK_RP);
                return;
            }
        }
    }

    void parse_symbol_list(ini_param_info & info) {
        parse_s_list(*(info.m_sym_list_val));
        if (m_params->m_param_vector.get() && test_next(ITK_LCB)) {
            for (;;) {
                svector<symbol> lst;
                parse_s_list(lst);
                m_params->m_param_vector->m_imp->insert_symbol_list_param(info.m_sym_list_val, lst);
                if (!test_next(ITK_COMMA)) {
                    check(ITK_RCB);
                    return;
                }
            }
        }
    }

    void parse_sn_list(svector<symbol_nat_pair> & result) {
        check(ITK_LP);
        for (;;) {
            symbol s(get_token_data());
            check(ITK_ID);
            check(ITK_CLN);
            unsigned val = strtol(get_token_data(), 0, 10);
            check(ITK_NUM);
            result.push_back(std::make_pair(s, val));
            if (!test_next(ITK_COMMA)) {
                check(ITK_RP);
                return;
            }
        }
    }

    void parse_symbol_nat_list(ini_param_info & info) {
        parse_sn_list(*(info.m_sym_nat_list_val));
        if (m_params->m_param_vector.get() && test_next(ITK_LCB)) {
            for (;;) {
                svector<symbol_nat_pair> lst;
                parse_sn_list(lst);
                m_params->m_param_vector->m_imp->insert_symbol_nat_list_param(info.m_sym_nat_list_val, lst);
                if (!test_next(ITK_COMMA)) {
                    check(ITK_RCB);
                    return;
                }
            }
        }
    }

    void parse() {
        while (get_curr_token() != ITK_EOS) {
            parse_param();
        }
    }
};

ini_params::ini_params(bool abort_on_error) {
    m_imp = alloc(ini_params_imp, abort_on_error);
}

ini_params::~ini_params() {
    dealloc(m_imp);
}

void ini_params::register_bool_param(char const * param_name, bool & value, char const * descr, bool is_mutable) {
    m_imp->register_bool_param(symbol(param_name), value, descr, is_mutable);
}

void ini_params::register_unsigned_param(char const * param_name, unsigned min, unsigned max, unsigned & value, char const * descr, bool is_mutable) {
    m_imp->register_unsigned_param(symbol(param_name), min, max, value, descr, is_mutable);
}

void ini_params::register_int_param(char const * param_name, int min, int max, int & value, char const * descr, bool is_mutable) {
    m_imp->register_int_param(symbol(param_name), min, max, value, descr, is_mutable);
}

void ini_params::register_double_param(char const * param_name, double & value, char const * descr, bool is_mutable) {
    m_imp->register_double_param(symbol(param_name), value, descr, is_mutable);
}

void ini_params::register_percentage_param(char const * param_name, double & value, char const * descr, bool is_mutable) {
    m_imp->register_percentage_param(symbol(param_name), value, descr, is_mutable);
}

void ini_params::register_string_param(char const * param_name, std::string & value, char const * descr, bool is_mutable) {
    m_imp->register_string_param(symbol(param_name), value, descr, is_mutable);
}

void ini_params::register_symbol_param(char const * param_name, symbol & value, char const * descr, bool is_mutable) {
    m_imp->register_symbol_param(symbol(param_name), value, descr, is_mutable);
}

void ini_params::register_symbol_list_param(char const * param_name, svector<symbol> & value, char const * descr, bool is_mutable) {
    m_imp->register_symbol_list_param(symbol(param_name), value, descr, is_mutable);
}

void ini_params::register_symbol_nat_list_param(char const * param_name, svector<symbol_nat_pair> & value, char const * descr, bool is_mutable) {
    m_imp->register_symbol_nat_list_param(symbol(param_name), value, descr, is_mutable);
}

void ini_params::register_param_vector(param_vector * pv) {
    m_imp->register_param_vector(pv);
}

void ini_params::read_ini_file(std::istream & in) {
    ini_parser p(in, m_imp);
    p.parse();
}

void ini_params::display_params(std::ostream & out) const {
    m_imp->display_params(out);
}

void ini_params::display_parameter_help(char const* param_id, std::ostream & out) const {
    m_imp->display_param_help(param_id, out);
}

void ini_params::display_params_documentation(std::ostream & out) const {
    m_imp->display_params_documentation(out);
}

void ini_params::set_param_value(char const * param_id, char const * param_value) {
    m_imp->set_param_value(param_id, param_value);
}
bool ini_params::get_param_value(char const * param_id, std::string& param_value) {
    return m_imp->get_param_value(param_id, param_value);
}

void ini_params::freeze(bool f) {
    m_imp->freeze(f);
}



