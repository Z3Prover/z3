/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    ini_file.h

Abstract:

    Configuration file support.

Author:

    Leonardo de Moura (leonardo) 2007-05-10.

Revision History:

--*/
#ifndef _INI_FILE_H_
#define _INI_FILE_H_

#include<iostream>
#include<limits.h>
#include<string>

#include"symbol.h"
#include"vector.h"
#include"ref.h"

#ifdef _EXTERNAL_RELEASE
#define PRIVATE_PARAMS(CODE) ((void) 0)
#else
#define PRIVATE_PARAMS(CODE) { CODE }
#endif

struct param_vector_imp;
struct ini_params_imp;
class  ini_parser;

typedef std::pair<symbol, unsigned> symbol_nat_pair;

inline std::ostream & operator<<(std::ostream & out, symbol_nat_pair const & p) {
    out << p.first << ":" << p.second;
    return out;
}

/**
   \brief Support for multiple values for a parameter. The values are used to configure
   different cores. 
*/
class param_vector {
    unsigned           m_ref_count;
    param_vector_imp * m_imp;
    friend struct ini_params_imp;
    friend class  ini_parser;
public:
    // TODO: onwer is a big hack
    param_vector(void * owner); 
    ~param_vector();
    void inc_ref();
    void dec_ref();
    void copy_params(void * curr_owner, unsigned idx);
    unsigned size(void) const;
};

class set_get_param_exception {
    std::string m_id;
    std::string m_msg;
public:
    set_get_param_exception(char const * id, char const * msg):m_id(id), m_msg(msg) {}
    char const * get_param_id() const { return m_id.c_str(); }
    char const * get_msg() const { return m_msg.c_str(); }
};

class ini_parser_exception {
    unsigned m_pos;
    std::string m_msg;
public:
    ini_parser_exception(unsigned pos, char const * msg):m_pos(pos), m_msg(msg) {}
    unsigned get_pos() const { return m_pos; }
    char const * get_msg() const { return m_msg.c_str(); }
};

class ini_params {
    ini_params_imp * m_imp;
public:
    ini_params(bool abort_on_error = true);
    ~ini_params();
    void freeze(bool f = true);
    void register_bool_param(char const * param_name, bool & value, char const * descr = 0, bool is_mutable = false);
    void register_unsigned_param(char const * param_name, unsigned min, unsigned max, unsigned & value, char const * descr = 0, bool is_mutable = false);
    void register_unsigned_param(char const * param_name, unsigned & value, char const * descr = 0, bool is_mutable = false) {
        register_unsigned_param(param_name, 0, INT_MAX, value, descr, is_mutable);
    }
    void register_int_param(char const * param_name, int min, int max, int & value, char const * descr = 0, bool is_mutable = false);
    void register_int_param(char const * param_name, int & value, char const * descr = 0, bool is_mutable = false) {
        register_int_param(param_name, INT_MIN, INT_MAX, value, descr, is_mutable);
    }
    void register_double_param(char const * param_name, double & value, char const * descr = 0,bool is_mutable = false);
    void register_percentage_param(char const * param_name, double & value, char const * descr = 0, bool is_mutable = false);
    void register_string_param(char const * param_name, std::string & value, char const * descr = 0, bool is_mutable = false);
    void register_symbol_param(char const * param_name, symbol & value, char const * descr = 0, bool is_mutable = false);
    void register_symbol_list_param(char const * param_name, svector<symbol> & value, char const * descr = 0, bool is_mutable = false);
    void register_symbol_nat_list_param(char const * param_name, svector<symbol_nat_pair> & value, char const * descr = 0, bool is_mutable = false);
    void register_param_vector(param_vector * pv);
    
    void read_ini_file(std::istream & in);
    void display_params(std::ostream & out) const;
    void display_parameter_help(char const* param_id, std::ostream & out) const;
    void set_param_value(char const * param_id, char const * param_value);
    void set_param_mutable(char const * param_id);
    bool get_param_value(char const * param_id, std::string& param_value);
    void display_params_documentation(std::ostream & out) const;
};

#endif /* _INI_FILE_H_ */

