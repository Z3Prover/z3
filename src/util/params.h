/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    params.h

Abstract:

    Parameters.

Author:

    Leonardo (leonardo) 2011-04-22

Notes:

--*/
#ifndef PARAMS_H_
#define PARAMS_H_

#include "util/cmd_context_types.h"
#include "util/vector.h"

std::string norm_param_name(char const * n);
std::string norm_param_name(symbol const & n);

typedef cmd_arg_kind param_kind;

class params;
class param_descrs;

class params_ref {
    static params_ref g_empty_params_ref;
    
    params * m_params;
    void init();
    void copy_core(params const * p);
public:
    params_ref():m_params(nullptr) {}
    params_ref(params_ref const & p);
    ~params_ref();
    
    static params_ref const & get_empty() { return g_empty_params_ref; }
    
    params_ref & operator=(params_ref const & p);
    
    // copy params from src
    void copy(params_ref const & src);
    void append(params_ref const & src) { copy(src); }

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

    bool empty() const;
    bool contains(symbol const & k) const;
    bool contains(char const * k) const;

    void reset();
    void reset(symbol const & k);
    void reset(char const * k);

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

    void display(std::ostream & out) const;
    void display_smt2(std::ostream& out, char const* module, param_descrs& module_desc) const;

    void validate(param_descrs const & p);

    /*
      \brief Display the value of the given parameter.
      
      It displays 'default' if k is not in the parameter set.
    */
    void display(std::ostream & out, char const * k) const;
    void display(std::ostream & out, symbol const & k) const;
};

inline std::ostream & operator<<(std::ostream & out, params_ref const & ref) {
    ref.display(out);
    return out;
}

class param_descrs {
    struct imp;
    imp *  m_imp;
public:
    param_descrs();
    ~param_descrs();
    void copy(param_descrs & other);
    void insert(char const * name, param_kind k, char const * descr, char const * def = nullptr, char const* module = nullptr);
    void insert(symbol const & name, param_kind k, char const * descr, char const * def = nullptr, char const* module = nullptr);
    bool contains(char const * name) const;
    bool contains(symbol const & name) const;
    void erase(char const * name);
    void erase(symbol const & name);
    param_kind get_kind(char const * name) const;
    param_kind get_kind(symbol const & name) const;
    param_kind get_kind_in_module(symbol & name) const;
    char const * get_descr(char const * name) const;
    char const * get_descr(symbol const & name) const;
    char const * get_default(char const * name) const;
    char const * get_default(symbol const & name) const;
    void display(std::ostream & out, unsigned indent = 0, bool smt2_style=false, bool include_descr=true) const;
    unsigned size() const; 
    symbol get_param_name(unsigned idx) const;
    char const * get_module(symbol const& name) const;
};

void insert_max_memory(param_descrs & r);
void insert_max_steps(param_descrs & r);
void insert_produce_models(param_descrs & r);
void insert_produce_proofs(param_descrs & r);
void insert_timeout(param_descrs & r);
void insert_rlimit(param_descrs & r);
void insert_ctrl_c(param_descrs & r);

#endif
