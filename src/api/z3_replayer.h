/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    z3_replayer.h

Abstract:

    Interpreter for Z3 logs

Author:

    Leonardo de Moura (leonardo) 2011-09-22

Notes:
    
--*/
#pragma once

#include<iostream>
#include "api/z3.h"
#include "util/z3_exception.h"

class z3_replayer;

typedef void (*z3_replayer_cmd)(z3_replayer &);

typedef default_exception z3_replayer_exception;

class z3_replayer {
    struct imp;
    imp *  m_imp;
public:
    z3_replayer(std::istream & in);
    ~z3_replayer();
    void parse();
    unsigned get_line() const;

    int get_int(unsigned pos) const;
    unsigned get_uint(unsigned pos) const;
    int64_t get_int64(unsigned pos) const;
    uint64_t get_uint64(unsigned pos) const;
    float get_float(unsigned pos) const;
    double get_double(unsigned pos) const;
    bool get_bool(unsigned pos) const;
    Z3_string get_str(unsigned pos) const;
    Z3_symbol get_symbol(unsigned pos) const;
    void * get_obj(unsigned pos) const;

    unsigned * get_uint_array(unsigned pos) const;
    int * get_int_array(unsigned pos) const;
    bool * get_bool_array(unsigned pos) const;
    Z3_symbol * get_symbol_array(unsigned pos) const;
    void ** get_obj_array(unsigned pos) const;

    int * get_int_addr(unsigned pos);
    int64_t * get_int64_addr(unsigned pos);
    unsigned * get_uint_addr(unsigned pos);
    uint64_t * get_uint64_addr(unsigned pos);
    Z3_string * get_str_addr(unsigned pos);
    void ** get_obj_addr(unsigned pos);

    void store_result(void * obj);
    void register_cmd(unsigned id, z3_replayer_cmd cmd, char const* name);
};

