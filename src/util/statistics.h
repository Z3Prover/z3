/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    statistics.h

Abstract:

    Wrapper for reporting statistics

Author:

    Leonardo (leonardo) 2011-05-17

Notes:

--*/
#pragma once

#include<iostream>
#include "util/vector.h"
#include "util/rlimit.h"

class statistics {
    typedef std::pair<char const *, unsigned> key_val_pair;
    svector<key_val_pair>   m_stats;
    typedef std::pair<char const *, double> key_d_val_pair;
    svector<key_d_val_pair> m_d_stats;
public:
    void copy(statistics const & st);
    void reset();
    void update(char const * key, unsigned inc);
    void update(char const * key, double inc);
    std::ostream& display(std::ostream & out) const;
    std::ostream& display_smt2(std::ostream & out) const;
    void display_internal(std::ostream & out) const;
    unsigned size() const;
    bool is_uint(unsigned idx) const;
    char const * get_key(unsigned idx) const;
    unsigned get_uint_value(unsigned idx) const;
    double get_double_value(unsigned idx) const;
};

inline std::ostream& operator<<(std::ostream& out, statistics const& st) { return st.display(out); }

void get_memory_statistics(statistics& st);
void get_rlimit_statistics(reslimit& l, statistics& st);

