/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    dimacs.cpp

Abstract:

    Dimacs CNF parser

Author:

    Leonardo de Moura (leonardo) 2011-07-26.

Revision History:

--*/
#include "sat/dimacs.h"
#undef max
#undef min
#include "sat/sat_solver.h"

struct lex_error {};

class stream_buffer {
    std::istream & m_stream;
    int            m_val;
    unsigned       m_line;
public:
    
    stream_buffer(std::istream & s):
        m_stream(s),
        m_line(0) {
        m_val = m_stream.get();
    }

    int  operator *() const { 
        return m_val;
    }

    void operator ++() { 
        m_val = m_stream.get();
        if (m_val == '\n') ++m_line;
    }

    unsigned line() const { return m_line; }
};

template<typename Buffer>
void skip_whitespace(Buffer & in) {
    while ((*in >= 9 && *in <= 13) || *in == 32) {
        ++in; 
    }
}

template<typename Buffer>
void skip_line(Buffer & in) {
    while(true) {
        if (*in == EOF) {
            return;
        }
        if (*in == '\n') { 
            ++in; 
            return; 
        }
        ++in; 
    } 
}

template<typename Buffer>
int parse_int(Buffer & in, std::ostream& err) {
    int     val = 0;
    bool    neg = false;
    skip_whitespace(in);

    if (*in == '-') {
        neg = true;
        ++in;
    }
    else if (*in == '+') {
        ++in;
    }

    if (*in < '0' || *in > '9') {
        err << "(error, \"unexpected char: " << *in << " line: " << in.line() << "\")\n";
        throw lex_error();
    }

    while (*in >= '0' && *in <= '9') {
        val = val*10 + (*in - '0');
        ++in;
    }

    return neg ? -val : val; 
}

template<typename Buffer>
void read_clause(Buffer & in, std::ostream& err, sat::solver & solver, sat::literal_vector & lits) {
    int     parsed_lit;
    int     var;
    
    lits.reset();

    while (true) { 
        parsed_lit = parse_int(in, err);
        if (parsed_lit == 0)
            break;
        var = abs(parsed_lit);
        SASSERT(var > 0);
        while (static_cast<unsigned>(var) >= solver.num_vars())
            solver.mk_var();
        lits.push_back(sat::literal(var, parsed_lit < 0));
    }
}

template<typename Buffer>
bool parse_dimacs_core(Buffer & in, std::ostream& err, sat::solver & solver) {
    sat::literal_vector lits;
    try {
        while (true) {
            skip_whitespace(in);
            if (*in == EOF) {
                break;
            }
            else if (*in == 'c' || *in == 'p') {
                skip_line(in);
            }
            else {
                read_clause(in, err, solver, lits);
                solver.mk_clause(lits.size(), lits.c_ptr());
            }
        }
    }
    catch (lex_error) {
        return false;
    }
    return true;
}

bool parse_dimacs(std::istream & in, std::ostream& err, sat::solver & solver) {
    stream_buffer _in(in);
    return parse_dimacs_core(_in, err, solver);
}
