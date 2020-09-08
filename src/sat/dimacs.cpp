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
#include "sat/sat_drat.h"

template<typename Buffer>
static bool is_whitespace(Buffer & in) {
    return (*in >= 9 && *in <= 13) || *in == 32;
}

template<typename Buffer>
static void skip_whitespace(Buffer & in) {
    while (is_whitespace(in))
        ++in; 
}

template<typename Buffer>
static void skip_line(Buffer & in) {
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
static int parse_int(Buffer & in, std::ostream& err) {
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
        if (20 <= *in && *in < 128) 
            err << "(error, \"unexpected char: " << ((char)*in) << " line: " << in.line() << "\")\n";
        else
            err << "(error, \"unexpected char: " << *in << " line: " << in.line() << "\")\n";
        throw dimacs::lex_error();
    }

    while (*in >= '0' && *in <= '9') {
        val = val*10 + (*in - '0');
        ++in;
    }

    return neg ? -val : val; 
}

template<typename Buffer>
static void read_clause(Buffer & in, std::ostream& err, sat::solver & solver, sat::literal_vector & lits) {
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
static void read_clause(Buffer & in, std::ostream& err, sat::literal_vector & lits) {
    int     parsed_lit;
    int     var;
    
    lits.reset();

    while (true) { 
        parsed_lit = parse_int(in, err);
        if (parsed_lit == 0)
            break;
        var = abs(parsed_lit);
        SASSERT(var > 0);
        lits.push_back(sat::literal(var, parsed_lit < 0));
    }
}

template<typename Buffer>
static bool parse_dimacs_core(Buffer & in, std::ostream& err, sat::solver & solver) {
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
    catch (dimacs::lex_error) {
        return false;
    }
    return true;
}


bool parse_dimacs(std::istream & in, std::ostream& err, sat::solver & solver) {
    dimacs::stream_buffer _in(in);
    return parse_dimacs_core(_in, err, solver);
}


namespace dimacs {

    std::ostream& operator<<(std::ostream& out, drat_record const& r) {
        switch (r.m_tag) {
        case drat_record::tag_t::is_clause:
            return out << r.m_status << " " << r.m_lits << "\n";
        case drat_record::tag_t::is_node:
            return out << "e " << r.m_node_id << " " << r.m_name << " " << r.m_args << "\n"; 
        case drat_record::is_bool_def:
            return out << "b " << r.m_node_id << " " << r.m_args << "\n";
        }
        return out;
    }

    char const* drat_parser::parse_identifier() {
        m_buffer.reset();
        while (!is_whitespace(in)) {
            m_buffer.push_back(*in);
            ++in;
        }
        m_buffer.push_back(0);
        return m_buffer.c_ptr();
    }

    char const* drat_parser::parse_sexpr() {
        m_buffer.reset();
        unsigned lp = 0;
        while (!is_whitespace(in) || lp > 0) {
            m_buffer.push_back(*in);
            if (*in == '(') 
                ++lp;
            else if (*in == ')') {
                if (lp == 0) { 
                    throw lex_error(); 
                } 
                else --lp;
            }
            ++in;
        }
        m_buffer.push_back(0);
        return m_buffer.c_ptr();        
    }

    int drat_parser::read_theory_id() {
        skip_whitespace(in);
        if ('a' <= *in && *in <= 'z') {
            if (!m_read_theory_id)
                throw lex_error();
            return m_read_theory_id(parse_identifier());
        }
        else {
            return -1;
        }
    }

    bool drat_parser::next() {
        int n, b, e, theory_id;
        try {
        loop:
            skip_whitespace(in);
            switch (*in) {
            case EOF:
                return false;
            case 'c':
            case 'p':
                skip_line(in);
                goto loop;
            case 'i':
                ++in;
                skip_whitespace(in);
                read_clause(in, err, m_record.m_lits);
                m_record.m_tag = drat_record::tag_t::is_clause;
                m_record.m_status = sat::status::input();
                break;
            case 'a':
                ++in;
                skip_whitespace(in);
                theory_id = read_theory_id();
                skip_whitespace(in);
                read_clause(in, err, m_record.m_lits);
                m_record.m_tag = drat_record::tag_t::is_clause;
                m_record.m_status = sat::status::th(false, theory_id);
                break;
            case 'e':
                ++in;
                skip_whitespace(in);
                n = parse_int(in, err);                    
                skip_whitespace(in);
                m_record.m_name = parse_sexpr();
                m_record.m_tag = drat_record::tag_t::is_node;
                m_record.m_node_id = n;
                m_record.m_args.reset();
                while (true) {
                    n = parse_int(in, err);
                    if (n == 0)
                        break;
                    if (n < 0)
                        throw lex_error();
                    m_record.m_args.push_back(n);
                }
                break;
            case 'b':
                ++in;
                skip_whitespace(in);
                b = parse_int(in, err);
                n = parse_int(in, err);
                e = parse_int(in, err);
                if (e != 0)
                    throw lex_error();
                m_record.m_tag = drat_record::tag_t::is_bool_def;
                m_record.m_node_id = b;
                m_record.m_args.reset();
                m_record.m_args.push_back(n);
                break;
            case 'd':
                ++in;
                skip_whitespace(in);
                read_clause(in, err, m_record.m_lits);
                m_record.m_tag = drat_record::tag_t::is_clause;
                m_record.m_status = sat::status::deleted();
                break;
            case 'r':
                ++in;
                skip_whitespace(in);
                theory_id = read_theory_id();
                read_clause(in, err, m_record.m_lits);
                m_record.m_tag = drat_record::tag_t::is_clause;
                m_record.m_status = sat::status::th(true, theory_id);
                break;
            default:
                read_clause(in, err, m_record.m_lits);
                m_record.m_tag = drat_record::tag_t::is_clause;
                m_record.m_status = sat::status::redundant();
                break;                
            }    
            return true;
        }
        catch (lex_error) {
            return false;
        }
    }
}
