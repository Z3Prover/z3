/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    dimacs.h

Abstract:

    Dimacs CNF parser

Author:

    Leonardo de Moura (leonardo) 2011-07-26.

Revision History:

    Nikolaj Bjorner (nbjorner) 2020-09-07
    Add parser to consume extended DRAT format.

--*/
#pragma once

#include "sat/sat_types.h"

bool parse_dimacs(std::istream & s, std::ostream& err, sat::solver & solver);

namespace dimacs {
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

    struct drat_record {
        enum tag_t { is_clause, is_node, is_bool_def };
        tag_t            m_tag;
        // a clause populates m_lits and m_status
        // a node populates m_node_id, m_name, m_args
        // a bool def populates m_node_id and one element in m_args
        sat::literal_vector  m_lits;
        sat::status     m_status;
        unsigned        m_node_id;
        std::string     m_name;
        unsigned_vector m_args;
        drat_record():
            m_tag(is_clause),
            m_status(sat::status::redundant())
        {}
    };

    std::ostream& operator<<(std::ostream& out, drat_record const& r);

    class drat_parser {
        dimacs::stream_buffer      in;
        std::ostream&      err;
        drat_record        m_record;
        std::function<int(char const*)> m_read_theory_id;
        svector<char>      m_buffer;

        char const* parse_sexpr();
        char const* parse_identifier();
        int read_theory_id();
        bool next();

    public:
        drat_parser(std::istream & _in, std::ostream& err):
            in(_in), err(err)
        {}

        class iterator {
            drat_parser& p;
            bool m_eof;
        public:
            iterator(drat_parser& p, bool is_eof):p(p), m_eof(is_eof) { if (!m_eof) m_eof = !p.next(); }
            drat_record const& operator*() { return p.m_record; }
            iterator& operator++() { if (!p.next()) m_eof = true; return *this;}
            bool operator==(iterator const& other) const { return m_eof == other.m_eof; }
            bool operator!=(iterator const& other) const { return m_eof != other.m_eof; }
        };
        
        iterator begin() { return iterator(*this, false); };
        iterator end() { return iterator(*this, true); }

        void set_read_theory(std::function<int(char const*)>& r) { m_read_theory_id = r; }

    };
};



