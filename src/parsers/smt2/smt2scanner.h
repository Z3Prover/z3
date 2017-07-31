/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt2scanner.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2011-03-09.

Revision History:

--*/
#ifndef SMT2SCANNER_H_
#define SMT2SCANNER_H_

#include<iostream>
#include "util/symbol.h"
#include "util/vector.h"
#include "util/rational.h"
#include "cmd_context/cmd_context.h"

namespace smt2 {

    typedef cmd_exception scanner_exception;
    
    class scanner {
    private:
        bool               m_interactive;
        int                m_spos; // position in the current line of the stream
        char               m_curr;  // current char;
        bool               m_at_eof;
        
        int                m_line;  // line
        int                m_pos;   // start position of the token
        // data
        symbol             m_id;
        rational           m_number;
        unsigned           m_bv_size;
        // end of data
        signed char        m_normalized[256];
#define SCANNER_BUFFER_SIZE 1024
        char               m_buffer[SCANNER_BUFFER_SIZE];
        unsigned           m_bpos;
        unsigned           m_bend;
        svector<char>      m_string;
        std::istream&      m_stream;
        
        bool               m_cache_input;
        svector<char>      m_cache;
        svector<char>      m_cache_result;
        
        bool               m_smtlib2_compliant;
        
        char curr() const { return m_curr; }
        void new_line() { m_line++; m_spos = 0; }
        void next();
        
    public:
        
        enum token {
            NULL_TOKEN = 0,
            LEFT_PAREN = 1,
            RIGHT_PAREN,
            KEYWORD_TOKEN,
            SYMBOL_TOKEN,
            STRING_TOKEN,
            INT_TOKEN,
            BV_TOKEN,
            FLOAT_TOKEN,
            EOF_TOKEN
        };
        
        scanner(cmd_context & ctx, std::istream& stream, bool interactive = false);
        
        ~scanner() {}    
        
        int get_line() const { return m_line; }
        int get_pos() const { return m_pos; }
        symbol const & get_id() const { return m_id; }
        rational get_number() const { return m_number; }
        unsigned get_bv_size() const { return m_bv_size; }
        char const * get_string() const { return m_string.begin(); }
        token scan();
        
        token read_symbol_core();
        token read_symbol();
        token read_quoted_symbol();
        void read_comment();
        token read_number();
        token read_signed_number();
        token read_string();
        token read_bv_literal();

        void start_caching() { m_cache_input = true; m_cache.reset(); }
        void stop_caching() { m_cache_input = false; }
        unsigned cache_size() const { return m_cache.size(); }
        void reset_cache() { m_cache.reset(); }
        char const * cached_str(unsigned begin, unsigned end);
    };

};

#endif /* SCANNER_H_ */

