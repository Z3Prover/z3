/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    scanner.h

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-03-31.

Revision History:

--*/
#ifndef SCANNER_H_
#define SCANNER_H_

#include "ast/ast.h"

class scanner {
public:

    enum token {
        LEFT_PAREN = 1,
        RIGHT_PAREN,
        COLON,
        ID_TOKEN,        
        STRING_TOKEN,
        COMMENT_TOKEN,
        INT_TOKEN,
        BV_TOKEN,
        FLOAT_TOKEN,
        EOF_TOKEN,
        ERROR_TOKEN
    };    

    scanner(std::istream& stream, std::ostream& err, bool smt2, bool bv_token=false);

    ~scanner() {}    
    
    int get_line() const { return m_line; }

    int get_pos() const { return m_pos; }

    symbol const & get_id() const { return m_id; }

    rational get_number() const { return m_number; }

    unsigned get_bv_size() const { return m_bv_size; }

    vector<parameter> const & get_params() const { return m_params; }
    
    token scan();
    
private:
    int                m_line;
    int                m_pos;
    symbol             m_id;
    rational           m_number;
    unsigned           m_bv_size;
    token              m_state;
    char        m_normalized[256];
    vector<char>       m_string;
    std::istream&      m_stream;
    std::ostream&      m_err;
    vector<parameter>  m_params;
    buffer<char>       m_buffer;
    unsigned           m_bpos;
    unsigned           m_bend;
    char               m_last_char;
    bool               m_is_interactive;
    bool               m_smt2;
    bool               m_bv_token;

    int read_char();
    token read_symbol(int ch);
    void unread_char();
    void comment(char delimiter);
    token read_id(char first_char);
    bool read_params();
    token read_number(char first_char, bool is_pos);
    token read_string(char delimiter, token result);
    token read_bv_literal();
    bool state_ok();
};

#endif /* SCANNER_H_ */

