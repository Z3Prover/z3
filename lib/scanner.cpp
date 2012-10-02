/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    scanner.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-03-31.

Revision History:

--*/
#include"scanner.h"

inline char scanner::read_char() {
    if (m_is_interactive) {
        ++m_pos;
        return m_stream.get();
    }

    if (m_bpos >= m_bend) {
        m_buffer[0] = m_last_char;
        m_stream.read(m_buffer.c_ptr()+1, m_buffer.size()-1);
        m_bend = 1 + static_cast<unsigned>(m_stream.gcount());
        m_bpos = 1;
        m_last_char = m_buffer[m_bend-1];
    }
    ++m_pos;
    if (m_bpos < m_bend) {        
        return m_buffer[m_bpos++];
    } else {
        // increment m_bpos, so unread_char() will work properly
        ++m_bpos;
        return -1;
    }    
}

inline void scanner::unread_char() {
    --m_pos;
    if (m_is_interactive) {
        m_stream.unget();
    } else {
        // at most one character can be unread.
        SASSERT(m_bpos > 0);
        --m_bpos;
    }
}

inline bool scanner::state_ok() {
    return m_state != ERROR_TOKEN && m_state != EOF_TOKEN;
}

void scanner::comment(char delimiter) {
    while(state_ok()) {
        char ch = read_char();
        if ('\n' == ch) {
            ++m_line;
        }
        if (delimiter == ch || -1 == ch) {
            return;
        }
    }        
}

scanner::token scanner::read_symbol(char ch) {
    bool escape = false;
    if (m_smt2)
        m_string.pop_back(); // remove leading '|'
    while (ch != '|' || escape) {
        if (ch == EOF) {
            // TODO: use error reporting
            m_err << "ERROR: unexpected end of file.\n";
            return EOF_TOKEN;
        }
        if (ch == '\n') {
            ++m_line;
        }
        escape = (ch == '\\');
        m_string.push_back(ch);
        ch = read_char();                
    }
    if (!m_smt2)
        m_string.push_back(ch); // don't add trailing '|'
    m_string.push_back(0);
    m_id = m_string.begin();
    return ID_TOKEN;
}


scanner::token scanner::read_id(char first_char) {
    char ch;
    m_string.reset();
    m_params.reset();
    m_string.push_back(first_char);

    bool is_arith = (m_normalized[(unsigned char) first_char] == '+');
    bool is_alpha = (m_normalized[(unsigned char) first_char] == 'a');
    
    ch = read_char();        
    // In SMT2 "-20" is an identifier.
    if (!m_smt2 && state_ok() && first_char == '-' && m_normalized[(unsigned char) ch] == '0') {
        return read_number(ch, false);
    }

    if (state_ok() && first_char == '|') {
        return read_symbol(ch);
    }
    
    while (state_ok()) {                        
        switch(m_normalized[(unsigned char) ch]) {
        case '+':
            if (is_arith) {
                m_string.push_back(ch);
                break;
            }
            // strings can have hyphens.
            if (!is_alpha || ch != '-') {
                goto bail_out;  
            }
        case 'a':
        case ':':
        case '.':
        case '0':
            if (is_arith) {
                goto bail_out;
            }
            m_string.push_back(ch);
            break;
        case '[':                
            m_string.push_back(0);
            m_id = m_string.begin();
            if (read_params()) {
                return ID_TOKEN;
            }
            else {
                return m_state;
            }
        default:
            goto bail_out;
        }
        ch = read_char();
    }
    return m_state;

 bail_out:
    m_string.push_back(0);
    m_id = m_string.begin();
    unread_char();
    return ID_TOKEN;
}

bool scanner::read_params() {
    unsigned param_num = 0;
    
    while (state_ok()) {
        char ch = read_char();
        switch (m_normalized[(unsigned char) ch]) {
        case '0': 
            param_num = 10*param_num + (ch - '0');
            break;
        case ']':
            m_params.push_back(parameter(param_num));
            return true;
        case ':':               
            m_params.push_back(parameter(param_num));
            param_num = 0;
            break;
        default:
            m_string.reset();
            m_string.push_back(ch);
            while (true) {
                ch = read_char();
                if (ch == ':' || ch == ']') {
                    m_string.push_back(0);
                    m_params.push_back(parameter(symbol(m_string.c_ptr())));
                    param_num = 0;
                    if (ch == ':') {
                        unread_char();
                    }
                    else {
                        return true;
                    }
                    break;
                }
                if (ch == EOF) {
                    // TODO: use error reporting
                    m_err << "ERROR: unexpected character: '" << ((int)ch) << " " << ch << "'.\n";
                    m_state = ERROR_TOKEN;
                    break;
                }
                m_string.push_back(ch);
            }
            break;
        }
    }
    return false;
}

scanner::token scanner::read_number(char first_char, bool is_pos) {
    unsigned divide_by = 0;
    m_number = rational(first_char - '0');
    m_state = INT_TOKEN;
    
    while (true) {
        char ch = read_char();
        if (m_normalized[(unsigned char) ch] == '0') {
            m_number = rational(10)*m_number + rational(ch - '0');
            if (m_state == FLOAT_TOKEN) {
                ++divide_by;
            }
        }
        else if (ch == '.') {
            m_state = FLOAT_TOKEN;
        }
        else {
            unread_char();
            break;
        }
    }
    if (!is_pos) {
        m_number.neg();            
    }
    if (m_state == FLOAT_TOKEN) {
        m_number /= power(rational(10), divide_by);
    }
    return m_state;
}
    
scanner::token scanner::read_string(char delimiter, token result) {
    m_string.reset();
    m_params.reset();
    while (true) {
        char ch = read_char();
        
        if (!state_ok()) {
            return m_state;
        }
        
        if (ch == '\n') {
            ++m_line;
        }
        
        if (ch == delimiter || ch == EOF) {
            m_string.push_back(0);
            m_id = m_string.begin();
            return result;
        }
        
        if (ch == '\\') {
            m_string.push_back('\\');
            ch = read_char();
        }
        m_string.push_back(ch);
    }
    
    return m_state;
}

scanner::token scanner::read_bv_literal() {
    TRACE("scanner", tout << "read_bv_literal\n";);
    if (m_bv_token) {
        char ch     = read_char();
        if (ch == 'x') {
            ch = read_char();
            m_number  = rational(0);
            m_bv_size = 0;
            while (true) {
                if ('0' <= ch && ch <= '9') {
                    m_number *= rational(16);
                    m_number += rational(ch - '0');
                }
                else if ('a' <= ch && ch <= 'f') {
                    m_number *= rational(16);
                    m_number += rational(10 + (ch - 'a')); 
                }
                else if ('A' <= ch && ch <= 'F') {
                    m_number *= rational(16);
                    m_number += rational(10 + (ch - 'A'));
                }
                else {
                    unread_char();
                    m_state = m_bv_size == 0 ? ERROR_TOKEN : BV_TOKEN;
                    TRACE("scanner", tout << m_state << ", bv-size: " << m_bv_size << ", INT_TOKEN: " << INT_TOKEN
                          << ", BV_TOKEN: " << BV_TOKEN << "\n";);
                    return m_state;
                }
                m_bv_size += 4;
                ch = read_char();
            }
        }
        else if (ch == 'b') {
            ch = read_char();
            m_number  = rational(0);
            m_bv_size = 0;
            while (ch == '0' || ch == '1') {
                m_number *= rational(2);
                m_number += rational(ch - '0');
                m_bv_size++;
                ch = read_char();
            }
            unread_char();
            m_state = m_bv_size == 0 ? ERROR_TOKEN : BV_TOKEN;
            return m_state;
        }
        else {
            m_state = ERROR_TOKEN;
            return m_state;
        }
    }
    else {
        // hack for the old parser
        char ch     = read_char();
        bool is_hex = false;
        
        m_state = ID_TOKEN;
        m_string.reset();
        m_params.reset();
        
        // convert to SMT1 format
        m_string.push_back('b');
        m_string.push_back('v');
        if (ch == 'x') {
            m_string.push_back('h');
            m_string.push_back('e');
            m_string.push_back('x');
            is_hex = true;
        } else if (ch == 'b') {
            m_string.push_back('b');
            m_string.push_back('i');
            m_string.push_back('n');
        } else {
            // TODO: use error reporting
            m_err << "ERROR: unexpected character after '#': '" << ((int)ch) << " " << ch << "'.\n";
            m_state = ERROR_TOKEN;
            return m_state;
        }
        
        while (true) {
            ch = read_char();
            if (ch == '0' || ch == '1' ||
                (is_hex &&
                 (('0' <= ch && ch <= '9') ||
                  ('a' <= ch && ch <= 'f') ||
                  ('A' <= ch && ch <= 'F')))) {
                m_string.push_back(ch);
            } else {
                unread_char();
                break;
            }
        }
        m_string.push_back(0);
        m_id = m_string.begin();
        
        return m_state;
    }
}

scanner::scanner(std::istream& stream, std::ostream& err, bool smt2, bool bv_token):
    m_line(1),
    m_pos(0),
    m_id(""),
    m_bv_size(UINT_MAX),
    m_state(ID_TOKEN),
    m_stream(stream),
    m_err(err),
    m_bpos(1 << 10),
    m_bend(1 << 10),
    m_last_char(0),
    m_smt2(smt2),
    m_bv_token(bv_token) {
    char ch;

    m_is_interactive = &stream == &std::cin;
    m_buffer.resize(m_bpos);
    
    for (int i = 0; i < 256; ++i) {
        m_normalized[i] = (char) i;
    }
    
    m_normalized[static_cast<int>('\t')] = ' ';
    m_normalized[static_cast<int>('\r')] = ' ';
    
    // assert ('a' < 'z');
    for (ch = 'b'; ch <= 'z'; ++ch) {
        m_normalized[static_cast<int>(ch)] = 'a';
    }
    for (ch = 'A'; ch <= 'Z'; ++ch) {
        m_normalized[static_cast<int>(ch)] = 'a';
    }
    // assert ('0' < '9', '9' - '0' == 9);
    for (ch = '1'; ch <= '9'; ++ch) {
        m_normalized[static_cast<int>(ch)] = '0';
    }

    if (m_smt2) {
        // SMT2 3.1, "Symbols": ~ ! @ $ % ^ & * _ - + = < > . ? /
        m_normalized[static_cast<int>('~')] = 'a';
        m_normalized[static_cast<int>('!')] = 'a';
        m_normalized[static_cast<int>('@')] = 'a';
        m_normalized[static_cast<int>('$')] = 'a';
        m_normalized[static_cast<int>('%')] = 'a';
        m_normalized[static_cast<int>('^')] = 'a';
        m_normalized[static_cast<int>('&')] = 'a';
        m_normalized[static_cast<int>('*')] = 'a';
        m_normalized[static_cast<int>('_')] = 'a';
        m_normalized[static_cast<int>('-')] = 'a';
        m_normalized[static_cast<int>('+')] = 'a';
        m_normalized[static_cast<int>('=')] = 'a';
        m_normalized[static_cast<int>('<')] = 'a';
        m_normalized[static_cast<int>('>')] = 'a';
        m_normalized[static_cast<int>('.')] = 'a';
        m_normalized[static_cast<int>('?')] = 'a';
        m_normalized[static_cast<int>('/')] = 'a';

        // SMT2 3.1, "Hexadecimals", "Binaries"
        m_normalized[static_cast<int>('#')] = '#';

        m_normalized[static_cast<int>('|')] = '+';
    } else {
        m_normalized[static_cast<int>('=')] = '+';
        m_normalized[static_cast<int>('<')] = '+';
        m_normalized[static_cast<int>('>')] = '+';
        m_normalized[static_cast<int>('+')] = '+';
        m_normalized[static_cast<int>('-')] = '+';
        m_normalized[static_cast<int>('*')] = '+';
        m_normalized[static_cast<int>('/')] = '+';
        m_normalized[static_cast<int>('%')] = '+';
        m_normalized[static_cast<int>('~')] = '+';
        m_normalized[static_cast<int>('&')] = '+';
        m_normalized[static_cast<int>('@')] = '+';
        m_normalized[static_cast<int>('#')] = '+';
        m_normalized[static_cast<int>('|')] = '+';
        m_normalized[static_cast<int>('\\')] = '+';

        m_normalized[static_cast<int>('.')]  = '.';

        m_normalized[static_cast<int>('_')]  = 'a';
        m_normalized[static_cast<int>('\'')] = 'a';
        m_normalized[static_cast<int>('!')] = 'a';
        m_normalized[static_cast<int>('?')] = 'a';
    }
}

scanner::token scanner::scan() {
    while (state_ok()) {
        char ch = read_char();        
        switch (m_normalized[(unsigned char) ch]) {
        case ' ':
            break;
        case '\n':
            m_pos = 0;
            ++m_line;
            break;
        case ';':
            comment('\n');
            break;
        case ':':
            return COLON;
        case '(':
            return LEFT_PAREN;
        case ')':
            return RIGHT_PAREN;
        case '?':
        case '$':
        case 'a':
        case '+':
        case '.':
            return read_id(ch);
        case '{':
            return read_string('}',COMMENT_TOKEN);
        case '"':
            return read_string('"',STRING_TOKEN);
        case '0':
            return read_number(ch, true);
        case '#':
            return read_bv_literal();
        case -1:
            m_state = EOF_TOKEN;
            break;
        default:
            // TODO: use error reporting 
            m_err << "ERROR: unexpected character: '" << ((int)ch) << " " << ch << "'.\n";
            m_state = ERROR_TOKEN;
            break;
        }
    }
    return m_state;
}


