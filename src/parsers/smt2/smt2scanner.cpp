/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smt2scanner.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2011-03-09.

Revision History:

--*/
#include "parsers/smt2/smt2scanner.h"
#include "parsers/util/parser_params.hpp"

namespace smt2 {

    void scanner::next() {
        if (m_cache_input)
            m_cache.push_back(m_curr);
        SASSERT(!m_at_eof);
        if (m_interactive) {
            m_curr = m_stream.get();
            if (m_stream.eof())
                m_at_eof = true;
        }
        else if (m_bpos < m_bend) {
            m_curr = m_buffer[m_bpos];
            m_bpos++;
        }
        else {
            m_stream.read(m_buffer, SCANNER_BUFFER_SIZE);
            m_bend = static_cast<unsigned>(m_stream.gcount());
            m_bpos = 0;
            if (m_bpos == m_bend) {
                m_at_eof = true;
            }
            else {
                m_curr = m_buffer[m_bpos];
                m_bpos++;
            }
        }
        m_spos++;
    }

    void scanner::read_comment() {
        SASSERT(curr() == ';');
        next();
        while (true) {
            char c = curr();
            if (m_at_eof)
                return;
            if (c == '\n') {
                new_line();
                next();
                return;
            }
            next();
        }
    }
    
    void scanner::read_multiline_comment() {
        SASSERT(curr() == '|');
        next();
        while (true) {
            char c = curr();
            if (m_at_eof)
                return;
            if (c == '\n') {
                new_line();
                next();
                continue;
            }
            next();
            if (c == '|' && curr() == '#') {
                next();
                return;
            }
        }
    }

    scanner::token scanner::read_quoted_symbol() {
        SASSERT(curr() == '|');
        bool escape = false;
        m_string.reset();
        next();
        while (true) {
            char c = curr();
            if (m_at_eof) {
                throw scanner_exception("unexpected end of quoted symbol", m_line, m_spos);
            }
            else if (c == '\n') {
                new_line();
            }
            else if (c == '|' && !escape) {
                next();
                m_string.push_back(0);
                m_id = m_string.begin();
                TRACE("scanner", tout << "new quoted symbol: " << m_id << "\n";);
                return SYMBOL_TOKEN;
            }
            escape = (c == '\\');
            m_string.push_back(c);
            next();
        }
    }

    scanner::token scanner::read_symbol_core() {
        while (!m_at_eof) {
            char c = curr();
            signed char n = m_normalized[static_cast<unsigned char>(c)];
            if (n == 'a' || n == '0' || n == '-') {
                m_string.push_back(c);
                next();
            }
            else {
                m_string.push_back(0);
                m_id = m_string.begin();
                TRACE("scanner", tout << "new symbol: " << m_id << "\n";);
                return SYMBOL_TOKEN;
            }
        }
        if (!m_string.empty()) {
            m_string.push_back(0);
            m_id = m_string.begin();
            return SYMBOL_TOKEN;
        }
        return EOF_TOKEN;
    }

    scanner::token scanner::read_symbol() {
        SASSERT(m_normalized[static_cast<unsigned>(curr())] == 'a' || curr() == ':' || curr() == '-');
        m_string.reset();
        m_string.push_back(curr());
        next();
        return read_symbol_core();
    }

    scanner::token scanner::read_number() {
        SASSERT('0' <= curr() && curr() <= '9');
        rational q(1);
        m_number = rational(curr() - '0');
        next();
        bool is_float = false;

        while (!m_at_eof) {
            char c = curr();
            if ('0' <= c && c <= '9') {
                m_number = rational(10)*m_number + rational(c - '0');
                if (is_float)
                    q *= rational(10);
                next();
            }
            else if (c == '.') {
                if (is_float)
                    break;
                is_float = true;
                next();
            }
            else {
                break;
            }
        }
        if (is_float)
            m_number /= q;
        TRACE("scanner", tout << "new number: " << m_number << "\n";);
        return is_float ? FLOAT_TOKEN : INT_TOKEN;
    }

    scanner::token scanner::read_signed_number() {
        SASSERT(curr() == '-');
        next();
        if ('0' <= curr() && curr() <= '9') {
            scanner::token r = read_number();
            m_number.neg();
            return r;
        }
        else {
            // it is a symbol.
            m_string.reset();
            m_string.push_back('-');
            return read_symbol_core();
        }
    }

    scanner::token scanner::read_string() {
        SASSERT(curr() == '\"');
        next();
        m_string.reset();
        while (true) {
            char c = curr();
            if (m_at_eof)
                throw scanner_exception("unexpected end of string", m_line, m_spos);
            if (c == '\n') {
                new_line();
            }
            else if (c == '\"') {
                next();
                if (curr() != '\"') {
                    m_string.push_back(0);
                    return STRING_TOKEN;
                }
            }
            m_string.push_back(c);
            next();
        }
    }

    scanner::token scanner::read_bv_literal() {
        SASSERT(curr() == '#');
        next();
        char c = curr();
        if (c == 'x') {
            next();
            c = curr();
            m_number  = rational(0);
            m_bv_size = 0;
            while (true) {
                if ('0' <= c && c <= '9') {
                    m_number *= rational(16);
                    m_number += rational(c - '0');
                }
                else if ('a' <= c && c <= 'f') {
                    m_number *= rational(16);
                    m_number += rational(10 + (c - 'a'));
                }
                else if ('A' <= c && c <= 'F') {
                    m_number *= rational(16);
                    m_number += rational(10 + (c - 'A'));
                }
                else {
                    if (m_bv_size == 0)
                        throw scanner_exception("invalid empty bit-vector literal", m_line, m_spos);
                    return BV_TOKEN;
                }
                m_bv_size += 4;
                next();
                c = curr();
            }
        }
        else if (c == 'b') {
            next();
            c = curr();
            m_number  = rational(0);
            m_bv_size = 0;
            while (c == '0' || c == '1') {
                m_number *= rational(2);
                m_number += rational(c - '0');
                m_bv_size++;
                next();
                c = curr();
            }
            if (m_bv_size == 0)
                throw scanner_exception("invalid empty bit-vector literal", m_line, m_spos);
            return BV_TOKEN;
        }
        else if (c == '|') {
            read_multiline_comment();
            return NULL_TOKEN;
        }
        else {
            throw scanner_exception("invalid bit-vector literal, expecting 'x' or 'b'", m_line, m_spos);
        }
    }

    scanner::scanner(cmd_context & ctx, std::istream& stream, bool interactive) :
        m_interactive(interactive),
        m_spos(0),
        m_curr(0), // avoid Valgrind warning
        m_at_eof(false),
        m_line(1),
        m_pos(0),
        m_bv_size(UINT_MAX),
        m_bpos(0),
        m_bend(0),
        m_stream(stream),
        m_cache_input(false) {

        m_smtlib2_compliant = ctx.params().m_smtlib2_compliant;

        for (int i = 0; i < 256; ++i) {
            m_normalized[i] = (signed char) i;
        }
        m_normalized[static_cast<int>('\t')] = ' ';
        m_normalized[static_cast<int>('\r')] = ' ';
        // assert ('a' < 'z');
        for (char ch = 'b'; ch <= 'z'; ++ch) {
            m_normalized[static_cast<int>(ch)] = 'a';
        }
        for (char ch = 'A'; ch <= 'Z'; ++ch) {
            m_normalized[static_cast<int>(ch)] = 'a';
        }
        // assert ('0' < '9', '9' - '0' == 9);
        for (char ch = '1'; ch <= '9'; ++ch) {
            m_normalized[static_cast<int>(ch)] = '0';
        }
        // SMT2 "Symbols": ~ ! @ $ % ^ & * _ - + = < > . ? /
        m_normalized[static_cast<int>('~')] = 'a';
        m_normalized[static_cast<int>('!')] = 'a';
        m_normalized[static_cast<int>('@')] = 'a';
        m_normalized[static_cast<int>('$')] = 'a';
        m_normalized[static_cast<int>('%')] = 'a';
        m_normalized[static_cast<int>('^')] = 'a';
        m_normalized[static_cast<int>('&')] = 'a';
        m_normalized[static_cast<int>('*')] = 'a';
        m_normalized[static_cast<int>('_')] = 'a';
        m_normalized[static_cast<int>('-')] = '-';
        m_normalized[static_cast<int>('+')] = 'a';
        m_normalized[static_cast<int>('=')] = 'a';
        m_normalized[static_cast<int>('<')] = 'a';
        m_normalized[static_cast<int>('>')] = 'a';
        m_normalized[static_cast<int>('.')] = 'a';
        m_normalized[static_cast<int>('?')] = 'a';
        m_normalized[static_cast<int>('/')] = 'a';
        m_normalized[static_cast<int>(',')] = 'a';
        next();
    }

    scanner::token scanner::scan() {
        while (true) {
            signed char c = curr();
            token t;
            
            m_pos = m_spos;

            if (m_at_eof)
                return EOF_TOKEN;

            switch (m_normalized[(unsigned char) c]) {
            case ' ':
                next();
                break;
            case '\n':
                next();
                new_line();
                break;
            case ';':
                read_comment();
                break;
            case ':':
                read_symbol();
                return KEYWORD_TOKEN;
            case '(':
                next();
                return LEFT_PAREN;
            case ')':
                next();
                return RIGHT_PAREN;
            case '|':
                return read_quoted_symbol();
            case 'a':
                return read_symbol();
            case '"':
                return read_string();
            case '0':
                return read_number();
            case '#':
                t = read_bv_literal();
                if (t == NULL_TOKEN) break;
                return t;
            case '-':
                if (m_smtlib2_compliant)
                    return read_symbol();
                else
                    return read_signed_number();
            default: {
                scanner_exception ex("unexpected character", m_line, m_spos);
                next();
                throw ex;
            }}
        }
    }

    char const * scanner::cached_str(unsigned begin, unsigned end) {
        m_cache_result.reset();
        while (isspace(m_cache[begin]) && begin < end)
            begin++;
        while (begin < end && isspace(m_cache[end-1]))
            end--;
        for (unsigned i = begin; i < end; i++)
            m_cache_result.push_back(m_cache[i]);
        m_cache_result.push_back(0);
        return m_cache_result.begin();
    }

};

