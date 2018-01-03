/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    opt_parse.cpp

Abstract:

    Parse utilities for optimization.

Author:

    Nikolaj Bjorner (nbjorner) 2017-11-19

Revision History:

--*/
#include "opt/opt_context.h"
#include "opt/opt_parse.h"


class opt_stream_buffer {
    std::istream & m_stream;
    int            m_val;
    unsigned       m_line;
public:    
    opt_stream_buffer(std::istream & s):
        m_stream(s),
        m_line(0) {
        m_val = m_stream.get();
    }
    int  operator *() const { return m_val;}
    void operator ++() { m_val = m_stream.get(); }
    int ch() const { return m_val; }
    void next() { m_val = m_stream.get(); }
    bool eof() const { return ch() == EOF; }
    unsigned line() const { return m_line; }
    void skip_whitespace();
    void skip_space();
    void skip_line();
    bool parse_token(char const* token);
    int parse_int();
    unsigned parse_unsigned();
};


void opt_stream_buffer::skip_whitespace() {
    while ((ch() >= 9 && ch() <= 13) || ch() == 32) {
        if (ch() == 10) ++m_line;
        next(); 
    }
}

void opt_stream_buffer::skip_space() {
    while (ch() != 10 && ((ch() >= 9 && ch() <= 13) || ch() == 32)) {
        next(); 
    }
}
void opt_stream_buffer::skip_line() {
    while(true) {
        if (eof()) {
            return;
        }
        if (ch() == '\n') { 
            ++m_line;
            next();
            return; 
        }
        next();
    } 
}

bool opt_stream_buffer::parse_token(char const* token) {
    skip_whitespace();
    char const* t = token;
    while (ch() == *t) {
        next();
        ++t;
    }
    return 0 == *t;
}

unsigned opt_stream_buffer::parse_unsigned() {
    skip_space();
    if (ch() == '\n') {
        return UINT_MAX;
    }
    unsigned val = 0;
    while (ch() >= '0' && ch() <= '9') {
        val = val*10 + (ch() - '0');
        next();
    }
    return val;
}

int opt_stream_buffer::parse_int() {
    int     val = 0;
    bool    neg = false;
    skip_whitespace();
    
    if (ch() == '-') {
        neg = true;
        next();
    }
    else if (ch() == '+') {
        next();
    }        
    if (ch() < '0' || ch() > '9') {
        std::cerr << "(error line " << line() << " \"unexpected char: " << ((char)ch()) << "\" )\n";
        exit(3);
    }        
    while (ch() >= '0' && ch() <= '9') {
        val = val*10 + (ch() - '0');
        next();
    }
    return neg ? -val : val; 
}


class wcnf {
    opt::context&  opt;
    ast_manager&   m;
    opt_stream_buffer& in;
    unsigned_vector& m_handles;

    app_ref read_clause(unsigned& weight) {
        int     parsed_lit;
        int     var;    
        weight = in.parse_unsigned();
        app_ref result(m), p(m);
        expr_ref_vector ors(m);
        while (true) { 
            parsed_lit = in.parse_int();
            if (parsed_lit == 0)
                break;
            var = abs(parsed_lit);
            p = m.mk_const(symbol(var), m.mk_bool_sort());
            if (parsed_lit < 0) p = m.mk_not(p);
            ors.push_back(p);
        }
        result = to_app(mk_or(m, ors.size(), ors.c_ptr()));
        return result;
    }
    
    void parse_spec(unsigned& num_vars, unsigned& num_clauses, unsigned& max_weight) {
        in.parse_token("wcnf");
        num_vars = in.parse_unsigned();
        num_clauses = in.parse_unsigned();
        max_weight = in.parse_unsigned();
    }

public:
    
    wcnf(opt::context& opt, opt_stream_buffer& in, unsigned_vector& h): opt(opt), m(opt.get_manager()), in(in), m_handles(h) {
        opt.set_clausal(true);
    }
    
    void parse() {
        unsigned num_vars = 0, num_clauses = 0, max_weight = 0;
        while (true) {
            in.skip_whitespace();
            if (in.eof()) {
                break;
            }
            else if (*in == 'c') {
                in.skip_line();
            }
            else if (*in == 'p') {
                ++in;
                parse_spec(num_vars, num_clauses, max_weight);
            }
            else {
                unsigned weight = 0;
                app_ref cls = read_clause(weight);
                if (weight >= max_weight) {
                    opt.add_hard_constraint(cls);
                }
                else {
                    unsigned id = opt.add_soft_constraint(cls, rational(weight), symbol::null);
                    if (m_handles.empty()) {
                        m_handles.push_back(id);
                    }
                }
            }
        }
    }    
};


class opb {
    opt::context&  opt;
    ast_manager&   m;    
    opt_stream_buffer& in;
    unsigned_vector& m_handles;
    arith_util     arith;

    app_ref parse_id() {
        bool negated = in.parse_token("~");
        if (!in.parse_token("x")) {
            std::cerr << "(error line " << in.line() << " \"unexpected char: " << ((char)in.ch()) << "\" expected \"x\")\n";
            exit(3);
        }
        app_ref p(m);
        int id = in.parse_int();
        p = m.mk_const(symbol(id), m.mk_bool_sort());
        if (negated) p = m.mk_not(p);
        in.skip_whitespace();
        return p;
    }

    app_ref parse_ids() {
        app_ref result = parse_id();
        while (*in == '~' || *in == 'x') {            
            result = m.mk_and(result, parse_id());
        }
        return result;
    }

    rational parse_coeff_r() {
        in.skip_whitespace();
        svector<char> num;
        bool pos = true;
        if (*in == '-') pos = false, ++in;
        if (*in == '+') ++in;
        if (!pos) num.push_back('-');
        in.skip_whitespace();
        while ('0' <= *in && *in <='9') num.push_back(*in), ++in;
        num.push_back(0);
        return rational(num.c_ptr());
    }

    app_ref parse_coeff() {
        return app_ref(arith.mk_numeral(parse_coeff_r(), true), m);
    }
    
    app_ref parse_term() {        
        app_ref c = parse_coeff();
        app_ref e = parse_ids();
        return app_ref(m.mk_ite(e, c, arith.mk_numeral(rational(0), true)), m);
    }

    void parse_objective(bool is_min) {
        app_ref t = parse_term();
        while (!in.parse_token(";") && !in.eof()) {
            if (is_min) {
                t = arith.mk_add(t, parse_term());
            }
            else {
                t = arith.mk_sub(t, parse_term());
            }
        }
        m_handles.push_back(opt.add_objective(t, false));
    }

    void parse_constraint() {
        app_ref t = parse_term();
        while (!in.eof()) {
            if (in.parse_token(">=")) {    
                t = arith.mk_ge(t, parse_coeff());
                in.parse_token(";");
                break;
            }
            if (in.parse_token("=")) {
                t = m.mk_eq(t, parse_coeff());
                in.parse_token(";");
                break;
            }            
            if (in.parse_token("<=")) {
                t = arith.mk_le(t, parse_coeff());
                in.parse_token(";");
                break;
            }            
            t = arith.mk_add(t, parse_term());
        }        
        opt.add_hard_constraint(t);
    }
public:
    opb(opt::context& opt, opt_stream_buffer& in, unsigned_vector& h): 
        opt(opt), m(opt.get_manager()), 
        in(in), m_handles(h), arith(m) {}

    void parse() {
        while (true) {
            in.skip_whitespace();
            if (in.eof()) {
                break;
            }
            else if (*in == '*') {
                in.skip_line();
            }
            else if (in.parse_token("min:")) {
                parse_objective(true);
            }
            else if (in.parse_token("max:")) {
                parse_objective(false);
            }
            else {
                parse_constraint();
            }
        }
    }
};

void parse_wcnf(opt::context& opt, std::istream& is, unsigned_vector& h) {
    opt_stream_buffer _is(is);
    wcnf w(opt, _is, h);
    w.parse();
}

void parse_opb(opt::context& opt, std::istream& is, unsigned_vector& h) {
    opt_stream_buffer _is(is);
    opb opb(opt, _is, h);
    opb.parse();
}


