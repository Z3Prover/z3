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
    void skip_whitespace() {
        while ((ch() >= 9 && ch() <= 13) || ch() == 32) {
            if (ch() == 10) ++m_line;
            next(); 
        }
    }
    void skip_space() {
        while (ch() != 10 && ((ch() >= 9 && ch() <= 13) || ch() == 32)) 
            next();  
    }
    void skip_line() {
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
    bool parse_token(char const* token);
    int parse_int();
    unsigned parse_unsigned();
};




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

#if 0

class lp_stream_buffer : opt_stream_buffer {
public:    
    lp_stream_buffer(std::istream & s):
        opt_stream_buffer(s)
    {}

    char lower(char c) {
        return ('A' <= c && c <= 'Z') ? c - 'A' + 'a' : c;
    }

    bool parse_token_nocase(char const* token) {
        skip_whitespace();
        char const* t = token;
        while (lower(ch()) == *t) {
            next();
            ++t;
        }
        return 0 == *t;
    }
};


class lp_tokenizer {
    opt_stream_buffer& in;
public:
    lp_tokenizer(opt_stream_buffer& in):
        in(in)
    {}
    
};

class lp_parse {
    opt::context& opt;
    lp_tokenizer& tok;
public:
    lp_parse(opt::context& opt, lp_stream_buffer& in): opt(opt), tok(is) {}
    
    void parse() {
        objective();
        subject_to();
        bounds();
        general();
        binary();
    }

    void objective() {
        m_objective.m_is_max = minmax();
        m_objective.m_name = try_name();
        m_objective.m_expr = expr();
    }

    bool minmax() {
        if (try_accept("minimize"))
            return false;
        if (try_accept("min"))
            return false;
        if (try_accept("maximize"))
            return true;
        if (try_accept("max"))
            return true;
        error("expected min or max objective");
        return false;
    }

    bool try_accept(char const* token) {
        return false;
    }

    bool indicator(symbol& var, bool& val) {
        if (!try_variable(var)) return false;
        check(in.parse_token("="));
        
    }

                
    def indicator(self):
        v = self.variable()
        self.accept("=")
        val = self.try_accept("1")
        if val is None:
            val = self.accept("0")            
        self.accept("->")
        return (var, val)

    def try_indicator(self):
        try:
            return self.indicator()
        with:
            return None

    def constraints(self):
        return [c for c in self._constraints()]
    
    def _constraints(self):
        while True:
            c = self.try_constraint()
            if c in None:
                return
            yield c

    def try_constraint(self):
        try:
            return self.constraint()
        except:
            return None
        
    def constraint(self):
        name = self.try_label()
        guard = self.try_guard()
        e = self.expr()
        op = self.relation()
        rhs = self.numeral()
        return (name, guard, e, ops, rhs)

    def expr(self):
        return [t for t in self.terms()]

    def terms(self):
        while True:
            t = self.term()
            if t is None:
                return None
            yield t

    def term(self):
        sign = self.sign()
        coeff = self.coeff()
        v = self.variable()
        return (sign*coeff, v)

    def sign(self):
        if self.try_accept("-"):
            return -1
        return 1

    def coeff(self):
        tok = self.peek()
        if tok is int:
            self.next()
            return (int) tok
        return 1

    def relation(self):
        if self.try_accept("<="):
            return "<="
        if self.try_accept(">="):
            return ">="
        if self.try_accept("=<"):
            return "<="
        if self.try_accept("=>"):
            return ">="
        if self.try_accept("="):
            return "="
        return None

    def subject_to(self):
        if self.accept("subject") and self.accept("to"):
            return
        if self.accept("such") and self.accept("that"):
            return
        if self.accept("st"):
            return
        if self.accept("s"):
            self.try_accept(".")
            self.accept("t")
            self.accept(".")
            return
        

};

void parse_lp(opt::context& opt, std::istream& is) {
    lp_stream_buffer _is(is);
    lp_parse lp(opt, _is);
    lp.parse();
}

#endif
