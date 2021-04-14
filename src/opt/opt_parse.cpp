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
            p = m.mk_const(symbol((unsigned)var), m.mk_bool_sort());
            if (parsed_lit < 0) p = m.mk_not(p);
            ors.push_back(p);
        }
        result = to_app(mk_or(m, ors.size(), ors.data()));
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
        p = m.mk_const(symbol((unsigned)id), m.mk_bool_sort());
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
        return rational(num.data());
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

/**
 * \brief Parser for a modest subset of the CPLEX LP format.
 * Reference: http://eaton.math.rpi.edu/cplex90html/reffileformatscplex/reffileformatscplex5.html
 */

struct asymbol {
    bool     m_is_num;
    symbol   m_sym;
    rational m_num;
    unsigned m_line;
    asymbol(symbol const& s, unsigned l): m_is_num(false), m_sym(s), m_line(l) {}
    asymbol(rational const& r, unsigned l): m_is_num(true), m_num(r), m_line(l) {}
};

std::ostream& operator<<(std::ostream& out, asymbol const& c) {
    if (c.m_is_num) {
        return out << c.m_num;
    }
    else {
        return out << c.m_sym;
    }
}

class lp_tokenizer {
    vector<asymbol>    m_tokens;
    unsigned           m_pos;
    svector<char>      m_buffer;
public:
    lp_tokenizer(opt_stream_buffer& in):
        m_pos(0)
    {
        parse_all(in);
    }

    symbol const& peek(unsigned i) {
        if (i + m_pos >= m_tokens.size()) {
            return symbol::null;
        }
        return m_tokens[i + m_pos].m_sym;
    }

    bool peek_num(unsigned i) {
        if (i + m_pos >= m_tokens.size()) {
            return false;
        }
        return m_tokens[i + m_pos].m_is_num;        
    }

    rational const& get_num(unsigned i) {
        return m_tokens[i + m_pos].m_num;
    }

    void next(unsigned delta = 1) {
        m_pos += delta;
    }

    bool eof() const {
        return m_pos == m_tokens.size();
    }

    unsigned line() const {
        if (m_pos < m_tokens.size()) return m_tokens[m_pos].m_line;
        return 0;
    }

private:

    bool is_separator(char c) {
        return c == '\n' || c == '\\' || c == '*' || c == '+'; 
    }

    char lower(char c) {
        if ('A' <= c && c <= 'Z')
            return c - ('A' - 'a');
        return c;
    }

    void parse_all(opt_stream_buffer& in) {
        while (!in.eof()) {
            in.skip_whitespace();
            char c = in.ch();  
            if (c == '\\') {
                in.skip_line();
                continue;
            }
            bool neg = false;
            if (c == '-') {
                in.next();
                c = in.ch();
                m_buffer.reset();
                m_buffer.push_back('-');
                if (is_num(c)) {
                    neg = true;
                }
                else {
                    while (!is_ws(c) && !in.eof()) {
                        m_buffer.push_back(c);
                        in.next();
                        c = in.ch();
                    }
                    m_buffer.push_back(0);
                    m_tokens.push_back(asymbol(symbol(m_buffer.data()), in.line()));
                    IF_VERBOSE(10, verbose_stream() << "tok: " << m_tokens.back() << "\n");
                    continue;
                }
            }

            if (is_num(c)) {
                rational n(0);
                rational div(1);
                while (is_num(c) && !in.eof()) {
                    n = n*rational(10) + rational(c - '0');
                    in.next();
                    c = in.ch();
                }
                if (c == '.') {
                    in.next();
                    c = in.ch();
                    while (is_num(c) && !in.eof()) {
                        n = n*rational(10) + rational(c - '0');
                        in.next();
                        div *= rational(10);
                        c = in.ch();
                    }
                }
                if (div > rational(1)) n = n / div;
                if (neg) n.neg();
                m_tokens.push_back(asymbol(n, in.line()));
                IF_VERBOSE(10, verbose_stream() << "num: " << m_tokens.back() << "\n");
                continue;
            }
            m_buffer.reset();
            if (is_alpha(c)) {
                while (is_sym(c) && !in.eof()) {
                    m_buffer.push_back(lower(c));
                    in.next();
                    c = in.ch();
                }
            }
            else {
                while (!is_ws(c) && !in.eof()) {
                    m_buffer.push_back(c);
                    in.next();
                    c = in.ch();
                }
            }
            m_buffer.push_back(0);
            m_tokens.push_back(asymbol(symbol(m_buffer.data()), in.line()));
            IF_VERBOSE(10, verbose_stream() << "tok: " << m_tokens.back() << "\n");
        }
    }

    bool is_alpha(char c) const {
        return ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z');
    }

    bool is_num(char c) const {
        return '0' <= c && c <= '9';
    }

    bool is_ws(char c) const {
        return c == ' ' || c == '\n' || c == '\t';
    }

    bool is_sym(char c) const {
        return 
            is_alpha(c) || 
            is_num(c) ||
            c == '!' ||
            c == '"' ||
            c == '-' ||
            c == '#' ||
            c == '$' ||
            c == '%' ||
            c == '&' ||
            c == '{' ||
            c == '}' ||
            c == ',' ||
            c == '_' ||
            c == '.' ||
            c == ';' ||
            c == '?' ||
            c == '@' ||
            c == '`' ||
            c == '\'' ||
            c == '(' ||
            c == ')' ||
            c == '~';
    }
    
};

class lp_parse {
    typedef vector<std::pair<rational, symbol> > lin_term;

    struct objective {
        bool      m_is_max;
        symbol    m_name;
        lin_term  m_expr;
    };

    enum rel_op {
        le, ge, eq
    };

    struct constraint {
        symbol   m_name;
        symbol   m_bvar;
        rational m_bval;
        lin_term m_expr;
        rel_op   m_rel;
        rational m_bound;
        constraint(symbol const& name, symbol const& v, rational const& val, lin_term& terms, rel_op r, rational const& bound):
            m_name(name), m_bvar(v), m_bval(val), m_expr(terms), m_rel(r), m_bound(bound) {}
    };

    struct bound {
        optional<rational>  m_lo, m_hi;
        bool m_int;
        bound() : m_int(false) {}
    };

    opt::context&       opt;
    unsigned_vector&    m_h;
    lp_tokenizer        tok;
    objective           m_objective;
    vector<constraint>  m_constraints;
    map<symbol, bound, symbol_hash_proc, symbol_eq_proc> m_bounds;

public:

    lp_parse(opt::context& opt, opt_stream_buffer& in, unsigned_vector& h) : 
        opt(opt), m_h(h), tok(in) {}
    
    void parse() {
        parse_objective();
        if (!try_subject_to()) {
            error("subject to section expected");
            return;
        }
         
        while (!is_section()) {
            parse_constraint();
        }

        while (true) {
            if (is_bounds()) {
                tok.next();
                while (!is_section()) {
                    parse_bound();
                }
            }
            else if (is_binary()) {
                tok.next();
                while (!is_section()) {
                    parse_binary();
                }
            }
            else if (is_general()) {
                tok.next();
                while (!is_section()) {
                    parse_general();
                }
            }
            else {
                break;
            }
        }
        post_process();
    }

private:

    void error(char const* msg) {
        std::ostringstream ous;
        ous << tok.line() << ": " << msg << " got: " << peek(0) << "\n";
        throw default_exception(ous.str());
    }
        
    symbol const& peek(unsigned i) { return tok.peek(i); }

    bool try_accept(char const * token) {
        if (peek(0) == token) {
            tok.next();
            return true;
        }
        return false;
    }

    void parse_objective() {
        m_objective.m_is_max = minmax();
        if (peek(1) == ":") {
            m_objective.m_name = peek(0);
            tok.next(2);
        }
        parse_expr(m_objective.m_expr);
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

    void parse_constraint() {
        symbol name;
        if (peek(1) == ":") {
            name = peek(0);
            tok.next(2);
        }
        IF_VERBOSE(10, verbose_stream() << name << "\n");
        rational val(0);
        symbol var;
        parse_indicator(var, val);
        lin_term terms;
        parse_expr(terms);
        rel_op op = parse_relation();
        rational rhs = tok.get_num(0);
        tok.next();
        m_constraints.push_back(constraint(name, var, val, terms, op, rhs));
    }

    void parse_expr(lin_term& terms) {
        if (is_relation()) {
            return;
        }
        bool pos = true;
        if (peek(0) == "-") {
            pos = false;
            tok.next();
        }
        while (peek(0) == "+") {
            tok.next();
        }
        terms.push_back(parse_term());
        if (!pos) terms.back().first = -terms.back().first; 
        while (peek(0) == "+" || peek(0) == "-") {
            bool pos = peek(0) == "+";
            tok.next();
            terms.push_back(parse_term());
            if (!pos) terms.back().first = -terms.back().first; 
        }
    }
    
    std::pair<rational, symbol> parse_term() {
        std::pair<rational, symbol> r(rational::one(), peek(0));
        if (tok.peek_num(0)) {
            r.first = tok.get_num(0);
            r.second = peek(1);
            tok.next(2);
        }
        else {
            tok.next(1);
        }
        return r;
    }

    rel_op parse_relation() {
        if (try_accept("<=")) return le;
        if (try_accept("=<")) return le;
        if (try_accept(">=")) return ge;
        if (try_accept("=>")) return ge;
        if (try_accept("=")) return eq;
        error("expected relation");
        return eq;
    }

    bool peek_le(unsigned pos) {
        return peek(pos) == "<=" || peek(pos) == "=<";
    }

    bool peek_minus_infty_long(unsigned pos) {
        return peek(pos) == "-" && (peek(pos+1) == "inf" || peek(pos+1) == "infinity");
    }

    bool peek_minus_infty_short(unsigned pos) {
        return peek(pos) == "-inf" || peek(pos) == "-infinity";
    }

    bool peek_plus_infty_long(unsigned pos) {
        return peek(pos) == "+" && (peek(pos+1) == "inf" || peek(pos+1) == "infinity");
    }

    bool peek_plus_infty_short(unsigned pos) {
        return peek(pos) == "+inf" || peek(pos) == "+infinity";
    }

    void parse_indicator(symbol& var, rational& val) {
        if (peek(1) == "=" && tok.peek_num(2) && peek(3) == "->") {
            var = peek(0);
            val = tok.get_num(2);
            tok.next(4);
        }
    }

    bool try_subject_to() {
        if (try_accept("subject") && try_accept("to")) return true;
        if (try_accept("such") && try_accept("that")) return true;
        if (try_accept("st")) return true;
        if (try_accept("s.t.")) return true;
        return false;
    }

    bool is_relation() { return peek(0) == "=" || peek(0) == "=<" || peek(0) == ">=" || peek(0) == "=>" || peek(0) == "<="; }
    bool is_section() { return is_general() || is_binary() || is_bounds() || is_end();}
    bool is_bounds() { return peek(0) == "bounds"; }
    bool is_general() { return peek(0) == "general" || peek(0) == "gen" || peek(0) == "generals"; }
    bool is_binary() { return peek(0) == "binary" || peek(0) == "binaries" || peek(0) == "bin"; }
    bool is_end() { return peek(0) == "end" || tok.eof(); }

    // lo <= x
    // x <= hi
    // lo <= x <= hi
    // 
    void parse_bound() {
        symbol v;
        if (peek_le(1) && tok.peek_num(0)) {
            rational lhs = tok.get_num(0);
            v = peek(2);
            update_lower(lhs, v);
            tok.next(3);
            parse_upper(v);
        }
        else if (peek_minus_infty_long(0) && peek_le(2)) {
            v = peek(3);
            tok.next(4);
            parse_upper(v);
        }
        else if (peek_minus_infty_short(0) && peek_le(1)) {
            v = peek(2);
            tok.next(3);
            parse_upper(v);
        }
        else if (peek_plus_infty_long(2) && peek_le(1)) {
            tok.next(4);            
        }
        else if (peek_plus_infty_short(2) && peek_le(1)) {
            tok.next(3);
        }
        else if (peek_le(1) && tok.peek_num(2)) {
            v = peek(0);
            tok.next(2);
            rational rhs = tok.get_num(0);
            update_upper(v, rhs);
            tok.next(1);
        }
        else {
            error("bound expected");
        }
    }

    void parse_upper(symbol const& v) {
        if (peek_le(0) && tok.peek_num(1)) {
            rational rhs = tok.get_num(1);
            update_upper(v, rhs);
            tok.next(2);
        }
        else if (peek_le(0) && peek_plus_infty_long(1)) {
            tok.next(3);            
        }
        else if (peek_le(0) && peek_plus_infty_short(1)) {
            tok.next(2);        }

    }

    void update_lower(rational const& r, symbol const& v) {
        bound b;
        m_bounds.find(v, b);
        b.m_lo = r;
        m_bounds.insert(v, b);
    }

    void update_upper(symbol const& v, rational const& r) {
        bound b;
        if (!m_bounds.find(v, b)) {
            // set the lower bound to default 0
            b.m_lo = rational::zero();
        }
        b.m_hi = r;
        m_bounds.insert(v, b);
    }

    void parse_binary() {
        symbol const& v = peek(0);
        update_lower(rational::zero(), v);
        update_upper(v, rational::one());
        m_bounds[v].m_int = true;
        tok.next();
    }

    void parse_general() {
        if (peek(1) == ":" && peek(3) == "=") {
            symbol const& v = peek(2);        
            std::cout << "TBD: " << v << "\n";
            return;
        }
        symbol const& v = peek(0);        
        bound b;
        m_bounds.find(v, b);        
        b.m_int = true;
        m_bounds.insert(v, b);
        tok.next();        
    }
    
    void post_process() {
        ast_manager& m = opt.get_manager();
        arith_util a(m);
        for (constraint const& c : m_constraints) {            
            expr_ref fml(m);
            expr_ref term = process_terms(c.m_expr);
            bool is_int = a.is_int(term) && c.m_bound.is_int();
            switch (c.m_rel) {
            case le: fml = a.mk_le(term, a.mk_numeral(c.m_bound, is_int)); break;
            case ge: fml = a.mk_ge(term, a.mk_numeral(c.m_bound, is_int)); break;
            case eq: fml = m.mk_eq(term, a.mk_numeral(c.m_bound, is_int)); break;
            }
            if (c.m_bvar != symbol::null) {
                term = mk_var(c.m_bvar);
                bool is_int = c.m_bval.is_int() && a.is_int(term);
                term = m.mk_eq(mk_var(c.m_bvar), a.mk_numeral(c.m_bval, is_int));
                fml = m.mk_implies(term, fml);
            }
            opt.add_hard_constraint(fml);
        }
        for (auto const& kv : m_bounds) {
            bound const& b = kv.m_value;
            expr_ref term = mk_var(kv.m_key);
            if (b.m_lo) {                
                bool is_int = b.m_lo->is_int() && a.is_int(term);
                opt.add_hard_constraint(a.mk_le(a.mk_numeral(*b.m_lo, is_int), term));
            }
            if (b.m_hi) {
                bool is_int = b.m_hi->is_int() && a.is_int(term);
                opt.add_hard_constraint(a.mk_le(term, a.mk_numeral(*b.m_hi, is_int)));
            }
        }
        expr_ref term = process_terms(m_objective.m_expr);
        m_h.push_back(opt.add_objective(to_app(term), m_objective.m_is_max));
    }

    expr_ref process_terms(lin_term const& terms) {
        ast_manager& m = opt.get_manager();
        arith_util a(m);
        expr_ref_vector result(m);
        for (auto const& kv : terms) {
            expr_ref term = mk_var(kv.second);
            if (!kv.first.is_one()) {
                bool is_int = kv.first.is_int() && a.is_int(term);
                term = a.mk_mul(a.mk_numeral(kv.first, is_int), term);
            }
            result.push_back(term);
        }
        return expr_ref(a.mk_add(result.size(), result.data()), m);
    }

    expr_ref mk_var(symbol const& v) {
        ast_manager& m = opt.get_manager();
        arith_util a(m);
        bound b;
        if (!m_bounds.find(v, b)) {
            b.m_lo = rational::zero();
            m_bounds.insert(v, b);
        }
        return expr_ref(m.mk_const(v, b.m_int ? a.mk_int() : a.mk_real()), m);
    }

};

void parse_lp(opt::context& opt, std::istream& is, unsigned_vector& h) {
    opt_stream_buffer _is(is);
    lp_parse lp(opt, _is, h);
    lp.parse();
}

