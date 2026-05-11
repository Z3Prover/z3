#include <cctype>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <memory>
#include <sstream>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "ast/arith_decl_plugin.h"
#include "ast/expr_abstract.h"
#include "ast/ast_util.h"
#include "cmd_context/cmd_context.h"
#include "cmd_context/tptp_frontend.h"
#include "smt/smt_solver.h"
#include "util/error_codes.h"
#include "util/z3_exception.h"

extern bool g_display_statistics;
extern bool g_display_model;

namespace {

enum class token_kind {
    eof_tok,
    id,
    str,
    lparen,
    rparen,
    lbrack,
    rbrack,
    comma,
    dot,
    colon,
    and_tok,
    or_tok,
    not_tok,
    forall_tok,
    exists_tok,
    equal_tok,
    neq_tok,
    iff_tok,
    implies_tok,
    implied_tok,
    xor_tok,
    nor_tok,
    nand_tok,
    gt_tok,
    star_tok,
    at_tok
};

struct parse_error : public std::exception {
    std::string m_msg;
    parse_error(std::string const& msg): m_msg(msg) {}
    char const* what() const noexcept override { return m_msg.c_str(); }
};

class scoped_regular_stream {
    cmd_context& m_ctx;
    std::string m_prev;
public:
    scoped_regular_stream(cmd_context& ctx, std::ostream& out): m_ctx(ctx), m_prev(ctx.get_regular_stream_name()) { m_ctx.set_regular_stream(out); }
    ~scoped_regular_stream() { m_ctx.set_regular_stream(m_prev.c_str()); }
};

struct token {
    token_kind kind = token_kind::eof_tok;
    std::string text;
    unsigned line = 1;
    unsigned col = 1;
};

class lexer {
    std::string const& m_input;
    size_t m_pos = 0;
    unsigned m_line = 1;
    unsigned m_col = 1;

    bool eof() const { return m_pos >= m_input.size(); }
    char peek(unsigned k = 0) const { return m_pos + k < m_input.size() ? m_input[m_pos + k] : '\0'; }
    char get() {
        char c = peek();
        if (!eof()) {
            ++m_pos;
            if (c == '\n') {
                ++m_line;
                m_col = 1;
            }
            else {
                ++m_col;
            }
        }
        return c;
    }

    static bool is_symbol_start(char c) {
        return std::isalnum(static_cast<unsigned char>(c)) || c == '$' || c == '_';
    }

    static bool is_id_char(char c) {
        return std::isalnum(static_cast<unsigned char>(c)) || c == '$' || c == '_' || c == '\'' || c == '-';
    }

    void skip_ws_comments() {
        while (!eof()) {
            if (std::isspace(static_cast<unsigned char>(peek()))) {
                get();
                continue;
            }
            if (peek() == '%') {
                while (!eof() && get() != '\n') {}
                continue;
            }
            if (peek() == '/' && peek(1) == '*') {
                get();
                get();
                while (!eof()) {
                    if (peek() == '*' && peek(1) == '/') {
                        get();
                        get();
                        break;
                    }
                    get();
                }
                continue;
            }
            break;
        }
    }

public:
    lexer(std::string const& input): m_input(input) {}

    token next() {
        skip_ws_comments();
        token t;
        t.line = m_line;
        t.col = m_col;
        if (eof()) {
            t.kind = token_kind::eof_tok;
            return t;
        }

        if (peek() == '\'' || peek() == '"') {
            char q = get();
            t.kind = token_kind::str;
            while (!eof()) {
                char c = get();
                if (c == '\\' && !eof()) {
                    t.text.push_back(c);
                    t.text.push_back(get());
                    continue;
                }
                if (c == q) return t;
                t.text.push_back(c);
            }
            throw parse_error("unterminated string literal");
        }

        if (peek() == '<' && peek(1) == '=' && peek(2) == '>') {
            get(); get(); get();
            t.kind = token_kind::iff_tok;
            t.text = "<=>";
            return t;
        }
        if (peek() == '<' && peek(1) == '~' && peek(2) == '>') {
            get(); get(); get();
            t.kind = token_kind::xor_tok;
            t.text = "<~>";
            return t;
        }
        if (peek() == '=' && peek(1) == '>') {
            get(); get();
            t.kind = token_kind::implies_tok;
            t.text = "=>";
            return t;
        }
        if (peek() == '<' && peek(1) == '=') {
            get(); get();
            t.kind = token_kind::implied_tok;
            t.text = "<=";
            return t;
        }
        if (peek() == '~' && peek(1) == '|') {
            get(); get();
            t.kind = token_kind::nor_tok;
            t.text = "~|";
            return t;
        }
        if (peek() == '~' && peek(1) == '&') {
            get(); get();
            t.kind = token_kind::nand_tok;
            t.text = "~&";
            return t;
        }
        if (peek() == '!' && peek(1) == '=') {
            get(); get();
            t.kind = token_kind::neq_tok;
            t.text = "!=";
            return t;
        }

        char c = get();
        switch (c) {
        case '(': t.kind = token_kind::lparen; return t;
        case ')': t.kind = token_kind::rparen; return t;
        case '[': t.kind = token_kind::lbrack; return t;
        case ']': t.kind = token_kind::rbrack; return t;
        case ',': t.kind = token_kind::comma; return t;
        case '.': t.kind = token_kind::dot; return t;
        case ':': t.kind = token_kind::colon; return t;
        case '&': t.kind = token_kind::and_tok; return t;
        case '|': t.kind = token_kind::or_tok; return t;
        case '~': t.kind = token_kind::not_tok; return t;
        case '!': t.kind = token_kind::forall_tok; return t;
        case '?': t.kind = token_kind::exists_tok; return t;
        case '=': t.kind = token_kind::equal_tok; return t;
        case '>': t.kind = token_kind::gt_tok; return t;
        case '*': t.kind = token_kind::star_tok; return t;
        case '@': t.kind = token_kind::at_tok; return t;
        default:
            break;
        }

        if (is_symbol_start(c)) {
            t.kind = token_kind::id;
            t.text.push_back(c);
            while (!eof() && is_id_char(peek()))
                t.text.push_back(get());
            return t;
        }

        std::ostringstream out;
        out << "unexpected character '" << c << "' at " << t.line << ":" << t.col;
        throw parse_error(out.str());
    }
};

struct parsed_type {
    std::vector<sort*> domain;
    sort* range = nullptr;
    parsed_type(sort* s): range(s) {}
    parsed_type(std::vector<sort*> const& d, sort* r): domain(d), range(r) {}
};

class tptp_parser {
    cmd_context& m_cmd;
    ast_manager& m;
    arith_util m_arith;
    sort* m_univ;
    bool m_has_conjecture = false;
    std::unordered_map<std::string, sort*> m_sorts;
    std::unordered_map<std::string, func_decl*> m_decls;
    std::unordered_map<std::string, std::pair<std::vector<sort*>, sort*>> m_typed_decls;
    std::vector<std::unordered_map<std::string, app*>> m_bound;
    std::unordered_set<std::string> m_seen_files;

    std::string m_input;
    std::unique_ptr<lexer> m_lex;
    token m_curr;

    static std::string to_lower(std::string s) {
        for (char& c : s) c = static_cast<char>(std::tolower(static_cast<unsigned char>(c)));
        return s;
    }

    static bool is_var_name(std::string const& s) {
        if (s.empty()) return false;
        unsigned char c = static_cast<unsigned char>(s[0]);
        return std::isupper(c) || s[0] == '_';
    }

    std::string loc() const {
        std::ostringstream out;
        out << m_curr.line << ":" << m_curr.col;
        return out.str();
    }

    void skip_wrapping_lparens() {
        while (accept(token_kind::lparen)) {}
    }

    void skip_wrapping_rparens() {
        while (accept(token_kind::rparen)) {}
    }

    void next() { m_curr = m_lex->next(); }

    bool is(token_kind k) const { return m_curr.kind == k; }

    bool accept(token_kind k) {
        if (is(k)) {
            next();
            return true;
        }
        return false;
    }

    void expect(token_kind k, char const* msg) {
        if (!accept(k)) {
            std::ostringstream out;
            out << "expected " << msg << " at " << loc();
            throw parse_error(out.str());
        }
    }

    std::string parse_name() {
        if (is(token_kind::id) || is(token_kind::str)) {
            std::string r = m_curr.text;
            next();
            return r;
        }
        std::ostringstream out;
        out << "expected identifier at " << loc();
        throw parse_error(out.str());
    }

    sort* get_sort(std::string const& n) {
        if (n == "$i") return m_univ;
        if (n == "$o") return m.mk_bool_sort();
        if (n == "$int") return m_arith.mk_int();
        if (n == "$real") return m_arith.mk_real();
        auto it = m_sorts.find(n);
        if (it != m_sorts.end()) return it->second;
        sort* s = m.mk_uninterpreted_sort(symbol(n));
        m_sorts.emplace(n, s);
        return s;
    }

    static bool is_ttype(sort* s) {
        return s->get_name() == symbol("$tType");
    }

    static std::string mk_decl_key(std::string const& name, unsigned arity, char tag) {
        return std::to_string(name.size()) + ":" + name + "\x1f" + std::to_string(arity) + "\x1f" + tag;
    }

    static std::string mk_typed_key(std::string const& name, unsigned arity) {
        return mk_decl_key(name, arity, 't');
    }

    func_decl* mk_decl(std::string const& name, unsigned arity, bool pred) {
        auto itt = m_typed_decls.find(mk_typed_key(name, arity));
        if (itt != m_typed_decls.end()) {
            std::string typed_decl_key = mk_decl_key(name, arity, 'd');
            auto itd = m_decls.find(typed_decl_key);
            if (itd != m_decls.end()) return itd->second;
            auto const& sig = itt->second;
            func_decl* f = m.mk_func_decl(symbol(name), sig.first.size(), sig.first.data(), sig.second);
            m_decls.emplace(typed_decl_key, f);
            return f;
        }

        std::string key = mk_decl_key(name, arity, pred ? 'p' : 'f');
        auto itd = m_decls.find(key);
        if (itd != m_decls.end()) return itd->second;

        std::vector<sort*> dom(arity, m_univ);
        func_decl* f = m.mk_func_decl(symbol(name), arity, dom.data(), pred ? m.mk_bool_sort() : m_univ);
        m_decls.emplace(key, f);
        return f;
    }

    bool find_bound(std::string const& n, expr_ref& e) const {
        for (auto it = m_bound.rbegin(); it != m_bound.rend(); ++it) {
            auto jt = it->find(n);
            if (jt != it->end()) {
                e = jt->second;
                return true;
            }
        }
        return false;
    }

    expr_ref mk_quantifier(bool is_forall, ptr_vector<app> const& bound, expr_ref const& body) {
        SASSERT(body);
        if (bound.empty()) return body;
        return is_forall ? ::mk_forall(m, bound.size(), bound.data(), body.get()) : ::mk_exists(m, bound.size(), bound.data(), body.get());
    }

    parsed_type parse_type_atom() {
        if (accept(token_kind::lparen)) {
            parsed_type t = parse_type_expr();
            expect(token_kind::rparen, "')'");
            return t;
        }
        std::string n = parse_name();
        return parsed_type(get_sort(n));
    }

    std::vector<sort*> parse_type_product() {
        parsed_type first = parse_type_atom();
        if (!first.domain.empty())
            throw parse_error("higher-order type in product is unsupported");
        std::vector<sort*> args;
        args.push_back(first.range);
        while (accept(token_kind::star_tok)) {
            parsed_type t = parse_type_atom();
            if (!t.domain.empty())
                throw parse_error("higher-order type in product is unsupported");
            args.push_back(t.range);
        }
        return args;
    }

    parsed_type parse_type_expr() {
        std::vector<sort*> prod = parse_type_product();
        if (accept(token_kind::gt_tok)) {
            parsed_type rhs = parse_type_expr();
            if (!rhs.domain.empty())
                throw parse_error("higher-order result type is unsupported");
            return parsed_type(prod, rhs.range);
        }
        if (prod.size() != 1)
            throw parse_error("type product must be followed by '>'");
        return parsed_type(prod[0]);
    }

    void skip_annotations_until_rparen() {
        int depth = 0;
        while (!is(token_kind::eof_tok)) {
            if (accept(token_kind::lparen) || accept(token_kind::lbrack)) {
                ++depth;
                continue;
            }
            if (is(token_kind::rparen) || is(token_kind::rbrack)) {
                if (depth == 0) return;
                --depth;
                next();
                continue;
            }
            next();
        }
    }

    void skip_balanced(token_kind open_k, token_kind close_k) {
        int depth = 1;
        while (depth > 0 && !is(token_kind::eof_tok)) {
            if (accept(open_k)) ++depth;
            else if (accept(close_k)) --depth;
            else next();
        }
    }

    expr_ref parse_term();

    expr_ref parse_term_primary() {
        if (accept(token_kind::lparen)) {
            expr_ref e = parse_term();
            expect(token_kind::rparen, "')'");
            return e;
        }
        std::string n = parse_name();
        if (n == "$true") return expr_ref(m.mk_true(), m);
        if (n == "$false") return expr_ref(m.mk_false(), m);

        expr_ref b(m);
        if (is_var_name(n) && find_bound(n, b))
            return b;

        expr_ref_vector args(m);
        if (accept(token_kind::lparen)) {
            if (!accept(token_kind::rparen)) {
                do { args.push_back(parse_term()); } while (accept(token_kind::comma));
                expect(token_kind::rparen, "')'");
            }
        }

        func_decl* f = mk_decl(n, args.size(), false);
        return expr_ref(args.empty() ? m.mk_const(f) : m.mk_app(f, args.size(), args.data()), m);
    }

    expr_ref parse_formula();

    expr_ref parse_atomic_formula() {
        if (accept(token_kind::lparen)) {
            expr_ref e = parse_formula();
            expect(token_kind::rparen, "')'");
            return e;
        }

        std::string n = parse_name();
        if (n == "$true") return expr_ref(m.mk_true(), m);
        if (n == "$false") return expr_ref(m.mk_false(), m);

        expr_ref_vector args(m);
        if (accept(token_kind::lparen)) {
            if (!accept(token_kind::rparen)) {
                do { args.push_back(parse_term()); } while (accept(token_kind::comma));
                expect(token_kind::rparen, "')'");
            }
        }

        expr_ref lhs(m);
        bool has_lhs = false;
        if (args.empty()) {
            expr_ref b(m);
            if (is_var_name(n) && find_bound(n, b)) {
                lhs = b;
                has_lhs = true;
            }
        }

        if (is(token_kind::equal_tok) || is(token_kind::neq_tok)) {
            if (!has_lhs) {
                func_decl* f = mk_decl(n, args.size(), false);
                lhs = args.empty() ? m.mk_const(f) : m.mk_app(f, args.size(), args.data());
            }
            bool neq = accept(token_kind::neq_tok);
            if (!neq) expect(token_kind::equal_tok, "'='");
            expr_ref rhs = parse_term();
            expr_ref eq(m.mk_eq(lhs, rhs), m);
            return neq ? expr_ref(m.mk_not(eq), m) : eq;
        }

        if (has_lhs) {
            if (m.is_bool(lhs)) return lhs;
            throw parse_error("non-boolean variable used as formula");
        }

        auto typed = m_typed_decls.find(mk_typed_key(n, args.size()));
        if (typed != m_typed_decls.end()) {
            func_decl* f = mk_decl(n, args.size(), false);
            expr_ref e(args.empty() ? m.mk_const(f) : m.mk_app(f, args.size(), args.data()), m);
            if (!m.is_bool(e))
                throw parse_error("typed non-boolean term used as formula");
            return e;
        }

        func_decl* pred = mk_decl(n, args.size(), true);
        return expr_ref(args.empty() ? m.mk_const(pred) : m.mk_app(pred, args.size(), args.data()), m);
    }

    expr_ref parse_unary_formula() {
        if (accept(token_kind::not_tok)) {
            expr_ref e = parse_unary_formula();
            return expr_ref(m.mk_not(e), m);
        }

        if (is(token_kind::forall_tok) || is(token_kind::exists_tok)) {
            bool is_forall = is(token_kind::forall_tok);
            next();
            expect(token_kind::lbrack, "'['");

            ptr_vector<app> vars;
            std::unordered_map<std::string, app*> scope;
            if (!accept(token_kind::rbrack)) {
                do {
                    std::string v = parse_name();
                    sort* s = m_univ;
                    if (accept(token_kind::colon)) {
                        parsed_type t = parse_type_expr();
                        if (!t.domain.empty())
                            throw parse_error("higher-order variable type is unsupported");
                        s = t.range;
                    }
                    app* c = m.mk_const(symbol(v), s);
                    vars.push_back(c);
                    scope.emplace(v, c);
                }
                while (accept(token_kind::comma));
                expect(token_kind::rbrack, "']'");
            }
            expect(token_kind::colon, "':'");
            m_bound.push_back(scope);
            expr_ref body = parse_formula();
            m_bound.pop_back();
            return mk_quantifier(is_forall, vars, body);
        }

        return parse_atomic_formula();
    }

    expr_ref parse_and_formula() {
        expr_ref e = parse_unary_formula();
        while (is(token_kind::and_tok) || is(token_kind::nand_tok)) {
            bool is_nand = accept(token_kind::nand_tok);
            if (!is_nand) expect(token_kind::and_tok, "'&'");
            expr_ref rhs = parse_unary_formula();
            expr_ref conj(::mk_and(m, e, rhs), m);
            e = is_nand ? expr_ref(m.mk_not(conj), m) : conj;
        }
        return e;
    }

    expr_ref parse_or_formula() {
        expr_ref e = parse_and_formula();
        while (is(token_kind::or_tok) || is(token_kind::nor_tok)) {
            bool is_nor = accept(token_kind::nor_tok);
            if (!is_nor) expect(token_kind::or_tok, "'|'");
            expr_ref rhs = parse_and_formula();
            expr_ref disj(::mk_or(m, e, rhs), m);
            e = is_nor ? expr_ref(m.mk_not(disj), m) : disj;
        }
        return e;
    }

    expr_ref parse_implies_formula() {
        expr_ref e = parse_or_formula();
        if (accept(token_kind::implies_tok)) {
            expr_ref rhs = parse_implies_formula();
            return expr_ref(m.mk_implies(e, rhs), m);
        }
        if (accept(token_kind::implied_tok)) {
            expr_ref rhs = parse_implies_formula();
            return expr_ref(m.mk_implies(rhs, e), m);
        }
        return e;
    }

    void parse_type_decl_formula() {
        skip_wrapping_lparens();
        std::string name = parse_name();
        expect(token_kind::colon, "':'");
        parsed_type t = parse_type_expr();
        skip_wrapping_rparens();

        if (t.domain.empty() && is_ttype(t.range)) {
            m_sorts.insert_or_assign(name, m.mk_uninterpreted_sort(symbol(name)));
            return;
        }

        m_typed_decls.insert_or_assign(mk_typed_key(name, t.domain.size()), std::make_pair(t.domain, t.range));
    }

    static bool file_exists(std::string const& f) {
        std::ifstream in(f);
        return !in.fail();
    }

    static bool is_absolute_path(std::string const& name) {
        return !name.empty() &&
            (name[0] == '/' ||
             (name.size() >= 2 && std::isalpha(static_cast<unsigned char>(name[0])) && name[1] == ':'));
    }

    std::string dirname(std::string const& f) const {
        size_t idx = f.find_last_of("/\\");
        return idx == std::string::npos ? "." : f.substr(0, idx);
    }

    std::string resolve_include(std::string const& curr_file, std::string const& name) const {
        if (is_absolute_path(name))
            return name;
        std::string local = dirname(curr_file) + "/" + name;
        if (file_exists(local)) return local;
        char const* root = std::getenv("TPTP");
        if (root) {
            std::string env = std::string(root) + "/" + name;
            if (file_exists(env)) return env;
        }
        return local;
    }

    void parse_include(std::string const& curr_file) {
        expect(token_kind::lparen, "'('");
        std::string file = parse_name();
        if (accept(token_kind::comma)) {
            if (accept(token_kind::lbrack)) {
                skip_balanced(token_kind::lbrack, token_kind::rbrack);
            }
            else {
                skip_annotations_until_rparen();
            }
        }
        expect(token_kind::rparen, "')'");
        expect(token_kind::dot, "'.'");
        parse_file(resolve_include(curr_file, file));
    }

    void parse_annotated() {
        expect(token_kind::lparen, "'('");
        parse_name();
        expect(token_kind::comma, "','");
        std::string role = to_lower(parse_name());
        expect(token_kind::comma, "','");

        if (role == "type") {
            parse_type_decl_formula();
        }
        else {
            expr_ref f = parse_formula();
            if (role == "conjecture") {
                m_has_conjecture = true;
                f = m.mk_not(f);
            }
            m_cmd.assert_expr(f);
        }

        if (accept(token_kind::comma)) {
            skip_annotations_until_rparen();
        }
        expect(token_kind::rparen, "')'");
        expect(token_kind::dot, "'.'");
    }

    void parse_toplevel(std::string const& current_file) {
        while (!is(token_kind::eof_tok)) {
            std::string kw = to_lower(parse_name());
            if (kw == "include") {
                parse_include(current_file);
            }
            else if (kw == "fof" || kw == "cnf" || kw == "tff" || kw == "thf") {
                parse_annotated();
            }
            else {
                std::ostringstream out;
                out << "unsupported TPTP unit '" << kw << "' at " << loc();
                throw parse_error(out.str());
            }
        }
    }

public:
    tptp_parser(cmd_context& cmd):
        m_cmd(cmd),
        m(m_cmd.m()),
        m_arith(m),
        m_univ(m.mk_uninterpreted_sort(symbol("U"))) {
        m_sorts.emplace("$tType", m.mk_uninterpreted_sort(symbol("$tType")));
        m_sorts.emplace("$i", m_univ);
        m_sorts.emplace("$o", m.mk_bool_sort());
        m_sorts.emplace("$int", m_arith.mk_int());
        m_sorts.emplace("$real", m_arith.mk_real());
    }

    void parse_stream(std::istream& in, std::string const& current_file) {
        std::ostringstream buf;
        buf << in.rdbuf();
        m_input = buf.str();
        m_lex = std::make_unique<lexer>(m_input);
        next();
        parse_toplevel(current_file);
    }

    void parse_file(std::string const& filename) {
        if (!m_seen_files.insert(filename).second) return;
        std::ifstream in(filename);
        if (in.fail()) {
            std::ostringstream out;
            out << "failed to open file '" << filename << "'";
            throw parse_error(out.str());
        }
        parse_stream(in, filename);
    }

    void parse_stream(std::istream& in) {
        parse_stream(in, ".");
    }

    bool has_conjecture() const { return m_has_conjecture; }
};

expr_ref tptp_parser::parse_term() {
    expr_ref e = parse_term_primary();
    while (accept(token_kind::at_tok)) {
        expr_ref arg = parse_term_primary();
        if (!is_app(e))
            throw parse_error("application operator (@) requires uninterpreted function on left-hand side");
        app* a = to_app(e);
        func_decl* d = a->get_decl();
        if (d->get_family_id() != null_family_id)
            throw parse_error("application operator (@) requires uninterpreted function on left-hand side");
        expr_ref_vector args(m);
        for (unsigned i = 0; i < a->get_num_args(); ++i) args.push_back(a->get_arg(i));
        args.push_back(arg);
        e = expr_ref(m.mk_app(d, args.size(), args.data()), m);
    }
    return e;
}

expr_ref tptp_parser::parse_formula() {
    expr_ref e = parse_implies_formula();
    while (is(token_kind::iff_tok) || is(token_kind::xor_tok)) {
        bool is_xor = accept(token_kind::xor_tok);
        if (!is_xor) expect(token_kind::iff_tok, "'<=>'");
        expr_ref rhs = parse_implies_formula();
        expr_ref iff(m.mk_iff(e, rhs), m);
        e = is_xor ? expr_ref(m.mk_not(iff), m) : iff;
    }
    return e;
}

}

static unsigned read_tptp_stream(std::istream& in, char const* current_file) {
    try {
        cmd_context ctx;
        ctx.set_solver_factory(mk_smt_strategic_solver_factory());

        tptp_parser p(ctx);
        p.parse_stream(in, current_file ? current_file : ".");

        // Suppress default check-sat output; TPTP frontend reports SZS status explicitly.
        std::ostringstream sink;
        scoped_regular_stream scoped_stream(ctx, sink);
        ctx.check_sat(0, nullptr);
        switch (ctx.cs_state()) {
        case cmd_context::css_unsat:
            if (p.has_conjecture()) std::cout << "% SZS status Theorem\n";
            else std::cout << "% SZS status Unsatisfiable\n";
            break;
        case cmd_context::css_sat:
            if (p.has_conjecture()) std::cout << "% SZS status CounterSatisfiable\n";
            else std::cout << "% SZS status Satisfiable\n";
            if (g_display_model) {
                model_ref mdl;
                if (ctx.is_model_available(mdl))
                    ctx.display_model(mdl);
            }
            break;
        case cmd_context::css_unknown:
            std::cout << "% SZS status GaveUp\n";
            {
                std::string reason = ctx.reason_unknown();
                if (!reason.empty()) std::cout << "% SZS reason " << reason << "\n";
            }
            break;
        default:
            break;
        }

        if (g_display_statistics) {
            ctx.set_regular_stream("stdout");
            ctx.display_statistics();
        }
        return 0;
    }
    catch (parse_error const& ex) {
        std::cerr << "TPTP parse error: " << ex.what() << "\n";
        return ERR_PARSER;
    }
    catch (z3_exception& ex) {
        std::cerr << "TPTP frontend error: " << ex.what() << "\n";
        return ERR_INTERNAL_FATAL;
    }
}

unsigned read_tptp(char const* file_name) {
    if (!file_name)
        return read_tptp_stream(std::cin, ".");
    std::ifstream in(file_name);
    if (in.fail()) {
        std::cerr << "TPTP parse error: failed to open file '" << file_name << "'\n";
        return ERR_PARSER;
    }
    return read_tptp_stream(in, file_name);
}

unsigned read_tptp_string(char const* input) {
    std::istringstream in(input ? input : "");
    return read_tptp_stream(in, "<string>");
}
