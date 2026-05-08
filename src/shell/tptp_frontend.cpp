#include <cctype>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <memory>
#include <vector>

#include <api/c++/z3++.h>
#include "shell/tptp_frontend.h"
#include "util/error_codes.h"

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
    const char* what() const noexcept override { return m_msg.c_str(); }
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
    std::vector<z3::sort> domain;
    z3::sort range;
    parsed_type(z3::sort const& s): range(s) {}
    parsed_type(std::vector<z3::sort> const& d, z3::sort const& r): domain(d), range(r) {}
};

class tptp_parser {
    z3::context& m_ctx;
    z3::solver& m_solver;
    z3::sort m_univ;
    bool m_has_conjecture = false;
    std::unordered_map<std::string, z3::sort> m_sorts;
    std::unordered_map<std::string, z3::func_decl> m_decls;
    std::unordered_map<std::string, std::pair<std::vector<z3::sort>, z3::sort>> m_typed_decls;
    std::vector<std::unordered_map<std::string, z3::expr>> m_bound;
    std::unordered_set<std::string> m_seen_files;

    std::string m_input;
    std::unique_ptr<lexer> m_lex;
    token m_curr;
    std::vector<std::string> m_file_stack;

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

    z3::sort get_sort(std::string const& n) {
        if (n == "$i") return m_univ;
        if (n == "$o") return m_ctx.bool_sort();
        if (n == "$int") return m_ctx.int_sort();
        if (n == "$real") return m_ctx.real_sort();
        auto it = m_sorts.find(n);
        if (it != m_sorts.end()) return it->second;
        z3::sort s = m_ctx.uninterpreted_sort(n.c_str());
        m_sorts.emplace(n, s);
        return s;
    }

    bool is_ttype(z3::sort const& s) const {
        return std::string(Z3_get_symbol_string(m_ctx, Z3_get_sort_name(m_ctx, s))) == "$tType";
    }

    static std::string mk_decl_key(std::string const& name, unsigned arity, char tag) {
        return std::to_string(name.size()) + ":" + name + "\x1f" + std::to_string(arity) + "\x1f" + tag;
    }

    static std::string mk_typed_key(std::string const& name, unsigned arity) {
        return mk_decl_key(name, arity, 't');
    }

    z3::func_decl mk_decl(std::string const& name, unsigned arity, bool pred) {
        auto itt = m_typed_decls.find(mk_typed_key(name, arity));
        if (itt != m_typed_decls.end()) {
            std::string typed_decl_key = mk_decl_key(name, arity, 'd');
            auto itd = m_decls.find(typed_decl_key);
            if (itd != m_decls.end()) return itd->second;
            auto const& sig = itt->second;
            z3::sort_vector dom(m_ctx);
            for (z3::sort const& s : sig.first) dom.push_back(s);
            z3::func_decl f = m_ctx.function(name.c_str(), dom, sig.second);
            m_decls.emplace(typed_decl_key, f);
            return f;
        }

        std::string key = mk_decl_key(name, arity, pred ? 'p' : 'f');
        auto itd = m_decls.find(key);
        if (itd != m_decls.end()) return itd->second;

        std::vector<z3::sort> dom(arity, m_univ);
        if (pred) {
            z3::func_decl f = m_ctx.function(name.c_str(), arity, dom.data(), m_ctx.bool_sort());
            m_decls.emplace(key, f);
            return f;
        }
        z3::func_decl f = m_ctx.function(name.c_str(), arity, dom.data(), m_univ);
        m_decls.emplace(key, f);
        return f;
    }

    bool find_bound(std::string const& n, z3::expr& e) const {
        for (auto it = m_bound.rbegin(); it != m_bound.rend(); ++it) {
            auto jt = it->find(n);
            if (jt != it->end()) {
                e = jt->second;
                return true;
            }
        }
        return false;
    }

    z3::expr mk_quantifier(bool is_forall, z3::expr_vector const& bound, z3::expr const& body) {
        if (bound.empty()) return body;
        std::vector<Z3_app> vars(bound.size());
        for (unsigned i = 0; i < bound.size(); ++i) vars[i] = (Z3_app)(Z3_ast)bound[i];
        Z3_ast q = Z3_mk_quantifier_const(m_ctx, is_forall, 0, bound.size(), vars.data(), 0, nullptr, body);
        return z3::expr(m_ctx, q);
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

    std::vector<z3::sort> parse_type_product() {
        parsed_type first = parse_type_atom();
        if (!first.domain.empty())
            throw parse_error("higher-order type in product is unsupported");
        std::vector<z3::sort> args;
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
        std::vector<z3::sort> prod = parse_type_product();
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

    z3::expr parse_term();

    z3::expr parse_term_primary() {
        if (accept(token_kind::lparen)) {
            z3::expr e = parse_term();
            expect(token_kind::rparen, "')'");
            return e;
        }
        std::string n = parse_name();
        if (n == "$true") return m_ctx.bool_val(true);
        if (n == "$false") return m_ctx.bool_val(false);

        z3::expr b(m_ctx);
        if (is_var_name(n) && find_bound(n, b))
            return b;

        std::vector<z3::expr> args;
        if (accept(token_kind::lparen)) {
            if (!accept(token_kind::rparen)) {
                do { args.push_back(parse_term()); } while (accept(token_kind::comma));
                expect(token_kind::rparen, "')'");
            }
        }
        z3::func_decl f = mk_decl(n, static_cast<unsigned>(args.size()), false);
        if (args.empty()) return f();
        std::vector<z3::expr> tmp(args.begin(), args.end());
        return f(static_cast<unsigned>(tmp.size()), tmp.data());
    }

    z3::expr parse_formula();

    z3::expr parse_atomic_formula() {
        if (accept(token_kind::lparen)) {
            z3::expr e = parse_formula();
            expect(token_kind::rparen, "')'");
            return e;
        }

        std::string n = parse_name();
        if (n == "$true") return m_ctx.bool_val(true);
        if (n == "$false") return m_ctx.bool_val(false);

        std::vector<z3::expr> args;
        if (accept(token_kind::lparen)) {
            if (!accept(token_kind::rparen)) {
                do { args.push_back(parse_term()); } while (accept(token_kind::comma));
                expect(token_kind::rparen, "')'");
            }
        }

        z3::expr lhs(m_ctx);
        bool has_lhs = false;
        if (args.empty()) {
            z3::expr b(m_ctx);
            if (is_var_name(n) && find_bound(n, b)) {
                lhs = b;
                has_lhs = true;
            }
        }
        if (is(token_kind::equal_tok) || is(token_kind::neq_tok)) {
            if (!has_lhs) {
                z3::func_decl f = mk_decl(n, static_cast<unsigned>(args.size()), false);
                lhs = args.empty() ? f() : f(static_cast<unsigned>(args.size()), args.data());
            }
            bool neq = accept(token_kind::neq_tok);
            if (!neq) expect(token_kind::equal_tok, "'='");
            z3::expr rhs = parse_term();
            return neq ? !(lhs == rhs) : (lhs == rhs);
        }

        if (has_lhs) {
            if (lhs.is_bool()) return lhs;
            throw parse_error("non-boolean variable used as formula");
        }

        auto typed = m_typed_decls.find(mk_typed_key(n, static_cast<unsigned>(args.size())));
        if (typed != m_typed_decls.end()) {
            z3::func_decl f = mk_decl(n, static_cast<unsigned>(args.size()), false);
            z3::expr e = args.empty() ? f() : f(static_cast<unsigned>(args.size()), args.data());
            if (!e.is_bool())
                throw parse_error("typed non-boolean term used as formula");
            return e;
        }

        z3::func_decl pred = mk_decl(n, static_cast<unsigned>(args.size()), true);
        if (args.empty()) return pred();
        return pred(static_cast<unsigned>(args.size()), args.data());
    }

    z3::expr parse_unary_formula() {
        if (accept(token_kind::not_tok)) return !parse_unary_formula();
        if (is(token_kind::forall_tok) || is(token_kind::exists_tok)) {
            bool is_forall = is(token_kind::forall_tok);
            next();
            expect(token_kind::lbrack, "'['");

            z3::expr_vector vars(m_ctx);
            std::unordered_map<std::string, z3::expr> scope;
            if (!accept(token_kind::rbrack)) {
                do {
                    std::string v = parse_name();
                    z3::sort s = m_univ;
                    if (accept(token_kind::colon)) {
                        parsed_type t = parse_type_expr();
                        if (!t.domain.empty())
                            throw parse_error("higher-order variable type is unsupported");
                        s = t.range;
                    }
                    z3::expr c = m_ctx.constant(v.c_str(), s);
                    vars.push_back(c);
                    scope.emplace(v, c);
                } while (accept(token_kind::comma));
                expect(token_kind::rbrack, "']'");
            }
            expect(token_kind::colon, "':'");
            m_bound.push_back(scope);
            z3::expr body = parse_formula();
            m_bound.pop_back();
            return mk_quantifier(is_forall, vars, body);
        }
        return parse_atomic_formula();
    }

    z3::expr parse_and_formula() {
        z3::expr e = parse_unary_formula();
        while (is(token_kind::and_tok) || is(token_kind::nand_tok)) {
            bool is_nand = accept(token_kind::nand_tok);
            if (!is_nand) expect(token_kind::and_tok, "'&'");
            z3::expr rhs = parse_unary_formula();
            e = is_nand ? !(e && rhs) : (e && rhs);
        }
        return e;
    }

    z3::expr parse_or_formula() {
        z3::expr e = parse_and_formula();
        while (is(token_kind::or_tok) || is(token_kind::nor_tok)) {
            bool is_nor = accept(token_kind::nor_tok);
            if (!is_nor) expect(token_kind::or_tok, "'|'");
            z3::expr rhs = parse_and_formula();
            e = is_nor ? !(e || rhs) : (e || rhs);
        }
        return e;
    }

    z3::expr parse_implies_formula() {
        z3::expr e = parse_or_formula();
        if (accept(token_kind::implies_tok)) {
            z3::expr rhs = parse_implies_formula();
            return implies(e, rhs);
        }
        if (accept(token_kind::implied_tok)) {
            z3::expr rhs = parse_implies_formula();
            return implies(rhs, e);
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
            m_sorts.insert_or_assign(name, m_ctx.uninterpreted_sort(name.c_str()));
            return;
        }
        m_typed_decls.insert_or_assign(mk_typed_key(name, static_cast<unsigned>(t.domain.size())), std::make_pair(t.domain, t.range));
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

    void parse_annotated(std::string const& kind) {
        expect(token_kind::lparen, "'('");
        parse_name();
        expect(token_kind::comma, "','");
        std::string role = to_lower(parse_name());
        expect(token_kind::comma, "','");

        if (role == "type") {
            parse_type_decl_formula();
        }
        else {
            z3::expr f = parse_formula();
            if (role == "conjecture") {
                m_has_conjecture = true;
                f = !f;
            }
            m_solver.add(f);
        }

        if (accept(token_kind::comma)) {
            skip_annotations_until_rparen();
        }
        expect(token_kind::rparen, "')'");
        expect(token_kind::dot, "'.'");

        (void)kind;
    }

    void parse_toplevel(std::string const& current_file) {
        while (!is(token_kind::eof_tok)) {
            std::string kw = to_lower(parse_name());
            if (kw == "include") {
                parse_include(current_file);
            }
            else if (kw == "fof" || kw == "cnf" || kw == "tff" || kw == "thf") {
                parse_annotated(kw);
            }
            else {
                std::ostringstream out;
                out << "unsupported TPTP unit '" << kw << "' at " << loc();
                throw parse_error(out.str());
            }
        }
    }

public:
    tptp_parser(z3::context& ctx, z3::solver& solver):
        m_ctx(ctx),
        m_solver(solver),
        m_univ(ctx.uninterpreted_sort("U")) {
        m_sorts.emplace("$tType", ctx.uninterpreted_sort("$tType"));
        m_sorts.emplace("$i", m_univ);
        m_sorts.emplace("$o", m_ctx.bool_sort());
        m_sorts.emplace("$int", m_ctx.int_sort());
        m_sorts.emplace("$real", m_ctx.real_sort());
    }

    void parse_file(std::string const& filename) {
        if (!m_seen_files.insert(filename).second) return;
        std::ifstream in(filename);
        if (in.fail()) {
            std::ostringstream out;
            out << "failed to open file '" << filename << "'";
            throw parse_error(out.str());
        }
        std::ostringstream buf;
        buf << in.rdbuf();
        m_input = buf.str();
        m_lex = std::make_unique<lexer>(m_input);
        next();
        m_file_stack.push_back(filename);
        parse_toplevel(filename);
        m_file_stack.pop_back();
    }

    void parse_stream(std::istream& in) {
        std::ostringstream buf;
        buf << in.rdbuf();
        m_input = buf.str();
        m_lex = std::make_unique<lexer>(m_input);
        next();
        parse_toplevel(".");
    }

    bool has_conjecture() const { return m_has_conjecture; }
};

z3::expr tptp_parser::parse_term() {
    z3::expr e = parse_term_primary();
    while (accept(token_kind::at_tok)) {
        z3::expr arg = parse_term_primary();
        if (!e.is_app() || e.decl().decl_kind() != Z3_OP_UNINTERPRETED)
            throw parse_error("application operator (@) requires uninterpreted function on left-hand side");
        z3::func_decl f = e.decl();
        std::vector<z3::expr> args;
        for (unsigned i = 0; i < e.num_args(); ++i) args.push_back(e.arg(i));
        args.push_back(arg);
        e = f(static_cast<unsigned>(args.size()), args.data());
    }
    return e;
}

z3::expr tptp_parser::parse_formula() {
    z3::expr e = parse_implies_formula();
    while (is(token_kind::iff_tok) || is(token_kind::xor_tok)) {
        bool is_xor = accept(token_kind::xor_tok);
        if (!is_xor) expect(token_kind::iff_tok, "'<=>'");
        z3::expr rhs = parse_implies_formula();
        e = is_xor ? !(e == rhs) : (e == rhs);
    }
    return e;
}

}

unsigned read_tptp(char const* file_name) {
    try {
        z3::context ctx;
        z3::solver solver(ctx);
        tptp_parser p(ctx, solver);
        if (file_name) p.parse_file(file_name);
        else p.parse_stream(std::cin);

        z3::check_result r = solver.check();
        if (r == z3::unsat) {
            if (p.has_conjecture()) std::cout << "% SZS status Theorem\n";
            else std::cout << "% SZS status Unsatisfiable\n";
        }
        else if (r == z3::sat) {
            if (p.has_conjecture()) std::cout << "% SZS status CounterSatisfiable\n";
            else std::cout << "% SZS status Satisfiable\n";
            if (g_display_model) std::cout << solver.get_model() << "\n";
        }
        else {
            std::cout << "% SZS status GaveUp\n";
            std::string reason = solver.reason_unknown();
            if (!reason.empty()) std::cout << "% SZS reason " << reason << "\n";
        }
        if (g_display_statistics) std::cout << solver.statistics() << "\n";
        return 0;
    }
    catch (parse_error const& ex) {
        std::cerr << "TPTP parse error: " << ex.what() << "\n";
        return ERR_PARSER;
    }
    catch (z3::exception const& ex) {
        std::cerr << "TPTP frontend error: " << ex.msg() << "\n";
        return ERR_INTERNAL_FATAL;
    }
}
