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
#include "solver/solver.h"
#include "util/error_codes.h"
#include "util/rational.h"
#include "util/timeout.h"
#include "util/z3_exception.h"

bool g_display_statistics = false;
bool g_display_model = false;

static void on_timeout() {
    std::cout << "% SZS status Timeout\n";
    std::cout.flush();
    _Exit(0);
}

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
    slash_tok,
    minus_tok,
    at_tok,
    lambda_tok
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
        case '/': t.kind = token_kind::slash_tok; return t;
        case '-': t.kind = token_kind::minus_tok; return t;
        case '@': t.kind = token_kind::at_tok; return t;
        case '^': t.kind = token_kind::lambda_tok; return t;
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
    bool m_last_name_quoted = false;
    unsigned m_lambda_counter = 0;
    std::unordered_map<std::string, sort*> m_sorts;
    sort_ref_vector m_pinned_sorts;       // prevents cached sorts from being freed
    std::unordered_map<sort*, std::pair<std::vector<sort*>, sort*>> m_ho_sort_info; // ho_sort → (domain, range)
    std::unordered_map<std::string, func_decl*> m_decls;
    func_decl_ref_vector m_pinned_decls;  // prevents cached func_decls from being freed
    std::unordered_map<std::string, std::pair<std::vector<sort*>, sort*>> m_typed_decls;
    std::vector<std::unordered_map<std::string, app*>> m_bound;
    struct implicit_var_scope {
        std::unordered_map<std::string, app*> vars;
        ptr_vector<app> order;
    };
    implicit_var_scope* m_implicit_scope = nullptr;
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
            m_last_name_quoted = is(token_kind::str);
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
        if (n == "$rat" || n == "$real") return m_arith.mk_real();
        auto it = m_sorts.find(n);
        if (it != m_sorts.end()) return it->second;
        sort* s = m.mk_uninterpreted_sort(symbol(n));
        m_sorts.emplace(n, s);
        m_pinned_sorts.push_back(s);
        return s;
    }

    // For higher-order types like ($i > $o), create an uninterpreted sort
    // that represents the function type. This is a first-order approximation.
    sort* get_ho_sort(std::vector<sort*> const& domain, sort* range) {
        std::ostringstream oss;
        oss << "(";
        for (size_t i = 0; i < domain.size(); ++i) {
            if (i > 0) oss << " * ";
            oss << domain[i]->get_name();
        }
        oss << " > " << range->get_name() << ")";
        std::string key = oss.str();
        auto it = m_sorts.find(key);
        if (it != m_sorts.end()) return it->second;
        sort* s = m.mk_uninterpreted_sort(symbol(key));
        m_sorts.emplace(key, s);
        m_pinned_sorts.push_back(s);
        m_ho_sort_info.emplace(s, std::make_pair(domain, range));
        return s;
    }

    static bool is_ttype(sort* s) {
        return s->get_name() == symbol("$tType");
    }

    static bool is_nonempty_digit_string(std::string const& s) {
        if (s.empty()) return false;
        for (char c : s) {
            if (!std::isdigit(static_cast<unsigned char>(c)))
                return false;
        }
        return true;
    }

    expr_ref parse_numeral_from_name(std::string const& n) {
        SASSERT(is_nonempty_digit_string(n));
        rational num(n.c_str());
        if (accept(token_kind::dot)) {
            std::string frac = parse_name();
            if (!is_nonempty_digit_string(frac))
                throw parse_error("fractional part of decimal literal must be a sequence of digits");
            rational den(1);
            for (unsigned i = 0; i < frac.size(); ++i) {
                den *= rational(10);
            }
            rational frac_num(frac.c_str());
            return expr_ref(m_arith.mk_numeral(num + frac_num / den, false), m);
        }
        if (accept(token_kind::slash_tok)) {
            std::string d = parse_name();
            if (!is_nonempty_digit_string(d))
                throw parse_error("denominator of rational literal must be a sequence of digits");
            rational den(d.c_str());
            if (den.is_zero())
                throw parse_error("denominator of rational literal cannot be zero");
            return expr_ref(m_arith.mk_numeral(num / den, false), m);
        }
        return expr_ref(m_arith.mk_numeral(num, true), m);
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
            m_pinned_decls.push_back(f);
            m_decls.emplace(typed_decl_key, f);
            return f;
        }

        std::string key = mk_decl_key(name, arity, pred ? 'p' : 'f');
        auto itd = m_decls.find(key);
        if (itd != m_decls.end()) return itd->second;

        std::vector<sort*> dom(arity, m_univ);
        func_decl* f = m.mk_func_decl(symbol(name), arity, dom.data(), pred ? m.mk_bool_sort() : m_univ);
        m_pinned_decls.push_back(f);
        m_decls.emplace(key, f);
        return f;
    }

    // When a symbol is used with 0 args but has a typed decl with arity > 0,
    // create a 0-arity constant with the function type sort (for THF function-as-value).
    func_decl* mk_decl_or_ho_const(std::string const& name, unsigned arity, bool pred) {
        if (arity == 0) {
            // Check if there's a typed decl at any arity > 0 for this name
            for (unsigned try_arity = 1; try_arity <= 10; ++try_arity) {
                auto itt = m_typed_decls.find(mk_typed_key(name, try_arity));
                if (itt != m_typed_decls.end()) {
                    auto const& sig = itt->second;
                    sort* ho = get_ho_sort(sig.first, sig.second);
                    std::string key = mk_decl_key(name, 0, 'h');
                    auto itd = m_decls.find(key);
                    if (itd != m_decls.end()) return itd->second;
                    func_decl* f = m.mk_func_decl(symbol(name), 0, static_cast<sort**>(nullptr), ho);
                    m_pinned_decls.push_back(f);
                    m_decls.emplace(key, f);
                    return f;
                }
            }
        }
        return mk_decl(name, arity, pred);
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

    bool is_bound_var(app* a) const {
        std::string name = a->get_decl()->get_name().str();
        for (auto it = m_bound.rbegin(); it != m_bound.rend(); ++it) {
            auto jt = it->find(name);
            if (jt != it->end() && jt->second == a)
                return true;
        }
        return false;
    }

    bool should_create_implicit_var(std::string const& n) const {
        return is_var_name(n) && m_implicit_scope;
    }

    app* get_or_create_implicit_var(std::string const& n) {
        if (!m_implicit_scope)
            throw parse_error("unexpected parser state: missing implicit variable scope");
        auto it = m_implicit_scope->vars.find(n);
        if (it != m_implicit_scope->vars.end()) return it->second;
        app* c = m.mk_const(symbol(n), m_univ);
        m_implicit_scope->vars.emplace(n, c);
        m_implicit_scope->order.push_back(c);
        return c;
    }

    class scoped_implicit_vars {
        tptp_parser& m_p;
        implicit_var_scope* m_prev_scope;
    public:
        scoped_implicit_vars(tptp_parser& p, implicit_var_scope& scope):
            m_p(p),
            m_prev_scope(p.m_implicit_scope) {
            m_p.m_implicit_scope = &scope;
        }
        scoped_implicit_vars(scoped_implicit_vars const&) = delete;
        scoped_implicit_vars& operator=(scoped_implicit_vars const&) = delete;
        scoped_implicit_vars(scoped_implicit_vars&&) = delete;
        scoped_implicit_vars& operator=(scoped_implicit_vars&&) = delete;
        ~scoped_implicit_vars() {
            m_p.m_implicit_scope = m_prev_scope;
        }
    };

    expr_ref mk_quantifier(bool is_forall, ptr_vector<app> const& bound, expr_ref const& body) {
        SASSERT(body);
        if (bound.empty()) return body;
        return is_forall ? ::mk_forall(m, bound.size(), bound.data(), body.get()) : ::mk_exists(m, bound.size(), bound.data(), body.get());
    }

    parsed_type parse_type_atom() {
        if (accept(token_kind::lparen)) {
            std::vector<sort*> prod = parse_type_product_raw();
            if (accept(token_kind::gt_tok)) {
                // Full function type inside parens: (A * B > C) or (A > B > C)
                parsed_type rhs = parse_type_expr();
                std::vector<sort*> full_domain = prod;
                if (!rhs.domain.empty()) {
                    // Nested higher-order: (A > B > C) → flatten
                    full_domain.insert(full_domain.end(), rhs.domain.begin(), rhs.domain.end());
                }
                expect(token_kind::rparen, "')'");
                // Return as a higher-order sort (uninterpreted)
                sort* ho = get_ho_sort(full_domain, rhs.range);
                return parsed_type(ho);
            }
            expect(token_kind::rparen, "')'");
            if (prod.size() == 1)
                return parsed_type(prod[0]);
            // Parenthesized product: (A * B) — used as domain in outer context
            return parsed_type(prod, nullptr);
        }
        std::string n = parse_name();
        return parsed_type(get_sort(n));
    }

    std::vector<sort*> parse_type_product_raw() {
        parsed_type first = parse_type_atom();
        if (!first.domain.empty() && first.range == nullptr) {
            // Already a parenthesized product from nested parens
            std::vector<sort*> args = first.domain;
            while (accept(token_kind::star_tok)) {
                parsed_type t = parse_type_atom();
                if (!t.domain.empty()) {
                    args.insert(args.end(), t.domain.begin(), t.domain.end());
                } else {
                    args.push_back(t.range);
                }
            }
            return args;
        }
        if (!first.domain.empty()) {
            // Function type as first element of product — use ho_sort
            sort* ho = get_ho_sort(first.domain, first.range);
            std::vector<sort*> args;
            args.push_back(ho);
            while (accept(token_kind::star_tok)) {
                parsed_type t = parse_type_atom();
                if (!t.domain.empty() && t.range != nullptr) {
                    args.push_back(get_ho_sort(t.domain, t.range));
                } else if (!t.domain.empty()) {
                    args.insert(args.end(), t.domain.begin(), t.domain.end());
                } else {
                    args.push_back(t.range);
                }
            }
            return args;
        }
        std::vector<sort*> args;
        args.push_back(first.range);
        while (accept(token_kind::star_tok)) {
            parsed_type t = parse_type_atom();
            if (!t.domain.empty() && t.range != nullptr) {
                args.push_back(get_ho_sort(t.domain, t.range));
            } else if (!t.domain.empty()) {
                args.insert(args.end(), t.domain.begin(), t.domain.end());
            } else {
                args.push_back(t.range);
            }
        }
        return args;
    }

    std::vector<sort*> parse_type_product() {
        return parse_type_product_raw();
    }

    parsed_type parse_type_expr() {
        std::vector<sort*> prod = parse_type_product();
        if (accept(token_kind::gt_tok)) {
            parsed_type rhs = parse_type_expr();
            if (!rhs.domain.empty()) {
                // Higher-order result type: A > (B > C) flattened to (A, B) > C
                prod.insert(prod.end(), rhs.domain.begin(), rhs.domain.end());
                return parsed_type(prod, rhs.range);
            }
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
        if (accept(token_kind::lambda_tok)) {
            return parse_lambda_expr();
        }
        if (accept(token_kind::minus_tok)) {
            expr_ref e = parse_term_primary();
            if (!m_arith.is_int_real(e))
                throw parse_error("unary '-' expects arithmetic term");
            return expr_ref(m_arith.mk_uminus(e), m);
        }
        std::string n = parse_name();
        if (n == "$true") return expr_ref(m.mk_true(), m);
        if (n == "$false") return expr_ref(m.mk_false(), m);

        if (is_nonempty_digit_string(n)) {
            return parse_numeral_from_name(n);
        }

        expr_ref b(m);
        if (!m_last_name_quoted && is_var_name(n) && find_bound(n, b))
            return b;
        if (!m_last_name_quoted && should_create_implicit_var(n))
            return expr_ref(get_or_create_implicit_var(n), m);

        expr_ref_vector args(m);
        if (accept(token_kind::lparen)) {
            if (!accept(token_kind::rparen)) {
                do { args.push_back(parse_term()); } while (accept(token_kind::comma));
                expect(token_kind::rparen, "')'");
            }
        }

        if (n == "$uminus") {
            if (args.size() != 1)
                throw parse_error("arithmetic function '$uminus' expects arity 1");
            expr_ref a(args.get(0), m);
            if (!m_arith.is_int_real(a))
                throw parse_error("arithmetic function '$uminus' expects arithmetic argument");
            return expr_ref(m_arith.mk_uminus(a), m);
        }

        if (n == "$sum" || n == "$difference" || n == "$product") {
            if (args.size() != 2)
                throw parse_error("arithmetic function expects arity 2");
            expr_ref a(args.get(0), m), b(args.get(1), m);
            if (!m_arith.is_int_real(a) || !m_arith.is_int_real(b))
                throw parse_error("arithmetic function expects arithmetic arguments");
            bool use_real = m_arith.is_real(a) || m_arith.is_real(b);
            if (use_real) {
                if (m_arith.is_int(a)) a = expr_ref(m_arith.mk_to_real(a), m);
                if (m_arith.is_int(b)) b = expr_ref(m_arith.mk_to_real(b), m);
            }
            if (n == "$sum")        return expr_ref(m_arith.mk_add(a, b), m);
            if (n == "$difference") return expr_ref(m_arith.mk_sub(a, b), m);
            /* $product */          return expr_ref(m_arith.mk_mul(a, b), m);
        }

        if (n == "$quotient_e" || n == "$quotient_t" || n == "$quotient_f" || n == "$quotient") {
            if (args.size() != 2)
                throw parse_error("arithmetic function expects arity 2");
            expr_ref a(args.get(0), m), b(args.get(1), m);
            if (!m_arith.is_int_real(a) || !m_arith.is_int_real(b))
                throw parse_error("arithmetic function expects arithmetic arguments");
            if (m_arith.is_int(a) && m_arith.is_int(b))
                return expr_ref(m_arith.mk_idiv(a, b), m);
            if (m_arith.is_int(a)) a = expr_ref(m_arith.mk_to_real(a), m);
            if (m_arith.is_int(b)) b = expr_ref(m_arith.mk_to_real(b), m);
            return expr_ref(m_arith.mk_div(a, b), m);
        }

        if (n == "$remainder_e" || n == "$remainder_t" || n == "$remainder_f") {
            if (args.size() != 2)
                throw parse_error("arithmetic function expects arity 2");
            expr_ref a(args.get(0), m), b(args.get(1), m);
            if (!m_arith.is_int_real(a) || !m_arith.is_int_real(b))
                throw parse_error("arithmetic function expects arithmetic arguments");
            return expr_ref(m_arith.mk_mod(a, b), m);
        }

        if (n == "$floor" || n == "$ceiling" || n == "$truncate" || n == "$round" || n == "$to_int") {
            if (args.size() != 1)
                throw parse_error("arithmetic function expects arity 1");
            expr_ref a(args.get(0), m);
            if (!m_arith.is_int_real(a))
                throw parse_error("arithmetic function expects arithmetic argument");
            if (m_arith.is_int(a)) return a;
            return expr_ref(m_arith.mk_to_int(a), m);
        }

        if (n == "$to_rat" || n == "$to_real") {
            if (args.size() != 1)
                throw parse_error("arithmetic function expects arity 1");
            expr_ref a(args.get(0), m);
            if (!m_arith.is_int_real(a))
                throw parse_error("arithmetic function expects arithmetic argument");
            if (m_arith.is_real(a)) return a;
            return expr_ref(m_arith.mk_to_real(a), m);
        }

        if (n == "$is_int") {
            if (args.size() != 1)
                throw parse_error("arithmetic predicate '$is_int' expects arity 1");
            expr_ref a(args.get(0), m);
            if (!m_arith.is_int_real(a))
                throw parse_error("arithmetic predicate '$is_int' expects arithmetic argument");
            return expr_ref(m_arith.mk_is_int(a), m);
        }

        func_decl* f = mk_decl(n, args.size(), false);
        return expr_ref(args.empty() ? m.mk_const(f) : m.mk_app(f, args.size(), args.data()), m);
    }

    expr_ref parse_formula();

    expr_ref apply_at(expr_ref e) {
        if (!is(token_kind::at_tok)) return e;
        if (!is_app(e))
            throw parse_error("application operator (@) requires function on left-hand side");
        
        // Collect all @ arguments
        app* a = to_app(e);
        func_decl* orig_d = a->get_decl();
        if (orig_d->get_family_id() != null_family_id)
            throw parse_error("application operator (@) requires uninterpreted function on left-hand side");
        
        expr_ref_vector args(m);
        for (unsigned i = 0; i < a->get_num_args(); ++i) args.push_back(a->get_arg(i));
        
        while (accept(token_kind::at_tok)) {
            expr_ref arg = parse_at_arg();
            args.push_back(arg);
        }
        
        unsigned new_arity = args.size();
        std::string name = orig_d->get_name().str();

        // Check if the LHS has a ho_sort (function type as value).
        // If so, use its type info to determine domain/range for the application.
        sort* lhs_sort = orig_d->get_range(); // sort of the 0-arity constant
        auto ho_it = m_ho_sort_info.find(lhs_sort);
        if (ho_it != m_ho_sort_info.end() && a->get_num_args() == 0) {
            auto& [ho_domain, ho_range] = ho_it->second;
            sort* range = ho_range;
            // If we're partially applying (fewer args than domain), result is a ho_sort
            if (new_arity < ho_domain.size()) {
                std::vector<sort*> remaining(ho_domain.begin() + new_arity, ho_domain.end());
                range = get_ho_sort(remaining, ho_range);
            }
            // For bound variables, use $apply so that the variable remains in the
            // expression body and mk_forall can properly abstract it.
            if (is_bound_var(a)) {
                std::vector<sort*> apply_dom;
                apply_dom.push_back(lhs_sort); // first arg is the function variable
                for (unsigned i = 0; i < new_arity; ++i) {
                    if (i < ho_domain.size())
                        apply_dom.push_back(ho_domain[i]);
                    else
                        apply_dom.push_back(args.get(i)->get_sort());
                }
                // Create unique apply function per signature
                std::ostringstream apn;
                apn << "$apply_" << lhs_sort->get_name() << "_" << new_arity;
                func_decl* apply_d = m.mk_func_decl(symbol(apn.str()), apply_dom.size(), apply_dom.data(), range);
                m_pinned_decls.push_back(apply_d);
                expr_ref_vector all_args(m);
                all_args.push_back(e); // the bound variable itself
                for (unsigned i = 0; i < new_arity; ++i) all_args.push_back(args.get(i));
                return expr_ref(m.mk_app(apply_d, all_args.size(), all_args.data()), m);
            }
            // For non-bound ho-typed constants, use the name directly
            std::vector<sort*> dom;
            for (unsigned i = 0; i < new_arity; ++i) {
                if (i < ho_domain.size())
                    dom.push_back(ho_domain[i]);
                else
                    dom.push_back(args.get(i)->get_sort());
            }
            func_decl* new_d = m.mk_func_decl(symbol(name), new_arity, dom.data(), range);
            m_pinned_decls.push_back(new_d);
            return expr_ref(m.mk_app(new_d, new_arity, args.data()), m);
        }

        func_decl* new_d = mk_decl(name, new_arity, false);
        // Verify argument sorts match; if not, create untyped func_decl with actual arg sorts
        bool sorts_ok = (new_d->get_arity() == new_arity);
        if (sorts_ok) {
            for (unsigned i = 0; i < new_arity; ++i) {
                if (new_d->get_domain(i) != args.get(i)->get_sort()) {
                    sorts_ok = false;
                    break;
                }
            }
        }
        if (!sorts_ok) {
            std::vector<sort*> dom;
            for (unsigned i = 0; i < new_arity; ++i) dom.push_back(args.get(i)->get_sort());
            sort* range = new_d->get_range();
            new_d = m.mk_func_decl(symbol(name), new_arity, dom.data(), range);
            m_pinned_decls.push_back(new_d);
        }
        return expr_ref(m.mk_app(new_d, new_arity, args.data()), m);
    }

    // Parse an argument to @ — can be a term, a formula (negation, quantifier, parens with connectives), or a lambda
    expr_ref parse_at_arg() {
        if (accept(token_kind::not_tok)) {
            expr_ref e = parse_at_arg();
            return expr_ref(m.mk_not(e), m);
        }
        if (accept(token_kind::lambda_tok)) {
            return parse_lambda_expr();
        }
        if (accept(token_kind::lparen)) {
            expr_ref e = parse_formula();
            expect(token_kind::rparen, "')'");
            // Do NOT call apply_at here — outer apply_at owns the remaining @ tokens
            return e;
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
                        if (!t.domain.empty()) s = get_ho_sort(t.domain, t.range);
                        else s = t.range;
                    }
                    app* c = m.mk_const(symbol(v), s);
                    vars.push_back(c);
                    scope.emplace(v, c);
                } while (accept(token_kind::comma));
                expect(token_kind::rbrack, "']'");
            }
            expect(token_kind::colon, "':'");
            m_bound.push_back(scope);
            expr_ref body = parse_formula();
            m_bound.pop_back();
            return mk_quantifier(is_forall, vars, body);
        }
        // Simple term (name with optional function args) — no @ consumption here
        return parse_term_primary();
    }

    // Build an arithmetic expression from a TPTP function name and arguments
    expr_ref mk_arith_expr(std::string const& n, expr_ref_vector const& args) {
        if (n == "$uminus") {
            if (args.size() != 1) throw parse_error("$uminus expects arity 1");
            expr_ref a(args.get(0), m);
            return expr_ref(m_arith.mk_uminus(a), m);
        }
        if (n == "$sum" || n == "$difference" || n == "$product") {
            if (args.size() != 2) throw parse_error("arithmetic binary function expects arity 2");
            expr_ref a(args.get(0), m), b(args.get(1), m);
            bool use_real = m_arith.is_real(a) || m_arith.is_real(b);
            if (use_real) {
                if (m_arith.is_int(a)) a = expr_ref(m_arith.mk_to_real(a), m);
                if (m_arith.is_int(b)) b = expr_ref(m_arith.mk_to_real(b), m);
            }
            if (n == "$sum")        return expr_ref(m_arith.mk_add(a, b), m);
            if (n == "$difference") return expr_ref(m_arith.mk_sub(a, b), m);
            return expr_ref(m_arith.mk_mul(a, b), m);
        }
        if (n == "$quotient" || n == "$quotient_e" || n == "$quotient_t" || n == "$quotient_f") {
            if (args.size() != 2) throw parse_error("quotient expects arity 2");
            expr_ref a(args.get(0), m), b(args.get(1), m);
            if (m_arith.is_int(a) && m_arith.is_int(b))
                return expr_ref(m_arith.mk_idiv(a, b), m);
            if (m_arith.is_int(a)) a = expr_ref(m_arith.mk_to_real(a), m);
            if (m_arith.is_int(b)) b = expr_ref(m_arith.mk_to_real(b), m);
            return expr_ref(m_arith.mk_div(a, b), m);
        }
        if (n == "$remainder_e" || n == "$remainder_t" || n == "$remainder_f") {
            if (args.size() != 2) throw parse_error("remainder expects arity 2");
            expr_ref a(args.get(0), m), b(args.get(1), m);
            return expr_ref(m_arith.mk_mod(a, b), m);
        }
        if (n == "$floor" || n == "$ceiling" || n == "$truncate" || n == "$round" || n == "$to_int") {
            if (args.size() != 1) throw parse_error("$to_int expects arity 1");
            expr_ref a(args.get(0), m);
            if (m_arith.is_int(a)) return a;
            return expr_ref(m_arith.mk_to_int(a), m);
        }
        if (n == "$to_rat" || n == "$to_real") {
            if (args.size() != 1) throw parse_error("$to_real expects arity 1");
            expr_ref a(args.get(0), m);
            if (m_arith.is_real(a)) return a;
            return expr_ref(m_arith.mk_to_real(a), m);
        }
        throw parse_error("unknown arithmetic function: " + n);
    }

    // Coerce two expressions to have the same sort for equality.
    // If sorts already match, returns lhs unchanged. Otherwise coerces the
    // 0-arity constant side to match the other's sort. If that's not possible,
    // coerces both to m_univ.
    expr_ref coerce_eq(expr_ref lhs, expr_ref& rhs) {
        if (lhs->get_sort() == rhs->get_sort()) return lhs;
        // Try coercing one side (0-arity constants can be reinterpreted)
        if (is_app(lhs) && to_app(lhs)->get_num_args() == 0 && lhs->get_sort() != rhs->get_sort()) {
            func_decl* fd = m.mk_func_decl(to_app(lhs)->get_decl()->get_name(), 0, static_cast<sort**>(nullptr), rhs->get_sort());
            m_pinned_decls.push_back(fd);
            return expr_ref(m.mk_const(fd), m);
        }
        if (is_app(rhs) && to_app(rhs)->get_num_args() == 0 && lhs->get_sort() != rhs->get_sort()) {
            func_decl* fd = m.mk_func_decl(to_app(rhs)->get_decl()->get_name(), 0, static_cast<sort**>(nullptr), lhs->get_sort());
            m_pinned_decls.push_back(fd);
            rhs = m.mk_const(fd);
            return lhs;
        }
        // Last resort: coerce both to m_univ
        if (is_app(lhs) && to_app(lhs)->get_num_args() == 0) {
            func_decl* fd = m.mk_func_decl(to_app(lhs)->get_decl()->get_name(), 0, static_cast<sort**>(nullptr), m_univ);
            m_pinned_decls.push_back(fd);
            lhs = m.mk_const(fd);
        }
        if (is_app(rhs) && to_app(rhs)->get_num_args() == 0) {
            func_decl* fd = m.mk_func_decl(to_app(rhs)->get_decl()->get_name(), 0, static_cast<sort**>(nullptr), m_univ);
            m_pinned_decls.push_back(fd);
            rhs = m.mk_const(fd);
        }
        return lhs;
    }

    expr_ref parse_atomic_formula() {
        if (accept(token_kind::lparen)) {
            expr_ref e = parse_formula();
            // Handle equality/inequality inside parenthesized expressions
            // In THF, (A = B) is used even for Bool-sorted expressions (meaning iff)
            if (is(token_kind::equal_tok) || is(token_kind::neq_tok)) {
                bool neq = accept(token_kind::neq_tok);
                if (!neq) expect(token_kind::equal_tok, "'='");
                expr_ref rhs = m.is_bool(e) ? parse_formula() : parse_term();
                e = coerce_eq(e, rhs);
                expr_ref eq(m.mk_eq(e, rhs), m);
                e = neq ? expr_ref(m.mk_not(eq), m) : eq;
            }
            expect(token_kind::rparen, "')'");
            return apply_at(e);
        }

        std::string n = parse_name();
        if (n == "$true") return expr_ref(m.mk_true(), m);
        if (n == "$false") return expr_ref(m.mk_false(), m);

        if (is_nonempty_digit_string(n)) {
            expr_ref lhs = parse_numeral_from_name(n);
            if (is(token_kind::equal_tok) || is(token_kind::neq_tok)) {
                bool neq = accept(token_kind::neq_tok);
                if (!neq) expect(token_kind::equal_tok, "'='");
                expr_ref rhs = parse_term();
                expr_ref eq(m.mk_eq(lhs, rhs), m);
                return neq ? expr_ref(m.mk_not(eq), m) : eq;
            }
            throw parse_error("numeric term used as formula");
        }

        expr_ref_vector args(m);
        if (accept(token_kind::lparen)) {
            if (!accept(token_kind::rparen)) {
                do { args.push_back(parse_term()); } while (accept(token_kind::comma));
                expect(token_kind::rparen, "')'");
            }
        }

        if (n == "$less" || n == "$lesseq" || n == "$greater" || n == "$greatereq") {
            if (args.size() != 2) {
                std::ostringstream out;
                out << "arithmetic predicate '" << n << "' expects arity 2";
                throw parse_error(out.str());
            }
            expr_ref lhs(args.get(0), m), rhs(args.get(1), m);
            if (!m_arith.is_int_real(lhs) || !m_arith.is_int_real(rhs)) {
                std::ostringstream out;
                out << "arithmetic predicate '" << n << "' expects arithmetic arguments";
                throw parse_error(out.str());
            }
            bool use_real = m_arith.is_real(lhs) || m_arith.is_real(rhs);
            if (use_real) {
                if (m_arith.is_int(lhs)) lhs = expr_ref(m_arith.mk_to_real(lhs), m);
                if (m_arith.is_int(rhs)) rhs = expr_ref(m_arith.mk_to_real(rhs), m);
            }
            if (n == "$less")      return expr_ref(m_arith.mk_lt(lhs, rhs), m);
            if (n == "$lesseq")    return expr_ref(m_arith.mk_le(lhs, rhs), m);
            if (n == "$greater")   return expr_ref(m_arith.mk_gt(lhs, rhs), m);
            /* n == "$greatereq"*/ return expr_ref(m_arith.mk_ge(lhs, rhs), m);
        }

        // Arithmetic terms that may appear before = or != in formula position
        if (n == "$sum" || n == "$difference" || n == "$product" ||
            n == "$quotient" || n == "$quotient_e" || n == "$quotient_t" || n == "$quotient_f" ||
            n == "$remainder_e" || n == "$remainder_t" || n == "$remainder_f" ||
            n == "$uminus" || n == "$floor" || n == "$ceiling" || n == "$truncate" ||
            n == "$round" || n == "$to_int" || n == "$to_rat" || n == "$to_real") {
            // Re-parse via the term path by constructing the arithmetic expression
            expr_ref arith_expr = mk_arith_expr(n, args);
            if (is(token_kind::equal_tok) || is(token_kind::neq_tok)) {
                bool neq = accept(token_kind::neq_tok);
                if (!neq) expect(token_kind::equal_tok, "'='");
                expr_ref rhs = parse_term();
                arith_expr = coerce_eq(arith_expr, rhs);
                expr_ref eq(m.mk_eq(arith_expr, rhs), m);
                return neq ? expr_ref(m.mk_not(eq), m) : eq;
            }
            return arith_expr;
        }

        expr_ref lhs(m);
        bool has_lhs = false;
        if (args.empty()) {
            expr_ref b(m);
            if (!m_last_name_quoted && is_var_name(n) && find_bound(n, b)) {
                lhs = b;
                has_lhs = true;
            }
            else if (!m_last_name_quoted && should_create_implicit_var(n)) {
                lhs = expr_ref(get_or_create_implicit_var(n), m);
                has_lhs = true;
            }
        }

        if (is(token_kind::equal_tok) || is(token_kind::neq_tok)) {
            if (!has_lhs) {
                func_decl* f = mk_decl_or_ho_const(n, args.size(), false);
                lhs = args.empty() ? m.mk_const(f) : m.mk_app(f, args.size(), args.data());
            }
            bool neq = accept(token_kind::neq_tok);
            if (!neq) expect(token_kind::equal_tok, "'='");
            expr_ref rhs = parse_term();
            lhs = coerce_eq(lhs, rhs);
            expr_ref eq(m.mk_eq(lhs, rhs), m);
            return neq ? expr_ref(m.mk_not(eq), m) : eq;
        }

        if (has_lhs) {
            lhs = apply_at(lhs);
            if (is(token_kind::equal_tok) || is(token_kind::neq_tok)) {
                bool neq = accept(token_kind::neq_tok);
                if (!neq) expect(token_kind::equal_tok, "'='");
                expr_ref rhs = parse_term();
                lhs = coerce_eq(lhs, rhs);
                expr_ref eq(m.mk_eq(lhs, rhs), m);
                return neq ? expr_ref(m.mk_not(eq), m) : eq;
            }
            return lhs;  // In THF, variables of any sort can appear in formula position (e.g., with @)
        }

        auto typed = m_typed_decls.find(mk_typed_key(n, args.size()));
        if (typed != m_typed_decls.end()) {
            func_decl* f = mk_decl(n, args.size(), false);
            expr_ref e(args.empty() ? m.mk_const(f) : m.mk_app(f, args.size(), args.data()), m);
            e = apply_at(e);
            if (is(token_kind::equal_tok) || is(token_kind::neq_tok)) {
                bool neq = accept(token_kind::neq_tok);
                if (!neq) expect(token_kind::equal_tok, "'='");
                expr_ref rhs = parse_term();
                e = coerce_eq(e, rhs);
                expr_ref eq(m.mk_eq(e, rhs), m);
                return neq ? expr_ref(m.mk_not(eq), m) : eq;
            }
            if (!m.is_bool(e))
                return e;  // In THF, non-Bool typed expressions can appear in formula position (e.g., as @ args)
            return e;
        }

        func_decl* pred = mk_decl(n, args.size(), true);
        expr_ref result(args.empty() ? m.mk_const(pred) : m.mk_app(pred, args.size(), args.data()), m);
        return apply_at(result);
    }

    // Parse THF lambda expression: ^ [X: T, ...] : body
    // Since Z3 doesn't support lambdas natively, we approximate:
    // - Parse the bound variables and body
    // - Return the body with variables universally quantified (over-approximation)
    expr_ref parse_lambda_expr() {
        expect(token_kind::lbrack, "'['");
        ptr_vector<app> vars;
        std::unordered_map<std::string, app*> scope;
        if (!accept(token_kind::rbrack)) {
            do {
                std::string v = parse_name();
                sort* s = m_univ;
                if (accept(token_kind::colon)) {
                    parsed_type t = parse_type_expr();
                    if (!t.domain.empty()) {
                        s = get_ho_sort(t.domain, t.range);
                    } else if (t.range) {
                        s = t.range;
                    }
                }
                app* c = m.mk_const(symbol(v), s);
                vars.push_back(c);
                scope.emplace(v, c);
            } while (accept(token_kind::comma));
            expect(token_kind::rbrack, "']'");
        }
        expect(token_kind::colon, "':'");
        m_bound.push_back(scope);
        expr_ref body = parse_formula();
        m_bound.pop_back();
        // For first-order approximation, create a fresh constant with the lambda's function type sort
        std::ostringstream oss;
        oss << "$lambda_" << m_lambda_counter++;
        std::string lname = oss.str();
        // Lambda type: param sorts → body sort
        // If the body sort is itself a ho_sort, flatten it into the lambda's type
        // e.g., ^ [X: mu] : (body with sort (U > Bool)) → sort (mu * U > Bool)
        std::vector<sort*> param_sorts;
        for (auto* v : vars) param_sorts.push_back(v->get_sort());
        sort* body_sort = body->get_sort();
        sort* lambda_sort;
        if (param_sorts.empty()) {
            lambda_sort = body_sort;
        } else {
            auto body_ho = m_ho_sort_info.find(body_sort);
            if (body_ho != m_ho_sort_info.end()) {
                // Flatten: params + body's domain → body's range
                std::vector<sort*> full_domain = param_sorts;
                full_domain.insert(full_domain.end(), body_ho->second.first.begin(), body_ho->second.first.end());
                lambda_sort = get_ho_sort(full_domain, body_ho->second.second);
            } else {
                lambda_sort = get_ho_sort(param_sorts, body_sort);
            }
        }
        func_decl* f = m.mk_func_decl(symbol(lname), 0, static_cast<sort**>(nullptr), lambda_sort);
        m_pinned_decls.push_back(f);
        return expr_ref(m.mk_const(f), m);
    }

    expr_ref parse_unary_formula() {
        if (accept(token_kind::not_tok)) {
            expr_ref e = parse_unary_formula();
            return expr_ref(m.mk_not(e), m);
        }

        if (accept(token_kind::lambda_tok)) {
            // THF lambda: ^ [X: T, ...] : body
            // Approximate as a fresh constant (first-order approximation)
            return parse_lambda_expr();
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
                        if (!t.domain.empty()) {
                            // Higher-order variable type — use uninterpreted sort approximation
                            s = get_ho_sort(t.domain, t.range);
                        } else {
                            s = t.range;
                        }
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
        unsigned lparen_count = 0;
        while (accept(token_kind::lparen)) ++lparen_count;
        std::string name = parse_name();
        expect(token_kind::colon, "':'");
        parsed_type t = parse_type_expr();
        while (lparen_count-- > 0)
            expect(token_kind::rparen, "')'");

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

    static std::string normalize_path(std::string path) {
#ifdef _WIN32
        for (auto& c : path)
            if (c == '/') c = '\\';
#endif
        return path;
    }

    std::string resolve_include(std::string const& curr_file, std::string const& name) const {
        if (is_absolute_path(name))
            return normalize_path(name);
        // Try relative to current file's directory
        std::string local = normalize_path(dirname(curr_file) + "/" + name);
        if (file_exists(local)) return local;
        // Try TPTP environment variable (standard TPTP convention)
        char const* root = std::getenv("TPTP");
        if (root) {
            std::string env = normalize_path(std::string(root) + "/" + name);
            if (file_exists(env)) return env;
        }
        // Try relative to current working directory (common when running from TPTP root)
        std::string cwd_relative = normalize_path(name);
        if (file_exists(cwd_relative)) return cwd_relative;
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
            implicit_var_scope implicit_scope;
            scoped_implicit_vars scoped(*this, implicit_scope);
            expr_ref f = parse_formula();
            if (!implicit_scope.order.empty()) {
                f = mk_quantifier(true, implicit_scope.order, f);
            }
            if (role == "conjecture") {
                m_has_conjecture = true;
                if (m.is_bool(f))
                    f = m.mk_not(f);
            }
            // Only assert Bool-sorted formulas; non-Bool results from
            // incomplete higher-order approximation are silently skipped.
            if (m.is_bool(f))
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
        m_pinned_sorts(m),
        m_pinned_decls(m),
        m_univ(m.mk_uninterpreted_sort(symbol("U"))) {
        m_pinned_sorts.push_back(m_univ);
        sort* tType = m.mk_uninterpreted_sort(symbol("$tType"));
        m_pinned_sorts.push_back(tType);
        m_sorts.emplace("$tType", tType);
        m_sorts.emplace("$i", m_univ);
        m_sorts.emplace("$o", m.mk_bool_sort());
        m_sorts.emplace("$int", m_arith.mk_int());
        m_sorts.emplace("$rat", m_arith.mk_real());
        m_sorts.emplace("$real", m_arith.mk_real());
    }

    void parse_input(std::istream& in, std::string const& current_file) {
        // Save parser state so that included files don't clobber the caller's lexer.
        std::string saved_input = std::move(m_input);
        std::unique_ptr<lexer> saved_lex = std::move(m_lex);
        token saved_curr = m_curr;

        std::ostringstream buf;
        buf << in.rdbuf();
        m_input = buf.str();
        m_lex = std::make_unique<lexer>(m_input);
        next();
        parse_toplevel(current_file);

        // Restore caller's parser state.
        m_input = std::move(saved_input);
        m_lex = std::move(saved_lex);
        m_curr = saved_curr;
    }

    void parse_file(std::string const& filename) {
        if (!m_seen_files.insert(filename).second) return;
        std::ifstream in(filename);
        if (in.fail()) {
            std::ostringstream out;
            out << "failed to open file '" << filename << "'";
            throw parse_error(out.str());
        }
        parse_input(in, filename);
    }

    void parse_stream(std::istream& in) {
        parse_input(in, ".");
    }

    bool has_conjecture() const { return m_has_conjecture; }
};

expr_ref tptp_parser::parse_term() {
    expr_ref e = parse_term_primary();
    if (!is(token_kind::at_tok)) return e;
    if (!is_app(e))
        throw parse_error("application operator (@) requires uninterpreted function on left-hand side");
    app* a = to_app(e);
    func_decl* orig_d = a->get_decl();
    if (orig_d->get_family_id() != null_family_id)
        throw parse_error("application operator (@) requires uninterpreted function on left-hand side");
    expr_ref_vector args(m);
    for (unsigned i = 0; i < a->get_num_args(); ++i) args.push_back(a->get_arg(i));
    while (accept(token_kind::at_tok)) {
        expr_ref arg = parse_at_arg();
        args.push_back(arg);
    }
    unsigned new_arity = args.size();
    std::string name = orig_d->get_name().str();
    func_decl* new_d = mk_decl(name, new_arity, false);
    // Verify argument sorts match; if not, create func_decl with actual arg sorts
    bool sorts_ok = (new_d->get_arity() == new_arity);
    if (sorts_ok) {
        for (unsigned i = 0; i < new_arity; ++i) {
            if (new_d->get_domain(i) != args.get(i)->get_sort()) {
                sorts_ok = false;
                break;
            }
        }
    }
    if (!sorts_ok) {
        std::vector<sort*> dom;
        for (unsigned i = 0; i < new_arity; ++i) dom.push_back(args.get(i)->get_sort());
        sort* range = new_d->get_range();
        new_d = m.mk_func_decl(symbol(name), new_arity, dom.data(), range);
        m_pinned_decls.push_back(new_d);
    }
    return expr_ref(m.mk_app(new_d, new_arity, args.data()), m);
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
    register_on_timeout_proc(on_timeout);
    try {
        cmd_context ctx;
        ctx.set_solver_factory(mk_smt_strategic_solver_factory());

        tptp_parser p(ctx);
        p.parse_input(in, current_file ? current_file : ".");

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
    catch (z3_error const& ex) {
        if (ex.error_code() == ERR_TIMEOUT) {
            std::cout << "% SZS status Timeout\n";
            return 0;
        }
        std::cerr << "TPTP frontend error: " << ex.what() << "\n";
        return ERR_INTERNAL_FATAL;
    }
    catch (z3_exception const& ex) {
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
