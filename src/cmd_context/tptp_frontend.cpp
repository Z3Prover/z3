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
#include "ast/array_decl_plugin.h"
#include "ast/expr_abstract.h"
#include "ast/ast_util.h"
#include "ast/rewriter/expr_safe_replace.h"
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
    type_forall_tok,  // !>
    type_exists_tok,  // ?*
    equal_tok,
    neq_tok,
    iff_tok,
    implies_tok,
    implied_tok,
    xor_tok,
    nor_tok,
    nand_tok,
    gt_tok,
    lt_tok,
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
        case '!':
            if (peek() == '>') { get(); t.kind = token_kind::type_forall_tok; return t; }
            if (peek() == '!') { get(); t.kind = token_kind::id; t.text = "!!"; return t; }
            t.kind = token_kind::forall_tok; return t;
        case '?':
            if (peek() == '*') { get(); t.kind = token_kind::type_exists_tok; return t; }
            if (peek() == '?') { get(); t.kind = token_kind::id; t.text = "??"; return t; }
            t.kind = token_kind::exists_tok; return t;
        case '=': t.kind = token_kind::equal_tok; return t;
        case '>': t.kind = token_kind::gt_tok; return t;
        case '<': t.kind = token_kind::lt_tok; return t;
        case '*': t.kind = token_kind::star_tok; return t;
        case '/': t.kind = token_kind::slash_tok; return t;
        case '-': t.kind = token_kind::minus_tok; return t;
        case '@':
            if (peek() == '+') { get(); t.kind = token_kind::id; t.text = "@+"; return t; }
            if (peek() == '-') { get(); t.kind = token_kind::id; t.text = "@-"; return t; }
            t.kind = token_kind::at_tok; return t;
        case '^': t.kind = token_kind::lambda_tok; return t;
        case '{':
            // Modal operators: {$box}, {$dia}, etc. — lex as identifier including braces
            t.kind = token_kind::id;
            t.text.push_back(c);
            while (!eof() && peek() != '}')
                t.text.push_back(get());
            if (!eof()) t.text.push_back(get()); // consume '}'
            return t;
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
    array_util m_array;
    sort* m_univ;
    bool m_has_conjecture = false;
    bool m_last_name_quoted = false;
    std::unordered_map<std::string, sort*> m_sorts;
    sort_ref_vector m_pinned_sorts;       // prevents cached sorts from being freed
    std::unordered_map<std::string, func_decl*> m_decls;
    func_decl_ref_vector m_pinned_decls;  // prevents cached func_decls from being freed
    expr_ref_vector m_pinned_exprs;       // prevents bound variable apps from being freed
    std::unordered_map<std::string, std::pair<std::vector<sort*>, sort*>> m_typed_decls;
    std::vector<std::unordered_map<std::string, app*>> m_bound;
    bool m_in_at_arg = false;  // true when parsing inside @ argument (lambda body stops consuming @)
    struct implicit_var_scope {
        std::unordered_map<std::string, app*> vars;
        ptr_vector<app> order;
    };
    implicit_var_scope* m_implicit_scope = nullptr;
    std::unordered_set<std::string> m_seen_files;

    // Table-driven operator dispatch
    using op_builder = std::function<expr_ref(expr_ref_vector const&)>;
    struct op_entry {
        bool        is_infix;
        unsigned    precedence; // only meaningful for infix; higher = tighter binding
        bool        right_assoc;
        op_builder  builder;
    };
    std::unordered_map<std::string, op_entry> m_ops;

    // Infix precedence levels:
    static constexpr unsigned PREC_IFF     = 1; // <=> <~>
    static constexpr unsigned PREC_IMPLIES = 2; // => <=
    static constexpr unsigned PREC_OR      = 3; // | ~|
    static constexpr unsigned PREC_AND     = 4; // & ~&
    static constexpr unsigned PREC_EQ      = 5; // = !=

    std::string m_input;
    std::unique_ptr<lexer> m_lex;
    token m_curr;

    // Helper: check arity for arithmetic operators
    void check_arith_arity(expr_ref_vector const& args, unsigned expected, char const* name) {
        if (args.size() != expected) {
            std::ostringstream out;
            out << "'" << name << "' expects arity " << expected;
            throw parse_error(out.str());
        }
    }

    // Helper: coerce two arithmetic args to same sort (promote int to real if needed)
    std::pair<expr_ref, expr_ref> coerce_arith2(expr_ref_vector const& args) {
        expr_ref a(args[0], m), b(args[1], m);
        // Coerce U-sorted args to Int (from HO encoding / $let bindings)
        if (!m_arith.is_int_real(a) && !m_arith.is_int_real(b)) {
            a = coerce_arg(a, m_arith.mk_int());
            b = coerce_arg(b, m_arith.mk_int());
        } else if (!m_arith.is_int_real(a)) {
            a = coerce_arg(a, b->get_sort());
        } else if (!m_arith.is_int_real(b)) {
            b = coerce_arg(b, a->get_sort());
        }
        if (m_arith.is_real(a) || m_arith.is_real(b)) {
            if (m_arith.is_int(a)) a = expr_ref(m_arith.mk_to_real(a), m);
            if (m_arith.is_int(b)) b = expr_ref(m_arith.mk_to_real(b), m);
        }
        return { a, b };
    }

    // Helper: quotient dispatch (integer division for int/int, real division otherwise)
    expr_ref mk_quotient(expr_ref_vector const& args) {
        expr_ref a(args[0], m), b(args[1], m);
        if (m_arith.is_int(a) && m_arith.is_int(b))
            return expr_ref(m_arith.mk_idiv(a, b), m);
        if (m_arith.is_int(a)) a = expr_ref(m_arith.mk_to_real(a), m);
        if (m_arith.is_int(b)) b = expr_ref(m_arith.mk_to_real(b), m);
        return expr_ref(m_arith.mk_div(a, b), m);
    }

    // Map infix token to operator name (returns nullptr if not an infix op token)
    char const* token_to_op_name() const {
        switch (m_curr.kind) {
        case token_kind::iff_tok:     return "<=>";
        case token_kind::xor_tok:     return "<~>";
        case token_kind::implies_tok: return "=>";
        case token_kind::implied_tok: return "<=";
        case token_kind::or_tok:      return "|";
        case token_kind::nor_tok:     return "~|";
        case token_kind::and_tok:     return "&";
        case token_kind::nand_tok:    return "~&";
        case token_kind::equal_tok:   return "=";
        case token_kind::neq_tok:     return "!=";
        default:                      return nullptr;
        }
    }
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

    // Grammar: <name>           ::= <atomic_word> | <integer>
    //          <atomic_word>    ::= <lower_word> | <single_quoted>
    //          Used universally for parsing identifiers, keywords, and quoted names.
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
    // Function type A > B is represented as Array(A, B).
    // Multi-argument A * B > C is represented as Array(A, Array(B, C)) (curried).
    sort* get_ho_sort(std::vector<sort*> const& domain, sort* range) {
        sort* s = range;
        for (int i = (int)domain.size() - 1; i >= 0; --i)
            s = m_array.mk_array_sort(domain[i], s);
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

    // Grammar: <number>  ::= <integer> | <rational> | <real>
    //          <integer> ::= <signed_integer> | <unsigned_integer>
    //          <rational>::= <signed_integer>/<positive_integer>
    //          <real>    ::= <signed_integer><dot_decimal> | ...
    //          Parses integer, rational (N/D), and real (N.D or N.DeE) numeric literals.
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

    // Create a modal operator declaration: Bool → Bool
    func_decl* mk_modal_op(std::string const& name) {
        std::string key = mk_decl_key(name, 1, 'm');
        auto it = m_decls.find(key);
        if (it != m_decls.end()) return it->second;
        sort* bool_sort = m.mk_bool_sort();
        func_decl* f = m.mk_func_decl(symbol(name), 1, &bool_sort, bool_sort);
        m_pinned_decls.push_back(f);
        m_decls.emplace(key, f);
        return f;
    }

    // When a symbol is used with 0 args but has a typed decl with arity > 0,
    // create a 0-arity constant with the function type sort (for THF function-as-value).
    func_decl* mk_decl_or_ho_const(std::string const& name, unsigned arity, bool pred) {
        if (arity == 0) {
            // Check if there's a typed decl at any arity > 0 for this name
            for (unsigned try_arity = 1; try_arity <= 30; ++try_arity) {
                auto itt = m_typed_decls.find(mk_typed_key(name, try_arity));
                if (itt != m_typed_decls.end()) {
                    auto const& sig = itt->second;
                    sort* ho = get_ho_sort(sig.first, sig.second);
                    std::string dkey = mk_decl_key(name, 0, 'h');
                    auto itd = m_decls.find(dkey);
                    if (itd != m_decls.end()) return itd->second;
                    func_decl* f = m.mk_func_decl(symbol(name), 0, static_cast<sort**>(nullptr), ho);
                    m_pinned_decls.push_back(f);
                    m_decls.emplace(dkey, f);
                    return f;
                }
            }
        }
        return mk_decl(name, arity, pred);
    }

    // Coerce an expression to a target sort using boxing/unboxing functions
    expr_ref coerce_arg(expr_ref const& e, sort* target) {
        sort* actual = e->get_sort();
        if (actual == target) return e;
        // Create a boxing function from actual sort to target sort
        std::string box_name = std::string("$box_") + actual->get_name().str() + "_to_" + target->get_name().str();
        std::string key = mk_decl_key(box_name, 1, 'f');
        auto it = m_decls.find(key);
        func_decl* f;
        if (it != m_decls.end()) {
            f = it->second;
        } else {
            f = m.mk_func_decl(symbol(box_name), 1, &actual, target);
            m_pinned_decls.push_back(f);
            m_decls.emplace(key, f);
        }
        return expr_ref(m.mk_app(f, e.get()), m);
    }

    // Coerce expression to Bool sort — if U-sorted, wrap with an uninterpreted predicate
    expr_ref ensure_bool(expr* e) {
        if (m.is_bool(e->get_sort())) return expr_ref(e, m);
        return coerce_arg(expr_ref(e, m), m.mk_bool_sort());
    }

    // Coerce arguments of a function application to match declared sorts
    void coerce_args(func_decl* f, expr_ref_vector& args) {
        for (unsigned i = 0; i < args.size() && i < f->get_arity(); ++i) {
            sort* expected = f->get_domain(i);
            sort* actual = args.get(i)->get_sort();
            if (expected != actual) {
                args[i] = coerce_arg(expr_ref(args.get(i), m), expected);
            }
        }
    }

    // Coerce result to expected sort if needed  
    expr_ref coerce_result(expr_ref const& e, sort* expected) {
        if (!expected || e->get_sort() == expected) return e;
        return coerce_arg(e, expected);
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
        m_pinned_exprs.push_back(c);
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
        expr_ref b = ensure_bool(body);
        return is_forall ? ::mk_forall(m, bound.size(), bound.data(), b.get()) : ::mk_exists(m, bound.size(), bound.data(), b.get());
    }

    // $is_rat(x) ≡ exists a:Int, b:Int. b != 0 && x = a/b
    expr_ref mk_is_rat(expr_ref const& x) {
        sort* int_sort = m_arith.mk_int();
        app* a = m.mk_fresh_const("a", int_sort);
        app* b = m.mk_fresh_const("b", int_sort);
        expr_ref ar(m_arith.mk_to_real(a), m);
        expr_ref br(m_arith.mk_to_real(b), m);
        expr_ref xr(x);
        if (m_arith.is_int(x))
            xr = expr_ref(m_arith.mk_to_real(x), m);
        expr_ref b_ne_zero(m.mk_not(m.mk_eq(b, m_arith.mk_int(0))), m);
        expr_ref x_eq_div(m.mk_eq(xr, m_arith.mk_div(ar, br)), m);
        expr_ref body(m.mk_and(b_ne_zero, x_eq_div), m);
        ptr_vector<app> bound;
        bound.push_back(a);
        bound.push_back(b);
        return expr_ref(::mk_exists(m, bound.size(), bound.data(), body.get()), m);
    }

    // Grammar: <thf_atomic_type>   ::= <type_constant> | <defined_type> | <variable> |
    //                                   <thf_mapping_type> | (<thf_binary_type>)
    //          <tff_atomic_type>   ::= <type_constant> | <defined_type> | <variable> |
    //                                   <type_functor>(<tff_type_arguments>)
    //          <defined_type>      ::= $oType | $o | $iType | $i | $tType | $real | $rat | $int
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
                // Return with domain/range preserved for proper flattening
                return parsed_type(full_domain, rhs.range);
            }
            expect(token_kind::rparen, "')'");
            if (prod.size() == 1)
                return parsed_type(prod[0]);
            // Parenthesized product: (A * B) — used as domain in outer context
            return parsed_type(prod, nullptr);
        }
        std::string n = parse_name();
        // Handle parameterized type constructors: fun(A, B), product_prod(A, B), etc.
        if (accept(token_kind::lparen)) {
            // Consume type arguments — for monomorphization, we ignore them
            // and return the base sort (or m_univ if the constructor result is $tType)
            if (!accept(token_kind::rparen)) {
                do { parse_type_expr(); } while (accept(token_kind::comma));
                expect(token_kind::rparen, "')'");
            }
            // Return m_univ as the monomorphized result of any type constructor application
            return parsed_type(m_univ);
        }
        sort* s = get_sort(n);
        // Handle type-level application with @: list @ nat, pair @ A @ B, etc.
        // Monomorphize by consuming all @ arguments and returning m_univ.
        if (is(token_kind::at_tok)) {
            while (accept(token_kind::at_tok)) {
                parse_type_atom(); // consume the argument type
            }
            return parsed_type(m_univ);
        }
        return parsed_type(s);
    }

    // Grammar: <thf_xprod_type>    ::= <thf_unitary_type> * <thf_unitary_type>
    //                                 | <thf_xprod_type> * <thf_unitary_type>
    //          Product types form the domain in mapping types: (A * B) > C
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

    // Grammar: <tff_top_level_type> ::= <tff_atomic_type> | <tff_mapping_type> | <tf1_quantified_type>
    //          <tff_mapping_type>   ::= <tff_unitary_type> > <tff_atomic_type>
    //          <thf_binary_type>    ::= <thf_mapping_type> | <thf_xprod_type>
    //          <thf_mapping_type>   ::= <thf_unitary_type> > <thf_unitary_type>
    parsed_type parse_type_product() {
        parsed_type first = parse_type_atom();
        // If atom returned a function type and no '*' follows, return it directly
        if (!first.domain.empty() && first.range != nullptr && !is(token_kind::star_tok)) {
            return first;
        }
        // Build product vector
        std::vector<sort*> args;
        if (!first.domain.empty() && first.range != nullptr) {
            // Function type used as element in a product
            args.push_back(get_ho_sort(first.domain, first.range));
        } else if (!first.domain.empty() && first.range == nullptr) {
            // Parenthesized product: flatten
            args = first.domain;
        } else {
            args.push_back(first.range);
        }
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
        return parsed_type(args, nullptr);
    }

    // Grammar: <tff_top_level_type>  ::= <tff_atomic_type> | <tff_mapping_type> | <tf1_quantified_type>
    //          <thf_binary_type>     ::= <thf_mapping_type> | <thf_xprod_type>
    //          <tf1_quantified_type> ::= !> [<tff_variable_list>] : <tff_monotype>
    //          Parses: atom, atom > atom, (A * B) > C, !>[X:$tType] : T
    parsed_type parse_type_expr() {
        // Handle type quantification at the expression level for proper domain/range preservation
        if (is(token_kind::type_forall_tok) || is(token_kind::type_exists_tok)) {
            next();
            expect(token_kind::lbrack, "'['");
            std::vector<sort*> type_params;
            if (!accept(token_kind::rbrack)) {
                do {
                    std::string tv = parse_name();
                    if (accept(token_kind::colon))
                        parse_type_expr(); // consume $tType annotation
                    m_sorts.insert_or_assign(tv, m_univ);
                    type_params.push_back(m_univ);
                } while (accept(token_kind::comma));
                expect(token_kind::rbrack, "']'");
            }
            expect(token_kind::colon, "':'");
            parsed_type inner = parse_type_expr();
            // Prepend type params to domain
            if (!type_params.empty()) {
                std::vector<sort*> full_domain = type_params;
                full_domain.insert(full_domain.end(), inner.domain.begin(), inner.domain.end());
                return parsed_type(full_domain, inner.range);
            }
            return inner;
        }
        parsed_type prod = parse_type_product();
        if (accept(token_kind::gt_tok)) {
            parsed_type rhs = parse_type_expr();
            // prod is either a product (domain non-empty, range==nullptr) or a single sort (domain empty)
            std::vector<sort*> domain;
            if (!prod.domain.empty() && prod.range == nullptr) {
                domain = prod.domain;
            } else if (!prod.domain.empty() && prod.range != nullptr) {
                // A function type as domain element — wrap it
                domain.push_back(get_ho_sort(prod.domain, prod.range));
            } else {
                domain.push_back(prod.range);
            }
            if (!rhs.domain.empty()) {
                // Higher-order result type: A > (B > C) flattened to (A, B) > C
                domain.insert(domain.end(), rhs.domain.begin(), rhs.domain.end());
                return parsed_type(domain, rhs.range);
            }
            return parsed_type(domain, rhs.range);
        }
        // No '>' follows — must be a single type or a function type from parens
        if (!prod.domain.empty() && prod.range != nullptr) {
            // Function type from parenthesized expression
            return prod;
        }
        if (!prod.domain.empty() && prod.range == nullptr) {
            if (prod.domain.size() != 1)
                throw parse_error("type product must be followed by '>'");
            return parsed_type(prod.domain[0]);
        }
        return parsed_type(prod.range);
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

    // Grammar: <tff_plain_atomic>  ::= <functor> | <functor>(<tff_arguments>)
    //          <tff_arguments>     ::= <tff_term> | <tff_term>,<tff_arguments>
    //          <defined_term>      ::= <defined_atom> | <defined_functor>(<tff_arguments>)
    //          <defined_functor>   ::= $uminus | $sum | $difference | $product | ...
    //          <tff_conditional>   ::= $ite(<tff_logic_formula>,<tff_term>,<tff_term>)
    //          Handles: numerals, bound variables, let-bound names, defined functors,
    //          plain function/constant symbols, parenthesized formulas.
    expr_ref parse_term();

    // Grammar: (same as parse_term, primary productions)
    expr_ref parse_term_primary() {
        if (accept(token_kind::lparen)) {
            expr_ref e = parse_formula();
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
        // Check bound variables: uppercase (quantifier vars) AND lowercase (let-bound names)
        if (!m_last_name_quoted && find_bound(n, b)) {
            // For let-bound names followed by '(', apply via array select (function-style let)
            if (is(token_kind::lparen)) {
                next();
                expr_ref_vector fargs(m);
                if (!accept(token_kind::rparen)) {
                    do { fargs.push_back(parse_term()); } while (accept(token_kind::comma));
                    expect(token_kind::rparen, "')'");
                }
                expr_ref result = b;
                for (unsigned i = 0; i < fargs.size(); ++i)
                    result = expr_ref(m_array.mk_select(result, fargs.get(i)), m);
                return result;
            }
            return b;
        }
        if (!m_last_name_quoted && should_create_implicit_var(n))
            return expr_ref(get_or_create_implicit_var(n), m);

        expr_ref_vector args(m);
        // $ite needs special parsing: first arg is formula, rest are formulas (branches can be equalities)
        if (n == "$ite") {
            expect(token_kind::lparen, "'('");
            args.push_back(parse_formula());
            expect(token_kind::comma, "','");
            args.push_back(parse_formula());
            expect(token_kind::comma, "','");
            args.push_back(parse_formula());
            expect(token_kind::rparen, "')'");
        }
        else if (n == "$let") {
            return parse_let_expr();
        }
        else if (accept(token_kind::lparen)) {
            if (!accept(token_kind::rparen)) {
                do { args.push_back(parse_term()); } while (accept(token_kind::comma));
                expect(token_kind::rparen, "')'");
            }
        }

        // Table-driven prefix operator dispatch
        auto op_it = m_ops.find(n);
        if (op_it != m_ops.end() && !op_it->second.is_infix) {
            return op_it->second.builder(args);
        }

        func_decl* f = mk_decl_or_ho_const(n, args.size(), false);
        if (!args.empty()) coerce_args(f, args);
        return expr_ref(args.empty() ? m.mk_const(f) : m.mk_app(f, args.size(), args.data()), m);
    }

    // Grammar: <tff_logic_formula>   ::= <tff_unitary_formula> | <tff_binary_formula>
    //          <thf_logic_formula>   ::= <thf_unitary_formula> | <thf_binary_formula>
    //          Entry point for formula parsing (wraps parse_expr with default precedence).
    expr_ref parse_formula();

    // Grammar: <thf_apply_formula> ::= <thf_unitary_formula> @ <thf_unitary_formula>
    //                               | <thf_apply_formula> @ <thf_unitary_formula>
    //          @ is THF function application, encoded via array select.
    expr_ref apply_at(expr_ref e) {
        if (!is(token_kind::at_tok)) return e;
        
        // @ corresponds to array select (function application)
        while (accept(token_kind::at_tok)) {
            expr_ref arg = parse_at_arg();
            sort* e_sort = e->get_sort();
            if (!m_array.is_array(e_sort)) {
                sort* arg_sort = arg->get_sort();
                sort* result_sort = m.is_bool(arg_sort) ? m.mk_bool_sort() : m_univ;
                sort* arr_sort = m_array.mk_array_sort(arg_sort, result_sort);
                e = coerce_arg(e, arr_sort);
            } else {
                // Array but domain may not match arg sort — coerce arg
                sort* dom = get_array_domain(e_sort, 0);
                if (dom != arg->get_sort())
                    arg = coerce_arg(arg, dom);
            }
            e = expr_ref(m_array.mk_select(e, arg), m);
        }
        return e;
    }

    // Grammar: Argument to @ (THF application); may be an atom, negation, quantified formula,
    //          parenthesized formula, or lambda. Handles the right-operand of <thf_apply_formula>.
    // Parse an argument to @ — can be a term, a formula (negation, quantifier, parens with connectives), or a lambda
    expr_ref parse_at_arg() {
        if (accept(token_kind::not_tok)) {
            expr_ref e = parse_at_arg();
            return expr_ref(m.mk_not(ensure_bool(e)), m);
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
                    m_pinned_exprs.push_back(c);
                    vars.push_back(c);
                    scope.emplace(v, c);
                } while (accept(token_kind::comma));
                expect(token_kind::rbrack, "']'");
            }
            expect(token_kind::colon, "':'");
            m_bound.push_back(scope);
            // Quantifier body in @-arg should NOT consume @ — those belong to enclosing application
            bool save_in_at_arg = m_in_at_arg;
            m_in_at_arg = true;
            expr_ref body = parse_formula();
            m_in_at_arg = save_in_at_arg;
            m_bound.pop_back();
            return mk_quantifier(is_forall, vars, body);
        }
        // Simple term (name with optional function args) — no @ consumption here
        return parse_term_primary();
    }

    func_decl* mk_zero_arity_decl(symbol const& name, sort* range) {
        std::string name_str = name.str();
        if (range == m_univ)
            return mk_decl_or_ho_const(name_str, 0, false);
        if (m.is_bool(range))
            return mk_decl_or_ho_const(name_str, 0, true);
        std::string key = mk_decl_key(name_str, 0, 'c') + "\x1f" + std::to_string(range->get_id());
        auto it = m_decls.find(key);
        if (it != m_decls.end()) return it->second;
        func_decl* f = m.mk_func_decl(name, 0, static_cast<sort**>(nullptr), range);
        m_pinned_decls.push_back(f);
        m_decls.emplace(key, f);
        return f;
    }

    expr_ref coerce_zero_arity(app* a, sort* range) {
        return expr_ref(m.mk_const(mk_zero_arity_decl(a->get_decl()->get_name(), range)), m);
    }

    // Coerce an expression from Bool sort to m_univ by rebuilding with a function decl.
    // Works for both 0-arity constants and function applications.
    expr_ref coerce_to_univ(expr_ref const& e) {
        if (!is_app(e) || e->get_sort() == m_univ)
            return e;
        app* a = to_app(e);
        if (a->get_num_args() == 0)
            return coerce_zero_arity(a, m_univ);
        // Rebuild with a function (non-predicate) declaration
        func_decl* f = mk_decl(a->get_decl()->get_name().str(), a->get_num_args(), false);
        expr_ref_vector args(m);
        for (unsigned i = 0; i < a->get_num_args(); ++i)
            args.push_back(a->get_arg(i));
        coerce_args(f, args);
        return expr_ref(m.mk_app(f, args.size(), args.data()), m);
    }

    // Coerce two expressions to have the same sort for equality.
    // In TPTP, = is term equality and m_univ is the default sort.
    // If one side has Bool sort (parsed as predicate), coerce it to m_univ.
    // If sorts already match and are not Bool, returns lhs unchanged.
    expr_ref coerce_eq(expr_ref lhs, expr_ref& rhs) {
        // Coerce Bool-sorted operands to m_univ since = is term equality in TPTP
        if (m.is_bool(lhs->get_sort()) && is_app(lhs) && !m.is_true(lhs) && !m.is_false(lhs))
            lhs = coerce_to_univ(lhs);
        if (m.is_bool(rhs->get_sort()) && is_app(rhs) && !m.is_true(rhs) && !m.is_false(rhs))
            rhs = coerce_to_univ(rhs);

        if (lhs->get_sort() == rhs->get_sort()) return lhs;

        // Coerce 0-arity constants to match the other side's sort
        if (is_app(lhs) && to_app(lhs)->get_num_args() == 0 && lhs->get_sort() != rhs->get_sort()) {
            return coerce_zero_arity(to_app(lhs), rhs->get_sort());
        }
        if (is_app(rhs) && to_app(rhs)->get_num_args() == 0 && lhs->get_sort() != rhs->get_sort()) {
            rhs = coerce_zero_arity(to_app(rhs), lhs->get_sort());
            return lhs;
        }
        // Last resort: coerce both sides to have the same sort
        if (lhs->get_sort() != rhs->get_sort()) {
            // Prefer coercing to rhs sort, falling back to m_univ
            sort* target = rhs->get_sort();
            lhs = coerce_arg(lhs, target);
        }
        return lhs;
    }

    // Grammar: <txf_let_defn>  ::= <txf_let_LHS> := <tff_term>
    //          <txf_let_LHS>  ::= <tff_plain_atomic> | <txf_tuple>
    //          <thf_let_defn> ::= <thf_logic_formula> := <thf_logic_formula>
    // Parse a single let definition: name := value or name(X,Y,...) := value.
    // For function-style definitions, wraps value in lambdas over the parameter variables.
    std::pair<std::string, expr_ref> parse_single_let_defn() {
        std::string name = parse_name();
        std::vector<app*> param_vars;
        std::unordered_map<std::string, app*> param_scope;
        if (accept(token_kind::lparen)) {
            if (!accept(token_kind::rparen)) {
                do {
                    std::string v = parse_name();
                    app* c = m.mk_const(symbol(v), m_univ);
                    m_pinned_exprs.push_back(c);
                    param_vars.push_back(c);
                    param_scope.emplace(v, c);
                } while (accept(token_kind::comma));
                expect(token_kind::rparen, "')'");
            }
        }
        // Parse ':='
        expect(token_kind::colon, "':'");
        expect(token_kind::equal_tok, "'='");
        // Bind parameter variables for parsing the RHS
        if (!param_scope.empty())
            m_bound.push_back(param_scope);
        expr_ref value = parse_formula();
        if (!param_scope.empty())
            m_bound.pop_back();
        // For function-style definitions, wrap value in lambdas
        if (!param_vars.empty()) {
            expr_ref result = value;
            for (int i = (int)param_vars.size() - 1; i >= 0; --i) {
                expr_ref abs_body(m);
                expr_abstract(m, 0, 1, (expr* const*)&param_vars[i], result, abs_body);
                sort* s = param_vars[i]->get_sort();
                symbol nm = param_vars[i]->get_decl()->get_name();
                result = expr_ref(m.mk_lambda(1, &s, &nm, abs_body), m);
            }
            value = result;
        }
        return {name, std::move(value)};
    }

    // Parse $let(types, defns, body)
    // Grammar:
    //   thf_let  ::= $let(thf_let_types, thf_let_defns, thf_logic_formula)
    //   txf_let  ::= $let(txf_let_types, txf_let_defns, tff_term)
    //   let_types ::= atom_typing | [atom_typing_list]
    //   let_defns ::= let_defn | [let_defn_list]
    //   let_defn  ::= LHS := RHS
    expr_ref parse_let_expr() {
        expect(token_kind::lparen, "'('");

        // --- Part 1: Parse type declarations ---
        std::vector<std::string> let_names;
        std::vector<sort*> let_sorts;

        auto parse_one_typing = [&]() {
            std::string name = parse_name();
            if (accept(token_kind::lparen)) {
                if (!accept(token_kind::rparen)) {
                    do { parse_type_expr(); } while (accept(token_kind::comma));
                    expect(token_kind::rparen, "')'");
                }
            }
            expect(token_kind::colon, "':'");
            parsed_type t = parse_type_expr();
            sort* s = t.domain.empty() ? t.range : get_ho_sort(t.domain, t.range);
            let_names.push_back(name);
            let_sorts.push_back(s);
        };

        if (is(token_kind::lbrack)) {
            next();
            if (!accept(token_kind::rbrack)) {
                do { parse_one_typing(); } while (accept(token_kind::comma));
                expect(token_kind::rbrack, "']'");
            }
        } else {
            parse_one_typing();
        }

        expect(token_kind::comma, "','");

        // --- Create bound constants for all let-bound names ---
        std::unordered_map<std::string, app*> scope;
        for (unsigned i = 0; i < let_names.size(); ++i) {
            app* c = m.mk_const(symbol(let_names[i]), let_sorts[i]);
            m_pinned_exprs.push_back(c);
            scope.emplace(let_names[i], c);
        }

        // --- Part 2: Parse definitions ---
        // Let-bound names are NOT in scope during RHS parsing (non-recursive semantics).
        // Each definition has its own ':=' operator.
        std::vector<std::pair<std::string, expr_ref>> defns;

        if (is(token_kind::lbrack)) {
            next();
            if (!accept(token_kind::rbrack)) {
                do {
                    defns.push_back(parse_single_let_defn());
                } while (accept(token_kind::comma));
                expect(token_kind::rbrack, "']'");
            }
        } else {
            defns.push_back(parse_single_let_defn());
        }

        expect(token_kind::comma, "','");

        // --- Part 3: Parse body with let-bound names in scope ---
        m_bound.push_back(scope);
        expr_ref body = parse_formula();
        m_bound.pop_back();
        expect(token_kind::rparen, "')'");

        // --- Substitute all let bindings in the body ---
        expr_safe_replace replacer(m);
        for (auto& [defn_name, defn_value] : defns) {
            auto it = scope.find(defn_name);
            if (it != scope.end())
                replacer.insert(it->second, defn_value.get());
        }
        expr_ref result(m);
        replacer(body, result);
        return result;
    }

    // Grammar: <tff_atomic_formula> ::= <tff_plain_atomic_formula> | <tff_defined_atomic_formula>
    //                                | <tff_system_atomic_formula>
    //          <tff_plain_atomic_formula> ::= <tff_plain_atomic>
    //          <tff_defined_atomic_formula> ::= <tff_defined_plain_formula> | <tff_defined_infix_formula>
    //          <tff_defined_plain_formula> ::= $true | $false | <defined_pred>(<tff_arguments>)
    //          <defined_pred>     ::= $less | $lesseq | $greater | $greatereq | $is_int | $is_rat | ...
    //          <defined_infix_pred> ::= = | !=
    //          Also handles: let-bound name resolution, implicit variable creation.
    expr_ref parse_atomic_formula() {
        if (accept(token_kind::lparen)) {
            // Check for parenthesized connective used as higher-order term: (~), (&), (|), etc.
            if (is(token_kind::not_tok) || is(token_kind::and_tok) || is(token_kind::or_tok) ||
                is(token_kind::implies_tok) || is(token_kind::iff_tok) || is(token_kind::xor_tok)) {
                std::string op_text;
                unsigned arity = 2;
                switch (m_curr.kind) {
                case token_kind::not_tok: op_text = "~"; arity = 1; break;
                case token_kind::and_tok: op_text = "&"; break;
                case token_kind::or_tok: op_text = "|"; break;
                case token_kind::implies_tok: op_text = "=>"; break;
                case token_kind::iff_tok: op_text = "<=>"; break;
                case token_kind::xor_tok: op_text = "<~>"; break;
                default: break;
                }
                token saved = m_curr;
                next();
                if (accept(token_kind::rparen)) {
                    // Parenthesized connective: treat as HO constant with array sort
                    sort* bool_sort = m.mk_bool_sort();
                    sort* ho_sort;
                    if (arity == 1)
                        ho_sort = m_array.mk_array_sort(bool_sort, bool_sort);
                    else
                        ho_sort = m_array.mk_array_sort(bool_sort, m_array.mk_array_sort(bool_sort, bool_sort));
                    std::string key = mk_decl_key(op_text, 0, 'h');
                    auto it = m_decls.find(key);
                    func_decl* f;
                    if (it != m_decls.end()) {
                        f = it->second;
                    } else {
                        f = m.mk_func_decl(symbol(op_text), 0, static_cast<sort**>(nullptr), ho_sort);
                        m_pinned_decls.push_back(f);
                        m_decls.emplace(key, f);
                    }
                    return expr_ref(m.mk_const(f), m);
                }
                // Not a parenthesized connective — lparen was consumed and connective was consumed
                // but ')' didn't follow. Parse as formula with the connective already consumed.
                expr_ref inner(m);
                if (saved.kind == token_kind::not_tok) {
                    expr_ref e = parse_formula();
                    inner = expr_ref(m.mk_not(e), m);
                } else {
                    // Binary connective at start of parens — shouldn't happen in valid TPTP
                    throw parse_error("unexpected connective after '(' at " + loc());
                }
                expect(token_kind::rparen, "')'");
                return inner;
            }
            // Parentheses create a new scope for @ consumption
            bool save_in_at_arg = m_in_at_arg;
            m_in_at_arg = false;
            expr_ref e = parse_formula();
            expect(token_kind::rparen, "')'");
            m_in_at_arg = save_in_at_arg;
            return e;
        }

        // Handle negative numerals in formula position: -2 = $uminus(2)
        if (accept(token_kind::minus_tok)) {
            expr_ref t = parse_term();
            return expr_ref(m_arith.mk_uminus(t), m);
        }

        // Tuple/list in formula position: [t1, t2, ...] — return first element for simplicity
        if (accept(token_kind::lbrack)) {
            if (accept(token_kind::rbrack))
                return expr_ref(m.mk_const(symbol("$nil"), m_univ), m);
            expr_ref first = parse_formula();
            while (accept(token_kind::comma))
                parse_formula(); // consume remaining elements
            expect(token_kind::rbrack, "']'");
            return first;
        }

        std::string n = parse_name();
        if (n == "$true") return expr_ref(m.mk_true(), m);
        if (n == "$false") return expr_ref(m.mk_false(), m);

        if (is_nonempty_digit_string(n)) {
            return parse_numeral_from_name(n);
        }

        // Check if name is let-bound (works for both uppercase vars and lowercase let-bound names)
        {
            expr_ref b(m);
            if (!m_last_name_quoted && find_bound(n, b)) {
                // If followed by '(' args, apply via array select (function-style let)
                if (is(token_kind::lparen)) {
                    next();
                    expr_ref_vector fargs(m);
                    if (!accept(token_kind::rparen)) {
                        do { fargs.push_back(parse_term()); } while (accept(token_kind::comma));
                        expect(token_kind::rparen, "')'");
                    }
                    expr_ref result = b;
                    for (unsigned i = 0; i < fargs.size(); ++i)
                        result = expr_ref(m_array.mk_select(result, fargs.get(i)), m);
                    return result;
                }
                return b;
            }
        }

        // Choice operators @+ and @- with quantifier-like syntax: @+[X: T] : body
        if ((n == "@+" || n == "@-") && is(token_kind::lbrack)) {
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
                    m_pinned_exprs.push_back(c);
                    vars.push_back(c);
                    scope.emplace(v, c);
                } while (accept(token_kind::comma));
                expect(token_kind::rbrack, "']'");
            }
            expect(token_kind::colon, "':'");
            m_bound.push_back(scope);
            expr_ref body = parse_formula();
            m_bound.pop_back();
            // Approximate choice as existential quantification
            return mk_quantifier(false, vars, body);
        }

        expr_ref_vector args(m);
        // $ite needs special parsing: first arg is formula, rest are formulas (branches can be equalities)
        if (n == "$ite") {
            expect(token_kind::lparen, "'('");
            args.push_back(parse_formula());
            expect(token_kind::comma, "','");
            args.push_back(parse_formula());
            expect(token_kind::comma, "','");
            args.push_back(parse_formula());
            expect(token_kind::rparen, "')'");
        }
        else if (n == "$let") {
            return parse_let_expr();
        }
        else if (accept(token_kind::lparen)) {
            if (!accept(token_kind::rparen)) {
                do { args.push_back(parse_term()); } while (accept(token_kind::comma));
                expect(token_kind::rparen, "')'");
            }
        }

        // Table-driven prefix operator dispatch
        auto op_it = m_ops.find(n);
        if (op_it != m_ops.end() && !op_it->second.is_infix) {
            return op_it->second.builder(args);
        }

        expr_ref lhs(m);
        bool has_lhs = false;
        if (args.empty()) {
            if (!m_last_name_quoted && should_create_implicit_var(n)) {
                lhs = expr_ref(get_or_create_implicit_var(n), m);
                has_lhs = true;
            }
        }

        if (has_lhs)
            return lhs;

        auto typed = m_typed_decls.find(mk_typed_key(n, args.size()));
        if (typed != m_typed_decls.end()) {
            func_decl* f = args.empty() ? mk_decl_or_ho_const(n, 0, false) : mk_decl(n, args.size(), false);
            if (!args.empty()) coerce_args(f, args);
            return expr_ref(args.empty() ? m.mk_const(f) : m.mk_app(f, args.size(), args.data()), m);
        }

        if (args.empty() && (is(token_kind::equal_tok) || is(token_kind::neq_tok))) {
            func_decl* f = mk_decl_or_ho_const(n, 0, false);
            return expr_ref(m.mk_const(f), m);
        }

        func_decl* pred = mk_decl_or_ho_const(n, args.size(), true);
        if (!args.empty()) coerce_args(pred, args);
        return expr_ref(args.empty() ? m.mk_const(pred) : m.mk_app(pred, args.size(), args.data()), m);
    }

    // Grammar: <thf_abstraction> ::= ^ [<thf_variable_list>] : <thf_unitary_formula>
    //          <thf_variable_list> ::= <thf_variable> | <thf_variable>,<thf_variable_list>
    //          <thf_variable>      ::= <thf_typed_variable> | <variable>
    //          Produces Z3 lambda terms (array-valued).
    // Parse THF lambda expression: ^ [X: T, ...] : body
    // Uses Z3's native lambda construct, which produces array terms.
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
                m_pinned_exprs.push_back(c);
                vars.push_back(c);
                scope.emplace(v, c);
            } while (accept(token_kind::comma));
            expect(token_kind::rbrack, "']'");
        }
        expect(token_kind::colon, "':'");
        m_bound.push_back(scope);
        // Lambda body does NOT consume @ — @ belongs to the enclosing application
        bool save_in_at_arg = m_in_at_arg;
        m_in_at_arg = true;
        expr_ref body = parse_formula();
        m_in_at_arg = save_in_at_arg;
        m_bound.pop_back();
        if (vars.empty())
            return body;
        // Create nested single-variable lambdas (curried) to match our curried array encoding.
        // ^[X:A, Y:B] : body  becomes  ^[X:A] : (^[Y:B] : body)  with sort Array(A, Array(B, body_sort))
        expr_ref result = body;
        for (int i = (int)vars.size() - 1; i >= 0; --i) {
            expr_ref abs_body(m);
            expr_abstract(m, 0, 1, (expr* const*)&vars[i], result, abs_body);
            sort* s = vars[i]->get_sort();
            symbol nm = vars[i]->get_decl()->get_name();
            result = expr_ref(m.mk_lambda(1, &s, &nm, abs_body), m);
        }
        return result;
    }

    // Grammar: <tff_unary_formula>   ::= <tff_prefix_unary> | <tff_infix_unary>
    //          <tff_prefix_unary>   ::= <unary_connective> <tff_preunit_formula>
    //          <unary_connective>   ::= ~
    //          <tff_quantified_formula> ::= <fof_quantifier> [<tff_variable_list>] : <tff_unit_formula>
    //          <thf_quantified_formula> ::= <thf_quantification> <thf_unitary_formula>
    //          <fof_quantifier>     ::= ! | ?
    //          Also handles: $ite, $let, lambda (^), parenthesized formulas, and atomic formulas.
    expr_ref parse_unary_formula() {
        if (accept(token_kind::not_tok)) {
            expr_ref e = parse_unary_formula();
            return expr_ref(m.mk_not(ensure_bool(e)), m);
        }

        // Modal box operators: [.] or [name] — only when followed by ']' (not a tuple)
        if (is(token_kind::lbrack)) {
            // Peek: if [.] pattern, parse as modal; if [name] (no comma), parse as modal
            // Otherwise fall through to parse_atomic_formula which handles tuples
            token saved = m_curr;
            next(); // consume '['
            if (accept(token_kind::dot)) {
                expect(token_kind::rbrack, "']'");
                expr_ref sub = parse_unary_formula();
                func_decl* f = mk_modal_op("box");
                return expr_ref(m.mk_app(f, sub.get()), m);
            }
            if ((is(token_kind::id) || is(token_kind::str)) && !is(token_kind::comma)) {
                std::string mod_name = "box_" + m_curr.text;
                std::string first_name = m_curr.text;
                next();
                if (accept(token_kind::rbrack)) {
                    expr_ref sub = parse_unary_formula();
                    func_decl* f = mk_modal_op(mod_name);
                    return expr_ref(m.mk_app(f, sub.get()), m);
                }
                // Not a simple [name] modal — it's a tuple starting with this name.
                // We've consumed '[' and a name. Parse the name as an expression and
                // continue as tuple.
                expr_ref first(m);
                expr_ref b(m);
                if (is_var_name(first_name) && find_bound(first_name, b))
                    first = b;
                else if (should_create_implicit_var(first_name))
                    first = expr_ref(get_or_create_implicit_var(first_name), m);
                else {
                    func_decl* f = mk_decl_or_ho_const(first_name, 0, false);
                    first = expr_ref(m.mk_const(f), m);
                }
                while (accept(token_kind::comma))
                    parse_formula(); // consume remaining elements
                expect(token_kind::rbrack, "']'");
                return first;
            }
            // Not a modal operator — it's a tuple [expr, expr, ...]
            // We already consumed '[', so parse as tuple inline
            if (accept(token_kind::rbrack))
                return expr_ref(m.mk_const(symbol("$nil"), m_univ), m);
            expr_ref first = parse_formula();
            while (accept(token_kind::comma))
                parse_formula(); // consume remaining elements
            expect(token_kind::rbrack, "']'");
            return first;
        }

        // Diamond modality: <.>, <name>
        if (is(token_kind::lt_tok)) {
            next();
            std::string mod_name = "dia";
            if (accept(token_kind::dot)) {
                mod_name = "dia";
            } else if (is(token_kind::id) || is(token_kind::str)) {
                mod_name = "dia_" + m_curr.text;
                next();
            }
            expect(token_kind::gt_tok, "'>'");
            expr_ref sub = parse_unary_formula();
            func_decl* f = mk_modal_op(mod_name);
            return expr_ref(m.mk_app(f, sub.get()), m);
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
                    // Monomorphize: $tType-sorted variables become U-sorted
                    // and register them as sorts for subsequent type references
                    if (is_ttype(s)) {
                        s = m_univ;
                        m_sorts.insert_or_assign(v, m_univ);
                    }
                    app* c = m.mk_const(symbol(v), s);
                    m_pinned_exprs.push_back(c);
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

        // Type quantification in formula context: !>[A: $tType, ...] : body
        // Erase type variables and parse body as formula
        if (is(token_kind::type_forall_tok) || is(token_kind::type_exists_tok)) {
            next();
            expect(token_kind::lbrack, "'['");
            if (!accept(token_kind::rbrack)) {
                do {
                    std::string tv = parse_name();
                    if (accept(token_kind::colon))
                        parse_type_expr(); // consume $tType annotation
                    m_sorts.insert_or_assign(tv, m_univ);
                } while (accept(token_kind::comma));
                expect(token_kind::rbrack, "']'");
            }
            expect(token_kind::colon, "':'");
            return parse_formula();
        }

        return parse_atomic_formula();
    }

    // Grammar: <tff_binary_formula>  ::= <tff_binary_nonassoc> | <tff_binary_assoc>
    //          <tff_binary_nonassoc> ::= <tff_unit_formula> <nonassoc_connective> <tff_unit_formula>
    //          <tff_binary_assoc>    ::= <tff_or_formula> | <tff_and_formula>
    //          <nonassoc_connective> ::= <=> | => | <= | <~> | ~<vline> | ~&
    //          <tff_or_formula>      ::= <tff_unit_formula> <vline> <tff_unit_formula>
    //                                  | <tff_or_formula> <vline> <tff_unit_formula>
    //          <tff_and_formula>     ::= <tff_unit_formula> & <tff_unit_formula>
    //                                  | <tff_and_formula> & <tff_unit_formula>
    //          Implements a Pratt-style (precedence climbing) parser for binary connectives.
    expr_ref parse_expr(unsigned min_prec, bool consume_at = true) {
        expr_ref e = parse_unary_formula();
        for (;;) {
            // Handle @ (function application) with highest precedence
            // But NOT when we're inside a lambda body that's an @ argument
            if (consume_at && !m_in_at_arg && is(token_kind::at_tok)) {
                next();
                expr_ref arg = parse_at_arg();
                sort* e_sort = e->get_sort();
                if (!m_array.is_array(e_sort)) {
                    // LHS doesn't have array sort — coerce it to Array(arg_sort, result_sort)
                    sort* arg_sort = arg->get_sort();
                    // If arg is Bool-sorted, result is likely Bool too (modal/connective application)
                    sort* result_sort = m.is_bool(arg_sort) ? m.mk_bool_sort() : m_univ;
                    sort* arr_sort = m_array.mk_array_sort(arg_sort, result_sort);
                    e = coerce_arg(e, arr_sort);
                } else {
                    // Array but domain may not match arg sort — coerce arg
                    sort* dom = get_array_domain(e_sort, 0);
                    if (dom != arg->get_sort())
                        arg = coerce_arg(arg, dom);
                }
                e = expr_ref(m_array.mk_select(e, arg), m);
                continue;
            }
            char const* op_name = token_to_op_name();
            if (!op_name) break;
            auto it = m_ops.find(op_name);
            if (it == m_ops.end() || !it->second.is_infix) break;
            if (it->second.precedence < min_prec) break;
            next(); // consume the operator token
            unsigned next_prec = it->second.right_assoc ? it->second.precedence : it->second.precedence + 1;
            expr_ref rhs = parse_expr(next_prec, consume_at);
            expr_ref_vector args(m);
            args.push_back(e);
            args.push_back(rhs);
            e = it->second.builder(args);
        }
        return e;
    }

    // Grammar: <tff_atom_typing>    ::= <untyped_atom> : <tff_top_level_type>
    //          <thf_atom_typing>    ::= <untyped_atom> : <thf_top_level_type>
    //          <untyped_atom>       ::= <constant> | <system_constant>
    //          Declares a new constant or type with the given type signature.
    void parse_type_decl_formula() {
        unsigned lparen_count = 0;
        while (accept(token_kind::lparen)) ++lparen_count;
        std::string name = parse_name();
        expect(token_kind::colon, "':'");
        parsed_type t = parse_type_expr();
        while (lparen_count-- > 0)
            expect(token_kind::rparen, "')'");

        if (t.domain.empty() && is_ttype(t.range)) {
            // Sort declaration: monomorphize to m_univ
            m_sorts.insert_or_assign(name, m_univ);
            return;
        }

        // Monomorphize: replace $tType in domain/range with m_univ
        for (auto& s : t.domain) {
            if (is_ttype(s)) s = m_univ;
        }
        if (t.range && is_ttype(t.range)) t.range = m_univ;

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

    // Grammar: <include> ::= include(<file_name><formula_selection>).
    //          <formula_selection> ::= ,[<name_list>] | <null>
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

    // Grammar: <annotated_formula>  ::= <tff_annotated> | <thf_annotated> | <fof_annotated> | <cnf_annotated>
    //          <tff_annotated>      ::= tff(<name>,<formula_role>,<tff_formula><annotations>).
    //          <thf_annotated>      ::= thf(<name>,<formula_role>,<thf_formula><annotations>).
    //          <formula_role>       ::= axiom | hypothesis | definition | assumption | lemma |
    //                                   theorem | corollary | conjecture | negated_conjecture |
    //                                   plain | type | ...
    //          <annotations>        ::= ,<source><optional_info> | <null>
    void parse_annotated() {
        expect(token_kind::lparen, "'('");
        parse_name();
        expect(token_kind::comma, "','");
        std::string role = to_lower(parse_name());
        expect(token_kind::comma, "','");

        if (role == "type") {
            parse_type_decl_formula();
        }
        else if (role == "logic") {
            // Modal logic declarations ($modal == [...]) — skip the formula body
            skip_annotations_until_rparen();
        }
        else {
            try {
                implicit_var_scope implicit_scope;
                scoped_implicit_vars scoped(*this, implicit_scope);
                expr_ref f = parse_formula();
                if (!implicit_scope.order.empty()) {
                    f = mk_quantifier(true, implicit_scope.order, f);
                }
                // Coerce to Bool if needed (HO encoding may produce U-sorted formulas)
                if (!m.is_bool(f))
                    f = ensure_bool(f);
                if (role == "conjecture") {
                    m_has_conjecture = true;
                    f = m.mk_not(f);
                }
                m_cmd.assert_expr(f);
            } catch (z3_exception const& ex) {
                // Sort mismatch or other semantic error in this formula — skip it
                IF_VERBOSE(2, verbose_stream() << "skipping formula due to: " << ex.what() << "\n");
                // Skip to '.' to resync the parser for the next annotated formula
                while (!is(token_kind::eof_tok) && !is(token_kind::dot))
                    next();
                if (is(token_kind::dot)) next();
                return;
            }
        }

        if (accept(token_kind::comma)) {
            skip_annotations_until_rparen();
        }
        expect(token_kind::rparen, "')'");
        expect(token_kind::dot, "'.'");
    }

    // Grammar: <TPTP_file>    ::= <TPTP_input>*
    //          <TPTP_input>   ::= <annotated_formula> | <include>
    //          Dispatches to parse_annotated() or parse_include() based on keyword.
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
        m_array(m),
        m_univ(m.mk_uninterpreted_sort(symbol("U"))),
        m_pinned_sorts(m),
        m_pinned_decls(m),
        m_pinned_exprs(m) {
        m_pinned_sorts.push_back(m_univ);
        sort* tType = m.mk_uninterpreted_sort(symbol("$tType"));
        m_pinned_sorts.push_back(tType);
        m_sorts.emplace("$tType", tType);
        m_sorts.emplace("$i", m_univ);
        m_sorts.emplace("$o", m.mk_bool_sort());
        m_sorts.emplace("$int", m_arith.mk_int());
        m_sorts.emplace("$rat", m_arith.mk_real());
        m_sorts.emplace("$real", m_arith.mk_real());
        init_op_table();
    }

    void init_op_table() {
        // Prefix arithmetic predicates (is_infix=false, precedence=0)
        m_ops["$less"] = { false, 0, false, [&](expr_ref_vector const& args) -> expr_ref {
            check_arith_arity(args, 2, "$less");
            auto [a, b] = coerce_arith2(args);
            return expr_ref(m_arith.mk_lt(a, b), m);
        }};
        m_ops["$lesseq"] = { false, 0, false, [&](expr_ref_vector const& args) -> expr_ref {
            check_arith_arity(args, 2, "$lesseq");
            auto [a, b] = coerce_arith2(args);
            return expr_ref(m_arith.mk_le(a, b), m);
        }};
        m_ops["$greater"] = { false, 0, false, [&](expr_ref_vector const& args) -> expr_ref {
            check_arith_arity(args, 2, "$greater");
            auto [a, b] = coerce_arith2(args);
            return expr_ref(m_arith.mk_gt(a, b), m);
        }};
        m_ops["$greatereq"] = { false, 0, false, [&](expr_ref_vector const& args) -> expr_ref {
            check_arith_arity(args, 2, "$greatereq");
            auto [a, b] = coerce_arith2(args);
            return expr_ref(m_arith.mk_ge(a, b), m);
        }};
        m_ops["$uminus"] = { false, 0, false, [&](expr_ref_vector const& args) -> expr_ref {
            check_arith_arity(args, 1, "$uminus");
            return expr_ref(m_arith.mk_uminus(args[0]), m);
        }};
        m_ops["$sum"] = { false, 0, false, [&](expr_ref_vector const& args) -> expr_ref {
            check_arith_arity(args, 2, "$sum");
            auto [a, b] = coerce_arith2(args);
            return expr_ref(m_arith.mk_add(a, b), m);
        }};
        m_ops["$plus"] = { false, 0, false, [&](expr_ref_vector const& args) -> expr_ref {
            check_arith_arity(args, 2, "$plus");
            auto [a, b] = coerce_arith2(args);
            return expr_ref(m_arith.mk_add(a, b), m);
        }};
        m_ops["$difference"] = { false, 0, false, [&](expr_ref_vector const& args) -> expr_ref {
            check_arith_arity(args, 2, "$difference");
            auto [a, b] = coerce_arith2(args);
            return expr_ref(m_arith.mk_sub(a, b), m);
        }};
        m_ops["$product"] = { false, 0, false, [&](expr_ref_vector const& args) -> expr_ref {
            check_arith_arity(args, 2, "$product");
            auto [a, b] = coerce_arith2(args);
            return expr_ref(m_arith.mk_mul(a, b), m);
        }};
        m_ops["$quotient"] = { false, 0, false, [&](expr_ref_vector const& args) -> expr_ref {
            check_arith_arity(args, 2, "$quotient");
            return mk_quotient(args);
        }};
        m_ops["$quotient_e"] = { false, 0, false, [&](expr_ref_vector const& args) -> expr_ref {
            check_arith_arity(args, 2, "$quotient_e");
            return mk_quotient(args);
        }};
        m_ops["$quotient_t"] = { false, 0, false, [&](expr_ref_vector const& args) -> expr_ref {
            check_arith_arity(args, 2, "$quotient_t");
            return mk_quotient(args);
        }};
        m_ops["$quotient_f"] = { false, 0, false, [&](expr_ref_vector const& args) -> expr_ref {
            check_arith_arity(args, 2, "$quotient_f");
            return mk_quotient(args);
        }};
        m_ops["$remainder_e"] = { false, 0, false, [&](expr_ref_vector const& args) -> expr_ref {
            check_arith_arity(args, 2, "$remainder_e");
            return expr_ref(m_arith.mk_mod(args[0], args[1]), m);
        }};
        m_ops["$remainder_t"] = { false, 0, false, [&](expr_ref_vector const& args) -> expr_ref {
            check_arith_arity(args, 2, "$remainder_t");
            return expr_ref(m_arith.mk_mod(args[0], args[1]), m);
        }};
        m_ops["$remainder_f"] = { false, 0, false, [&](expr_ref_vector const& args) -> expr_ref {
            check_arith_arity(args, 2, "$remainder_f");
            return expr_ref(m_arith.mk_mod(args[0], args[1]), m);
        }};
        m_ops["$floor"] = { false, 0, false, [&](expr_ref_vector const& args) -> expr_ref {
            check_arith_arity(args, 1, "$floor");
            expr_ref a(args[0], m);
            if (m_arith.is_int(a)) return a;
            return expr_ref(m_arith.mk_to_int(a), m);
        }};
        m_ops["$ceiling"] = { false, 0, false, [&](expr_ref_vector const& args) -> expr_ref {
            check_arith_arity(args, 1, "$ceiling");
            expr_ref a(args[0], m);
            if (m_arith.is_int(a)) return a;
            // ceiling(x) = -floor(-x)
            return expr_ref(m_arith.mk_uminus(m_arith.mk_to_int(m_arith.mk_uminus(a))), m);
        }};
        m_ops["$truncate"] = { false, 0, false, [&](expr_ref_vector const& args) -> expr_ref {
            check_arith_arity(args, 1, "$truncate");
            expr_ref a(args[0], m);
            if (m_arith.is_int(a)) return a;
            // truncate(x) = if x >= 0 then floor(x) else ceiling(x)
            expr_ref zero(m_arith.mk_real(0), m);
            expr_ref fl(m_arith.mk_to_int(a), m);
            expr_ref neg_fl(m_arith.mk_uminus(m_arith.mk_to_int(m_arith.mk_uminus(a))), m);
            return expr_ref(m.mk_ite(m_arith.mk_ge(a, zero), fl, neg_fl), m);
        }};
        m_ops["$round"] = { false, 0, false, [&](expr_ref_vector const& args) -> expr_ref {
            check_arith_arity(args, 1, "$round");
            expr_ref a(args[0], m);
            if (m_arith.is_int(a)) return a;
            // round to nearest even
            expr_ref i(m_arith.mk_to_int(a), m);
            expr_ref half(m_arith.mk_add(m_arith.mk_to_real(i), m_arith.mk_numeral(rational(1, 2), false)), m);
            expr_ref i1(m_arith.mk_add(i, m_arith.mk_int(1)), m);
            expr_ref is_even(m.mk_eq(m_arith.mk_mod(i, m_arith.mk_int(2)), m_arith.mk_int(0)), m);
            return expr_ref(m.mk_ite(m_arith.mk_gt(a, half), i1,
                           m.mk_ite(m.mk_eq(a, half), m.mk_ite(is_even, i, i1), i)), m);
        }};
        m_ops["$to_int"] = { false, 0, false, [&](expr_ref_vector const& args) -> expr_ref {
            check_arith_arity(args, 1, "$to_int");
            expr_ref a(args[0], m);
            if (m_arith.is_int(a)) return a;
            return expr_ref(m_arith.mk_to_int(a), m);
        }};
        m_ops["$to_real"] = { false, 0, false, [&](expr_ref_vector const& args) -> expr_ref {
            check_arith_arity(args, 1, "$to_real");
            expr_ref a(args[0], m);
            if (m_arith.is_real(a)) return a;
            return expr_ref(m_arith.mk_to_real(a), m);
        }};
        m_ops["$to_rat"] = { false, 0, false, [&](expr_ref_vector const& args) -> expr_ref {
            check_arith_arity(args, 1, "$to_rat");
            expr_ref a(args[0], m);
            if (m_arith.is_real(a)) return a;
            return expr_ref(m_arith.mk_to_real(a), m);
        }};
        m_ops["$is_int"] = { false, 0, false, [&](expr_ref_vector const& args) -> expr_ref {
            check_arith_arity(args, 1, "$is_int");
            return expr_ref(m_arith.mk_is_int(args[0]), m);
        }};
        m_ops["$is_rat"] = { false, 0, false, [&](expr_ref_vector const& args) -> expr_ref {
            check_arith_arity(args, 1, "$is_rat");
            expr_ref a(args[0], m);
            return mk_is_rat(a);
        }};
        m_ops["$distinct"] = { false, 0, false, [&](expr_ref_vector const& args) -> expr_ref {
            if (args.size() == 2) return expr_ref(m.mk_not(m.mk_eq(args[0], args[1])), m);
            return expr_ref(m.mk_distinct(args.size(), args.data()), m);
        }};
        m_ops["$ite"] = { false, 0, false, [&](expr_ref_vector const& args) -> expr_ref {
            check_arith_arity(args, 3, "$ite");
            expr_ref cond(args[0], m), t(args[1], m), f(args[2], m);
            if (!m.is_bool(cond))
                throw parse_error("$ite expects Bool condition as first argument");
            return expr_ref(m.mk_ite(cond, t, f), m);
        }};
        m_ops["$abs"] = { false, 0, false, [&](expr_ref_vector const& args) -> expr_ref {
            check_arith_arity(args, 1, "$abs");
            expr_ref a(args[0], m);
            if (!m_arith.is_int_real(a))
                throw parse_error("$abs expects arithmetic argument");
            expr_ref zero(m_arith.is_int(a) ? m_arith.mk_int(0) : m_arith.mk_numeral(rational(0), false), m);
            return expr_ref(m.mk_ite(m_arith.mk_ge(a, zero), a, expr_ref(m_arith.mk_uminus(a), m)), m);
        }};
        m_ops["$true"] = { false, 0, false, [&](expr_ref_vector const&) -> expr_ref {
            return expr_ref(m.mk_true(), m);
        }};
        m_ops["$false"] = { false, 0, false, [&](expr_ref_vector const&) -> expr_ref {
            return expr_ref(m.mk_false(), m);
        }};

        // Infix logical operators (token-based, matched by token_to_op_name)
        m_ops["<=>"] = { true, PREC_IFF, false, [&](expr_ref_vector const& args) -> expr_ref {
            return expr_ref(m.mk_iff(ensure_bool(args[0]), ensure_bool(args[1])), m);
        }};
        m_ops["<~>"] = { true, PREC_IFF, false, [&](expr_ref_vector const& args) -> expr_ref {
            return expr_ref(m.mk_not(m.mk_iff(ensure_bool(args[0]), ensure_bool(args[1]))), m);
        }};
        m_ops["=>"] = { true, PREC_IMPLIES, true, [&](expr_ref_vector const& args) -> expr_ref {
            return expr_ref(m.mk_implies(ensure_bool(args[0]), ensure_bool(args[1])), m);
        }};
        m_ops["<="] = { true, PREC_IMPLIES, false, [&](expr_ref_vector const& args) -> expr_ref {
            return expr_ref(m.mk_implies(ensure_bool(args[1]), ensure_bool(args[0])), m);
        }};
        m_ops["|"] = { true, PREC_OR, false, [&](expr_ref_vector const& args) -> expr_ref {
            return expr_ref(m.mk_or(ensure_bool(args[0]), ensure_bool(args[1])), m);
        }};
        m_ops["~|"] = { true, PREC_OR, false, [&](expr_ref_vector const& args) -> expr_ref {
            return expr_ref(m.mk_not(m.mk_or(ensure_bool(args[0]), ensure_bool(args[1]))), m);
        }};
        m_ops["&"] = { true, PREC_AND, false, [&](expr_ref_vector const& args) -> expr_ref {
            return expr_ref(m.mk_and(ensure_bool(args[0]), ensure_bool(args[1])), m);
        }};
        m_ops["~&"] = { true, PREC_AND, false, [&](expr_ref_vector const& args) -> expr_ref {
            return expr_ref(m.mk_not(m.mk_and(ensure_bool(args[0]), ensure_bool(args[1]))), m);
        }};
        m_ops["="] = { true, PREC_EQ, false, [&](expr_ref_vector const& args) -> expr_ref {
            expr_ref lhs(args[0], m);
            expr_ref rhs(args[1], m);
            lhs = coerce_eq(lhs, rhs);
            return expr_ref(m.mk_eq(lhs, rhs), m);
        }};
        m_ops["!="] = { true, PREC_EQ, false, [&](expr_ref_vector const& args) -> expr_ref {
            expr_ref lhs(args[0], m);
            expr_ref rhs(args[1], m);
            lhs = coerce_eq(lhs, rhs);
            return expr_ref(m.mk_not(m.mk_eq(lhs, rhs)), m);
        }};
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
    // @ corresponds to array select (function application)
    while (accept(token_kind::at_tok)) {
        expr_ref arg = parse_at_arg();
        sort* e_sort = e->get_sort();
        if (!m_array.is_array(e_sort)) {
            sort* arg_sort = arg->get_sort();
            sort* arr_sort = m_array.mk_array_sort(arg_sort, m_univ);
            e = coerce_arg(e, arr_sort);
        } else {
            sort* dom = get_array_domain(e_sort, 0);
            if (dom != arg->get_sort())
                arg = coerce_arg(arg, dom);
        }
        e = expr_ref(m_array.mk_select(e, arg), m);
    }
    return e;
}

expr_ref tptp_parser::parse_formula() {
    return parse_expr(PREC_IFF);
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
        TRACE(parser, ctx.get_solver()->display(tout));
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
