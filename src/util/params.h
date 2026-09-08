/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    params.h

Abstract:

    Parameters.

Author:

    Leonardo (leonardo) 2011-04-22

Notes:

--*/
#pragma once

#include <array>
#include <climits>
#include <limits>
#include "util/cmd_context_types.h"
#include "util/vector.h"

// Support for hand-written <module>_params.hpp headers (formerly generated at build time
// from a <module>.pyg file by scripts/pyg2hpp.py). Each such header defines an X-macro
// listing its parameters, one row per parameter, e.g.:
//
//   #define SLS_PARAMS(UINT_, BOOL_, DOUBLE_, STRING_, SYMBOL_)                             \
//     UINT_(max_memory, "max_memory", UINT_MAX, "maximum amount of memory in megabytes")     \
//     BOOL_(walksat,    "walksat",    true,     "use walksat assertion selection")           \
//     ...
//
//   Z3_DEFINE_MODULE_PARAMS(sls_params, "sls", SLS_PARAMS);
//
// Row shape is the same for every kind: (method, key, default, doc). `method` is the C++
// accessor name; `key` is the (possibly dotted) parameter name used at the params_ref/gparams
// level, so the two can differ (e.g. `solve_eqs_non_ground` / "solve_eqs.non_ground").
//
// Z3_DEFINE_MODULE_PARAMS expands the param-list macro twice: once to collect param_descrs
// (self-documentation, `-pd`, option validation) and once to define the typed accessors.

// Stringizes a macro argument after expanding it, e.g. Z3_PARAM_STR(20.0) -> "20.0". Only
// safe for defaults that are already plain literals (DOUBLE parameters in practice): unlike
// Z3_PARAM_UINT_STR below, it renders whatever text the default happens to expand to, so a
// macro that expands to an expression (e.g. some libcs' <climits> UINT_MAX) would leak into
// the display string verbatim.
#define Z3_PARAM_STR2(x) #x
#define Z3_PARAM_STR(x) Z3_PARAM_STR2(x)

// Renders an unsigned default's decimal digits at compile time from its *value*, not its
// spelling, via a constexpr non-type template parameter: whatever `deflt` expands to (a
// literal, or <climits>'s UINT_MAX -- however that macro happens to be defined, e.g. some
// libcs spell it as an expression like `(2147483647 *2U +1U)`) is fully constant-folded
// into an `unsigned` before formatting, so the display string can never end up as that
// stray expression text.
template <unsigned N>
struct z3_param_uint_str {
    static constexpr auto arr = [] {
        std::array<char, std::numeric_limits<unsigned>::digits10 + 3> a{};
        unsigned v = N;
        unsigned len = 0;
        char digits[a.size()]{};
        do {
            digits[len++] = char('0' + (v % 10));
            v /= 10;
        } while (v != 0);
        for (unsigned i = 0; i < len; ++i)
            a[i] = digits[len - 1 - i];
        return a;
    }();
    static constexpr char const * value = arr.data();
};
#define Z3_PARAM_UINT_STR(deflt) (z3_param_uint_str<(unsigned)(deflt)>::value)

#define Z3_PARAM_DESCR_UINT(method, key, deflt, doc)   d.insert(key, CPK_UINT, doc, Z3_PARAM_UINT_STR(deflt), module);
#define Z3_PARAM_DESCR_BOOL(method, key, deflt, doc)   d.insert(key, CPK_BOOL, doc, (deflt) ? "true" : "false", module);
#define Z3_PARAM_DESCR_DOUBLE(method, key, deflt, doc) d.insert(key, CPK_DOUBLE, doc, Z3_PARAM_STR(deflt), module);
#define Z3_PARAM_DESCR_STRING(method, key, deflt, doc) d.insert(key, CPK_STRING, doc, deflt, module);
#define Z3_PARAM_DESCR_SYMBOL(method, key, deflt, doc) d.insert(key, CPK_SYMBOL, doc, deflt, module);

#define Z3_PARAM_GET_UINT(method, key, deflt, doc)   unsigned method() const { return p.get_uint(key, g, deflt); }
#define Z3_PARAM_GET_BOOL(method, key, deflt, doc)   bool method() const { return p.get_bool(key, g, deflt); }
#define Z3_PARAM_GET_DOUBLE(method, key, deflt, doc) double method() const { return p.get_double(key, g, deflt); }
#define Z3_PARAM_GET_STRING(method, key, deflt, doc) char const * method() const { return p.get_str(key, g, deflt); }
#define Z3_PARAM_GET_SYMBOL(method, key, deflt, doc) symbol method() const { return p.get_sym(key, g, symbol(deflt)); }

#define Z3_DEFINE_MODULE_PARAMS(CLASS, MODULE, PARAMS)                                    \
  struct CLASS {                                                                          \
    params_ref const & p;                                                                 \
    params_ref g;                                                                         \
    CLASS(params_ref const & _p = params_ref::get_empty()):                               \
       p(_p), g(gparams::get_module(MODULE)) {}                                           \
    static void collect_param_descrs(param_descrs & d) {                                  \
      char const * const module = MODULE;                                                 \
      PARAMS(Z3_PARAM_DESCR_UINT, Z3_PARAM_DESCR_BOOL, Z3_PARAM_DESCR_DOUBLE,              \
             Z3_PARAM_DESCR_STRING, Z3_PARAM_DESCR_SYMBOL)                                 \
    }                                                                                      \
    PARAMS(Z3_PARAM_GET_UINT, Z3_PARAM_GET_BOOL, Z3_PARAM_GET_DOUBLE,                      \
           Z3_PARAM_GET_STRING, Z3_PARAM_GET_SYMBOL)                                       \
  }

std::string norm_param_name(char const * n);
std::string norm_param_name(symbol const & n);

typedef cmd_arg_kind param_kind;

class params;
class param_descrs;

class params_ref {
    static params_ref g_empty_params_ref;
    
    params * m_params = nullptr;
    void init();
    void copy_core(params const * p);
    void set(params_ref const& p);
public:
    params_ref() = default;
    params_ref(params_ref const & p);
    ~params_ref();
    
    params_ref& operator=(params_ref const& p) = delete;

    static params_ref const & get_empty() { return g_empty_params_ref; }
    
        
    // copy params from src
    void copy(params_ref const & src);
    void append(params_ref const & src) { copy(src); }

    bool get_bool(symbol const & k, bool _default) const;
    bool get_bool(char const * k, bool _default) const;
    unsigned get_uint(symbol const & k, unsigned _default) const;
    unsigned get_uint(char const * k, unsigned _default) const;
    double get_double(symbol const & k, double _default) const;
    double get_double(char const * k, double _default) const;
    char const * get_str(symbol const & k, char const * _default) const;
    char const * get_str(char const * k, char const * _default) const;
    rational get_rat(symbol const & k, rational const & _default) const;
    rational get_rat(char const * k, rational const & _default) const;
    symbol get_sym(symbol const & k, symbol const & _default) const;
    symbol get_sym(char const * k, symbol const & _default) const;

    bool get_bool(char const * k, params_ref const & fallback, bool _default) const;
    unsigned get_uint(char const * k, params_ref const & fallback, unsigned _default) const;
    double get_double(char const * k, params_ref const & fallback, double _default) const;
    char const * get_str(char const * k, params_ref const & fallback, char const * _default) const;
    symbol get_sym(char const * k, params_ref const & fallback, symbol const & _default) const;

    bool empty() const;
    bool contains(symbol const & k) const;
    bool contains(char const * k) const;

    void reset();
    void reset(symbol const & k);
    void reset(char const * k);

    void set_bool(symbol const & k, bool v);
    void set_bool(char const * k, bool  v);
    void set_uint(symbol const & k, unsigned v);
    void set_uint(char const * k, unsigned v);
    void set_double(symbol const & k, double v);
    void set_double(char const * k, double v);
    void set_str(symbol const & k, char const * v);
    void set_str(char const * k, char const * v);
    void set_rat(symbol const & k, rational const & v);
    void set_rat(char const * k, rational const & v); 
    void set_sym(symbol const & k, symbol const & v);
    void set_sym(char const * k, symbol const & v);

    void display(std::ostream & out) const;
    void display_smt2(std::ostream& out, char const* module, param_descrs& module_desc) const;

    void validate(param_descrs const & p);

    /*
      \brief Display the value of the given parameter.
      
      It displays 'default' if k is not in the parameter set.
    */
    void display(std::ostream & out, char const * k) const;
    void display(std::ostream & out, symbol const & k) const;
};

inline std::ostream & operator<<(std::ostream & out, params_ref const & ref) {
    ref.display(out);
    return out;
}

class param_descrs {
    struct imp;
    imp *  m_imp;
public:
    param_descrs();
    ~param_descrs();
    param_descrs& operator=(param_descrs const&) = delete;
    void copy(param_descrs & other);
    void insert(char const * name, param_kind k, char const * descr, char const * def = nullptr, char const* module = nullptr);
    void insert(symbol const & name, param_kind k, char const * descr, char const * def = nullptr, char const* module = nullptr);
    bool contains(char const * name) const;
    bool contains(symbol const & name) const;
    void erase(char const * name);
    void erase(symbol const & name);
    param_kind get_kind(char const * name) const;
    param_kind get_kind(symbol const & name) const;
    param_kind get_kind_in_module(symbol & name) const;
    char const * get_descr(char const * name) const;
    char const * get_descr(symbol const & name) const;
    char const * get_default(char const * name) const;
    char const * get_default(symbol const & name) const;
    void display(std::ostream & out, unsigned indent = 0, bool smt2_style=false, bool include_descr=true) const;
    void display_markdown(std::ostream& out, bool smt2_style = false, bool include_descr = true) const;
    unsigned size() const; 
    symbol get_param_name(unsigned idx) const;
    char const * get_module(symbol const& name) const;
};

void insert_max_memory(param_descrs & r);
void insert_max_steps(param_descrs & r);
void insert_produce_models(param_descrs & r);
void insert_produce_proofs(param_descrs & r);
void insert_timeout(param_descrs & r);
void insert_rlimit(param_descrs & r);
void insert_ctrl_c(param_descrs & r);

