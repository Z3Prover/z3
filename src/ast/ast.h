/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    ast.h

Abstract:

    Expression DAG

Author:

    Leonardo de Moura (leonardo) 2006-09-18.

Revision History:

--*/
#pragma once


#include "util/vector.h"
#include "util/hashtable.h"
#include "util/buffer.h"
#include "util/zstring.h"
#include "util/symbol.h"
#include "util/rational.h"
#include "util/hash.h"
#include "util/optional.h"
#include "util/trace.h"
#include "util/bit_vector.h"
#include "util/symbol_table.h"
#include "util/tptr.h"
#include "util/memory_manager.h"
#include "util/small_object_allocator.h"
#include "util/obj_ref.h"
#include "util/ref_vector.h"
#include "util/ref_pair_vector.h"
#include "util/ref_buffer.h"
#include "util/obj_mark.h"
#include "util/obj_hashtable.h"
#include "util/id_gen.h"
#include "util/map.h"
#include "util/parray.h"
#include "util/dictionary.h"
#include "util/chashtable.h"
#include "util/z3_exception.h"
#include "util/dependency.h"
#include "util/rlimit.h"
#include <variant>

#define RECYCLE_FREE_AST_INDICES

#ifdef _MSC_VER
#pragma warning(disable : 4200)
#pragma warning(disable : 4355)
#endif

#ifdef _MSC_VER
#  define Z3_NORETURN __declspec(noreturn)
#else
#  define Z3_NORETURN [[noreturn]]
#endif

class ast;
class ast_manager;

/**
   \brief Generic exception for AST related errors.

   We used to use fatal_error_msg to report errors inside plugins.
*/
class ast_exception : public default_exception {
public:
    ast_exception(std::string && msg) : default_exception(std::move(msg)) {}
};

typedef int     family_id;
const family_id null_family_id = -1;
const family_id basic_family_id = 0;
const family_id label_family_id = 1;
const family_id pattern_family_id = 2;
const family_id model_value_family_id = 3;
const family_id user_sort_family_id = 4;
const family_id last_builtin_family_id = 4;

const family_id arith_family_id = 5;

// -----------------------------------
//
// parameter
//
// -----------------------------------

/**
   \brief Interpreted function declarations and sorts may have parameters that are used
   to encode extra information associated with them.
*/
class parameter {
public:
    // NOTE: these must be in the same order as the entries in the variant below
    enum kind_t {
        PARAM_INT,
        PARAM_AST,
        PARAM_SYMBOL,
        PARAM_ZSTRING,
        PARAM_RATIONAL,
        PARAM_DOUBLE,
        // PARAM_EXTERNAL is used for handling decl_plugin specific parameters.
        // For example, it is used for handling mpf numbers in float_decl_plugin,
        // and irrational algebraic numbers in arith_decl_plugin.
        // PARAM_EXTERNAL is not supported by z3 low level input format. This format is legacy, so
        // this is not a big problem.
        // Remark: PARAM_EXTERNAL can only be used to decorate theory decls.
        PARAM_EXTERNAL
    };
private:
    // It is not possible to use tag pointers, since symbols are already tagged.
    std::variant<
        int,       // for PARAM_INT
        ast*,      // for PARAM_AST
        symbol,    // for PARAM_SYMBOL
        zstring*,  // for PARAM_ZSTRING
        rational*, // for PARAM_RATIONAL
        double,    // for PARAM_DOUBLE (remark: this is not used in float_decl_plugin)
        unsigned   // for PARAM_EXTERNAL
    > m_val;

public:

    parameter() : m_val(0) {}
    explicit parameter(int val): m_val(val) {}
    explicit parameter(unsigned val): m_val((int)val) {}
    explicit parameter(ast * p): m_val(p) {}
    explicit parameter(symbol const & s): m_val(s) {}
    explicit parameter(rational const & r): m_val(alloc(rational, r)) {}
    explicit parameter(rational && r) : m_val(alloc(rational, std::move(r))) {} 
    explicit parameter(zstring const& s): m_val(alloc(zstring, s)) {}
    explicit parameter(zstring && s): m_val(alloc(zstring, std::move(s))) {}
    explicit parameter(double d): m_val(d) {}
    explicit parameter(const char *s): m_val(symbol(s)) {}
    explicit parameter(const std::string &s): m_val(symbol(s)) {}
    explicit parameter(unsigned ext_id, bool): m_val(ext_id) {}
    parameter(parameter const& other) { *this = other; }

    parameter(parameter && other) noexcept : m_val(std::move(other.m_val)) {
        other.m_val = 0;
    }

    ~parameter();

    parameter& operator=(parameter const& other);

    kind_t get_kind() const { return static_cast<kind_t>(m_val.index()); }
    bool is_int() const { return get_kind() == PARAM_INT; }
    bool is_ast() const { return get_kind() == PARAM_AST; }
    bool is_symbol() const { return get_kind() == PARAM_SYMBOL; }
    bool is_rational() const { return get_kind() == PARAM_RATIONAL; }
    bool is_double() const { return get_kind() == PARAM_DOUBLE; }
    bool is_external() const { return get_kind() == PARAM_EXTERNAL; }
    bool is_zstring() const { return get_kind() == PARAM_ZSTRING; }

    bool is_int(int & i) const { return is_int() && (i = get_int(), true); }
    bool is_ast(ast * & a) const { return is_ast() && (a = get_ast(), true); }
    bool is_symbol(symbol & s) const { return is_symbol() && (s = get_symbol(), true); }
    bool is_rational(rational & r) const { return is_rational() && (r = get_rational(), true); }
    bool is_double(double & d) const { return is_double() && (d = get_double(), true); }
    bool is_external(unsigned & id) const { return is_external() && (id = get_ext_id(), true); }
    bool is_zstring(zstring& s) const { return is_zstring() && (s = get_zstring(), true); }

    /**
       \brief This method is invoked when the parameter is
       attached to a function declaration or sort.
    */
    void init_eh(ast_manager & m);
    /**
       \brief This method is invoked before the function
       declaration or sort associated with the parameter is
       deleted.
    */
    void del_eh(ast_manager & m, family_id fid);

    int get_int() const { return std::get<int>(m_val); }
    ast * get_ast() const { return std::get<ast*>(m_val); }
    symbol get_symbol() const { return std::get<symbol>(m_val); }
    rational const & get_rational() const { return *std::get<rational*>(m_val); }
    zstring const& get_zstring() const { return *std::get<zstring*>(m_val); }
    double get_double() const { return std::get<double>(m_val); }
    unsigned get_ext_id() const { return std::get<unsigned>(m_val); }

    bool operator==(parameter const & p) const;
    bool operator!=(parameter const & p) const { return !operator==(p); }

    unsigned hash() const;

    std::ostream& display(std::ostream& out) const;
};

inline std::ostream& operator<<(std::ostream& out, parameter const & p) {
    return p.display(out);
}

void display_parameters(std::ostream & out, unsigned n, parameter const * p);

// -----------------------------------
//
// family_manager
//
// -----------------------------------

/**
   \brief Interpreted functions and sorts are grouped in families.
   Each family has an unique ID. This class models the mapping
   between symbols (family names) and the unique IDs.
*/
class family_manager {
    family_id               m_next_id = 0;
    symbol_table<family_id> m_families;
    svector<symbol>         m_names;
public:
    /**
       \brief Return the family_id for s, a new id is created if !has_family(s)

       If has_family(s), then this method is equivalent to get_family_id(s)
    */
    family_id mk_family_id(symbol const & s);

    /**
       \brief Return the family_id for s, return null_family_id if s was not registered in the manager.
    */
    family_id get_family_id(symbol const & s) const;

    bool has_family(symbol const & s) const;

    void get_dom(svector<symbol>& dom) const { m_families.get_dom(dom); }

    void get_range(svector<family_id> & range) const { m_families.get_range(range); }

    symbol const & get_name(family_id fid) const { return fid >= 0 && fid < static_cast<int>(m_names.size()) ? m_names[fid] : symbol::null; }

    bool has_family(family_id fid) const { return fid >= 0 && fid < static_cast<int>(m_names.size()); }
};

// -----------------------------------
//
// decl_info
//
// -----------------------------------

/**
   \brief Each interpreted function declaration or sort has a kind.
   Kinds are used to identify interpreted functions and sorts in a family.
*/
typedef int     decl_kind;
const decl_kind null_decl_kind = -1;

/**
   \brief Interpreted function declarations and sorts are associated with
   a family id, kind, and parameters.
*/
class decl_info {
    family_id            m_family_id;
    decl_kind            m_kind;
    vector<parameter>    m_parameters;
public:
    bool                 m_private_parameters;
    decl_info(family_id family_id = null_family_id, decl_kind k = null_decl_kind,
              unsigned num_parameters = 0, parameter const * parameters = nullptr, bool private_params = false);

    void init_eh(ast_manager & m);
    void del_eh(ast_manager & m);

    family_id get_family_id() const { return m_family_id; }
    decl_kind get_decl_kind() const { return m_kind; }
    unsigned get_num_parameters() const { return m_parameters.size(); }
    parameter const & get_parameter(unsigned idx) const { return m_parameters[idx]; }
    parameter const * get_parameters() const { return m_parameters.begin(); }
    bool private_parameters() const { return m_private_parameters; }

    struct iterator {
        decl_info const& d;
        iterator(decl_info const& d) : d(d) {}
        parameter const* begin() const { return d.get_parameters(); }
        parameter const* end() const { return begin() + d.get_num_parameters(); }
    };
    iterator parameters() const { return iterator(*this); }

    unsigned hash() const;
    bool operator==(decl_info const & info) const;
};

std::ostream & operator<<(std::ostream & out, decl_info const & info);

// -----------------------------------
//
// sort_size
//
// -----------------------------------

/**
   \brief Models the number of elements of a sort.
*/
class sort_size {
    enum kind_t {
        SS_FINITE,
        // For some sorts it may be too expensive to compute the
        // number of elements precisely (e.g., arrays).  In this
        // cases, we mark the sort as too big. That is, the number
        // of elements is at least bigger than 2^64.
        SS_FINITE_VERY_BIG,
        SS_INFINITE
    } m_kind;
    uint64_t m_size; // It is only meaningful if m_kind == SS_FINITE
    sort_size(kind_t k, uint64_t r):m_kind(k), m_size(r) {}
public:
    sort_size():m_kind(SS_INFINITE), m_size(0) {}
    sort_size(uint64_t const & sz):m_kind(SS_FINITE), m_size(sz) {}
    explicit sort_size(rational const& r) {
        if (r.is_uint64()) {
            m_kind = SS_FINITE;
            m_size = r.get_uint64();
        }
        else {
            m_kind = SS_FINITE_VERY_BIG;
            m_size = 0;
        }
    }
    static sort_size mk_infinite() { return sort_size(SS_INFINITE, 0); }
    static sort_size mk_very_big() { return sort_size(SS_FINITE_VERY_BIG, 0); }
    static sort_size mk_finite(uint64_t r) { return sort_size(SS_FINITE, r); }

    bool is_infinite() const { return m_kind == SS_INFINITE; }
    bool is_very_big() const { return m_kind == SS_FINITE_VERY_BIG; }
    bool is_finite() const { return m_kind == SS_FINITE; }

    static bool is_very_big_base2(unsigned power) { return power >= 64; }

    uint64_t size() const { SASSERT(is_finite()); return m_size; }
};

std::ostream& operator<<(std::ostream& out, sort_size const & ss);

// -----------------------------------
//
// sort_info
//
// -----------------------------------

/**
   \brief Extra information that may be attached to interpreted sorts.
*/
class sort_info : public decl_info {
    sort_size m_num_elements;
public:
    sort_info(family_id family_id = null_family_id, decl_kind k = null_decl_kind,
              unsigned num_parameters = 0, parameter const * parameters = nullptr, bool private_parameters = false):
        decl_info(family_id, k, num_parameters, parameters, private_parameters) {
    }

    sort_info(family_id family_id, decl_kind k, uint64_t num_elements,
              unsigned num_parameters = 0, parameter const * parameters = nullptr, bool private_parameters = false):
        decl_info(family_id, k, num_parameters, parameters, private_parameters), m_num_elements(num_elements) {
    }

    sort_info(family_id family_id, decl_kind k, sort_size const& num_elements,
              unsigned num_parameters = 0, parameter const * parameters = nullptr, bool private_parameters = false):
        decl_info(family_id, k, num_parameters, parameters, private_parameters), m_num_elements(num_elements) {
    }

    sort_info(decl_info const& di, sort_size const& num_elements) : 
        decl_info(di), m_num_elements(num_elements) {}

    bool is_infinite() const { return m_num_elements.is_infinite(); }
    bool is_very_big() const { return m_num_elements.is_very_big(); }
    sort_size const & get_num_elements() const { return m_num_elements; }
    void set_num_elements(sort_size const& s) { m_num_elements = s; }
};

std::ostream & operator<<(std::ostream & out, sort_info const & info);

// -----------------------------------
//
// func_decl_info
//
// -----------------------------------

/**
   \brief Extra information that may be attached to interpreted function decls.
*/
struct func_decl_info : public decl_info {
    bool m_left_assoc:1;
    bool m_right_assoc:1;
    bool m_flat_associative:1;
    bool m_commutative:1;
    bool m_chainable:1;
    bool m_pairwise:1;
    bool m_injective:1;
    bool m_idempotent:1;
    bool m_skolem:1;
    bool m_lambda:1;

    func_decl_info(family_id family_id = null_family_id, decl_kind k = null_decl_kind, unsigned num_parameters = 0, parameter const * parameters = nullptr);

    bool is_associative() const { return m_left_assoc && m_right_assoc; }
    bool is_left_associative() const { return m_left_assoc; }
    bool is_right_associative() const { return m_right_assoc; }
    bool is_flat_associative() const { return m_flat_associative; }
    bool is_commutative() const { return m_commutative; }
    bool is_chainable() const { return m_chainable; }
    bool is_pairwise() const { return m_pairwise; }
    bool is_injective() const { return m_injective; }
    bool is_idempotent() const { return m_idempotent; }
    bool is_skolem() const { return m_skolem; }
    bool is_lambda() const { return m_lambda; }

    void set_associative(bool flag = true) { m_left_assoc = flag; m_right_assoc = flag; }
    void set_left_associative(bool flag = true) { m_left_assoc = flag; }
    void set_right_associative(bool flag = true) { m_right_assoc = flag; }
    void set_flat_associative(bool flag = true) { m_flat_associative = flag; }
    void set_commutative(bool flag = true) { m_commutative = flag; }
    void set_chainable(bool flag = true) { m_chainable = flag; }
    void set_pairwise(bool flag = true) { m_pairwise = flag; }
    void set_injective(bool flag = true) { m_injective = flag; }
    void set_idempotent(bool flag = true) { m_idempotent = flag; }
    void set_skolem(bool flag = true) { m_skolem = flag; }
    void set_lambda(bool flag = true) { m_lambda = flag; }

    bool operator==(func_decl_info const & info) const;

    // Return true if the func_decl_info is equivalent to the null one (i.e., it does not contain any useful info).
    bool is_null() const {
        return
            get_family_id() == null_family_id && !is_left_associative() && !is_right_associative() && !is_commutative() &&
            !is_chainable() && !is_pairwise() && !is_injective() && !is_idempotent() && !is_skolem();
    }
};

std::ostream & operator<<(std::ostream & out, func_decl_info const & info);

// -----------------------------------
//
// ast
//
// -----------------------------------

typedef enum { AST_APP, AST_VAR, AST_QUANTIFIER, AST_SORT, AST_FUNC_DECL } ast_kind;
char const * get_ast_kind_name(ast_kind k);

class shared_occs_mark;

class ast {
protected:
    friend class ast_manager;

    unsigned m_id;
    unsigned m_kind:16;
    // Warning: the marks should be used carefully, since they are shared.
    unsigned m_mark1:1;
    unsigned m_mark2:1;
    // Private mark used by shared_occs functor
    // Motivation for this field:
    //  - A mark cannot be used by more than one owner.
    //    So, it is only safe to use mark by "self-contained" code.
    //    They should be viewed as temporary information.
    //  - The functor shared_occs is used by some AST pretty printers.
    //  - So, a code that uses marks could not use the pretty printer if
    //    shared_occs used one of the public marks.
    //  - This was a constant source of assertion violations.
    unsigned m_mark_shared_occs:1;
    friend class shared_occs_mark;
    void mark_so(bool flag) { m_mark_shared_occs = flag; }
    void reset_mark_so() { m_mark_shared_occs = false; }
    bool is_marked_so() const { return m_mark_shared_occs; }
    unsigned m_ref_count;
    unsigned m_hash;
#ifdef Z3DEBUG
    // In debug mode, we store who is the owner of the mark.
    void *   m_mark1_owner;
    void *   m_mark2_owner;
#endif

    void inc_ref() {
        SASSERT(m_ref_count < UINT_MAX);
        m_ref_count ++;
    }

    void dec_ref() {
        SASSERT(m_ref_count > 0);
        --m_ref_count;
    }

    ast(ast_kind k):m_id(UINT_MAX), m_kind(k), m_mark1(false), m_mark2(false), m_mark_shared_occs(false), m_ref_count(0) {
        DEBUG_CODE({
            m_mark1_owner = 0;
            m_mark2_owner = 0;
        });
    }
public:
    unsigned get_id() const { return m_id; }
    unsigned get_ref_count() const { return m_ref_count; }
    ast_kind get_kind() const { return static_cast<ast_kind>(m_kind); }
    unsigned hash() const { return m_hash; }

#ifdef Z3DEBUG
    void mark1(bool flag, void * owner) { SASSERT(m_mark1_owner == 0 || m_mark1_owner == owner); m_mark1 = flag; m_mark1_owner = owner; }
    void mark2(bool flag, void * owner) { SASSERT(m_mark2_owner == 0 || m_mark2_owner == owner); m_mark2 = flag; m_mark2_owner = owner; }
    void reset_mark1(void * owner) { SASSERT(m_mark1_owner == 0 || m_mark1_owner == owner); m_mark1 = false; m_mark1_owner = 0; }
    void reset_mark2(void * owner) { SASSERT(m_mark2_owner == 0 || m_mark2_owner == owner); m_mark2 = false; m_mark2_owner = 0; }
    bool is_marked1(void * owner) const { SASSERT(m_mark1_owner == 0 || m_mark1_owner == owner); return m_mark1; }
    bool is_marked2(void * owner) const { SASSERT(m_mark2_owner == 0 || m_mark2_owner == owner); return m_mark2; }
#define AST_MARK1(A,F,O) A->mark1(F, O)
#define AST_MARK2(A,F,O) A->mark2(F, O)
#define AST_RESET_MARK1(A,O) A->reset_mark1(O)
#define AST_RESET_MARK2(A,O) A->reset_mark2(O)
#define AST_IS_MARKED1(A,O) A->is_marked1(O)
#define AST_IS_MARKED2(A,O) A->is_marked2(O)
#else
    void mark1(bool flag) { m_mark1 = flag; }
    void mark2(bool flag) { m_mark2 = flag; }
    void reset_mark1() { m_mark1 = false; }
    void reset_mark2() { m_mark2 = false; }
    bool is_marked1() const { return m_mark1; }
    bool is_marked2() const { return m_mark2; }
#define AST_MARK1(A,F,O) A->mark1(F)
#define AST_MARK2(A,F,O) A->mark2(F)
#define AST_RESET_MARK1(A,O) A->reset_mark1()
#define AST_RESET_MARK2(A,O) A->reset_mark2()
#define AST_IS_MARKED1(A,O) A->is_marked1()
#define AST_IS_MARKED2(A,O) A->is_marked2()
#endif
};

#define MATCH_TERNARY(_MATCHER_)                                                                                \
    bool _MATCHER_(expr const* n, expr*& a1, expr*& a2, expr *& a3) const {                                     \
        if (_MATCHER_(n) && to_app(n)->get_num_args() == 3) {                                                   \
            a1 = to_app(n)->get_arg(0); a2 = to_app(n)->get_arg(1); a3 = to_app(n)->get_arg(2); return true; }  \
        return false;                                                                                           \
    }

#define MATCH_BINARY(_MATCHER_)                                                                                                         \
    bool _MATCHER_(expr const* n, expr*& s, expr*& t) const {                                                                           \
        if (_MATCHER_(n) && to_app(n)->get_num_args() == 2) { s = to_app(n)->get_arg(0); t = to_app(n)->get_arg(1); return true; }      \
        return false;                                                                                                                   \
    }

#define MATCH_UNARY(_MATCHER_)                                                                          \
    bool _MATCHER_(expr const* n, expr*& s) const {                                                     \
        if (_MATCHER_(n) && to_app(n)->get_num_args() == 1) { s = to_app(n)->get_arg(0); return true; } \
        return false;                                                                                   \
    }

// -----------------------------------
//
// decl
//
// -----------------------------------

/**
   The ids of expressions and declarations are in different ranges.
*/
const unsigned c_first_decl_id = (1u << 31u);

/**
   \brief Superclass for function declarations and sorts.
*/
class decl : public ast {
protected:
    friend class ast_manager;

    symbol      m_name;
    decl_info * m_info;

    decl(ast_kind k, symbol const & name, decl_info * info):ast(k), m_name(name), m_info(info) {}
public:
    unsigned get_decl_id() const { SASSERT(get_id() >= c_first_decl_id); return get_id() - c_first_decl_id; }
    symbol const & get_name() const { return m_name; }
    decl_info * get_info() const { return m_info; }
    family_id get_family_id() const { return m_info == nullptr ? null_family_id : m_info->get_family_id(); }
    decl_kind get_decl_kind() const { return m_info == nullptr ? null_decl_kind : m_info->get_decl_kind(); }
    unsigned get_num_parameters() const { return m_info == nullptr ? 0 : m_info->get_num_parameters(); }
    parameter const & get_parameter(unsigned idx) const { return m_info->get_parameter(idx); }
    parameter const * get_parameters() const { return m_info == nullptr ? nullptr : m_info->get_parameters(); }
    bool private_parameters() const { return m_info != nullptr && m_info->private_parameters(); }

    struct iterator {
        decl const& d;
        iterator(decl const& d) : d(d) {}
        parameter const* begin() const { return d.get_parameters(); }
        parameter const* end() const { return begin() + d.get_num_parameters(); }
    };
    iterator parameters() const { return iterator(*this); }


};

// -----------------------------------
//
// sort
//
// -----------------------------------

class sort : public decl {
    friend class ast_manager;

    static unsigned get_obj_size() { return sizeof(sort); }

    sort(symbol const & name, sort_info * info):decl(AST_SORT, name, info) {}
public:
    sort_info * get_info() const { return static_cast<sort_info*>(m_info); }
    bool is_infinite() const { return get_info() == nullptr || get_info()->is_infinite(); }
    bool is_very_big() const { return get_info() == nullptr || get_info()->is_very_big(); }
    bool is_sort_of(family_id fid, decl_kind k) const { return get_family_id() == fid && get_decl_kind() == k; }
    sort_size const & get_num_elements() const { return get_info()->get_num_elements(); }
    void set_num_elements(sort_size const& s) { get_info()->set_num_elements(s); }
    unsigned get_size() const { return get_obj_size(); }
};

// -----------------------------------
//
// func_decl
//
// -----------------------------------

class func_decl : public decl {
    friend class ast_manager;

    unsigned         m_arity;
    sort *           m_range;
    sort *           m_domain[0];

    static unsigned get_obj_size(unsigned arity) { return sizeof(func_decl) + arity * sizeof(sort *); }

    func_decl(symbol const & name, unsigned arity, sort * const * domain, sort * range, func_decl_info * info);
public:
    func_decl_info * get_info() const { return static_cast<func_decl_info*>(m_info); }
    bool is_associative() const { return get_info() != nullptr && get_info()->is_associative(); }
    bool is_left_associative() const { return get_info() != nullptr && get_info()->is_left_associative(); }
    bool is_right_associative() const { return get_info() != nullptr && get_info()->is_right_associative(); }
    bool is_flat_associative() const { return get_info() != nullptr && get_info()->is_flat_associative(); }
    bool is_commutative() const { return get_info() != nullptr && get_info()->is_commutative(); }
    bool is_chainable() const { return get_info() != nullptr && get_info()->is_chainable(); }
    bool is_pairwise() const { return get_info() != nullptr && get_info()->is_pairwise(); }
    bool is_injective() const { return get_info() != nullptr && get_info()->is_injective(); }
    bool is_skolem() const { return get_info() != nullptr && get_info()->is_skolem(); }
    bool is_lambda() const { return get_info() != nullptr && get_info()->is_lambda(); }
    bool is_idempotent() const { return get_info() != nullptr && get_info()->is_idempotent(); }
    unsigned get_arity() const { return m_arity; }
    sort * get_domain(unsigned idx) const { SASSERT(idx < get_arity()); return m_domain[idx]; }
    sort * const * get_domain() const { return m_domain; }
    sort * get_range() const { return m_range; }
    unsigned get_size() const { return get_obj_size(m_arity); }
    sort * const * begin() const { return get_domain(); }
    sort * const * end() const { return get_domain() + get_arity(); }

};

// -----------------------------------
//
// expression
//
// -----------------------------------

/**
   \brief Superclass for applications, variables and quantifiers.
*/
class expr : public ast {
protected:
    friend class ast_manager;

    expr(ast_kind k):ast(k) {}
public:

    sort* get_sort() const;
};

// -----------------------------------
//
// application
//
// -----------------------------------

#define APP_DEPTH_NUM_BITS 16
const unsigned c_max_depth = ((1 << APP_DEPTH_NUM_BITS) - 1);
struct app_flags {
    unsigned     m_depth:APP_DEPTH_NUM_BITS;  // if app is to deep, it doesn't matter.
    unsigned     m_ground:1;   // application does not have free variables or nested quantifiers.
    unsigned     m_has_quantifiers:1; // application has nested quantifiers.
    unsigned     m_has_labels:1; // application has nested labels.
};

class app : public expr {
    friend class ast_manager;

    func_decl *  m_decl;
    unsigned     m_num_args;
    expr *       m_args[0];

    static app_flags g_constant_flags;

    // remark: store term depth in the end of the app. the depth is only stored if the num_args > 0
    static unsigned get_obj_size(unsigned num_args) {
        return num_args == 0 ? sizeof(app) : sizeof(app) + num_args * sizeof(expr *) + sizeof(app_flags);
    }

    friend class tmp_app;

    app_flags * flags() const { return m_num_args == 0 ? &g_constant_flags : reinterpret_cast<app_flags*>(const_cast<expr**>(m_args + m_num_args)); }

    app(func_decl * decl, unsigned num_args, expr * const * args);
public:
    func_decl * get_decl() const { return m_decl; }
    family_id get_family_id() const { return get_decl()->get_family_id(); }
    decl_kind get_decl_kind() const { return get_decl()->get_decl_kind(); }
    symbol const& get_name() const { return get_decl()->get_name(); }
    unsigned get_num_parameters() const { return get_decl()->get_num_parameters(); }
    parameter const& get_parameter(unsigned idx) const { return get_decl()->get_parameter(idx); }
    parameter const* get_parameters() const { return get_decl()->get_parameters(); }
    bool is_app_of(family_id fid, decl_kind k) const { return get_family_id() == fid && get_decl_kind() == k; }
    unsigned get_num_args() const { return m_num_args; }
    expr * get_arg(unsigned idx) const { SASSERT(idx < m_num_args); return m_args[idx]; }
    expr * const * get_args() const { return m_args; }
    unsigned get_size() const { return get_obj_size(get_num_args()); }
    expr * const * begin() const { return m_args; }
    expr * const * end() const { return m_args + m_num_args; }
    sort * _get_sort() const { return get_decl()->get_range(); }

    unsigned get_depth() const { return flags()->m_depth; }
    bool is_ground() const { return flags()->m_ground; }
    bool has_quantifiers() const { return flags()->m_has_quantifiers; }
    bool has_labels() const { return flags()->m_has_labels; }
};

// -----------------------------------
//
// temporary application: little hack to avoid
// the creation of temporary expressions to just
// check the presence of the expression in
// some container/index.
//
// -----------------------------------

class tmp_app {
    unsigned m_num_args;
    char *   m_data;
public:
    tmp_app(unsigned num_args):
        m_num_args(num_args) {
        unsigned sz = app::get_obj_size(num_args);
        m_data = alloc_svect(char, sz);
        memset(m_data, 0, sz);
        get_app()->m_num_args = m_num_args;
    }

    ~tmp_app() {
        dealloc_svect(m_data);
    }

    app * get_app() {
        return reinterpret_cast<app*>(m_data);
    }

    expr ** get_args() {
        return get_app()->m_args;
    }

    void set_decl(func_decl * d) {
        get_app()->m_decl = d;
    }

    void set_num_args(unsigned num_args) {
        get_app()->m_num_args = num_args;
    }

    void set_arg(unsigned idx, expr * arg) {
        get_args()[idx] = arg;
        SASSERT(get_app()->get_arg(idx) == arg);
    }

    void copy(app * source) {
        SASSERT(source->get_num_args() <= m_num_args);
        new (m_data) app(source->get_decl(), source->get_num_args(), source->get_args());
        SASSERT(get_app()->get_decl() == source->get_decl());
        SASSERT(get_app()->get_arg(0) == source->get_arg(0));
        SASSERT(get_app()->get_arg(1) == source->get_arg(1));
    }

    void copy_swapping_args(app * source) {
        SASSERT(source->get_num_args() == 2 && m_num_args >= 2);
        expr * args[2] = { source->get_arg(1), source->get_arg(0) };
        new (m_data) app(source->get_decl(), 2, args);
        SASSERT(get_app()->get_decl() == source->get_decl());
        SASSERT(get_app()->get_arg(0) == source->get_arg(1));
        SASSERT(get_app()->get_arg(1) == source->get_arg(0));
    }
};

// -----------------------------------
//
// variables
//
// -----------------------------------

class var : public expr {
    friend class ast_manager;

    unsigned     m_idx;
    sort *       m_sort;

    static unsigned get_obj_size() { return sizeof(var); }

    var(unsigned idx, sort * s):expr(AST_VAR), m_idx(idx), m_sort(s) {}
public:
    unsigned get_idx() const { return m_idx; }
    sort * _get_sort() const { return m_sort; }
    unsigned get_size() const { return get_obj_size(); }
};

// -----------------------------------
//
// quantifier
//
// -----------------------------------

enum quantifier_kind {
    forall_k,
    exists_k,
    lambda_k
};

class quantifier : public expr {
    friend class ast_manager;
    quantifier_kind     m_kind;
    unsigned            m_num_decls;
    expr *              m_expr;
    sort *              m_sort;
    unsigned            m_depth;
    // extra fields
    int                 m_weight;
    bool                m_has_unused_vars;
    bool                m_has_labels;
    symbol              m_qid;
    symbol              m_skid;
    unsigned            m_num_patterns;
    unsigned            m_num_no_patterns;
    char                m_patterns_decls[0];

    static unsigned get_obj_size(unsigned num_decls, unsigned num_patterns, unsigned num_no_patterns) {
        return sizeof(quantifier) + num_decls * (sizeof(sort *) + sizeof(symbol)) + (num_patterns + num_no_patterns) * sizeof(expr*);
    }

    quantifier(quantifier_kind k, unsigned num_decls, sort * const * decl_sorts, symbol const * decl_names, expr * body, sort* s,
               int weight, symbol const & qid, symbol const & skid, unsigned num_patterns, expr * const * patterns,
               unsigned num_no_patterns, expr * const * no_patterns);

    quantifier(unsigned num_decls, sort * const * decl_sorts, symbol const * decl_names, expr * body, sort* sort);

public:
    quantifier_kind get_kind() const { return m_kind; }
//    bool is_forall() const { return m_kind == forall_k; }
//    bool is_exists() const { return m_kind == exists_k; }
//    bool is_lambda() const { return m_kind == lambda_k; }

    unsigned get_num_decls() const { return m_num_decls; }
    sort * const * get_decl_sorts() const { return reinterpret_cast<sort * const *>(m_patterns_decls); }
    symbol const * get_decl_names() const { return reinterpret_cast<symbol const *>(get_decl_sorts() + m_num_decls); }
    sort * get_decl_sort(unsigned idx) const { return get_decl_sorts()[idx]; }
    symbol const & get_decl_name(unsigned idx) const { return get_decl_names()[idx]; }
    expr * get_expr() const { return m_expr; }

    sort * _get_sort() const { return m_sort; }

    unsigned get_depth() const { return m_depth; }

    int get_weight() const { return m_weight; }
    symbol const & get_qid() const { return m_qid; }
    symbol const & get_skid() const { return m_skid; }
    unsigned get_num_patterns() const { return m_num_patterns; }
    expr * const * get_patterns() const { return reinterpret_cast<expr * const *>(get_decl_names() + m_num_decls); }
    expr * get_pattern(unsigned idx) const { return get_patterns()[idx]; }
    unsigned get_num_no_patterns() const { return m_num_no_patterns; }
    expr * const * get_no_patterns() const { return reinterpret_cast<expr * const *>(get_decl_names() + m_num_decls); }
    expr * get_no_pattern(unsigned idx) const { return get_no_patterns()[idx]; }
    bool has_patterns() const { return m_num_patterns > 0 || m_num_no_patterns > 0; }
    unsigned get_size() const { return get_obj_size(m_num_decls, m_num_patterns, m_num_no_patterns); }

    bool may_have_unused_vars() const { return m_has_unused_vars; }
    void set_no_unused_vars() { m_has_unused_vars = false; }

    bool has_labels() const { return m_has_labels; }
    

    unsigned get_num_children() const { return 1 + get_num_patterns() + get_num_no_patterns(); }
    expr * get_child(unsigned idx) const {
        SASSERT(idx < get_num_children());
        if (idx == 0)
            return get_expr();
        else if (idx <= get_num_patterns())
            return get_pattern(idx - 1);
        else
            return get_no_pattern(idx - get_num_patterns() - 1);
    }
};

// -----------------------------------
//
// AST recognisers
//
// -----------------------------------

inline bool is_decl(ast const * n)       { ast_kind k = n->get_kind(); return k == AST_FUNC_DECL || k == AST_SORT; }
inline bool is_sort(ast const * n)       { return n->get_kind() == AST_SORT; }
inline bool is_func_decl(ast const * n)  { return n->get_kind() == AST_FUNC_DECL; }
inline bool is_expr(ast const * n)       { return !is_decl(n); }
inline bool is_app(ast const * n)        { return n->get_kind() == AST_APP; }
inline bool is_var(ast const * n)        { return n->get_kind() == AST_VAR; }
inline bool is_var(ast const * n, unsigned& idx) { return is_var(n) && (idx = static_cast<var const*>(n)->get_idx(), true); }
inline bool is_quantifier(ast const * n) { return n->get_kind() == AST_QUANTIFIER; }
inline bool is_forall(ast const * n)     { return is_quantifier(n) && static_cast<quantifier const *>(n)->get_kind() == forall_k; }
inline bool is_exists(ast const * n)     { return is_quantifier(n) && static_cast<quantifier const *>(n)->get_kind() == exists_k; }
inline bool is_lambda(ast const * n)     { return is_quantifier(n) && static_cast<quantifier const *>(n)->get_kind() == lambda_k; }

// -----------------------------------
//
// AST coercions
//
// -----------------------------------

inline decl *       to_decl(ast * n)       { SASSERT(is_decl(n)); return static_cast<decl *>(n); }
inline sort *       to_sort(ast * n)       { SASSERT(is_sort(n)); return static_cast<sort *>(n); }
inline func_decl *  to_func_decl(ast * n)  { SASSERT(is_func_decl(n)); return static_cast<func_decl *>(n); }
inline expr *       to_expr(ast * n)       { SASSERT(is_expr(n)); return static_cast<expr *>(n); }
inline app *        to_app(ast * n)        { SASSERT(is_app(n)); return static_cast<app *>(n); }
inline var *        to_var(ast * n)        { SASSERT(is_var(n)); return static_cast<var *>(n); }
inline quantifier * to_quantifier(ast * n) { SASSERT(is_quantifier(n)); return static_cast<quantifier *>(n); }

inline decl const *       to_decl(ast const * n)       { SASSERT(is_decl(n)); return static_cast<decl const *>(n); }
inline sort const *       to_sort(ast const * n)       { SASSERT(is_sort(n)); return static_cast<sort const *>(n); }
inline func_decl const *  to_func_decl(ast const * n)  { SASSERT(is_func_decl(n)); return static_cast<func_decl const *>(n); }
inline expr const *       to_expr(ast const * n)       { SASSERT(is_expr(n)); return static_cast<expr const *>(n); }
inline app const *        to_app(ast const * n)        { SASSERT(is_app(n)); return static_cast<app const *>(n); }
inline var const *        to_var(ast const * n)        { SASSERT(is_var(n)); return static_cast<var const *>(n); }
inline quantifier const * to_quantifier(ast const * n) { SASSERT(is_quantifier(n)); return static_cast<quantifier const *>(n); }

// -----------------------------------
//
// AST hash-consing
//
// -----------------------------------

unsigned get_node_hash(ast const * n);
bool compare_nodes(ast const * n1, ast const * n2);
unsigned get_node_size(ast const * n);
unsigned get_asts_hash(unsigned sz, ast * const* ns, unsigned init);
unsigned get_apps_hash(unsigned sz, app * const* ns, unsigned init);
unsigned get_exprs_hash(unsigned sz, expr * const* ns, unsigned init);
unsigned get_sorts_hash(unsigned sz, sort * const* ns, unsigned init);
unsigned get_decl_hash(unsigned sz, func_decl* const* ns, unsigned init);

// This is the internal comparison functor for hash-consing AST nodes.
struct ast_eq_proc {
    bool operator()(ast const * n1, ast const * n2) const {
        return n1->hash() == n2->hash() && compare_nodes(n1, n2);
    }
};

class ast_translation;

class ast_table : public chashtable<ast*, obj_ptr_hash<ast>, ast_eq_proc> {
public:
    ast_table() : chashtable({}, {}, 512 * 1024, 8 * 1024) {}
    void push_erase(ast * n);
    ast* pop_erase();
};

// -----------------------------------
//
// decl_plugin
//
// -----------------------------------

/**
   \brief Auxiliary data-structure used to initialize the parser symbol tables.
*/
struct builtin_name {
    decl_kind m_kind;
    symbol    m_name;
    builtin_name(char const * name, decl_kind k) : m_kind(k), m_name(name) {}
    builtin_name(const std::string &name, decl_kind k) : m_kind(k), m_name(name) {}
};

/**
   \brief Each family of interpreted function declarations and sorts must provide a plugin
   to build sorts and decls of the family.
*/
class decl_plugin {
protected:
    ast_manager * m_manager = nullptr;
    family_id     m_family_id = null_family_id;

    virtual void set_manager(ast_manager * m, family_id id) {
        SASSERT(m_manager == nullptr);
        m_manager   = m;
        m_family_id = id;
    }

    virtual void inherit(decl_plugin* other_p, ast_translation& ) { }

    /**
       \brief Checks whether a log is being generated and, if necessary, adds the beginning of an "[attach-meaning]" line
       to that log. The theory solver should add some description of the meaning of the term in terms of the theory's
       internal reasoning to the end of the line and insert a line break.
       
       \param a the term that should be described.

       \return true if a log is being generated, false otherwise.
    */
    bool log_constant_meaning_prelude(app * a);

    friend class ast_manager;

public:
    virtual ~decl_plugin() {}
    virtual void finalize() {}


    virtual decl_plugin * mk_fresh() = 0;

    family_id get_family_id() const { return m_family_id; }

    virtual sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) = 0;

    virtual func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                     unsigned arity, sort * const * domain, sort * range) = 0;

    virtual func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const* parameters,
                                     unsigned num_args, expr * const * args, sort * range);

    /**
       \brief Return true if the plugin can decide whether two
       interpreted constants are equal or not.

       For all a, b:
          If is_value(a) and is_value(b)
          Then,
               are_equal(a, b) != are_distinct(a, b)

       The may be much more expensive than checking a pointer.

       We need this because some plugin values are too expensive too canonize.
    */
    virtual bool is_value(app * a) const { return false; }

    /**
       \brief Return true if \c a is a unique plugin value.
       The following property should hold for unique theory values:

       For all a, b:
          If is_unique_value(a) and is_unique_value(b)
          Then,
              a == b (pointer equality)
              IFF
              the interpretations of these theory terms are equal.

       \remark This is a stronger version of is_value.
    */
    virtual bool is_unique_value(app * a) const { return false; }

    virtual bool are_equal(app * a, app * b) const { return a == b; }

    virtual bool are_distinct(app * a, app * b) const { return a != b && is_unique_value(a) && is_unique_value(b); }

    virtual void get_op_names(svector<builtin_name> & op_names, symbol const & logic = symbol()) {}

    virtual void get_sort_names(svector<builtin_name> & sort_names, symbol const & logic = symbol()) {}

    virtual expr * get_some_value(sort * s) { return nullptr; }

    // Return true if the interpreted sort s does not depend on uninterpreted sorts.
    // This may be the case, for example, for array and datatype sorts.
    virtual bool is_fully_interp(sort * s) const { return true; }

    // Event handlers for deleting/translating PARAM_EXTERNAL
    virtual void del(parameter const & p) {}
    virtual parameter translate(parameter const & p, decl_plugin & target) { UNREACHABLE(); return p; }

    virtual bool is_considered_uninterpreted(func_decl * f) { return false; }
};

// -----------------------------------
//
// basic_decl_plugin (i.e., builtin plugin)
//
// -----------------------------------

enum basic_sort_kind {
    BOOL_SORT,
    PROOF_SORT
};

enum basic_op_kind {
    OP_TRUE, OP_FALSE, OP_EQ, OP_DISTINCT, OP_ITE, OP_AND, OP_OR, OP_XOR, OP_NOT, OP_IMPLIES, OP_OEQ, LAST_BASIC_OP,

    PR_UNDEF, PR_TRUE, PR_ASSERTED, PR_GOAL, PR_MODUS_PONENS, PR_REFLEXIVITY, PR_SYMMETRY, PR_TRANSITIVITY, PR_TRANSITIVITY_STAR, PR_MONOTONICITY, PR_QUANT_INTRO, PR_BIND,
    PR_DISTRIBUTIVITY, PR_AND_ELIM, PR_NOT_OR_ELIM, PR_REWRITE, PR_REWRITE_STAR, PR_PULL_QUANT,
    PR_PUSH_QUANT, PR_ELIM_UNUSED_VARS, PR_DER, PR_QUANT_INST,

    PR_HYPOTHESIS, PR_LEMMA, PR_UNIT_RESOLUTION, PR_IFF_TRUE, PR_IFF_FALSE, PR_COMMUTATIVITY, PR_DEF_AXIOM,

    PR_ASSUMPTION_ADD, PR_TH_ASSUMPTION_ADD, PR_LEMMA_ADD, PR_TH_LEMMA_ADD, PR_REDUNDANT_DEL, PR_CLAUSE_TRAIL,

    PR_DEF_INTRO, PR_APPLY_DEF, PR_IFF_OEQ, PR_NNF_POS, PR_NNF_NEG, PR_SKOLEMIZE, 
    PR_MODUS_PONENS_OEQ, PR_TH_LEMMA, PR_HYPER_RESOLVE, LAST_BASIC_PR
};

class basic_decl_plugin : public decl_plugin {
protected:
    sort *      m_bool_sort = nullptr;
    func_decl * m_true_decl = nullptr;
    func_decl * m_false_decl = nullptr;
    func_decl * m_and_decl = nullptr;
    func_decl * m_or_decl = nullptr;
    func_decl * m_xor_decl = nullptr;
    func_decl * m_not_decl = nullptr;
    func_decl * m_implies_decl = nullptr;
    ptr_vector<func_decl> m_eq_decls;  // cached eqs
    ptr_vector<func_decl> m_ite_decls; // cached ites

    ptr_vector<func_decl> m_oeq_decls;  // cached observational eqs
    sort *      m_proof_sort = nullptr;
    func_decl * m_undef_decl = nullptr;
    func_decl * m_true_pr_decl = nullptr;
    func_decl * m_asserted_decl = nullptr;
    func_decl * m_goal_decl = nullptr;
    func_decl * m_modus_ponens_decl = nullptr;
    func_decl * m_reflexivity_decl = nullptr;
    func_decl * m_symmetry_decl = nullptr;
    func_decl * m_transitivity_decl = nullptr;
    func_decl * m_quant_intro_decl = nullptr;
    func_decl * m_and_elim_decl = nullptr;
    func_decl * m_not_or_elim_decl = nullptr;
    func_decl * m_rewrite_decl = nullptr;
    func_decl * m_pull_quant_decl = nullptr;
    func_decl * m_push_quant_decl = nullptr;
    func_decl * m_elim_unused_vars_decl = nullptr;
    func_decl * m_der_decl = nullptr;
    func_decl * m_quant_inst_decl = nullptr;
    ptr_vector<func_decl> m_monotonicity_decls;
    ptr_vector<func_decl> m_transitivity_star_decls;
    ptr_vector<func_decl> m_distributivity_decls;
    ptr_vector<func_decl> m_assoc_flat_decls;
    ptr_vector<func_decl> m_rewrite_star_decls;

    func_decl * m_hypothesis_decl = nullptr;
    func_decl * m_iff_true_decl = nullptr;
    func_decl * m_iff_false_decl = nullptr;
    func_decl * m_commutativity_decl = nullptr;
    func_decl * m_def_axiom_decl = nullptr;
    func_decl * m_lemma_decl = nullptr;
    ptr_vector<func_decl> m_unit_resolution_decls;

    func_decl * m_def_intro_decl = nullptr;
    func_decl * m_iff_oeq_decl = nullptr;
    func_decl * m_skolemize_decl = nullptr;
    func_decl * m_mp_oeq_decl = nullptr;
    func_decl * m_assumption_add_decl = nullptr;
    func_decl * m_lemma_add_decl = nullptr;
    func_decl * m_th_assumption_add_decl = nullptr;
    func_decl * m_th_lemma_add_decl = nullptr;
    func_decl * m_redundant_del_decl = nullptr;
    ptr_vector<func_decl> m_apply_def_decls;
    ptr_vector<func_decl> m_nnf_pos_decls;
    ptr_vector<func_decl> m_nnf_neg_decls;

    ptr_vector<func_decl> m_th_lemma_decls;
    func_decl * m_hyper_res_decl0 = nullptr;

    static bool is_proof(decl_kind k) { return k > LAST_BASIC_OP; }
    bool check_proof_sorts(basic_op_kind k, unsigned arity, sort * const * domain) const;
    bool check_proof_args(basic_op_kind k, unsigned num_args, expr * const * args) const;
    func_decl * mk_bool_op_decl(char const * name, basic_op_kind k, unsigned num_args = 0,
                                bool asooc = false, bool comm = false, bool idempotent = false, bool flat_associative = false, bool chainable = false);
    func_decl * mk_implies_decl();
    func_decl * mk_proof_decl(char const * name, basic_op_kind k, unsigned num_parents, bool inc_ref);
    func_decl * mk_proof_decl(char const * name, basic_op_kind k, unsigned num_parents, func_decl*& fn);
    func_decl * mk_proof_decl(char const * name, basic_op_kind k, unsigned num_parents, ptr_vector<func_decl> & cache);
    func_decl * mk_compressed_proof_decl(char const * name, basic_op_kind k, unsigned num_parents);
    func_decl * mk_proof_decl(basic_op_kind k, unsigned num_parents);
    func_decl * mk_proof_decl(basic_op_kind k, unsigned num_parameters, parameter const* params, unsigned num_parents);
    func_decl * mk_proof_decl(
        char const * name, basic_op_kind k,
        unsigned num_parameters, parameter const* params, unsigned num_parents);


    void set_manager(ast_manager * m, family_id id) override;
    func_decl * mk_eq_decl_core(char const * name, decl_kind k, sort * s, ptr_vector<func_decl> & cache);
    func_decl * mk_ite_decl(sort * s);
    sort* join(sort* s1, sort* s2);
    sort* join(unsigned n, sort*const* srts);
    sort* join(unsigned n, expr*const* es);
public:

    void finalize() override;

    decl_plugin * mk_fresh() override {
        return alloc(basic_decl_plugin);
    }

    sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const* parameters) override;

    func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                             unsigned arity, sort * const * domain, sort * range) override;

    func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                             unsigned num_args, expr * const * args, sort * range) override;

    void get_op_names(svector<builtin_name> & op_names, symbol const & logic) override;

    void get_sort_names(svector<builtin_name> & sort_names, symbol const & logic) override;

    bool is_value(app* a) const override;

    bool is_unique_value(app* a) const override;

    sort * mk_bool_sort() const { return m_bool_sort; }
    sort * mk_proof_sort() const { return m_proof_sort; }

    expr * get_some_value(sort * s) override;
};

typedef app proof; /* a proof is just an application */

// -----------------------------------
//
// label_decl_plugin
//
// -----------------------------------

enum label_op_kind {
    OP_LABEL,
    OP_LABEL_LIT
};

/**
   \brief Labels are identity functions used to mark sub-expressions.
*/
class label_decl_plugin : public decl_plugin {
    symbol m_lblpos;
    symbol m_lblneg;
    symbol m_lbllit;

    void set_manager(ast_manager * m, family_id id) override;

public:
    label_decl_plugin();

    decl_plugin * mk_fresh() override { return alloc(label_decl_plugin); }

    sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) override;

    /**
       contract: when label
       parameter[0] (int):      0 - if the label is negative, 1 - if positive.
       parameter[1] (symbol):   label's tag.
       ...
       parameter[n-1] (symbol): label's tag.

       contract: when label literal (they are always positive)
       parameter[0] (symbol):   label's tag
       ...
       parameter[n-1] (symbol): label's tag.
    */
    func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                             unsigned arity, sort * const * domain, sort * range) override;
};

// -----------------------------------
//
// pattern_decl_plugin
//
// -----------------------------------

enum pattern_op_kind {
    OP_PATTERN
};

/**
   \brief Patterns are used to group expressions. These expressions are using during E-matching for
   heuristic quantifier instantiation.
*/
class pattern_decl_plugin : public decl_plugin {
public:
    decl_plugin * mk_fresh() override { return alloc(pattern_decl_plugin); }

    sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) override;

    func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                             unsigned arity, sort * const * domain, sort * range) override;
};

// -----------------------------------
//
// model_value_plugin
//
// -----------------------------------

enum model_value_op_kind {
    OP_MODEL_VALUE
};

/**
   \brief Values are used during model construction. All values are
   assumed to be different.  Users should not use them, since they may
   introduce unsoundness if the sort of a value is finite.

   Moreover, values should never be internalized in a logical context.

   However, values can be used during evaluation (i.e., simplification).

   \remark Model values can be viewed as the partition ids in Z3 1.x.
*/
class model_value_decl_plugin : public decl_plugin {
public:
    decl_plugin * mk_fresh() override { return alloc(model_value_decl_plugin); }

    sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) override;

    /**
       contract:
       parameter[0]: (integer) value idx
       parameter[1]: (ast)     sort of the value.
    */
    func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                             unsigned arity, sort * const * domain, sort * range) override;

    bool is_value(app* n) const override;

    bool is_unique_value(app* a) const override;
};

// -----------------------------------
//
// user_sort_plugin for supporting user declared sorts in SMT2
//
// -----------------------------------

class user_sort_plugin : public decl_plugin {
    svector<symbol> m_sort_names;
    dictionary<int> m_name2decl_kind;
public:
    sort * mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) override;
    func_decl * mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                             unsigned arity, sort * const * domain, sort * range) override;
    decl_kind register_name(symbol s);
    decl_plugin * mk_fresh() override;
};


// -----------------------------------
//
// Auxiliary functions
//
// -----------------------------------

// Return true if n is an application of d.
inline bool is_app_of(expr const * n, func_decl const * d) { return n->get_kind() == AST_APP && to_app(n)->get_decl() == d; }
inline bool is_app_of(expr const * n, family_id fid, decl_kind k) { return n->get_kind() == AST_APP && to_app(n)->is_app_of(fid, k); }
inline bool is_sort_of(sort const * s, family_id fid, decl_kind k) { return s->is_sort_of(fid, k); }
inline bool is_uninterp_const(expr const * n) { return n->get_kind() == AST_APP && to_app(n)->get_num_args() == 0 && to_app(n)->get_family_id() == null_family_id; }
inline bool is_uninterp(expr const * n) { return n->get_kind() == AST_APP && to_app(n)->get_family_id() == null_family_id; }
inline bool is_decl_of(func_decl const * d, family_id fid, decl_kind k) { return d->get_family_id() == fid && d->get_decl_kind() == k; }
inline bool is_ground(expr const * n) { return is_app(n) && to_app(n)->is_ground(); }
inline bool is_non_ground(expr const * n) { return ( ! is_ground(n)); }

inline unsigned get_depth(expr const * n) {
    if (is_app(n)) return to_app(n)->get_depth();
    else if (is_quantifier(n)) return to_quantifier(n)->get_depth();
    else return 1;
}

inline bool has_quantifiers(expr const * n) {
    return is_app(n) ? to_app(n)->has_quantifiers() : is_quantifier(n);
}

inline bool has_labels(expr const * n) {
    if (is_app(n)) return to_app(n)->has_labels();
    else if (is_quantifier(n)) return to_quantifier(n)->has_labels();
    else return false;
}


// -----------------------------------
//
// Get Some Value functor
//
// Functor for returning some value
// of the given sort.
//
// -----------------------------------
class some_value_proc {
public:
    virtual expr * operator()(sort * s) = 0;
};

// -----------------------------------
//
// Proof generation mode
//
// -----------------------------------

enum proof_gen_mode {
    PGM_DISABLED,
    PGM_ENABLED
};

// -----------------------------------
//
// ast_manager
//
// -----------------------------------

class ast_manager {
    friend class basic_decl_plugin;
protected:
    struct config {
        typedef ast_manager              value_manager;
        typedef small_object_allocator   allocator;
        static const bool ref_count        = true;
    };

    struct array_config : public config {
        static const bool preserve_roots   = true;
        static const unsigned max_trail_sz = 16;
        static const unsigned factor       = 2;
    };

    struct expr_array_config : public array_config {
        typedef expr *                   value;
    };

    typedef parray_manager<expr_array_config> expr_array_manager;

    struct expr_dependency_config : public config {
        typedef expr *                   value;
    };

    typedef dependency_manager<expr_dependency_config> expr_dependency_manager;

public:
    typedef expr_array_manager::ref expr_array;
    typedef expr_dependency_manager::dependency expr_dependency;

protected:
    struct expr_dependency_array_config : public array_config {
        typedef expr_dependency *        value;
    };

    typedef parray_manager<expr_dependency_array_config> expr_dependency_array_manager;

public:
    typedef expr_dependency_array_manager::ref expr_dependency_array;

    void show_id_gen();

    void update_fresh_id(ast_manager const& other);

    unsigned mk_fresh_id() { return ++m_fresh_id; }

protected:
    reslimit                  m_limit;
    small_object_allocator    m_alloc;
    family_manager            m_family_manager;
    expr_array_manager        m_expr_array_manager;
    expr_dependency_manager   m_expr_dependency_manager;
    expr_dependency_array_manager m_expr_dependency_array_manager;
    ptr_vector<decl_plugin>   m_plugins;
    proof_gen_mode            m_proof_mode;
    bool                      m_int_real_coercions; // If true, use hack that automatically introduces to_int/to_real when needed.
    ast_table                 m_ast_table;
    obj_map<func_decl, quantifier*> m_lambda_defs;
    id_gen                    m_expr_id_gen;
    id_gen                    m_decl_id_gen;
    sort *                    m_bool_sort;
    sort *                    m_proof_sort;
    app *                     m_true;
    app *                     m_false;
    proof *                   m_undef_proof;
    unsigned                  m_fresh_id;
    bool                      m_debug_ref_count;
    u_map<unsigned>           m_debug_free_indices;
    std::fstream*             m_trace_stream;
    bool                      m_trace_stream_owner;
#ifdef Z3DEBUG
    bool slow_not_contains(ast const * n);
#endif
    ast_manager *             m_format_manager; // hack for isolating format objects in a different manager.
    symbol                    m_lambda_def;

    void init();

    bool coercion_needed(func_decl * decl, unsigned num_args, expr * const * args);

    void check_args(func_decl* f, unsigned n, expr* const* es);


public:
    ast_manager(proof_gen_mode = PGM_DISABLED, char const * trace_file = nullptr, bool is_format_manager = false);
    ast_manager(proof_gen_mode, std::fstream * trace_stream, bool is_format_manager = false);
    ast_manager(ast_manager const & src, bool disable_proofs = false);
    ~ast_manager();

    // propagate cancellation signal to decl_plugins

    bool has_trace_stream() const { return m_trace_stream != nullptr; }
    std::ostream & trace_stream() { SASSERT(has_trace_stream()); return *m_trace_stream; }
    struct suspend_trace {
        ast_manager& m;
        std::fstream* m_tr;
        suspend_trace(ast_manager& m): m(m), m_tr(m.m_trace_stream) { m.m_trace_stream = nullptr; }
        ~suspend_trace() { m.m_trace_stream = m_tr; }
    };

    void enable_int_real_coercions(bool f) { m_int_real_coercions = f; }
    bool int_real_coercions() const { return m_int_real_coercions; }

    // Return true if s1 and s2 are equal, or coercions are enabled, and s1 and s2 are compatible.
    bool compatible_sorts(sort * s1, sort * s2) const;
    expr* coerce_to(expr* e, sort* s);

    // For debugging purposes
    void display_free_ids(std::ostream & out) { m_expr_id_gen.display_free_ids(out); out << "\n"; m_decl_id_gen.display_free_ids(out); }

    void compact_memory();

    void compress_ids();

    // Equivalent to throw ast_exception(msg)
    Z3_NORETURN void raise_exception(char const * msg);
    Z3_NORETURN void raise_exception(std::string && s);

    std::ostream& display(std::ostream& out, parameter const& p);

    bool is_format_manager() const { return m_format_manager == nullptr; }

    ast_manager & get_format_manager() { return is_format_manager() ? *this : *m_format_manager; }

    void copy_families_plugins(ast_manager const & from);

    small_object_allocator & get_allocator() { return m_alloc; }

    family_id mk_family_id(symbol const & s) { return m_family_manager.mk_family_id(s); }
    family_id mk_family_id(char const * s) { return mk_family_id(symbol(s)); }

    family_id get_family_id(symbol const & s) const { return m_family_manager.get_family_id(s); }
    family_id get_family_id(char const * s) const { return get_family_id(symbol(s)); }

    symbol const & get_family_name(family_id fid) const { return m_family_manager.get_name(fid); }

    bool is_builtin_family_id(family_id fid) const {
        return fid >= null_family_id && fid <= last_builtin_family_id;
    }

    reslimit& limit() { return m_limit; }
    // bool canceled() { return !limit().inc(); }
    bool inc() { return limit().inc(); }

    void register_plugin(symbol const & s, decl_plugin * plugin);

    void register_plugin(family_id id, decl_plugin * plugin);

    decl_plugin * get_plugin(family_id fid) const;

    bool has_plugin(family_id fid) const { return get_plugin(fid) != nullptr; }

    bool has_plugin(symbol const & s) const { return m_family_manager.has_family(s) && has_plugin(m_family_manager.get_family_id(s)); }

    void get_dom(svector<symbol> & dom) const { m_family_manager.get_dom(dom); }

    void get_range(svector<family_id> & range) const { m_family_manager.get_range(range); }

    family_id get_basic_family_id() const { return basic_family_id; }

    basic_decl_plugin * get_basic_decl_plugin() const { return static_cast<basic_decl_plugin*>(get_plugin(basic_family_id)); }

    family_id get_user_sort_family_id() const { return user_sort_family_id; }

    user_sort_plugin * get_user_sort_plugin() const { return static_cast<user_sort_plugin*>(get_plugin(user_sort_family_id)); }

    /**
       \brief Debugging support method: set the next expression identifier to be the least value id' s.t.
              - id' >= id
              - id' is not used by any AST in m_table
              - id' is not in the expression m_free_ids

        This method should be only used to create small repros that exposes bugs in Z3.
    */
    void set_next_expr_id(unsigned id);

    bool is_value(expr * e) const;

    bool is_unique_value(expr * e) const;

    bool are_equal(expr * a, expr * b) const;

    bool are_distinct(expr * a, expr * b) const;

    bool contains(ast * a) const { return m_ast_table.contains(a); }
    
    bool is_lambda_def(quantifier* q) const { return q->get_qid() == m_lambda_def; }
    void add_lambda_def(func_decl* f, quantifier* q);
    quantifier* is_lambda_def(func_decl* f);
    

    symbol const& lambda_def_qid() const { return m_lambda_def; }

    unsigned get_num_asts() const { return m_ast_table.size(); }

    void debug_ref_count() { m_debug_ref_count = true; }

    void inc_ref(ast* n) {
        if (n) 
            n->inc_ref();
    }
    
    void dec_ref(ast* n) {
        if (n) {
            n->dec_ref();
            if (n->get_ref_count() == 0)
                delete_node(n);
        }
    }

    template<typename T>
    void inc_array_ref(unsigned sz, T * const * a) {
        for(unsigned i = 0; i < sz; i++) {
            inc_ref(a[i]);
        }
    }

    template<typename T>
    void dec_array_ref(unsigned sz, T * const * a) {
        for(unsigned i = 0; i < sz; i++) {
            dec_ref(a[i]);
        }
    }

    static unsigned get_node_size(ast const * n);

    size_t get_allocation_size() const {
        return m_alloc.get_allocation_size();
    }

    std::ostream& display(std::ostream& out) const;

protected:
    ast * register_node_core(ast * n);

    template<typename T>
    T * register_node(T * n) {
        return static_cast<T *>(register_node_core(n));
    }

    void delete_node(ast * n);

    void * allocate_node(unsigned size) {
        return m_alloc.allocate(size);
    }

    void deallocate_node(ast * n, unsigned sz) {
        m_alloc.deallocate(sz, n);
    }

public:
    void check_sort(func_decl const * decl, unsigned num_args, expr * const * args) const;
    void check_sorts_core(ast const * n) const;
    bool check_sorts(ast const * n) const;

    bool is_bool(expr const * n) const;
    bool is_bool(sort const * s) const { return s == m_bool_sort; }
    decl_kind get_eq_op(expr const * n) const { return OP_EQ; }

private:
    sort * mk_sort(symbol const & name, sort_info * info);

public:
    sort * mk_uninterpreted_sort(symbol const & name, unsigned num_parameters, parameter const * parameters);

    sort * mk_uninterpreted_sort(symbol const & name) { return mk_uninterpreted_sort(name, 0, nullptr); }

    sort * mk_sort(symbol const & name, sort_info const & info) {
        if (info.get_family_id() == null_family_id) {
            return mk_uninterpreted_sort(name);
        }
        else {
            return mk_sort(name, &const_cast<sort_info &>(info));
        }
    }

    sort * mk_sort(family_id fid, decl_kind k, unsigned num_parameters = 0, parameter const * parameters = nullptr);

    sort * substitute(sort* s, unsigned n, sort * const * src, sort * const * dst);

    sort * mk_bool_sort() const { return m_bool_sort; }

    sort * mk_proof_sort() const { return m_proof_sort; }

    sort * mk_fresh_sort(char const * prefix = "");

    bool is_uninterp(sort const * s) const { return s->get_family_id() == null_family_id || s->get_family_id() == user_sort_family_id; }

    /**
       \brief A sort is "fully" interpreted if it is interpreted,
       and doesn't depend on other uninterpreted sorts.
    */
    bool is_fully_interp(sort * s) const;

    func_decl * mk_func_decl(family_id fid, decl_kind k, unsigned num_parameters, parameter const * parameters,
                             unsigned arity, sort * const * domain, sort * range = nullptr);

    func_decl * mk_func_decl(family_id fid, decl_kind k, unsigned num_parameters, parameter const * parameters,
                             unsigned num_args, expr * const * args, sort * range = nullptr);

    app * mk_app(family_id fid, decl_kind k, unsigned num_parameters = 0, parameter const * parameters = nullptr,
                 unsigned num_args = 0, expr * const * args = nullptr, sort * range = nullptr);

    app * mk_app(family_id fid, decl_kind k, unsigned num_args, expr * const * args);

    app * mk_app(family_id fid, decl_kind k, expr * arg);

    app * mk_app(family_id fid, decl_kind k, expr * arg1, expr * arg2);

    app * mk_app(family_id fid, decl_kind k, expr * arg1, expr * arg2, expr * arg3);

    app * mk_const(family_id fid, decl_kind k) { return mk_app(fid, k, 0, static_cast<expr * const *>(nullptr)); }
private:
    func_decl * mk_func_decl(symbol const & name, unsigned arity, sort * const * domain, sort * range,
                             func_decl_info * info);

    app * mk_app_core(func_decl * decl, expr * arg1, expr * arg2);

    app * mk_app_core(func_decl * decl, unsigned num_args, expr * const * args);

public:
    func_decl * mk_func_decl(symbol const & name, unsigned arity, sort * const * domain, sort * range) {
        return mk_func_decl(name, arity, domain, range, static_cast<func_decl_info *>(nullptr));
    }

    func_decl * mk_func_decl(symbol const & name, unsigned arity, sort * const * domain, sort * range,
                             func_decl_info const & info) {
        if (info.is_null()) {
            return mk_func_decl(name, arity, domain, range, static_cast<func_decl_info *>(nullptr));
        }
        else {
            return mk_func_decl(name, arity, domain, range, & const_cast<func_decl_info&>(info));
        }
    }

    func_decl * mk_func_decl(unsigned arity, sort * const * domain, func_decl_info const & info) {
        return mk_func_decl(info.get_family_id(), info.get_decl_kind(), info.get_num_parameters(), info.get_parameters(),
                            arity, domain);
    }

    func_decl * mk_skolem_const_decl(symbol const& name, sort* s) {
        func_decl_info info;
        info.set_skolem(true);
        return mk_func_decl(name, static_cast<unsigned>(0), nullptr, s, info);
    }

    func_decl * mk_const_decl(const char* name, sort * s) {
        return mk_func_decl(symbol(name), static_cast<unsigned>(0), nullptr, s);
    }

    func_decl * mk_const_decl(std::string const& name, sort * s) {
        return mk_func_decl(symbol(name.c_str()), static_cast<unsigned>(0), nullptr, s);
    }

    func_decl * mk_const_decl(symbol const & name, sort * s) {
        return mk_func_decl(name, static_cast<unsigned>(0), nullptr, s);
    }

    func_decl * mk_const_decl(symbol const & name, sort * s, func_decl_info const & info) {
        return mk_func_decl(name, static_cast<unsigned>(0), nullptr, s, info);
    }

    func_decl * mk_func_decl(symbol const & name, sort * domain, sort * range, func_decl_info const & info) {
        return mk_func_decl(name, 1, &domain, range, info);
    }

    func_decl * mk_func_decl(symbol const & name, sort * domain, sort * range) {
        return mk_func_decl(name, 1, &domain, range);
    }

    func_decl * mk_func_decl(symbol const & name, sort * domain1, sort * domain2, sort * range, func_decl_info const & info) {
        sort * d[2] = { domain1, domain2 };
        return mk_func_decl(name, 2, d, range, info);
    }

    func_decl * mk_func_decl(symbol const & name, sort * domain1, sort * domain2, sort * range) {
        sort * d[2] = { domain1, domain2 };
        return mk_func_decl(name, 2, d, range);
    }

    func_decl * mk_func_decl(symbol const & name, unsigned arity, sort * const * domain, sort * range,
                             bool assoc, bool comm = false, bool inj = false);

    func_decl * mk_func_decl(symbol const & name, sort * domain1, sort * domain2, sort * range, bool assoc, bool comm = false) {
        sort * d[2] = { domain1, domain2 };
        return mk_func_decl(name, 2, d, range, assoc, comm, false);
    }

    bool is_considered_uninterpreted(func_decl* f) {
        if (f->get_family_id() == null_family_id) {
            return true;
        }
        decl_plugin* p = get_plugin(f->get_family_id());
        return !p || p->is_considered_uninterpreted(f);        
    }

    app * mk_app(func_decl * decl, unsigned num_args, expr * const * args);

    app* mk_app(func_decl* decl, ref_vector<expr, ast_manager> const& args) {
        return mk_app(decl, args.size(), args.data());
    }

    app* mk_app(func_decl* decl, ref_buffer<expr, ast_manager> const& args) {
        return mk_app(decl, args.size(), args.data());
    }

    app* mk_app(func_decl* decl, ref_vector<app, ast_manager> const& args) {
        return mk_app(decl, args.size(), (expr*const*)args.data());
    }

    app * mk_app(func_decl * decl, ptr_vector<expr> const& args) {
        return mk_app(decl, args.size(), args.data());
    }

    app * mk_app(func_decl * decl, ptr_buffer<expr> const& args) {
        return mk_app(decl, args.size(), args.data());
    }

    app * mk_app(func_decl * decl, ptr_vector<app> const& args) {
        return mk_app(decl, args.size(), (expr*const*)args.data());
    }

    app * mk_app(func_decl * decl, expr * const * args) {
        return mk_app(decl, decl->get_arity(), args);
    }

    app * mk_app(func_decl * decl, expr * arg) {
        SASSERT(decl->get_arity() == 1);
        return mk_app(decl, 1, &arg);
    }

    app * mk_app(func_decl * decl, expr * arg1, expr * arg2) {
        SASSERT(decl->get_arity() == 2);
        expr * args[2] = { arg1, arg2 };
        return mk_app(decl, 2, args);
    }

    app * mk_app(func_decl * decl, expr * arg1, expr * arg2, expr * arg3) {
        SASSERT(decl->get_arity() == 3);
        expr * args[3] = { arg1, arg2, arg3 };
        return mk_app(decl, 3, args);
    }

    app * mk_const(func_decl * decl) {
        SASSERT(decl->get_arity() == 0);
        return mk_app(decl, static_cast<unsigned>(0), static_cast<expr**>(nullptr));
    }

    app * mk_skolem_const(symbol const & name, sort * s) {
        return mk_const(mk_skolem_const_decl(name, s));
    }

    app * mk_const(symbol const & name, sort * s) {
        return mk_const(mk_const_decl(name, s));
    }

    app * mk_const(std::string const & name, sort * s) {
        return mk_const(mk_const_decl(name, s));
    }

    app * mk_const(char const* name, sort * s) {
        return mk_const(mk_const_decl(name, s));
    }

    func_decl * mk_fresh_func_decl(symbol const & prefix, symbol const & suffix, unsigned arity,
                                   sort * const * domain, sort * range, bool skolem = true);

    func_decl * mk_fresh_func_decl(unsigned arity, sort * const * domain, sort * range, bool skolem = true) { 
        return mk_fresh_func_decl(symbol::null, symbol::null, arity, domain, range, skolem); 
    }

    func_decl * mk_fresh_func_decl(char const * prefix, char const * suffix, unsigned arity,
                                   sort * const * domain, sort * range, bool skolem = true) {
        return mk_fresh_func_decl(symbol(prefix), symbol(suffix), arity, domain, range, skolem);
    }

    func_decl * mk_fresh_func_decl(char const * prefix, unsigned arity, sort * const * domain, sort * range, bool skolem = true) {
        return mk_fresh_func_decl(symbol(prefix), symbol::null, arity, domain, range, skolem);
    }

    app * mk_fresh_const(char const * prefix, sort * s, bool skolem = true) { 
        return mk_const(mk_fresh_func_decl(prefix, 0, nullptr, s, skolem)); 
    }

    app * mk_fresh_const(std::string const& prefix, sort * s, bool skolem = true) { 
        return mk_fresh_const(prefix.c_str(), s, skolem);        
    }

    app * mk_fresh_const(symbol const& prefix, sort * s, bool skolem = true) { 
        auto str = prefix.str();
        return mk_fresh_const(str.c_str(), s, skolem);
    }

    symbol mk_fresh_var_name(char const * prefix = nullptr);

    var * mk_var(unsigned idx, sort * ty);

    app * mk_label(bool pos, unsigned num_names, symbol const * names, expr * n);

    app * mk_label(bool pos, symbol const & name, expr * n);

    bool is_label(expr const * n, bool & pos, buffer<symbol> & names) const;

    bool is_label(expr const * n, bool & pos, buffer<symbol> & names, expr*& l) const {
        return is_label(n, pos, names)?(l = to_app(n)->get_arg(0), true):false;
    }

    bool is_label(expr const * n) const { return is_app_of(n, label_family_id, OP_LABEL); }

    bool is_label(expr const * n, expr*& l) const {
        return is_label(n)?(l = to_app(n)->get_arg(0), true):false;
    }

    bool is_label(expr const * n, bool& pos) const {
        if (is_app_of(n, label_family_id, OP_LABEL)) {
            pos  = to_app(n)->get_decl()->get_parameter(0).get_int() != 0;
            return true;
        }
        else {
            return false;
        }
    }

    app * mk_label_lit(unsigned num_names, symbol const * names);

    app * mk_label_lit(symbol const & name);

    bool is_label_lit(expr const * n, buffer<symbol> & names) const;

    bool is_label_lit(expr const * n) const { return is_app_of(n, label_family_id, OP_LABEL_LIT); }

    family_id get_label_family_id() const { return label_family_id; }

    app * mk_pattern(unsigned num_exprs, app * const * exprs);

    app * mk_pattern(app * expr) { return mk_pattern(1, &expr); }

    bool is_pattern(expr const * n) const;

    bool is_pattern(expr const *n, ptr_vector<expr> &args);

public:

    quantifier * mk_quantifier(quantifier_kind k, unsigned num_decls, sort * const * decl_sorts, symbol const * decl_names, expr * body, 
                               int weight = 0, symbol const & qid = symbol::null, symbol const & skid = symbol::null,
                               unsigned num_patterns = 0, expr * const * patterns = nullptr,
                               unsigned num_no_patterns = 0, expr * const * no_patterns = nullptr);

    quantifier * mk_forall(unsigned num_decls, sort * const * decl_sorts, symbol const * decl_names, expr * body,
                           int weight = 0, symbol const & qid = symbol::null, symbol const & skid = symbol::null,
                           unsigned num_patterns = 0, expr * const * patterns = nullptr,
                           unsigned num_no_patterns = 0, expr * const * no_patterns = nullptr) {
        return mk_quantifier(forall_k, num_decls, decl_sorts, decl_names, body, weight, qid, skid, num_patterns, patterns,
                             num_no_patterns, no_patterns);
    }

    quantifier * mk_exists(unsigned num_decls, sort * const * decl_sorts, symbol const * decl_names, expr * body,
                           int weight = 0, symbol const & qid = symbol::null, symbol const & skid = symbol::null,
                           unsigned num_patterns = 0, expr * const * patterns = nullptr,
                           unsigned num_no_patterns = 0, expr * const * no_patterns = nullptr) {
        return mk_quantifier(exists_k, num_decls, decl_sorts, decl_names, body, weight, qid, skid, num_patterns, patterns,
                             num_no_patterns, no_patterns);
    }

    quantifier * mk_lambda(unsigned num_decls, sort * const * decl_sorts, symbol const * decl_names, expr * body);

    quantifier * update_quantifier(quantifier * q, unsigned new_num_patterns, expr * const * new_patterns, expr * new_body);

    quantifier * update_quantifier(quantifier * q, unsigned new_num_patterns, expr * const * new_patterns, unsigned new_num_no_patterns, expr * const * new_no_patterns, expr * new_body);

    quantifier * update_quantifier(quantifier * q, expr * new_body);

    quantifier * update_quantifier_weight(quantifier * q, int new_weight);

    quantifier * update_quantifier(quantifier * q, quantifier_kind new_kind, expr * new_body);

    quantifier * update_quantifier(quantifier * q, quantifier_kind new_kind, unsigned new_num_patterns, expr * const * new_patterns, expr * new_body);

// -----------------------------------
//
// expr_array
//
// -----------------------------------
public:
    void mk(expr_array & r) { m_expr_array_manager.mk(r); }
    void del(expr_array & r) { m_expr_array_manager.del(r); }
    void copy(expr_array const & s, expr_array & r) { m_expr_array_manager.copy(s, r); }
    unsigned size(expr_array const & r) const { return m_expr_array_manager.size(r); }
    bool empty(expr_array const & r) const { return m_expr_array_manager.empty(r); }
    expr * get(expr_array const & r, unsigned i) const { return m_expr_array_manager.get(r, i); }
    void set(expr_array & r, unsigned i, expr * v) { m_expr_array_manager.set(r, i, v); }
    void set(expr_array const & s, unsigned i, expr * v, expr_array & r) { m_expr_array_manager.set(s, i, v, r); }
    void push_back(expr_array & r, expr * v) { m_expr_array_manager.push_back(r, v); }
    void push_back(expr_array const & s, expr * v, expr_array & r) { m_expr_array_manager.push_back(s, v, r); }
    void pop_back(expr_array & r) { m_expr_array_manager.pop_back(r); }
    void pop_back(expr_array const & s, expr_array & r) { m_expr_array_manager.pop_back(s, r); }
    void unshare(expr_array & r) { m_expr_array_manager.unshare(r); }
    void unfold(expr_array & r) { m_expr_array_manager.unfold(r); }
    void reroot(expr_array & r) { m_expr_array_manager.reroot(r); }

// -----------------------------------
//
// expr_dependency
//
// -----------------------------------
public:
    expr_dependency * mk_empty_dependencies() { return m_expr_dependency_manager.mk_empty(); }
    expr_dependency * mk_leaf(expr * t);
    expr_dependency * mk_join(unsigned n, expr * const * ts);
    expr_dependency * mk_join(expr_dependency * d1, expr_dependency * d2) { return m_expr_dependency_manager.mk_join(d1, d2); }
    void inc_ref(expr_dependency * d) { if (d) m_expr_dependency_manager.inc_ref(d); }
    void dec_ref(expr_dependency * d) { if (d) m_expr_dependency_manager.dec_ref(d); }
    void linearize(expr_dependency * d, ptr_vector<expr> & ts);
    bool contains(expr_dependency * d, expr * t) { return m_expr_dependency_manager.contains(d, t); }

// -----------------------------------
//
// expr_dependency_array
//
// -----------------------------------
public:
    void mk(expr_dependency_array & r) { m_expr_dependency_array_manager.mk(r); }
    void del(expr_dependency_array & r) { m_expr_dependency_array_manager.del(r); }
    void copy(expr_dependency_array const & s, expr_dependency_array & r) { m_expr_dependency_array_manager.copy(s, r); }
    unsigned size(expr_dependency_array const & r) const { return m_expr_dependency_array_manager.size(r); }
    bool empty(expr_dependency_array const & r) const { return m_expr_dependency_array_manager.empty(r); }
    expr_dependency * get(expr_dependency_array const & r, unsigned i) const { return m_expr_dependency_array_manager.get(r, i); }
    void set(expr_dependency_array & r, unsigned i, expr_dependency * v) { m_expr_dependency_array_manager.set(r, i, v); }
    void set(expr_dependency_array const & s, unsigned i, expr_dependency * v, expr_dependency_array & r) {
        m_expr_dependency_array_manager.set(s, i, v, r);
    }
    void push_back(expr_dependency_array & r, expr_dependency * v) { m_expr_dependency_array_manager.push_back(r, v); }
    void push_back(expr_dependency_array const & s, expr_dependency * v, expr_dependency_array & r) {
        m_expr_dependency_array_manager.push_back(s, v, r);
    }
    void pop_back(expr_dependency_array & r) { m_expr_dependency_array_manager.pop_back(r); }
    void pop_back(expr_dependency_array const & s, expr_dependency_array & r) { m_expr_dependency_array_manager.pop_back(s, r); }
    void unshare(expr_dependency_array & r) { m_expr_dependency_array_manager.unshare(r); }
    void unfold(expr_dependency_array & r) { m_expr_dependency_array_manager.unfold(r); }
    void reroot(expr_dependency_array & r) { m_expr_dependency_array_manager.reroot(r); }

// -----------------------------------
//
// Builtin operators
//
// -----------------------------------

public:

    bool is_or(expr const * n) const { return is_app_of(n, basic_family_id, OP_OR); }
    bool is_implies(expr const * n) const { return is_app_of(n, basic_family_id, OP_IMPLIES); }
    bool is_and(expr const * n) const { return is_app_of(n, basic_family_id, OP_AND); }
    bool is_not(expr const * n) const { return is_app_of(n, basic_family_id, OP_NOT); }
    bool is_eq(expr const * n) const { return is_app_of(n, basic_family_id, OP_EQ); }
    bool is_iff(expr const * n) const { return is_eq(n) && is_bool(to_app(n)->get_arg(0)); }
    bool is_oeq(expr const * n) const { return is_app_of(n, basic_family_id, OP_OEQ); }
    bool is_distinct(expr const * n) const { return is_app_of(n, basic_family_id, OP_DISTINCT); }
    bool is_xor(expr const * n) const { return is_app_of(n, basic_family_id, OP_XOR); }
    bool is_ite(expr const * n) const { return is_app_of(n, basic_family_id, OP_ITE); }
    bool is_term_ite(expr const * n) const { return is_ite(n) && !is_bool(n); }
    bool is_true(expr const * n) const { return n == m_true; }
    bool is_false(expr const * n) const { return n == m_false; }
    bool is_complement_core(expr const * n1, expr const * n2) const {
        return (is_true(n1) && is_false(n2)) || (is_not(n1) && to_app(n1)->get_arg(0) == n2);
    }
    bool is_complement(expr const * n1, expr const * n2) const { return is_complement_core(n1, n2) || is_complement_core(n2, n1); }

    bool is_or(func_decl const * d) const { return is_decl_of(d, basic_family_id, OP_OR); }
    bool is_implies(func_decl const * d) const { return is_decl_of(d, basic_family_id, OP_IMPLIES); }
    bool is_and(func_decl const * d) const { return is_decl_of(d, basic_family_id, OP_AND); }
    bool is_not(func_decl const * d) const { return is_decl_of(d, basic_family_id, OP_NOT); }
    bool is_eq(func_decl const * d) const { return is_decl_of(d, basic_family_id, OP_EQ); }
    bool is_iff(func_decl const * d) const { return is_decl_of(d, basic_family_id, OP_EQ) && is_bool(d->get_range()); }
    bool is_xor(func_decl const * d) const { return is_decl_of(d, basic_family_id, OP_XOR); }
    bool is_ite(func_decl const * d) const { return is_decl_of(d, basic_family_id, OP_ITE); }
    bool is_term_ite(func_decl const * d) const { return is_ite(d) && !is_bool(d->get_range()); }
    bool is_distinct(func_decl const * d) const { return is_decl_of(d, basic_family_id, OP_DISTINCT); }

public:

    MATCH_UNARY(is_not);
    MATCH_BINARY(is_eq);
    MATCH_BINARY(is_implies);
    MATCH_BINARY(is_and);
    MATCH_BINARY(is_or);
    MATCH_BINARY(is_xor);
    MATCH_TERNARY(is_and);
    MATCH_TERNARY(is_or);

    bool is_iff(expr const* n, expr*& lhs, expr*& rhs) const { return is_eq(n, lhs, rhs) && is_bool(lhs); } 

    bool is_ite(expr const* n, expr*& t1, expr*& t2, expr*& t3) const {
        if (is_ite(n)) {
            t1 = to_app(n)->get_arg(0);
            t2 = to_app(n)->get_arg(1);
            t3 = to_app(n)->get_arg(2);
            return true;
        }
        return false;
    }

public:
    app * mk_eq(expr * lhs, expr * rhs) { return mk_app(basic_family_id, get_eq_op(lhs), lhs, rhs); }
    app * mk_iff(expr * lhs, expr * rhs) { return mk_app(basic_family_id, OP_EQ, lhs, rhs); }
    app * mk_oeq(expr * lhs, expr * rhs) { return mk_app(basic_family_id, OP_OEQ, lhs, rhs); }
    app * mk_xor(expr * lhs, expr * rhs) { return mk_app(basic_family_id, OP_XOR, lhs, rhs); }
    app * mk_ite(expr * c, expr * t, expr * e) { return mk_app(basic_family_id, OP_ITE, c, t, e); }
    app * mk_xor(unsigned num_args, expr * const * args) { return mk_app(basic_family_id, OP_XOR, num_args, args); }
    app * mk_xor(ptr_buffer<expr> const& args) { return mk_xor(args.size(), args.data()); }
    app * mk_xor(ptr_vector<expr> const& args) { return mk_xor(args.size(), args.data()); }
    app * mk_xor(ref_buffer<expr, ast_manager> const& args) { return mk_xor(args.size(), args.data()); }
    app * mk_or(unsigned num_args, expr * const * args) { return mk_app(basic_family_id, OP_OR, num_args, args); }
    app * mk_and(unsigned num_args, expr * const * args) { return mk_app(basic_family_id, OP_AND, num_args, args); }
    app * mk_or(expr * arg1, expr * arg2) { return mk_app(basic_family_id, OP_OR, arg1, arg2); }
    app * mk_and(expr * arg1, expr * arg2) { return mk_app(basic_family_id, OP_AND, arg1, arg2); }
    app * mk_or(expr * arg1, expr * arg2, expr * arg3) { return mk_app(basic_family_id, OP_OR, arg1, arg2, arg3); }
    app * mk_or(expr* a, expr* b, expr* c, expr* d) { expr* args[4] = { a, b, c, d }; return mk_app(basic_family_id, OP_OR, 4, args); }
    app * mk_and(expr * arg1, expr * arg2, expr * arg3) { return mk_app(basic_family_id, OP_AND, arg1, arg2, arg3); }

    app * mk_and(ref_vector<expr, ast_manager> const& args) { return mk_and(args.size(), args.data()); }
    app * mk_and(ptr_vector<expr> const& args) { return mk_and(args.size(), args.data()); }
    app * mk_and(ref_buffer<expr, ast_manager> const& args) { return mk_and(args.size(), args.data()); }
    app * mk_and(ptr_buffer<expr> const& args) { return mk_and(args.size(), args.data()); }
    app * mk_or(ref_vector<expr, ast_manager> const& args) { return mk_or(args.size(), args.data()); }
    app * mk_or(ptr_vector<expr> const& args) { return mk_or(args.size(), args.data()); }
    app * mk_or(ref_buffer<expr, ast_manager> const& args) { return mk_or(args.size(), args.data()); }
    app * mk_or(ptr_buffer<expr> const& args) { return mk_or(args.size(), args.data()); }
    app * mk_implies(expr * arg1, expr * arg2) { return mk_app(basic_family_id, OP_IMPLIES, arg1, arg2); }
    app * mk_not(expr * n) { return mk_app(basic_family_id, OP_NOT, n); }
    app * mk_distinct(unsigned num_args, expr * const * args);
    app * mk_distinct_expanded(unsigned num_args, expr * const * args);
    app * mk_true() const { return m_true; }
    app * mk_false() const { return m_false; }
    app * mk_bool_val(bool b) { return b?m_true:m_false; }


    func_decl* mk_and_decl() {
        sort* domain[2] = { m_bool_sort, m_bool_sort };
        return mk_func_decl(basic_family_id, OP_AND, 0, nullptr, 2, domain);
    }
    func_decl* mk_not_decl() { return mk_func_decl(basic_family_id, OP_NOT, 0, nullptr, 1, &m_bool_sort); }
    func_decl* mk_or_decl() {
        sort* domain[2] = { m_bool_sort, m_bool_sort };
        return mk_func_decl(basic_family_id, OP_OR, 0, nullptr, 2, domain);
    }

// -----------------------------------
//
// Values
//
// -----------------------------------

protected:
    some_value_proc * m_some_value_proc;
public:
    app * mk_model_value(unsigned idx, sort * s);
    bool is_model_value(expr const * n) const { return is_app_of(n, model_value_family_id, OP_MODEL_VALUE); }
    bool is_model_value(func_decl const * d) const { return is_decl_of(d, model_value_family_id, OP_MODEL_VALUE); }

    expr * get_some_value(sort * s, some_value_proc * p);
    expr * get_some_value(sort * s);

// -----------------------------------
//
// Proof generation
//
// -----------------------------------

protected:
    proof * mk_proof(family_id fid, decl_kind k, unsigned num_args, expr * const * args);
    proof * mk_proof(family_id fid, decl_kind k, expr * arg);
    proof * mk_proof(family_id fid, decl_kind k, expr * arg1, expr * arg2);
    proof * mk_proof(family_id fid, decl_kind k, expr * arg1, expr * arg2, expr * arg3);

    proof * mk_undef_proof() const { return m_undef_proof; }

public:
    bool proofs_enabled() const { return m_proof_mode != PGM_DISABLED; }
    bool proofs_disabled() const { return m_proof_mode == PGM_DISABLED; }
    proof_gen_mode proof_mode() const { return m_proof_mode; }
    void toggle_proof_mode(proof_gen_mode m) { m_proof_mode = m; } // APIs for creating proof objects return [undef]


    bool is_proof(expr const * n) const { return is_app(n) && to_app(n)->get_decl()->get_range() == m_proof_sort; }

    proof* mk_hyper_resolve(unsigned num_premises, proof* const* premises, expr* concl,
                            svector<std::pair<unsigned, unsigned> > const& positions,
                            vector<ref_vector<expr, ast_manager> > const& substs);


    bool is_undef_proof(expr const * e) const { return e == m_undef_proof; }
    bool is_asserted(expr const * e) const { return is_app_of(e, basic_family_id, PR_ASSERTED); }
    bool is_hypothesis (expr const *e) const {return is_app_of (e, basic_family_id, PR_HYPOTHESIS);}
    bool is_goal(expr const * e) const { return is_app_of(e, basic_family_id, PR_GOAL); }
    bool is_modus_ponens(expr const * e) const { return is_app_of(e, basic_family_id, PR_MODUS_PONENS); }
    bool is_reflexivity(expr const * e) const { return is_app_of(e, basic_family_id, PR_REFLEXIVITY); }
    bool is_symmetry(expr const * e) const { return is_app_of(e, basic_family_id, PR_SYMMETRY); }
    bool is_transitivity(expr const * e) const { return is_app_of(e, basic_family_id, PR_TRANSITIVITY); }
    bool is_monotonicity(expr const * e) const { return is_app_of(e, basic_family_id, PR_MONOTONICITY); }
    bool is_quant_intro(expr const * e) const { return is_app_of(e, basic_family_id, PR_QUANT_INTRO); }
    bool is_quant_inst(expr const * e) const { return is_app_of(e, basic_family_id, PR_QUANT_INST); }
    bool is_distributivity(expr const * e) const { return is_app_of(e, basic_family_id, PR_DISTRIBUTIVITY); }
    bool is_and_elim(expr const * e) const { return is_app_of(e, basic_family_id, PR_AND_ELIM); }
    bool is_not_or_elim(expr const * e) const { return is_app_of(e, basic_family_id, PR_NOT_OR_ELIM); }
    bool is_rewrite(expr const * e) const { return is_app_of(e, basic_family_id, PR_REWRITE); }
    bool is_rewrite_star(expr const * e) const { return is_app_of(e, basic_family_id, PR_REWRITE_STAR); }
    bool is_unit_resolution(expr const * e) const { return is_app_of(e, basic_family_id, PR_UNIT_RESOLUTION); }
    bool is_lemma(expr const * e) const { return is_app_of(e, basic_family_id, PR_LEMMA); }
    bool is_quant_inst(expr const* e, expr*& not_q_or_i, ptr_vector<expr>& binding) const;
    bool is_rewrite(expr const* e, expr*& r1, expr*& r2) const;
    bool is_hyper_resolve(proof* p) const { return is_app_of(p, basic_family_id, PR_HYPER_RESOLVE); }
    bool is_hyper_resolve(proof* p,
                          ref_vector<proof, ast_manager>& premises,
                          obj_ref<expr, ast_manager>& conclusion,
                          svector<std::pair<unsigned, unsigned> > & positions,
                          vector<ref_vector<expr, ast_manager> >& substs);


    bool is_def_intro(expr const * e) const { return is_app_of(e, basic_family_id, PR_DEF_INTRO); }
    bool is_apply_def(expr const * e) const { return is_app_of(e, basic_family_id, PR_APPLY_DEF); }
    bool is_skolemize(expr const * e) const { return is_app_of(e, basic_family_id, PR_SKOLEMIZE); }

    MATCH_UNARY(is_asserted);
    MATCH_UNARY(is_hypothesis);
    MATCH_UNARY(is_lemma);

    bool has_fact(proof const * p) const {
        SASSERT(is_proof(p));
        unsigned n = p->get_num_args();
        return n > 0 && p->get_arg(n - 1)->get_sort() != m_proof_sort;
    }
    expr * get_fact(proof const * p) const { SASSERT(is_proof(p)); SASSERT(has_fact(p)); return p->get_arg(p->get_num_args() - 1); }
    
    class proof_parents {
        ast_manager& m;
        proof * m_proof;
    public:
        proof_parents(ast_manager& m, proof * p): m(m), m_proof(p) {}
        proof * const * begin() const { return (proof* const*)(m_proof->begin()); }
        proof * const * end() const { 
            unsigned n = m_proof->get_num_args();
            return (proof* const*)(begin() + (m.has_fact(m_proof) ?  n - 1 : n));
        }
    };

    proof_parents get_parents(proof* p) {
        return proof_parents(*this, p);
    }

    unsigned get_num_parents(proof const * p) const {
        SASSERT(is_proof(p));
        unsigned n = p->get_num_args();
        return !has_fact(p) ? n : n - 1;
    }
    proof * get_parent(proof const * p, unsigned idx) const { SASSERT(is_proof(p)); return to_app(p->get_arg(idx)); }
    proof * mk_true_proof();
    proof * mk_asserted(expr * f);
    proof * mk_goal(expr * f);
    proof * mk_modus_ponens(proof * p1, proof * p2);
    proof * mk_reflexivity(expr * e);
    proof * mk_oeq_reflexivity(expr * e);
    proof * mk_symmetry(proof * p);
    proof * mk_transitivity(proof * p1, proof * p2);
    proof * mk_transitivity(proof * p1, proof * p2, proof * p3);
    proof * mk_transitivity(proof * p1, proof * p2, proof * p3, proof * p4);
    proof * mk_transitivity(unsigned num_proofs, proof * const * proofs);
    proof * mk_transitivity(unsigned num_proofs, proof * const * proofs, expr * n1, expr * n2);
    proof * mk_monotonicity(func_decl * R, app * f1, app * f2, unsigned num_proofs, proof * const * proofs);
    proof * mk_congruence(app * f1, app * f2, unsigned num_proofs, proof * const * proofs);
    proof * mk_oeq_congruence(app * f1, app * f2, unsigned num_proofs, proof * const * proofs);
    proof * mk_commutativity(app * f);
    proof * mk_iff_true(proof * pr);
    proof * mk_iff_false(proof * pr);
    proof * mk_quant_intro(quantifier * q1, quantifier * q2, proof * p);
    proof * mk_oeq_quant_intro(quantifier * q1, quantifier * q2, proof * p);
    proof * mk_distributivity(expr * s, expr * r);
    proof * mk_rewrite(expr * s, expr * t);
    proof * mk_oeq_rewrite(expr * s, expr * t);
    proof * mk_rewrite_star(expr * s, expr * t, unsigned num_proofs, proof * const * proofs);
    proof * mk_bind_proof(quantifier * q, proof * p);
    proof * mk_pull_quant(expr * e, quantifier * q);
    proof * mk_push_quant(quantifier * q, expr * e);
    proof * mk_elim_unused_vars(quantifier * q, expr * r);
    proof * mk_der(quantifier * q, expr * r);
    proof * mk_quant_inst(expr * not_q_or_i, unsigned num_bind, expr* const* binding);

    proof * mk_clause_trail_elem(proof* p, expr* e, decl_kind k);
    proof * mk_assumption_add(proof* pr, expr* e);
    proof * mk_lemma_add(proof* pr, expr* e);
    proof * mk_th_assumption_add(proof* pr, expr* e);
    proof * mk_th_lemma_add(proof* pr, expr* e);
    proof * mk_redundant_del(expr* e);
    proof * mk_clause_trail(unsigned n, proof* const* ps);

    proof * mk_def_axiom(expr * ax);
    proof * mk_unit_resolution(unsigned num_proofs, proof * const * proofs);
    proof * mk_unit_resolution(unsigned num_proofs, proof * const * proofs, expr * new_fact);
    proof * mk_hypothesis(expr * h);
    proof * mk_lemma(proof * p, expr * lemma);

    proof * mk_def_intro(expr * new_def);
    proof * mk_apply_defs(expr * n, expr * def, unsigned num_proofs, proof * const * proofs);
    proof * mk_apply_def(expr * n, expr * def, proof * p) { return mk_apply_defs(n, def, 1, &p); }
    proof * mk_iff_oeq(proof * parent);

    proof * mk_nnf_pos(expr * s, expr * t, unsigned num_proofs, proof * const * proofs);
    proof * mk_nnf_neg(expr * s, expr * t, unsigned num_proofs, proof * const * proofs);
    proof * mk_skolemization(expr * q, expr * e);


    proof * mk_and_elim(proof * p, unsigned i);
    proof * mk_not_or_elim(proof * p, unsigned i);

    proof * mk_th_lemma(family_id tid,
                        expr * fact, unsigned num_proofs, proof * const * proofs,
                        unsigned num_params = 0, parameter const* params = nullptr);

protected:
    bool check_nnf_proof_parents(unsigned num_proofs, proof * const * proofs) const;

private:
    void push_dec_ref(ast * n) {
        n->dec_ref();
        if (n->get_ref_count() == 0) {
            m_ast_table.push_erase(n);
        }
    }

    template<typename T>
    void push_dec_array_ref(unsigned sz, T * const * a) {
        for(unsigned i = 0; i < sz; i++) {
            push_dec_ref(a[i]);
        }
    }
};

typedef ast_manager::expr_array expr_array;
typedef ast_manager::expr_dependency expr_dependency;
typedef ast_manager::expr_dependency_array expr_dependency_array;
typedef obj_ref<expr_dependency, ast_manager> expr_dependency_ref;
typedef ref_vector<expr_dependency, ast_manager> expr_dependency_ref_vector;
typedef ref_buffer<expr_dependency, ast_manager> expr_dependency_ref_buffer;

// -----------------------------------
//
// More Auxiliary Functions
//
// -----------------------------------

inline bool is_predicate(ast_manager const & m, func_decl const * d) {
    return m.is_bool(d->get_range());
}

struct ast_lt_proc {
    bool operator()(ast const * n1, ast const * n2) const {
        return n1->get_id() < n2->get_id();
    }
};

// -----------------------------------
//
// ast_ref (smart pointer)
//
// -----------------------------------

typedef obj_ref<ast, ast_manager>        ast_ref;
typedef obj_ref<expr, ast_manager>       expr_ref;
typedef obj_ref<sort, ast_manager>       sort_ref;
typedef obj_ref<func_decl, ast_manager>  func_decl_ref;
typedef obj_ref<quantifier, ast_manager> quantifier_ref;
typedef obj_ref<app, ast_manager>        app_ref;
typedef obj_ref<var,ast_manager>         var_ref;
typedef app_ref proof_ref;

inline expr_ref operator~(expr_ref const & e) {
    if (e.m().is_not(e))
        return expr_ref(to_app(e)->get_arg(0), e.m());
    return expr_ref(e.m().mk_not(e), e.m());
}

// -----------------------------------
//
// ast_vector (smart pointer vector)
//
// -----------------------------------

typedef ref_vector<ast, ast_manager>       ast_ref_vector;
typedef ref_vector<decl, ast_manager>      decl_ref_vector;
typedef ref_vector<sort, ast_manager>      sort_ref_vector;
typedef ref_vector<func_decl, ast_manager> func_decl_ref_vector;
typedef ref_vector<expr, ast_manager>      expr_ref_vector;
typedef ref_vector<app, ast_manager>       app_ref_vector;
typedef ref_vector<var, ast_manager>       var_ref_vector;
typedef ref_vector<quantifier, ast_manager> quantifier_ref_vector;
typedef app_ref_vector                     proof_ref_vector;

typedef ref_pair_vector<expr, ast_manager> expr_ref_pair_vector;


// -----------------------------------
//
// ast_buffer
//
// -----------------------------------

typedef ref_buffer<ast, ast_manager>  ast_ref_buffer;
typedef ref_buffer<expr, ast_manager> expr_ref_buffer;
typedef ref_buffer<sort, ast_manager> sort_ref_buffer;
typedef ref_buffer<app, ast_manager>  app_ref_buffer;
typedef app_ref_buffer                proof_ref_buffer;

// -----------------------------------
//
// expr_mark
//
// -----------------------------------

typedef obj_mark<expr> expr_mark;

class expr_sparse_mark {
    obj_hashtable<expr> m_marked;
public:
    bool is_marked(expr * n) const { return m_marked.contains(n); }
    void mark(expr * n) { m_marked.insert(n); }
    void mark(expr * n, bool flag) { if (flag) m_marked.insert(n); else m_marked.erase(n); }
    void reset() { m_marked.reset(); }
};

template<unsigned IDX>
class ast_fast_mark {
    ptr_buffer<ast> m_to_unmark;
public:
    ~ast_fast_mark() {
        reset();
    }
    bool is_marked(ast * n) { return IDX == 1 ? AST_IS_MARKED1(n, this) : AST_IS_MARKED2(n, this); }
    void reset_mark(ast * n) {
        if (IDX == 1) {
            AST_RESET_MARK1(n, this);
        }
        else {
            AST_RESET_MARK2(n, this);
        }
    }
    void mark(ast * n) {
        if (IDX == 1) {
            if (AST_IS_MARKED1(n, this))
                return;
            AST_MARK1(n, true, this);
        }
        else {
            if (AST_IS_MARKED2(n, this))
                return;
            AST_MARK2(n, true, this);
        }
        m_to_unmark.push_back(n);
    }

    void reset() {
        for (ast* a : m_to_unmark) reset_mark(a); 
        m_to_unmark.reset();
    }

    void mark(ast * n, bool flag) { if (flag) mark(n); else reset_mark(n); }

    unsigned get_level() {
        return m_to_unmark.size();
    }

    void set_level(unsigned new_size) {
        SASSERT(new_size <= m_to_unmark.size());
        while (new_size < m_to_unmark.size()) {
            reset_mark(m_to_unmark.back());
            m_to_unmark.pop_back();
        }
    }
};

typedef ast_fast_mark<1> ast_fast_mark1;
typedef ast_fast_mark<2> ast_fast_mark2;
typedef ast_fast_mark1   expr_fast_mark1;
typedef ast_fast_mark2   expr_fast_mark2;

/**
   Similar to ast_fast_mark, but increases reference counter.
*/
template<unsigned IDX>
class ast_ref_fast_mark {
    ast_ref_buffer m_to_unmark;
public:
    ast_ref_fast_mark(ast_manager & m):m_to_unmark(m) {}
    ~ast_ref_fast_mark() {
        reset();
    }
    bool is_marked(ast * n) { return IDX == 1 ? AST_IS_MARKED1(n, this) : AST_IS_MARKED2(n, this); }

    // It will not decrease the reference counter
    void reset_mark(ast * n) {
        if (IDX == 1) {
            AST_RESET_MARK1(n, this);
        }
        else {
            AST_RESET_MARK2(n, this);
        }
    }

    void mark(ast * n) {
        if (IDX == 1) {
            if (AST_IS_MARKED1(n, this))
                return;
            AST_MARK1(n, true, this);
        }
        else {
            if (AST_IS_MARKED2(n, this))
                return;
            AST_MARK2(n, true, this);
        }
        m_to_unmark.push_back(n);
    }

    void reset() {
        for (ast * a : m_to_unmark) 
            reset_mark(a);
        m_to_unmark.reset();
    }

    void mark(ast * n, bool flag) { if (flag) mark(n); else reset_mark(n); }
};


typedef ast_ref_fast_mark<1> ast_ref_fast_mark1;
typedef ast_ref_fast_mark<2> ast_ref_fast_mark2;
typedef ast_ref_fast_mark1   expr_ref_fast_mark1;
typedef ast_ref_fast_mark2   expr_ref_fast_mark2;

// -----------------------------------
//
// ast_mark
//
// -----------------------------------

/**
   \brief A mapping from AST to Boolean

   \warning This map does not cleanup the entry associated with a node N,
   when N is deleted.
*/
class ast_mark {
    struct decl2uint { unsigned operator()(decl const & d) const { return d.get_decl_id(); } };
    obj_mark<expr>                        m_expr_marks;
    obj_mark<decl, bit_vector, decl2uint> m_decl_marks;
public:
    virtual ~ast_mark() {}
    bool is_marked(ast * n) const;
    virtual void mark(ast * n, bool flag);
    virtual void reset();
};

// -----------------------------------
//
// scoped_mark
//
// -----------------------------------

/**
   \brief Class for scoped-based marking of asts.
   This class is safe with respect to life-times of asts.
*/
class scoped_mark : public ast_mark {
    ast_ref_vector  m_stack;
    unsigned_vector m_lim;
public:
    scoped_mark(ast_manager& m): m_stack(m) {}
    void mark(ast * n, bool flag) override;
    void reset() override;
    void mark(ast * n);
    void push_scope();
    void pop_scope();
    void pop_scope(unsigned num_scopes);
};

// -------------------------------------
//
// inc_ref & dec_ref functors
//
// -------------------------------------

template<typename AST>
class dec_ref_proc {
    ast_manager & m_manager;
public:
    dec_ref_proc(ast_manager & m):m_manager(m) {}
    void operator()(AST * n) { m_manager.dec_ref(n); }
};


template<typename AST>
class inc_ref_proc {
    ast_manager & m_manager;
public:
    inc_ref_proc(ast_manager & m):m_manager(m) {}
    void operator()(AST * n) { m_manager.inc_ref(n); }
};

struct parameter_pp {
    parameter const& p;
    ast_manager& m;
    parameter_pp(parameter const& p, ast_manager& m): p(p), m(m) {}
};

inline std::ostream& operator<<(std::ostream& out, parameter_pp const& pp) {
    return pp.m.display(out, pp.p);
}
