/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    ast.cpp

Abstract:

   Expression DAG

Author:

    Leonardo de Moura (leonardo) 2006-09-28.

Revision History:

--*/
#include <sstream>
#include <cstring>
#include "ast/ast.h"
#include "ast/ast_pp.h"
#include "ast/ast_ll_pp.h"
#include "util/buffer.h"
#include "util/warning.h"
#include "util/string_buffer.h"
#include "ast/ast_util.h"
#include "ast/ast_smt2_pp.h"
#include "ast/array_decl_plugin.h"
#include "ast/ast_translation.h"
#include "util/z3_version.h"


// -----------------------------------
//
// parameter
//
// -----------------------------------

parameter::~parameter() {
    if (auto p = std::get_if<rational*>(&m_val)) {
        dealloc(*p);
    }
    if (auto p = std::get_if<zstring*>(&m_val)) {
        dealloc(*p);
    }
}

parameter& parameter::operator=(parameter const& other) {
    if (this == &other) {
        return *this;
    }

    this->~parameter();
    m_val = other.m_val;

    if (auto p = std::get_if<rational*>(&m_val)) {
        m_val = alloc(rational, **p);
    }
    if (auto p = std::get_if<zstring*>(&m_val)) {
        m_val = alloc(zstring, **p);
    }
    return *this;
}

void parameter::init_eh(ast_manager & m) {
    if (is_ast()) {
        m.inc_ref(get_ast());
    }
}

void parameter::del_eh(ast_manager & m, family_id fid) {
    if (is_ast()) {
        m.dec_ref(get_ast());
    }
    else if (is_external()) {
        SASSERT(fid != null_family_id);
        decl_plugin * plugin = m.get_plugin(fid);
        if (plugin) {
            plugin->del(*this);
        }
    }
}

bool parameter::operator==(parameter const & p) const {
    if (get_kind() != p.get_kind()) return false;
    switch (get_kind()) {
    case PARAM_RATIONAL: return get_rational() == p.get_rational();
    case PARAM_ZSTRING: return get_zstring() == p.get_zstring();
    default: return m_val == p.m_val;
    }
}

unsigned parameter::hash() const {
    unsigned b = 0;
    switch (get_kind()) {
    case PARAM_INT:      b = get_int(); break;
    case PARAM_AST:      b = get_ast()->hash(); break;
    case PARAM_SYMBOL:   b = get_symbol().hash(); break;
    case PARAM_RATIONAL: b = get_rational().hash(); break;
    case PARAM_DOUBLE:   b = static_cast<unsigned>(get_double()); break;
    case PARAM_ZSTRING:  b = get_zstring().hash(); break;
    case PARAM_EXTERNAL: b = get_ext_id(); break;
    }
    return b;
}

std::ostream& parameter::display(std::ostream& out) const {
    switch (get_kind()) {
    case PARAM_INT:      return out << get_int();
    case PARAM_SYMBOL:   return out << get_symbol();
    case PARAM_RATIONAL: return out << get_rational();
    case PARAM_AST:      return out << '#' << get_ast()->get_id();
    case PARAM_DOUBLE:   return out << get_double();
    case PARAM_EXTERNAL: return out << '@' << get_ext_id();
    case PARAM_ZSTRING:  return out << get_zstring();
    default:
        UNREACHABLE();
        return out;
    }
}

void display_parameters(std::ostream & out, unsigned n, parameter const * p) {
    if (n > 0) {
        out << "[";
        for (unsigned i = 0; i < n; i ++)
            out << p[i] << (i < n-1 ? ":" : "");
        out << "]";
    }
}

// -----------------------------------
//
// family_manager
//
// -----------------------------------

family_id family_manager::mk_family_id(symbol const & s) {
    family_id r;
    if (m_families.find(s, r)) {
        return r;
    }
    r = m_next_id;
    m_next_id++;
    m_families.insert(s, r);
    m_names.push_back(s);
    return r;
}

family_id family_manager::get_family_id(symbol const & s) const {
    family_id r;
    if (m_families.find(s, r))
        return r;
    else
        return null_family_id;
}

bool family_manager::has_family(symbol const & s) const {
    return m_families.contains(s);
}


// -----------------------------------
//
// decl_info
//
// -----------------------------------

decl_info::decl_info(family_id family_id, decl_kind k, unsigned num_parameters,
                     parameter const * parameters, bool private_params):
    m_family_id(family_id),
    m_kind(k),
    m_parameters(num_parameters, const_cast<parameter *>(parameters)),
    m_private_parameters(private_params) {
}

void decl_info::init_eh(ast_manager & m) {
    for (parameter & p : m_parameters) {
        p.init_eh(m);
    }
}

void decl_info::del_eh(ast_manager & m) {
    for (parameter & p : m_parameters) {
        p.del_eh(m, m_family_id);
    }
}

struct decl_info_child_hash_proc {
    unsigned operator()(decl_info const * info, unsigned idx) const { return info->get_parameter(idx).hash(); }
};

unsigned decl_info::hash() const {
    unsigned a = m_family_id;
    unsigned b = m_kind;
    unsigned c = get_num_parameters() == 0 ? 0 : get_composite_hash<decl_info const *, default_kind_hash_proc<decl_info const *>, decl_info_child_hash_proc>(this, get_num_parameters());
    mix(a, b, c);
    return c;
}

bool decl_info::operator==(decl_info const & info) const {
    return m_family_id == info.m_family_id && m_kind == info.m_kind &&
        m_parameters.size() == info.m_parameters.size() && 
        compare_arrays<parameter>(m_parameters.begin(), info.m_parameters.begin(), m_parameters.size());
}

std::ostream & operator<<(std::ostream & out, decl_info const & info) {
    out << ":fid " << info.get_family_id() << " :decl-kind " << info.get_decl_kind() << " :parameters (";
    for (unsigned i = 0; i < info.get_num_parameters(); i++) {
        if (i > 0) out << " ";
        out << info.get_parameter(i);
    }
    out << ")";
    return out;
}

// -----------------------------------
//
// sort_size
//
// -----------------------------------

std::ostream& operator<<(std::ostream& out, sort_size const & ss) {
    if (ss.is_infinite()) { return out << "infinite"; }
    else if (ss.is_very_big()) { return out << "very-big"; }
    else { SASSERT(ss.is_finite()); return out << ss.size(); }
}

// -----------------------------------
//
// sort_info
//
// -----------------------------------
std::ostream & operator<<(std::ostream & out, sort_info const & info) {
    operator<<(out, static_cast<decl_info const&>(info));
    out << " :size " << info.get_num_elements();
    return out;
}

// -----------------------------------
//
// func_decl_info
//
// -----------------------------------

func_decl_info::func_decl_info(family_id family_id, decl_kind k, unsigned num_parameters, parameter const * parameters):
    decl_info(family_id, k, num_parameters, parameters),
    m_left_assoc(false),
    m_right_assoc(false),
    m_flat_associative(false),
    m_commutative(false),
    m_chainable(false),
    m_pairwise(false),
    m_injective(false),
    m_idempotent(false),
    m_skolem(false),
    m_lambda(false) {
}

bool func_decl_info::operator==(func_decl_info const & info) const {
    return decl_info::operator==(info) &&
        m_left_assoc == info.m_left_assoc &&
        m_right_assoc == info.m_right_assoc &&
        m_flat_associative == info.m_flat_associative &&
        m_commutative == info.m_commutative &&
        m_chainable == info.m_chainable &&
        m_pairwise == info.m_pairwise &&
        m_injective == info.m_injective &&
        m_skolem == info.m_skolem &&
        m_lambda == info.m_lambda;
}

std::ostream & operator<<(std::ostream & out, func_decl_info const & info) {
    operator<<(out, static_cast<decl_info const&>(info));
    if (info.is_left_associative()) out << " :left-assoc ";
    if (info.is_right_associative()) out << " :right-assoc ";
    if (info.is_flat_associative()) out << " :flat-associative ";
    if (info.is_commutative()) out << " :commutative ";
    if (info.is_chainable()) out << " :chainable ";
    if (info.is_pairwise()) out << " :pairwise ";
    if (info.is_injective()) out << " :injective ";
    if (info.is_idempotent()) out << " :idempotent ";
    if (info.is_skolem()) out << " :skolem ";
    if (info.is_lambda()) out << " :lambda ";
    return out;
}

// -----------------------------------
//
// ast
//
// -----------------------------------

static char const * g_ast_kind_names[] = {"application", "variable", "quantifier", "sort", "function declaration" };

char const * get_ast_kind_name(ast_kind k) {
    return g_ast_kind_names[k];
}

// -----------------------------------
//
// func_decl
//
// -----------------------------------

func_decl::func_decl(symbol const & name, unsigned arity, sort * const * domain, sort * range, func_decl_info * info):
    decl(AST_FUNC_DECL, name, info),
    m_arity(arity),
    m_range(range) {
    if (arity != 0)
        memcpy(const_cast<sort **>(get_domain()), domain, sizeof(sort *) * arity);
}

// -----------------------------------
//
// application
//
// -----------------------------------

static app_flags mk_const_flags() {
    app_flags r;
    r.m_depth           = 1;
    r.m_ground          = true;
    r.m_has_quantifiers = false;
    r.m_has_labels      = false;
    return r;
}

static app_flags mk_default_app_flags() {
    app_flags r;
    r.m_depth           = 1;
    r.m_ground          = true;
    r.m_has_quantifiers = false;
    r.m_has_labels      = false;
    return r;
}

app_flags app::g_constant_flags = mk_const_flags();

app::app(func_decl * decl, unsigned num_args, expr * const * args):
    expr(AST_APP),
    m_decl(decl),
    m_num_args(num_args) {
    for (unsigned i = 0; i < num_args; i++)
        m_args[i] = args[i];
}

// -----------------------------------
//
// quantifier
//
// -----------------------------------

quantifier::quantifier(quantifier_kind k, unsigned num_decls, sort * const * decl_sorts, symbol const * decl_names, expr * body, sort* s,
                       int weight, symbol const & qid, symbol const & skid, unsigned num_patterns, expr * const * patterns,
                       unsigned num_no_patterns, expr * const * no_patterns):
    expr(AST_QUANTIFIER),
    m_kind(k),
    m_num_decls(num_decls),
    m_expr(body),
    m_sort(s),
    m_depth(::get_depth(body) + 1),
    m_weight(weight),
    m_has_unused_vars(true),
    m_has_labels(::has_labels(body)),
    m_qid(qid),
    m_skid(skid),
    m_num_patterns(num_patterns),
    m_num_no_patterns(num_no_patterns) {
    SASSERT(m_num_patterns == 0 || m_num_no_patterns == 0);

    memcpy(const_cast<sort **>(get_decl_sorts()), decl_sorts, sizeof(sort *) * num_decls);
    memcpy(const_cast<symbol*>(get_decl_names()), decl_names, sizeof(symbol) * num_decls);
    if (num_patterns != 0)
        memcpy(const_cast<expr **>(get_patterns()), patterns, sizeof(expr *) * num_patterns);
    if (num_no_patterns != 0)
        memcpy(const_cast<expr **>(get_no_patterns()), no_patterns, sizeof(expr *) * num_no_patterns);
}

quantifier::quantifier(unsigned num_decls, sort * const * decl_sorts, symbol const * decl_names, expr * body, sort* s):
    expr(AST_QUANTIFIER),
    m_kind(lambda_k),
    m_num_decls(num_decls),
    m_expr(body),
    m_sort(s),
    m_depth(::get_depth(body) + 1),
    m_weight(1),
    m_has_unused_vars(true),
    m_has_labels(::has_labels(body)),
    m_qid(symbol()),
    m_skid(symbol()),
    m_num_patterns(0),
    m_num_no_patterns(0) {
    memcpy(const_cast<sort **>(get_decl_sorts()), decl_sorts, sizeof(sort *) * num_decls);
    memcpy(const_cast<symbol*>(get_decl_names()), decl_names, sizeof(symbol) * num_decls);   
}


// -----------------------------------
//
// Auxiliary functions
//
// -----------------------------------

sort* expr::get_sort() const {
    switch (get_kind()) {
    case AST_APP:
        return to_app(this)->get_decl()->get_range();
    case AST_VAR:
        return to_var(this)->_get_sort();
    case AST_QUANTIFIER:
        return to_quantifier(this)->_get_sort();
    default:
        UNREACHABLE();
        return nullptr;
    }
}

// -----------------------------------
//
// AST hash-consing
//
// -----------------------------------

unsigned get_node_size(ast const * n) {
    switch(n->get_kind()) {
    case AST_SORT:       return to_sort(n)->get_size();
    case AST_FUNC_DECL:  return to_func_decl(n)->get_size();
    case AST_APP:        return to_app(n)->get_size();
    case AST_VAR:        return to_var(n)->get_size();
    case AST_QUANTIFIER: return to_quantifier(n)->get_size();
    default: UNREACHABLE();
    }
    return 0;
}

bool compare_nodes(ast const * n1, ast const * n2) {
    if (n1->get_kind() != n2->get_kind()) {
        return false;
    }
    switch (n1->get_kind()) {
    case AST_SORT:
        if ((to_sort(n1)->get_info() == nullptr) != (to_sort(n2)->get_info() == nullptr)) {
            return false;
        }
        if (to_sort(n1)->get_info() != nullptr && !(*to_sort(n1)->get_info() == *to_sort(n2)->get_info())) {
            return false;
        }
        return to_sort(n1)->get_name()  == to_sort(n2)->get_name();
    case AST_FUNC_DECL:
        if ((to_func_decl(n1)->get_info() == nullptr) != (to_func_decl(n2)->get_info() == nullptr)) {
            return false;
        }
        if (to_func_decl(n1)->get_info() != nullptr && !(*to_func_decl(n1)->get_info() == *to_func_decl(n2)->get_info())) {
            return false;
        }
        return
            to_func_decl(n1)->get_name()  == to_func_decl(n2)->get_name() &&
            to_func_decl(n1)->get_arity() == to_func_decl(n2)->get_arity() &&
            to_func_decl(n1)->get_range() == to_func_decl(n2)->get_range() &&
            compare_arrays(to_func_decl(n1)->get_domain(),
                           to_func_decl(n2)->get_domain(),
                           to_func_decl(n1)->get_arity());
    case AST_APP:
        return
            to_app(n1)->get_decl()     == to_app(n2)->get_decl() &&
            to_app(n1)->get_num_args() == to_app(n2)->get_num_args() &&
            compare_arrays(to_app(n1)->get_args(), to_app(n2)->get_args(), to_app(n1)->get_num_args());
    case AST_VAR:
        return
            to_var(n1)->get_idx()  == to_var(n2)->get_idx() &&
            to_var(n1)->get_sort() == to_var(n2)->get_sort();
    case AST_QUANTIFIER:
        return
            to_quantifier(n1)->get_kind()            == to_quantifier(n2)->get_kind() &&
            to_quantifier(n1)->get_num_decls()       == to_quantifier(n2)->get_num_decls() &&
            compare_arrays(to_quantifier(n1)->get_decl_sorts(),
                           to_quantifier(n2)->get_decl_sorts(),
                           to_quantifier(n1)->get_num_decls()) &&
            compare_arrays(to_quantifier(n1)->get_decl_names(),
                           to_quantifier(n2)->get_decl_names(),
                           to_quantifier(n1)->get_num_decls()) &&
            to_quantifier(n1)->get_expr()            == to_quantifier(n2)->get_expr() &&
            to_quantifier(n1)->get_weight()          == to_quantifier(n2)->get_weight() &&
            to_quantifier(n1)->get_num_patterns() == to_quantifier(n2)->get_num_patterns() &&
            compare_arrays(to_quantifier(n1)->get_patterns(),
                           to_quantifier(n2)->get_patterns(),
                           to_quantifier(n1)->get_num_patterns()) &&
            to_quantifier(n1)->get_num_no_patterns() == to_quantifier(n2)->get_num_no_patterns() &&
            compare_arrays(to_quantifier(n1)->get_no_patterns(),
                           to_quantifier(n2)->get_no_patterns(),
                           to_quantifier(n1)->get_num_no_patterns());
    default:
        UNREACHABLE();
    }
    return false;
}

template<typename T>
inline unsigned ast_array_hash(T * const * array, unsigned size, unsigned init_value) {
    if (size == 0)
        return init_value;
    switch (size) {
    case 1:
        return combine_hash(array[0]->hash(), init_value);
    case 2:
        return combine_hash(combine_hash(array[0]->hash(), array[1]->hash()),
                            init_value);
    case 3:
        return combine_hash(combine_hash(array[0]->hash(), array[1]->hash()),
                            combine_hash(array[2]->hash(), init_value));
    default: {
        unsigned a, b, c;
        a = b = 0x9e3779b9;
        c = init_value;
        while (size >= 3) {
            size--;
            a += array[size]->hash();
            size--;
            b += array[size]->hash();
            size--;
            c += array[size]->hash();
            mix(a, b, c);
        }
        switch (size) {
        case 2:
            b += array[1]->hash();
            Z3_fallthrough;
        case 1:
            c += array[0]->hash();
        }
        mix(a, b, c);
        return c;
    } }
}

unsigned get_asts_hash(unsigned sz, ast * const* ns, unsigned init) {
    return ast_array_hash<ast>(ns, sz, init);
}
unsigned get_apps_hash(unsigned sz, app * const* ns, unsigned init) {
    return ast_array_hash<app>(ns, sz, init);
}
unsigned get_exprs_hash(unsigned sz, expr * const* ns, unsigned init) {
    return ast_array_hash<expr>(ns, sz, init);
}
unsigned get_sorts_hash(unsigned sz, sort * const* ns, unsigned init) {
    return ast_array_hash<sort>(ns, sz, init);
}
unsigned get_decl_hash(unsigned sz, func_decl* const* ns, unsigned init) {
    return ast_array_hash<func_decl>(ns, sz, init);
}

unsigned get_node_hash(ast const * n) {
    unsigned a, b, c;

    switch (n->get_kind()) {
    case AST_SORT:
        if (to_sort(n)->get_info() == nullptr)
            return to_sort(n)->get_name().hash();
        else
            return combine_hash(to_sort(n)->get_name().hash(), to_sort(n)->get_info()->hash());
    case AST_FUNC_DECL: {
        unsigned h = combine_hash(to_func_decl(n)->get_name().hash(), to_func_decl(n)->get_range()->hash());
        return ast_array_hash(to_func_decl(n)->get_domain(), to_func_decl(n)->get_arity(),
            combine_hash(h, to_func_decl(n)->get_info() == nullptr ?  0 : to_func_decl(n)->get_info()->hash()));
    }
    case AST_APP:
        return ast_array_hash(to_app(n)->get_args(),
                              to_app(n)->get_num_args(),
                              to_app(n)->get_decl()->hash());
    case AST_VAR:
        return combine_hash(to_var(n)->get_idx(), to_var(n)->get_sort()->hash());
    case AST_QUANTIFIER:
        a = ast_array_hash(to_quantifier(n)->get_decl_sorts(),
                           to_quantifier(n)->get_num_decls(),
                           to_quantifier(n)->get_kind() == forall_k ? 31 : 19);
        b = to_quantifier(n)->get_num_patterns();
        c = to_quantifier(n)->get_expr()->hash();
        mix(a,b,c);
        return c;
    default:
        UNREACHABLE();
    }
    return 0;
}

void ast_table::push_erase(ast * n) {
    // It uses two important properties:
    // 1. n is known to be in the table.
    // 2. operator== can be used instead of compare_nodes (big savings)
    unsigned mask = m_slots - 1;
    unsigned h    = n->hash();
    unsigned idx  = h & mask;
    cell * c      = m_table + idx;
    cell * prev = nullptr;
    while (true) {
        SASSERT(!c->is_free());
        cell * next = c->m_next;
        if (c->m_data == n) {
            m_size--;
            if (prev == nullptr) {
                if (next == nullptr) {
                    m_used_slots--;
                    push_recycle_cell(c);
                    c->mark_free();
                    SASSERT(c->is_free());
                }
                else {
                    *c = *next;
                    next->m_data = n;
                    push_recycle_cell(next);
                }
            }
            else {
                prev->m_next = next;
                push_recycle_cell(c);
            }
            return;
        }
        CHS_CODE(m_collisions++;);
        prev = c;
        c = next;
        SASSERT(c);
    }
}

ast* ast_table::pop_erase() {
    cell* c = m_tofree_cell;
    if (c == nullptr) {
        return nullptr;
    }
    if (c->is_free()) {
        // cell was marked free, should not be recycled.
        c->unmark_free();
        m_tofree_cell = c->m_next;
        c->mark_free();
    }
    else {
        // cell should be recycled with m_free_cell
        m_tofree_cell = c->m_next;
        recycle_cell(c);
    }        
    return c->m_data;
}



// -----------------------------------
//
// decl_plugin
//
// -----------------------------------

/**
     \brief Checks whether a log is being generated and, if necessary, adds the beginning of an "[attach-meaning]" line
    to that log. The theory solver should add some description of the meaning of the term in terms of the theory's
    internal reasoning to the end of the line and insert a line break.
    
    \param a the term that should be described.

    \return true if a log is being generated, false otherwise.
*/
bool decl_plugin::log_constant_meaning_prelude(app * a) {
    if (m_manager->has_trace_stream()) {
        m_manager->trace_stream() << "[attach-meaning] #" << a->get_id() << " " << m_manager->get_family_name(m_family_id).str() << " ";
        return true;
    }
    return false;
}

func_decl * decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                        unsigned num_args, expr * const * args, sort * range) {
    ptr_buffer<sort> sorts;
    for (unsigned i = 0; i < num_args; i++) {
        sorts.push_back(args[i]->get_sort());
    }
    return mk_func_decl(k, num_parameters, parameters, num_args, sorts.data(), range);
}

// -----------------------------------
//
// basic_decl_plugin (i.e., builtin plugin)
//
// -----------------------------------

bool basic_decl_plugin::check_proof_sorts(basic_op_kind k, unsigned arity, sort * const * domain) const {
    if (k == PR_UNDEF)
        return arity == 0;
    if (arity == 0)
        return false;
    else {
        for (unsigned i = 0; i < arity - 1; i++)
            if (domain[i] != m_proof_sort)
                return false;
#define is_array(_x_) true
        return domain[arity-1] == m_bool_sort || domain[arity-1] == m_proof_sort || is_array(domain[arity-1]);
    }
}

bool basic_decl_plugin::check_proof_args(basic_op_kind k, unsigned num_args, expr * const * args) const {
    if (k == PR_UNDEF)
        return num_args == 0;
    if (num_args == 0)
        return false;
    else {
        for (unsigned i = 0; i < num_args - 1; i++)
            if (args[i]->get_sort() != m_proof_sort)
                return false;
        return
            args[num_args - 1]->get_sort() == m_bool_sort ||
            args[num_args - 1]->get_sort() == m_proof_sort ||
            is_lambda(args[num_args-1]);
    }
}

func_decl * basic_decl_plugin::mk_bool_op_decl(char const * name, basic_op_kind k, unsigned num_args, bool assoc, bool comm, bool idempotent,
                                               bool flat_associative, bool chainable) {
    ptr_buffer<sort> domain;
    for (unsigned i = 0; i < num_args; i++)
        domain.push_back(m_bool_sort);
    func_decl_info info(m_family_id, k);
    info.set_associative(assoc);
    info.set_flat_associative(flat_associative);
    info.set_commutative(comm);
    info.set_idempotent(idempotent);
    info.set_chainable(chainable);
    func_decl * d           = m_manager->mk_func_decl(symbol(name), num_args, domain.data(), m_bool_sort, info);
    m_manager->inc_ref(d);
    return d;
}

func_decl * basic_decl_plugin::mk_implies_decl() {
    sort * domain[2] = { m_bool_sort, m_bool_sort };
    func_decl_info info(m_family_id, OP_IMPLIES);
    info.set_right_associative();
    func_decl * d = m_manager->mk_func_decl(symbol("=>"), 2, domain, m_bool_sort, info);
    m_manager->inc_ref(d);
    return d;
}

func_decl * basic_decl_plugin::mk_proof_decl(
    char const * name, basic_op_kind k,
    unsigned num_parameters, parameter const* params, unsigned num_parents) {
    ptr_buffer<sort> domain;
    for (unsigned i = 0; i < num_parents; i++)
        domain.push_back(m_proof_sort);
    domain.push_back(m_bool_sort);
    func_decl_info info(m_family_id, k, num_parameters, params);
    return m_manager->mk_func_decl(symbol(name), num_parents+1, domain.data(), m_proof_sort, info);
}

func_decl * basic_decl_plugin::mk_proof_decl(char const * name, basic_op_kind k, unsigned num_parents, bool inc_ref) {
    ptr_buffer<sort> domain;
    for (unsigned i = 0; i < num_parents; i++)
        domain.push_back(m_proof_sort);
    domain.push_back(m_bool_sort);
    func_decl * d = m_manager->mk_func_decl(symbol(name), num_parents+1, domain.data(), m_proof_sort, func_decl_info(m_family_id, k));
    if (inc_ref) m_manager->inc_ref(d);
    return d;
}

func_decl * basic_decl_plugin::mk_compressed_proof_decl(char const * name, basic_op_kind k, unsigned num_parents) {
    ptr_buffer<sort> domain;
    for (unsigned i = 0; i < num_parents; i++)
        domain.push_back(m_proof_sort);
    func_decl * d = m_manager->mk_func_decl(symbol(name), num_parents, domain.data(), m_proof_sort, func_decl_info(m_family_id, k));
    m_manager->inc_ref(d);
    return d;
}

func_decl * basic_decl_plugin::mk_proof_decl(char const * name, basic_op_kind k, unsigned num_parents, ptr_vector<func_decl> & cache) {
    if (num_parents >= cache.size()) {
        cache.resize(num_parents+1, nullptr);
    }
    if (!cache[num_parents]) {
        cache[num_parents] = mk_proof_decl(name, k, num_parents, true);
    }
    return cache[num_parents];
}

func_decl * basic_decl_plugin::mk_proof_decl(basic_op_kind k, unsigned num_parameters, parameter const* params, unsigned num_parents) {
    switch(k) {
    case PR_TH_LEMMA: {
        return mk_proof_decl("th-lemma", k, num_parameters, params, num_parents);
    }
    case PR_QUANT_INST: {
        SASSERT(num_parents == 0);
        return mk_proof_decl("quant-inst", k, num_parameters, params, num_parents);
    }
    case PR_HYPER_RESOLVE: {
        return mk_proof_decl("hyper-res", k, num_parameters, params, num_parents);
    }
    default:
        UNREACHABLE();
        return nullptr;
    }
}

#define MK_DECL(_decl_,_mk_decl_) if (!_decl_) _decl_ = _mk_decl_; return _decl_;


func_decl * basic_decl_plugin::mk_proof_decl(char const* name, basic_op_kind k, unsigned num_parents, func_decl*& fn) {
    if (!fn) {
        fn = mk_proof_decl(name, k, num_parents, true);
    }
    return fn;
}

func_decl * basic_decl_plugin::mk_proof_decl(basic_op_kind k, unsigned num_parents) {
    switch (static_cast<basic_op_kind>(k)) {
        //
        // A description of the semantics of the proof
        // declarations is provided in z3_api.h
        //
    case PR_UNDEF:                        return m_undef_decl;
    case PR_TRUE:                         return mk_proof_decl("true-axiom", k, 0, m_true_pr_decl);
    case PR_ASSERTED:                     return mk_proof_decl("asserted", k, 0, m_asserted_decl);
    case PR_GOAL:                         return mk_proof_decl("goal", k, 2, m_goal_decl);
    case PR_MODUS_PONENS:                 return mk_proof_decl("mp", k, 2, m_modus_ponens_decl);
    case PR_REFLEXIVITY:                  return mk_proof_decl("refl", k, 0, m_reflexivity_decl);
    case PR_SYMMETRY:                     return mk_proof_decl("symm", k, 1, m_symmetry_decl);
    case PR_TRANSITIVITY:                 return mk_proof_decl("trans", k, 2, m_transitivity_decl);
    case PR_TRANSITIVITY_STAR:            return mk_proof_decl("trans*", k, num_parents, m_transitivity_star_decls);
    case PR_MONOTONICITY:                 return mk_proof_decl("monotonicity", k, num_parents, m_monotonicity_decls);
    case PR_QUANT_INTRO:                  return mk_proof_decl("quant-intro", k, 1, m_quant_intro_decl);
    case PR_BIND:                         UNREACHABLE();
    case PR_DISTRIBUTIVITY:               return mk_proof_decl("distributivity", k, num_parents, m_distributivity_decls);
    case PR_AND_ELIM:                     return mk_proof_decl("and-elim", k, 1, m_and_elim_decl);
    case PR_NOT_OR_ELIM:                  return mk_proof_decl("not-or-elim", k, 1, m_not_or_elim_decl);
    case PR_REWRITE:                      return mk_proof_decl("rewrite", k, 0, m_rewrite_decl);
    case PR_REWRITE_STAR:                 return mk_proof_decl("rewrite*", k, num_parents, m_rewrite_star_decls);
    case PR_PULL_QUANT:                   return mk_proof_decl("pull-quant", k, 0, m_pull_quant_decl);
    case PR_PUSH_QUANT:                   return mk_proof_decl("push-quant", k, 0, m_push_quant_decl);
    case PR_ELIM_UNUSED_VARS:             return mk_proof_decl("elim-unused", k, 0, m_elim_unused_vars_decl);
    case PR_DER:                          return mk_proof_decl("der", k, 0, m_der_decl);
    case PR_QUANT_INST:                   return mk_proof_decl("quant-inst", k, 0, m_quant_inst_decl);
    case PR_HYPOTHESIS:                   return mk_proof_decl("hypothesis", k, 0, m_hypothesis_decl);
    case PR_LEMMA:                        return mk_proof_decl("lemma", k, 1, m_lemma_decl);
    case PR_UNIT_RESOLUTION:              return mk_proof_decl("unit-resolution", k, num_parents, m_unit_resolution_decls);
    case PR_IFF_TRUE:                     return mk_proof_decl("iff-true", k, 1, m_iff_true_decl);
    case PR_IFF_FALSE:                    return mk_proof_decl("iff-false", k, 1, m_iff_false_decl);
    case PR_COMMUTATIVITY:                return mk_proof_decl("commutativity", k, 0, m_commutativity_decl);
    case PR_DEF_AXIOM:                    return mk_proof_decl("def-axiom", k, 0, m_def_axiom_decl);
    case PR_DEF_INTRO:                    return mk_proof_decl("intro-def", k, 0, m_def_intro_decl);
    case PR_APPLY_DEF:                    return mk_proof_decl("apply-def", k, num_parents, m_apply_def_decls);
    case PR_IFF_OEQ:                      return mk_proof_decl("iff~", k, 1, m_iff_oeq_decl);
    case PR_NNF_POS:                      return mk_proof_decl("nnf-pos", k, num_parents, m_nnf_pos_decls);
    case PR_NNF_NEG:                      return mk_proof_decl("nnf-neg", k, num_parents, m_nnf_neg_decls);
    case PR_SKOLEMIZE:                    return mk_proof_decl("sk", k, 0, m_skolemize_decl);
    case PR_MODUS_PONENS_OEQ:             return mk_proof_decl("mp~", k, 2, m_mp_oeq_decl);
    case PR_TH_LEMMA:                     return mk_proof_decl("th-lemma", k, num_parents, m_th_lemma_decls);
    case PR_HYPER_RESOLVE:                return mk_proof_decl("hyper-res", k, num_parents, m_hyper_res_decl0);
    case PR_ASSUMPTION_ADD:               return mk_proof_decl("add-assume", k, num_parents, m_assumption_add_decl);
    case PR_LEMMA_ADD:                    return mk_proof_decl("add-lemma", k, num_parents, m_lemma_add_decl);
    case PR_TH_ASSUMPTION_ADD:            return mk_proof_decl("add-th-assume", k, num_parents, m_th_assumption_add_decl);
    case PR_TH_LEMMA_ADD:                 return mk_proof_decl("add-th-lemma", k, num_parents, m_th_lemma_add_decl);
    case PR_REDUNDANT_DEL:                return mk_proof_decl("del-redundant", k, num_parents, m_redundant_del_decl);
    case PR_CLAUSE_TRAIL:                 return mk_proof_decl("proof-trail", k, num_parents, false);
    default:
        UNREACHABLE();
        return nullptr;
    }
}

void basic_decl_plugin::set_manager(ast_manager * m, family_id id) {
    decl_plugin::set_manager(m, id);

    m_bool_sort = m->mk_sort(symbol("Bool"), sort_info(id, BOOL_SORT, sort_size(2)));
    m->inc_ref(m_bool_sort);

    m_true_decl    = mk_bool_op_decl("true", OP_TRUE);
    m_false_decl   = mk_bool_op_decl("false", OP_FALSE);
    m_and_decl     = mk_bool_op_decl("and", OP_AND, 2, true, true, true, true);
    m_or_decl      = mk_bool_op_decl("or", OP_OR, 2, true, true, true, true);
    m_xor_decl     = mk_bool_op_decl("xor", OP_XOR, 2, true, true);
    m_not_decl     = mk_bool_op_decl("not", OP_NOT, 1);
    m_implies_decl = mk_implies_decl();

    m_proof_sort = m->mk_sort(symbol("Proof"), sort_info(id, PROOF_SORT));
    m->inc_ref(m_proof_sort);

    m_undef_decl = mk_compressed_proof_decl("undef", PR_UNDEF, 0);
}

void basic_decl_plugin::get_sort_names(svector<builtin_name> & sort_names, symbol const & logic) {
    if (logic == symbol::null)
        sort_names.push_back(builtin_name("bool", BOOL_SORT));
    sort_names.push_back(builtin_name("Bool", BOOL_SORT));
}

void basic_decl_plugin::get_op_names(svector<builtin_name> & op_names, symbol const & logic) {
    op_names.push_back(builtin_name("true", OP_TRUE));
    op_names.push_back(builtin_name("false", OP_FALSE));
    op_names.push_back(builtin_name("=", OP_EQ));
    op_names.push_back(builtin_name("distinct", OP_DISTINCT));
    op_names.push_back(builtin_name("ite", OP_ITE));
    op_names.push_back(builtin_name("if", OP_ITE));
    op_names.push_back(builtin_name("and", OP_AND));
    op_names.push_back(builtin_name("or", OP_OR));
    op_names.push_back(builtin_name("xor", OP_XOR));
    op_names.push_back(builtin_name("not", OP_NOT));
    op_names.push_back(builtin_name("=>", OP_IMPLIES));
    if (logic == symbol::null) {
        // user friendly aliases
        op_names.push_back(builtin_name("implies", OP_IMPLIES));
        op_names.push_back(builtin_name("iff", OP_EQ));
        op_names.push_back(builtin_name("if_then_else", OP_ITE));
        op_names.push_back(builtin_name("&&", OP_AND));
        op_names.push_back(builtin_name("||", OP_OR));
        op_names.push_back(builtin_name("equals", OP_EQ));
        op_names.push_back(builtin_name("equiv", OP_EQ));
    }
}

bool basic_decl_plugin::is_value(app* a) const {
    return a->get_decl() == m_true_decl || a->get_decl() == m_false_decl;
}

bool basic_decl_plugin::is_unique_value(app* a) const {
    return is_value(a);
}

void basic_decl_plugin::finalize() {
#define DEC_REF(FIELD) if (FIELD) { m_manager->dec_ref(FIELD); }
#define DEC_ARRAY_REF(FIELD) m_manager->dec_array_ref(FIELD.size(), FIELD.begin())
    DEC_REF(m_bool_sort);
    DEC_REF(m_true_decl);
    DEC_REF(m_false_decl);
    DEC_REF(m_and_decl);
    DEC_REF(m_or_decl);
    DEC_REF(m_not_decl);
    DEC_REF(m_xor_decl);
    DEC_REF(m_implies_decl);
    DEC_ARRAY_REF(m_eq_decls);
    DEC_ARRAY_REF(m_ite_decls);

    DEC_ARRAY_REF(m_oeq_decls);
    DEC_REF(m_proof_sort);
    DEC_REF(m_undef_decl);
    DEC_REF(m_true_pr_decl);
    DEC_REF(m_asserted_decl);
    DEC_REF(m_goal_decl);
    DEC_REF(m_modus_ponens_decl);
    DEC_REF(m_reflexivity_decl);
    DEC_REF(m_symmetry_decl);
    DEC_REF(m_transitivity_decl);
    DEC_REF(m_quant_intro_decl);
    DEC_REF(m_and_elim_decl);
    DEC_REF(m_not_or_elim_decl);
    DEC_REF(m_rewrite_decl);
    DEC_REF(m_pull_quant_decl);
    DEC_REF(m_push_quant_decl);
    DEC_REF(m_elim_unused_vars_decl);
    DEC_REF(m_der_decl);
    DEC_REF(m_quant_inst_decl);
    DEC_ARRAY_REF(m_monotonicity_decls);
    DEC_ARRAY_REF(m_transitivity_star_decls);
    DEC_ARRAY_REF(m_distributivity_decls);
    DEC_ARRAY_REF(m_assoc_flat_decls);
    DEC_ARRAY_REF(m_rewrite_star_decls);

    DEC_REF(m_hypothesis_decl);
    DEC_REF(m_iff_true_decl);
    DEC_REF(m_iff_false_decl);
    DEC_REF(m_commutativity_decl);
    DEC_REF(m_def_axiom_decl);
    DEC_REF(m_lemma_decl);
    DEC_ARRAY_REF(m_unit_resolution_decls);

    DEC_REF(m_def_intro_decl);
    DEC_REF(m_iff_oeq_decl);
    DEC_REF(m_skolemize_decl);
    DEC_REF(m_mp_oeq_decl);
    DEC_REF(m_assumption_add_decl);
    DEC_REF(m_lemma_add_decl);
    DEC_REF(m_th_assumption_add_decl);
    DEC_REF(m_th_lemma_add_decl);
    DEC_REF(m_redundant_del_decl);
    DEC_ARRAY_REF(m_apply_def_decls);
    DEC_ARRAY_REF(m_nnf_pos_decls);
    DEC_ARRAY_REF(m_nnf_neg_decls);

    DEC_ARRAY_REF(m_th_lemma_decls);
    DEC_REF(m_hyper_res_decl0);

}

sort * basic_decl_plugin::mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) {
    if (k == BOOL_SORT)
        return m_bool_sort;
    SASSERT(k == PROOF_SORT);
    return m_proof_sort;
}

func_decl * basic_decl_plugin::mk_eq_decl_core(char const * name, decl_kind k, sort * s, ptr_vector<func_decl> & cache) {
    unsigned id = s->get_decl_id();
    force_ptr_array_size(cache, id + 1);
    if (cache[id] == 0) {
        sort * domain[2] = { s, s};
        func_decl_info info(m_family_id, k);
        info.set_commutative();
        info.set_chainable();
        func_decl * decl = m_manager->mk_func_decl(symbol(name), 2, domain, m_bool_sort, info);
        SASSERT(decl->is_chainable());
        cache[id] = decl;
        m_manager->inc_ref(decl);
    }
    return cache[id];
}

func_decl * basic_decl_plugin::mk_ite_decl(sort * s) {
    unsigned id = s->get_decl_id();
    force_ptr_array_size(m_ite_decls, id + 1);
    if (m_ite_decls[id] == 0) {
        sort * domain[3] = { m_bool_sort, s, s};
        func_decl * decl = m_manager->mk_func_decl(symbol("if"), 3, domain, s, func_decl_info(m_family_id, OP_ITE));
        m_ite_decls[id] = decl;
        m_manager->inc_ref(decl);
    }
    return m_ite_decls[id];
}

sort* basic_decl_plugin::join(unsigned n, sort* const* srts) {
    SASSERT(n > 0);
    sort* s = srts[0];
    while (n > 1) {
        ++srts;
        --n;
        s = join(s, *srts);
    }
    return s;
}

sort* basic_decl_plugin::join(unsigned n, expr* const* es) {
    SASSERT(n > 0);
    sort* s = es[0]->get_sort();
    while (n > 1) {
        ++es;
        --n;
        s = join(s, (*es)->get_sort());
    }
    return s;
}

sort* basic_decl_plugin::join(sort* s1, sort* s2) {
    if (s1 == s2) return s1;
    if (s1->get_family_id() == arith_family_id &&
        s2->get_family_id() == arith_family_id) {
        if (s1->get_decl_kind() == REAL_SORT) {
            return s1;
        }
        return s2;
    }
    std::ostringstream buffer;
    buffer << "Sorts " << mk_pp(s1, *m_manager) << " and " << mk_pp(s2, *m_manager) << " are incompatible";
    throw ast_exception(buffer.str());
}


func_decl * basic_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                          unsigned arity, sort * const * domain, sort * range) {
    switch (static_cast<basic_op_kind>(k)) {
    case OP_TRUE:    return m_true_decl;
    case OP_FALSE:   return m_false_decl;
    case OP_AND:     return m_and_decl;
    case OP_OR:      return m_or_decl;
    case OP_NOT:     return m_not_decl;
    case OP_IMPLIES: return m_implies_decl;
    case OP_XOR:     return m_xor_decl;
    case OP_ITE:     return arity == 3 ? mk_ite_decl(join(domain[1], domain[2])) : nullptr;
        // eq and oeq must have at least two arguments, they can have more since they are chainable
    case OP_EQ:      return arity >= 2 ? mk_eq_decl_core("=", OP_EQ, join(arity, domain), m_eq_decls) : nullptr;
    case OP_OEQ:     return arity >= 2 ? mk_eq_decl_core("~", OP_OEQ, join(arity, domain), m_oeq_decls) : nullptr;
    case PR_BIND: {
        func_decl_info info(m_family_id, PR_BIND);
        return m_manager->mk_func_decl(symbol("proof-bind"), arity, domain, m_proof_sort, info);
    }
    case OP_DISTINCT: {
        func_decl_info info(m_family_id, OP_DISTINCT);
        info.set_pairwise();
        ptr_buffer<sort> sorts;
        for (unsigned i = 1; i < arity; i++) {
            if (domain[i] != domain[0]) {
                sort* srt = join(arity, domain);
                for (unsigned j = 0; j < arity; ++j) 
                    sorts.push_back(srt);
                domain = sorts.data();
            }
        }
        return m_manager->mk_func_decl(symbol("distinct"), arity, domain, m_bool_sort, info);
    }
    default:
        break;
    }

    SASSERT(is_proof(k));

    if (!check_proof_sorts(static_cast<basic_op_kind>(k), arity, domain))
        m_manager->raise_exception("Invalid proof object.");

    if (num_parameters == 0) {
        return mk_proof_decl(static_cast<basic_op_kind>(k), arity - 1);
    }
    return mk_proof_decl(static_cast<basic_op_kind>(k), num_parameters, parameters, arity - 1);
}

func_decl * basic_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                            unsigned num_args, expr * const * args, sort * range) {
    switch (static_cast<basic_op_kind>(k)) {
    case OP_TRUE:    return m_true_decl;
    case OP_FALSE:   return m_false_decl;
    case OP_AND:     return m_and_decl;
    case OP_OR:      return m_or_decl;
    case OP_NOT:     return m_not_decl;
    case OP_IMPLIES: return m_implies_decl;
    case OP_XOR:     return m_xor_decl;
    case OP_ITE:     return num_args == 3 ? mk_ite_decl(join(args[1]->get_sort(), args[2]->get_sort())): nullptr;
        // eq and oeq must have at least two arguments, they can have more since they are chainable
    case OP_EQ:      return num_args >= 2 ? mk_eq_decl_core("=", OP_EQ, join(num_args, args), m_eq_decls) : nullptr;
    case OP_OEQ:     return num_args >= 2 ? mk_eq_decl_core("~", OP_OEQ, join(num_args, args), m_oeq_decls) : nullptr;
    case OP_DISTINCT:
        return decl_plugin::mk_func_decl(k, num_parameters, parameters, num_args, args, range);
    case PR_BIND: {
        ptr_buffer<sort> sorts;
        for (unsigned i = 0; i < num_args; ++i) sorts.push_back(args[i]->get_sort());
        return mk_func_decl(k, num_parameters, parameters, num_args, sorts.data(), range);
    }
    default:
        break;
    }

    SASSERT(is_proof(k));

    if (!check_proof_args(static_cast<basic_op_kind>(k), num_args, args))
        m_manager->raise_exception("Invalid proof object.");

    if (num_parameters == 0) {
        return mk_proof_decl(static_cast<basic_op_kind>(k), num_args - 1);
    }
    return mk_proof_decl(static_cast<basic_op_kind>(k), num_parameters, parameters, num_args - 1);
}

expr * basic_decl_plugin::get_some_value(sort * s) {
    if (s == m_bool_sort)
        return m_manager->mk_false();
    return nullptr;
}

// -----------------------------------
//
// label_decl_plugin
//
// -----------------------------------

label_decl_plugin::label_decl_plugin():
    m_lblpos("lblpos"),
    m_lblneg("lblneg"),
    m_lbllit("lbl-lit") {
}

void label_decl_plugin::set_manager(ast_manager * m, family_id id) {
    decl_plugin::set_manager(m, id);
}

sort * label_decl_plugin::mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) {
    UNREACHABLE();
    return nullptr;
}

func_decl * label_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                          unsigned arity, sort * const * domain, sort * range) {
    if (k == OP_LABEL) {
        if (arity != 1 || num_parameters < 2 || !parameters[0].is_int() || !parameters[1].is_symbol() || !m_manager->is_bool(domain[0])) {
            m_manager->raise_exception("invalid label declaration");
            return nullptr;
        }
        for (unsigned i = 2; i < num_parameters; i++) {
            if (!parameters[i].is_symbol()) {
                m_manager->raise_exception("invalid label declaration");
                return nullptr;
            }
        }
        return m_manager->mk_func_decl(parameters[0].get_int() ? m_lblpos : m_lblneg, arity, domain, domain[0],
                                       func_decl_info(m_family_id, OP_LABEL, num_parameters, parameters));
    }
    else {
        SASSERT(k == OP_LABEL_LIT);
        if (arity != 0) {
            m_manager->raise_exception("invalid label literal declaration");
            return nullptr;
        }
        for (unsigned i = 0; i < num_parameters; i++) {
            if (!parameters[i].is_symbol()) {
                m_manager->raise_exception("invalid label literal declaration");
                return nullptr;
            }
        }
        return m_manager->mk_func_decl(m_lbllit, 0, static_cast<sort * const *>(nullptr), m_manager->mk_bool_sort(),
                                       func_decl_info(m_family_id, OP_LABEL_LIT, num_parameters, parameters));
    }
}

// -----------------------------------
//
// pattern_decl_plugin
//
// -----------------------------------

sort * pattern_decl_plugin::mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) {
    UNREACHABLE();
    return nullptr;
}

func_decl * pattern_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                            unsigned arity, sort * const * domain, sort * range) {
    return m_manager->mk_func_decl(symbol("pattern"), arity, domain,
                                   m_manager->mk_bool_sort(), // the range can be an arbitrary sort.
                                   func_decl_info(m_family_id, OP_PATTERN));
}

// -----------------------------------
//
// model_value_decl_plugin
//
// -----------------------------------

sort * model_value_decl_plugin::mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) {
    UNREACHABLE();
    return nullptr;
}

func_decl * model_value_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                                  unsigned arity, sort * const * domain, sort * range) {
    SASSERT(k == OP_MODEL_VALUE);
    if (arity != 0 || num_parameters != 2 || !parameters[0].is_int() || !parameters[1].is_ast() || !is_sort(parameters[1].get_ast())) {
        m_manager->raise_exception("invalid model value");
        return nullptr;
    }
    int idx  = parameters[0].get_int();
    sort * s = to_sort(parameters[1].get_ast());
    string_buffer<64> buffer;
    buffer << s->get_name().str() << "!val!" << idx;
    func_decl_info info(m_family_id, k, num_parameters, parameters);
    info.m_private_parameters = true;
    return m_manager->mk_func_decl(symbol(buffer.c_str()), 0, static_cast<sort * const *>(nullptr), s, info);
}

bool model_value_decl_plugin::is_value(app* n) const {
    return is_app_of(n, m_family_id, OP_MODEL_VALUE);
}

bool model_value_decl_plugin::is_unique_value(app* n) const {
    return is_value(n);
}

// -----------------------------------
//
// user_sort_plugin
//
// -----------------------------------

sort * user_sort_plugin::mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) {
    SASSERT(m_family_id != null_family_id);
    SASSERT(k < static_cast<int>(m_sort_names.size()));
    sort_info si(m_family_id, k, num_parameters, parameters);
    return m_manager->mk_sort(m_sort_names[k], si);
}

func_decl * user_sort_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                           unsigned arity, sort * const * domain, sort * range) {
    UNREACHABLE();
    return nullptr;
}

decl_kind user_sort_plugin::register_name(symbol s) {
    decl_kind k;
    if (m_name2decl_kind.find(s, k))
        return k;
    k = m_sort_names.size();
    m_sort_names.push_back(s);
    m_name2decl_kind.insert(s, k);
    return k;
}

decl_plugin * user_sort_plugin::mk_fresh() {
    user_sort_plugin * p = alloc(user_sort_plugin);
    for (symbol const& s : m_sort_names)
        p->register_name(s);
    return p;
}


// -----------------------------------
//
// ast_manager
//
// -----------------------------------

ast_manager::ast_manager(proof_gen_mode m, char const * trace_file, bool is_format_manager):
    m_alloc("ast_manager"),
    m_expr_array_manager(*this, m_alloc),
    m_expr_dependency_manager(*this, m_alloc),
    m_expr_dependency_array_manager(*this, m_alloc),
    m_proof_mode(m),
    m_trace_stream(nullptr),
    m_trace_stream_owner(false),
    m_lambda_def(":lambda-def") {

    if (trace_file) {
        m_trace_stream       = alloc(std::fstream, trace_file, std::ios_base::out);
        m_trace_stream_owner = true;
        *m_trace_stream << "[tool-version] Z3 " << Z3_MAJOR_VERSION << "." << Z3_MINOR_VERSION << "." << Z3_BUILD_NUMBER << "\n";
    }

    if (!is_format_manager)
        m_format_manager = alloc(ast_manager, PGM_DISABLED, m_trace_stream, true);
    else
        m_format_manager = nullptr;
    init();
}

ast_manager::ast_manager(proof_gen_mode m, std::fstream * trace_stream, bool is_format_manager):
    m_alloc("ast_manager"),
    m_expr_array_manager(*this, m_alloc),
    m_expr_dependency_manager(*this, m_alloc),
    m_expr_dependency_array_manager(*this, m_alloc),
    m_proof_mode(m),
    m_trace_stream(trace_stream),
    m_trace_stream_owner(false),
    m_lambda_def(":lambda-def") {

    if (!is_format_manager)
        m_format_manager = alloc(ast_manager, PGM_DISABLED, trace_stream, true);
    else
        m_format_manager = nullptr;
    init();
}

ast_manager::ast_manager(ast_manager const & src, bool disable_proofs):
    m_alloc("ast_manager"),
    m_expr_array_manager(*this, m_alloc),
    m_expr_dependency_manager(*this, m_alloc),
    m_expr_dependency_array_manager(*this, m_alloc),
    m_proof_mode(disable_proofs ? PGM_DISABLED : src.m_proof_mode),
    m_trace_stream(src.m_trace_stream),
    m_trace_stream_owner(false),
    m_lambda_def(":lambda-def") {
    SASSERT(!src.is_format_manager());
    m_format_manager = alloc(ast_manager, PGM_DISABLED, m_trace_stream, true);
    init();
    copy_families_plugins(src);
    update_fresh_id(src);
}

void ast_manager::update_fresh_id(ast_manager const& m) {
    m_fresh_id = std::max(m_fresh_id, m.m_fresh_id);
}


void ast_manager::init() {
    m_int_real_coercions = true;
    m_debug_ref_count = false;
    m_fresh_id = 0;
    m_expr_id_gen.reset(0);
    m_decl_id_gen.reset(c_first_decl_id);
    m_some_value_proc = nullptr;
    ENSURE(basic_family_id       == mk_family_id("basic"));
    ENSURE(label_family_id       == mk_family_id("label"));
    ENSURE(pattern_family_id     == mk_family_id("pattern"));
    ENSURE(model_value_family_id == mk_family_id("model-value"));
    ENSURE(user_sort_family_id   == mk_family_id("user-sort"));
    ENSURE(arith_family_id       == mk_family_id("arith"));
    basic_decl_plugin * plugin = alloc(basic_decl_plugin);
    register_plugin(basic_family_id, plugin);
    m_bool_sort = plugin->mk_bool_sort();
    inc_ref(m_bool_sort);
    m_proof_sort = plugin->mk_proof_sort();
    inc_ref(m_proof_sort);
    m_undef_proof = mk_const(basic_family_id, PR_UNDEF);
    inc_ref(m_undef_proof);
    register_plugin(label_family_id, alloc(label_decl_plugin));
    register_plugin(pattern_family_id, alloc(pattern_decl_plugin));
    register_plugin(model_value_family_id, alloc(model_value_decl_plugin));
    register_plugin(user_sort_family_id, alloc(user_sort_plugin));
    m_true  = mk_const(basic_family_id, OP_TRUE);
    inc_ref(m_true);
    m_false = mk_const(basic_family_id, OP_FALSE);
    inc_ref(m_false);
}


template<typename T>
static void mark_array_ref(ast_mark& mark, unsigned sz, T * const * a) {
    for(unsigned i = 0; i < sz; i++) {
        mark.mark(a[i], true);
    }
}

static void mark_array_ref(ast_mark& mark, unsigned sz, parameter const * a) {
    for(unsigned i = 0; i < sz; i++) {
        if (a[i].is_ast()) {
            mark.mark(a[i].get_ast(), true);
        }
    }
}


ast_manager::~ast_manager() {
    SASSERT(is_format_manager() || !m_family_manager.has_family(symbol("format")));

    dec_ref(m_bool_sort);
    dec_ref(m_proof_sort);
    dec_ref(m_true);
    dec_ref(m_false);
    dec_ref(m_undef_proof);
    for (decl_plugin* p : m_plugins) {
        if (p)
            p->finalize();
    }
    for (decl_plugin* p : m_plugins) {
        if (p)
            dealloc(p);
    }
    m_plugins.reset();
    while (!m_ast_table.empty()) {
        DEBUG_CODE(IF_VERBOSE(0, verbose_stream() << "ast_manager LEAKED: " << m_ast_table.size() << std::endl););
        ptr_vector<ast> roots;
        ast_mark mark;
        for (ast * n : m_ast_table) {
            switch (n->get_kind()) {
            case AST_SORT: {
                sort_info* info = to_sort(n)->get_info();
                if (info != nullptr) {
                    mark_array_ref(mark, info->get_num_parameters(), info->get_parameters());
                }
                break;
            }
            case AST_FUNC_DECL: {
                func_decl_info* info = to_func_decl(n)->get_info();
                if (info != nullptr) {
                    mark_array_ref(mark, info->get_num_parameters(), info->get_parameters());
                }
                mark_array_ref(mark, to_func_decl(n)->get_arity(), to_func_decl(n)->get_domain());
                mark.mark(to_func_decl(n)->get_range(), true);
                break;
            }
            case AST_APP:
                mark.mark(to_app(n)->get_decl(), true);
                mark_array_ref(mark, to_app(n)->get_num_args(), to_app(n)->get_args());
                break;
            case AST_VAR:
                mark.mark(to_var(n)->get_sort(), true);
                break;
            case AST_QUANTIFIER:
                mark_array_ref(mark, to_quantifier(n)->get_num_decls(), to_quantifier(n)->get_decl_sorts());
                mark.mark(to_quantifier(n)->get_expr(), true);
                mark_array_ref(mark, to_quantifier(n)->get_num_patterns(), to_quantifier(n)->get_patterns());
                mark_array_ref(mark, to_quantifier(n)->get_num_no_patterns(), to_quantifier(n)->get_no_patterns());
                break;
            }
        }
        for (ast * n : m_ast_table) {
            if (!mark.is_marked(n)) {
                roots.push_back(n);
            }
        }
        SASSERT(!roots.empty());
        for (unsigned i = 0; i < roots.size(); ++i) {
            ast* a = roots[i];
            DEBUG_CODE(
                std::cout << "Leaked: ";
                if (is_sort(a)) {
                    std::cout << to_sort(a)->get_name() << "\n";
                }
                else {
                    std::cout << mk_ll_pp(a, *this, false) << "id: " << a->get_id() << "\n";
                });
            a->m_ref_count = 0;
            delete_node(a);
        }
    }
    if (m_format_manager != nullptr)
        dealloc(m_format_manager);
    if (m_trace_stream_owner) {
        std::fstream & tmp = * m_trace_stream;
        tmp << "[eof]\n";
        tmp.close();
        dealloc(m_trace_stream);
        m_trace_stream = nullptr;
    }
}

void ast_manager::compact_memory() {
    m_alloc.consolidate();
    unsigned capacity = m_ast_table.capacity();
    if (capacity > 4*m_ast_table.size()) {
        ast_table new_ast_table;
        for (ast* curr : m_ast_table)
            new_ast_table.insert(curr);
        m_ast_table.swap(new_ast_table);
        IF_VERBOSE(10, verbose_stream() << "(ast-table :prev-capacity " << capacity
                   << " :capacity " << m_ast_table.capacity() << " :size " << m_ast_table.size() << ")\n";);
    }
    else {
        IF_VERBOSE(10, verbose_stream() << "(ast-table :capacity " << m_ast_table.capacity() << " :size " << m_ast_table.size() << ")\n";);
    }
}

void ast_manager::compress_ids() {
    ptr_vector<ast> asts;
    m_expr_id_gen.cleanup();
    m_decl_id_gen.cleanup(c_first_decl_id);
    for (ast * n : m_ast_table) {
        if (is_decl(n))
            n->m_id = m_decl_id_gen.mk();
        else
            n->m_id = m_expr_id_gen.mk();
        asts.push_back(n);
    }    
    m_ast_table.finalize();
    for (ast* a : asts) 
        m_ast_table.insert(a);
}

void ast_manager::raise_exception(char const * msg) {
    throw ast_exception(msg);
}

void ast_manager::raise_exception(std::string &&  msg) {
    throw ast_exception(std::move(msg));
}


std::ostream& ast_manager::display(std::ostream& out, parameter const& p) {
    switch (p.get_kind()) {
    case parameter::PARAM_AST:
        return out << mk_pp(p.get_ast(), *this);
    default:
        return p.display(out);
    }
    return out;
}

void ast_manager::copy_families_plugins(ast_manager const & from) {
    TRACE("copy_families_plugins",
          tout << "target:\n";
          for (family_id fid = 0; m_family_manager.has_family(fid); fid++) {
              tout << "fid: " << fid << " fidname: " << get_family_name(fid) << "\n";
          });
    ast_translation trans(const_cast<ast_manager&>(from), *this, false);
    // Inheriting plugins can create new family ids. Since new family ids are
    // assigned in the order that they are created, this can result in differing
    // family ids. To avoid this, we first assign all family ids and only then inherit plugins.
    for (family_id fid = 0; from.m_family_manager.has_family(fid); fid++) {
        symbol fid_name   = from.get_family_name(fid);
        if (!m_family_manager.has_family(fid)) {
            family_id new_fid = mk_family_id(fid_name);
            (void)new_fid;
            TRACE("copy_families_plugins", tout << "new target fid created: " << new_fid << " fid_name: " << fid_name << "\n";);
        }
    }
    for (family_id fid = 0; from.m_family_manager.has_family(fid); fid++) {
        SASSERT(from.is_builtin_family_id(fid) == is_builtin_family_id(fid));
        SASSERT(!from.is_builtin_family_id(fid) || m_family_manager.has_family(fid));
        symbol fid_name   = from.get_family_name(fid);
        (void)fid_name;
        TRACE("copy_families_plugins", tout << "copying: " << fid_name << ", src fid: " << fid
              << ", target has_family: " << m_family_manager.has_family(fid) << "\n";
              if (m_family_manager.has_family(fid)) tout << get_family_id(fid_name) << "\n";);
        TRACE("copy_families_plugins", tout << "target fid: " << get_family_id(fid_name) << "\n";);
        SASSERT(fid == get_family_id(fid_name));
        if (from.has_plugin(fid) && !has_plugin(fid)) {
            decl_plugin * new_p = from.get_plugin(fid)->mk_fresh();
            register_plugin(fid, new_p);
            SASSERT(new_p->get_family_id() == fid);
            SASSERT(has_plugin(fid));
        }
        if (from.has_plugin(fid)) {
            get_plugin(fid)->inherit(from.get_plugin(fid), trans);
        }
        SASSERT(from.m_family_manager.has_family(fid) == m_family_manager.has_family(fid));
        SASSERT(from.get_family_id(fid_name) == get_family_id(fid_name));
        SASSERT(!from.has_plugin(fid) || has_plugin(fid));
    }
}

void ast_manager::set_next_expr_id(unsigned id) {
 try_again:
    id = m_expr_id_gen.set_next_id(id);
    for (ast * curr : m_ast_table) {
        if (curr->get_id() == id) {
            // id is in use, move to the next one.
            ++id;
            goto try_again;
        }
    }    
}

unsigned ast_manager::get_node_size(ast const * n) { return ::get_node_size(n); }

std::ostream& ast_manager::display(std::ostream& out) const {
    for (ast * a : m_ast_table) {
        if (is_func_decl(a)) {
            out << to_func_decl(a)->get_name() << " " << a->get_id() << "\n";
        }
    }
    return out;
}


void ast_manager::register_plugin(symbol const & s, decl_plugin * plugin) {
    family_id id = m_family_manager.mk_family_id(s);
    SASSERT(is_format_manager() || s != symbol("format"));
    register_plugin(id, plugin);
}

decl_plugin * ast_manager::get_plugin(family_id fid) const {
    return m_plugins.get(fid, 0);
}


bool ast_manager::is_value(expr* e) const {
    decl_plugin const * p = nullptr;
    if (is_app(e)) {
        p = get_plugin(to_app(e)->get_family_id());
        return p && p->is_value(to_app(e));
    }
    return false;
}

bool ast_manager::is_unique_value(expr* e) const {
    decl_plugin const * p = nullptr;
    if (is_app(e)) {
        p = get_plugin(to_app(e)->get_family_id());
        return p && p->is_unique_value(to_app(e));
    }
    return false;
}

bool ast_manager::are_equal(expr * a, expr * b) const {
    if (a == b) {
        return true;
    }
    if (is_app(a) && is_app(b)) {
        app* ap = to_app(a), *bp = to_app(b);
        decl_plugin const * p = get_plugin(ap->get_family_id());
        if (!p) {
            p = get_plugin(bp->get_family_id());
        }
        return p && p->are_equal(ap, bp);
    }
    return false;
}


bool ast_manager::are_distinct(expr* a, expr* b) const {
    if (is_app(a) && is_app(b)) {
        app* ap = to_app(a), *bp = to_app(b);
        decl_plugin const * p = get_plugin(ap->get_family_id());
        if (!p) {
            p = get_plugin(bp->get_family_id());
        }
        return p && p->are_distinct(ap, bp);
    }
    return false;
}

void ast_manager::add_lambda_def(func_decl* f, quantifier* q) {
    m_lambda_defs.insert(f, q);
    f->get_info()->set_lambda(true);
    inc_ref(q);
}

quantifier* ast_manager::is_lambda_def(func_decl* f) {
    if (f->get_info() && f->get_info()->is_lambda()) {
        return m_lambda_defs[f];
    }
    return nullptr;
}

void ast_manager::register_plugin(family_id id, decl_plugin * plugin) {
    SASSERT(m_plugins.get(id, 0) == 0);
    m_plugins.setx(id, plugin, 0);
    plugin->set_manager(this, id);
}

bool ast_manager::is_bool(expr const * n) const {
    return n->get_sort() == m_bool_sort;
}

#ifdef Z3DEBUG
bool ast_manager::slow_not_contains(ast const * n) {
    unsigned num = 0;
    for (ast * curr : m_ast_table) {
        if (compare_nodes(curr, n)) {
            TRACE("nondet_bug",
                  tout << "id1:   " << curr->get_id() << ", id2: " << n->get_id() << "\n";
                  tout << "hash1: " << get_node_hash(curr) << ", hash2: " << get_node_hash(n) << "\n";);
            return false;
        }
        SASSERT(!(is_app(n) && is_app(curr) &&
                  to_app(n)->get_decl() == to_app(curr)->get_decl() &&
                  to_app(n)->get_num_args() == 0 &&
                  to_app(curr)->get_num_args() == 0));
        num++;
    }
    SASSERT(num == m_ast_table.size());
    return true;
}
#endif

#if 0
static unsigned s_count = 0;

static void track_id(ast_manager& m, ast* n, unsigned id) {
    if (n->get_id() != id) return;
    ++s_count;
    TRACE("ast", tout << s_count << "\n";);
//    SASSERT(s_count != 5);
}
#endif

ast * ast_manager::register_node_core(ast * n) {
    unsigned h = get_node_hash(n);
    n->m_hash = h;
#ifdef Z3DEBUG
    bool contains = m_ast_table.contains(n);
    CASSERT("nondet_bug", contains || slow_not_contains(n));
#endif

    ast* r = m_ast_table.insert_if_not_there(n);    

    SASSERT(r->m_hash == h);
    if (r != n) {
        SASSERT(contains);
        SASSERT(m_ast_table.contains(n));
        if (is_func_decl(r) && to_func_decl(r)->get_range() != to_func_decl(n)->get_range()) {
            std::ostringstream buffer;
            buffer << "Recycling of declaration for the same name '" << to_func_decl(r)->get_name().str()
                   << "' and domain, but different range type is not permitted";
            throw ast_exception(buffer.str());
        }
        deallocate_node(n, ::get_node_size(n));
        return r;
    }
    else {
        SASSERT(!contains);
        SASSERT(m_ast_table.contains(n));
    }

    n->m_id = is_decl(n) ? m_decl_id_gen.mk() : m_expr_id_gen.mk();        

//    track_id(*this, n, 77);
    
//    TRACE("ast", tout << (s_count++) << " Object " << n->m_id << " was created.\n";);
    TRACE("mk_var_bug", tout << "mk_ast: " << n->m_id << "\n";);
    // increment reference counters
    switch (n->get_kind()) {
    case AST_SORT:
        if (to_sort(n)->m_info != nullptr) {
            to_sort(n)->m_info = alloc(sort_info, *(to_sort(n)->get_info()));
            to_sort(n)->m_info->init_eh(*this);
        }
        break;
    case AST_FUNC_DECL:
        if (to_func_decl(n)->m_info != nullptr) {
            to_func_decl(n)->m_info = alloc(func_decl_info, *(to_func_decl(n)->get_info()));
            to_func_decl(n)->m_info->init_eh(*this);
        }
        inc_array_ref(to_func_decl(n)->get_arity(), to_func_decl(n)->get_domain());
        inc_ref(to_func_decl(n)->get_range());
        break;
    case AST_APP: {
        app * t = to_app(n);
        inc_ref(t->get_decl());
        unsigned num_args = t->get_num_args();
        if (num_args > 0) {
            app_flags * f     = t->flags();
            *f = mk_default_app_flags();
            SASSERT(t->is_ground());
            SASSERT(!t->has_quantifiers());
            SASSERT(!t->has_labels());
            if (is_label(t))
                f->m_has_labels = true;
            unsigned depth = 0;
            for (unsigned i = 0; i < num_args; i++) {
                expr * arg = t->get_arg(i);
                inc_ref(arg);
                unsigned arg_depth = 0;
                switch (arg->get_kind()) {
                case AST_APP: {
                    app_flags * arg_flags = to_app(arg)->flags();
                    arg_depth = arg_flags->m_depth;
                    if (arg_flags->m_has_quantifiers)
                        f->m_has_quantifiers = true;
                    if (arg_flags->m_has_labels)
                        f->m_has_labels = true;
                    if (!arg_flags->m_ground)
                        f->m_ground = false;
                    break;
                }
                case AST_QUANTIFIER:
                    f->m_has_quantifiers = true;
                    f->m_ground          = false;
                    arg_depth            = to_quantifier(arg)->get_depth();
                    break;
                case AST_VAR:
                    f->m_ground          = false;
                    arg_depth            = 1;
                    break;
                default:
                    UNREACHABLE();
                }
                if (arg_depth > depth)
                    depth = arg_depth;
            }
            depth++;
            if (depth > c_max_depth)
                depth = c_max_depth;
            f->m_depth = depth;
            SASSERT(t->get_depth() == depth);
        }
        break;
    }
    case AST_VAR:
        inc_ref(to_var(n)->get_sort());
        break;
    case AST_QUANTIFIER:
        inc_array_ref(to_quantifier(n)->get_num_decls(), to_quantifier(n)->get_decl_sorts());
        inc_ref(to_quantifier(n)->get_expr());
        inc_ref(to_quantifier(n)->get_sort());
        inc_array_ref(to_quantifier(n)->get_num_patterns(), to_quantifier(n)->get_patterns());
        inc_array_ref(to_quantifier(n)->get_num_no_patterns(), to_quantifier(n)->get_no_patterns());
        break;
    default:
        break;
    }
    return n;
}


void ast_manager::delete_node(ast * n) {
    TRACE("delete_node_bug", tout << mk_ll_pp(n, *this) << "\n";);

    SASSERT(m_ast_table.contains(n));
    m_ast_table.push_erase(n);

    while ((n = m_ast_table.pop_erase())) {

        CTRACE("del_quantifier", is_quantifier(n), tout << "deleting quantifier " << n->m_id << " " << n << "\n";);
        TRACE("mk_var_bug", tout << "del_ast: " << " " << n->m_ref_count << "\n";);
        TRACE("ast_delete_node", tout << mk_bounded_pp(n, *this) << "\n";);

        SASSERT(!m_debug_ref_count || !m_debug_free_indices.contains(n->m_id));

#ifdef RECYCLE_FREE_AST_INDICES
        if (!m_debug_ref_count) {
            if (is_decl(n))
                m_decl_id_gen.recycle(n->m_id);
            else
                m_expr_id_gen.recycle(n->m_id);
        }
#endif
        switch (n->get_kind()) {
        case AST_SORT:
            if (to_sort(n)->m_info != nullptr) {
                sort_info * info = to_sort(n)->get_info();
                info->del_eh(*this);
                dealloc(info);
            }
            break;
        case AST_FUNC_DECL: {
            func_decl* f = to_func_decl(n);
            if (f->m_info != nullptr) {
                func_decl_info * info = f->get_info();
                if (info->is_lambda()) {
                    push_dec_ref(m_lambda_defs[f]);
                    m_lambda_defs.remove(f);
                }
                info->del_eh(*this);
                dealloc(info);
            }
            push_dec_array_ref(f->get_arity(), f->get_domain());
            push_dec_ref(f->get_range());
            break;
        }
        case AST_APP: {
            app* a = to_app(n);
            push_dec_ref(a->get_decl());
            push_dec_array_ref(a->get_num_args(), a->get_args());
            break;
        }
        case AST_VAR:
            push_dec_ref(to_var(n)->get_sort());
            break;
        case AST_QUANTIFIER: {
            quantifier* q = to_quantifier(n);
            push_dec_array_ref(q->get_num_decls(), q->get_decl_sorts());
            push_dec_ref(q->get_expr());
            push_dec_ref(q->get_sort());
            push_dec_array_ref(q->get_num_patterns(), q->get_patterns());
            push_dec_array_ref(q->get_num_no_patterns(), q->get_no_patterns());
            break;
        }
        default:
            break;
        }
        if (m_debug_ref_count) {
            m_debug_free_indices.insert(n->m_id,0);
        }       
        deallocate_node(n, ::get_node_size(n));
    }
}


sort * ast_manager::mk_sort(family_id fid, decl_kind k, unsigned num_parameters, parameter const * parameters) {
    decl_plugin * p = get_plugin(fid);
    if (p)
        return p->mk_sort(k, num_parameters, parameters);
    return nullptr;
}

func_decl * ast_manager::mk_func_decl(family_id fid, decl_kind k, unsigned num_parameters, parameter const * parameters,
                                      unsigned arity, sort * const * domain, sort * range) {
    decl_plugin * p = get_plugin(fid);
    if (p)
        return p->mk_func_decl(k, num_parameters, parameters, arity, domain, range);
    return nullptr;
}

func_decl * ast_manager::mk_func_decl(family_id fid, decl_kind k, unsigned num_parameters, parameter const * parameters,
                                      unsigned num_args, expr * const * args, sort * range) {
    decl_plugin * p = get_plugin(fid);
    if (p)
        return p->mk_func_decl(k, num_parameters, parameters, num_args, args, range);
    return nullptr;
}

app * ast_manager::mk_app(family_id fid, decl_kind k, unsigned num_parameters, parameter const * parameters,
                          unsigned num_args, expr * const * args, sort * range) {
    func_decl * decl = mk_func_decl(fid, k, num_parameters, parameters, num_args, args, range);
    if (decl != nullptr)
        return mk_app(decl, num_args, args);
    return nullptr;
}

app * ast_manager::mk_app(family_id fid, decl_kind k, unsigned num_args, expr * const * args) {
    return mk_app(fid, k, 0, nullptr, num_args, args);
}

app * ast_manager::mk_app(family_id fid, decl_kind k, expr * arg) {
    return mk_app(fid, k, 0, nullptr, 1, &arg);
}

app * ast_manager::mk_app(family_id fid, decl_kind k, expr * arg1, expr * arg2) {
    expr * args[2] = { arg1, arg2 };
    return mk_app(fid, k, 0, nullptr, 2, args);
}

app * ast_manager::mk_app(family_id fid, decl_kind k, expr * arg1, expr * arg2, expr * arg3) {
    expr * args[3] = { arg1, arg2, arg3 };
    return mk_app(fid, k, 0, nullptr, 3, args);
}

sort * ast_manager::mk_sort(symbol const & name, sort_info * info) {
    unsigned sz      = sort::get_obj_size();
    void * mem       = allocate_node(sz);
    sort * new_node  = new (mem) sort(name, info);
    return register_node(new_node);
}

sort * ast_manager::substitute(sort* s, unsigned n, sort * const * src, sort * const * dst) {
    for (unsigned i = 0; i < n; ++i) {
        if (s == src[i]) return dst[i];
    }

    vector<parameter> ps;
    bool change = false;
    sort_ref_vector sorts(*this);
    for (parameter const& p : s->parameters()) {
        if (p.is_ast()) {
            SASSERT(is_sort(p.get_ast()));
            change = true;
            sorts.push_back(substitute(to_sort(p.get_ast()), n, src, dst));
            ps.push_back(parameter(sorts.back()));
        }
        else {
            ps.push_back(p);
        }
    }
    if (!change) {
        return s;
    }
    decl_info dinfo(s->get_family_id(), s->get_decl_kind(), ps.size(), ps.data(), s->private_parameters());
    sort_info sinfo(dinfo, s->get_num_elements());
    return mk_sort(s->get_name(), &sinfo);
}


sort * ast_manager::mk_uninterpreted_sort(symbol const & name, unsigned num_parameters, parameter const * parameters) {
    user_sort_plugin * plugin = get_user_sort_plugin();
    decl_kind kind = plugin->register_name(name);
    return plugin->mk_sort(kind, num_parameters, parameters);
}

func_decl * ast_manager::mk_func_decl(symbol const & name, unsigned arity, sort * const * domain, sort * range,
                                      bool assoc, bool comm, bool inj) {
    func_decl_info info(null_family_id, null_decl_kind);
    info.set_associative(assoc);
    info.set_commutative(comm);
    info.set_injective(inj);
    return mk_func_decl(name, arity, domain, range, info);
}

func_decl * ast_manager::mk_func_decl(symbol const & name, unsigned arity, sort * const * domain, sort * range, func_decl_info * info) {
    SASSERT(arity == 1 || info == 0 || !info->is_injective());
    SASSERT(arity == 2 || info == 0 || !info->is_associative());
    SASSERT(arity == 2 || info == 0 || !info->is_commutative());
    unsigned sz               = func_decl::get_obj_size(arity);
    void * mem                = allocate_node(sz);
    func_decl * new_node = new (mem) func_decl(name, arity, domain, range, info);
    return register_node(new_node);
}

void ast_manager::check_sort(func_decl const * decl, unsigned num_args, expr * const * args) const {
    ast_manager& m = const_cast<ast_manager&>(*this);

    if (decl->is_associative()) {
        sort * expected = decl->get_domain(0);
        for (unsigned i = 0; i < num_args; i++) {
            sort * given = args[i]->get_sort();
            if (!compatible_sorts(expected, given)) {
                std::ostringstream buff;
                buff << "invalid function application for " << decl->get_name() << ", ";
                buff << "sort mismatch on argument at position " << (i+1) << ", ";
                buff << "expected " << mk_pp(expected, m) << " but given " << mk_pp(given, m);
                throw ast_exception(buff.str());
            }
        }
    }
    else {
        if (decl->get_arity() != num_args) {
            throw ast_exception("invalid function application, wrong number of arguments");
        }
        for (unsigned i = 0; i < num_args; i++) {
            sort * expected = decl->get_domain(i);
            sort * given    = args[i]->get_sort();
            if (!compatible_sorts(expected, given)) {
                std::ostringstream buff;
                buff << "invalid function application for " << decl->get_name() << ", ";
                buff << "sort mismatch on argument at position " << (i+1) << ", ";
                buff << "expected " << mk_pp(expected, m) << " but given " << mk_pp(given, m);
                throw ast_exception(buff.str());
            }
        }
    }
}

/**
   \brief Shallow sort checker.
   Return true if success.
   If n == 0, then fail.
   If n is an application, checks whether the arguments of n match the expected types.
*/
void ast_manager::check_sorts_core(ast const * n) const {
    if (!n) {
        throw ast_exception("expression is null");
    }
    if  (n->get_kind() != AST_APP)
        return; // nothing else to check...
    app const * a = to_app(n);
    func_decl* d = a->get_decl();
    check_sort(d, a->get_num_args(), a->get_args());
    if (a->get_num_args() == 2 &&
        !d->is_flat_associative() &&
        d->is_right_associative()) {
        check_sorts_core(a->get_arg(1));
    }
    if (a->get_num_args() == 2 &&
        !d->is_flat_associative() &&
        d->is_left_associative()) {
        check_sorts_core(a->get_arg(0));
    }
}

bool ast_manager::check_sorts(ast const * n) const {
    try {
        check_sorts_core(n);
        return true;
    }
    catch (ast_exception & ex) {
        warning_msg("%s", ex.msg());
        return false;
    }
}

bool ast_manager::compatible_sorts(sort * s1, sort * s2) const {
    if (s1 == s2)
        return true;
    if (m_int_real_coercions)
        return s1->get_family_id() == arith_family_id && s2->get_family_id() == arith_family_id;
    return false;
}

bool ast_manager::coercion_needed(func_decl * decl, unsigned num_args, expr * const * args) {
    SASSERT(m_int_real_coercions);
    if (decl->is_associative()) {
        sort * d = decl->get_domain(0);
        if (d->get_family_id() == arith_family_id) {
            for (unsigned i = 0; i < num_args; i++) {
                if (d != args[i]->get_sort())
                    return true;
            }
        }
    }
    else {
        if (decl->get_arity() != num_args) {
            // Invalid input: unexpected number of arguments for non-associative operator.
            // So, there is no point in coercing the input arguments.
            return false;
        }
        for (unsigned i = 0; i < num_args; i++) {
            sort * d = decl->get_domain(i);
            if (d->get_family_id() == arith_family_id && d != args[i]->get_sort())
                return true;
        }
    }
    return false;
}

expr* ast_manager::coerce_to(expr* e, sort* s) {
    sort* se = e->get_sort();
    if (s != se && s->get_family_id() == arith_family_id && se->get_family_id() == arith_family_id) {
        if (s->get_decl_kind() == REAL_SORT) {
            return mk_app(arith_family_id, OP_TO_REAL, e);
        }
        else {
            return mk_app(arith_family_id, OP_TO_INT, e);        
        }
    }
    else {
        return e;
    }
}

app * ast_manager::mk_app_core(func_decl * decl, unsigned num_args, expr * const * args) {
    app * r = nullptr;
    app * new_node = nullptr;
    unsigned sz = app::get_obj_size(num_args);
    void * mem = allocate_node(sz);
    try {
        if (m_int_real_coercions && coercion_needed(decl, num_args, args)) {
            expr_ref_buffer new_args(*this);
            for (unsigned i = 0; i < num_args; i++) {
                sort * d = decl->is_associative() ? decl->get_domain(0) : decl->get_domain(i);
                new_args.push_back(coerce_to(args[i], d));
            }
            check_args(decl, num_args, new_args.data());
            SASSERT(new_args.size() == num_args);
            new_node = new (mem)app(decl, num_args, new_args.data());
            r = register_node(new_node);
        }
        else {
            check_args(decl, num_args, args);
            new_node = new (mem)app(decl, num_args, args);
            r = register_node(new_node);
        }

        if (m_trace_stream && r == new_node) {
            if (is_proof(r)) {
                if (decl == mk_func_decl(basic_family_id, PR_UNDEF, 0, nullptr, 0, static_cast<expr * const *>(nullptr)))
                    return r;
                *m_trace_stream << "[mk-proof] #";
            } else {
                *m_trace_stream << "[mk-app] #";
            }
            *m_trace_stream << r->get_id() << " ";
            if (r->get_num_args() == 0 && r->get_decl()->get_name() == "int") {
                ast_ll_pp(*m_trace_stream, *this, r);
            }
            else if (is_label_lit(r)) {
                ast_ll_pp(*m_trace_stream, *this, r);
            }
            else {
                *m_trace_stream << r->get_decl()->get_name();
                for (unsigned i = 0; i < r->get_num_args(); i++)
                    *m_trace_stream << " #" << r->get_arg(i)->get_id();
                *m_trace_stream << "\n";
            }
        }
    }
    catch (...) {
        deallocate_node(static_cast<ast*>(mem), sz);
        throw;
    }

    return r;
}

void ast_manager::check_args(func_decl* f, unsigned n, expr* const* es) {
    for (unsigned i = 0; i < n; i++) {
        sort * actual_sort   = es[i]->get_sort();
        sort * expected_sort = f->is_associative() ? f->get_domain(0) : f->get_domain(i);
        if (expected_sort != actual_sort) {
            std::ostringstream buffer;
            buffer << "Sort mismatch at argument #" << (i+1)
                   << " for function " << mk_pp(f,*this)
                   << " supplied sort is "
                   << mk_pp(actual_sort, *this);
            throw ast_exception(buffer.str());
        }
    }
}


inline app * ast_manager::mk_app_core(func_decl * decl, expr * arg1, expr * arg2) {
    expr * args[2] = { arg1, arg2 };
    return mk_app_core(decl, 2, args);
}

app * ast_manager::mk_app(func_decl * decl, unsigned num_args, expr * const * args) {

    bool type_error =
        decl->get_arity() != num_args && !decl->is_right_associative() &&
        !decl->is_left_associative() && !decl->is_chainable();

    type_error |= (decl->get_arity() != num_args && num_args < 2 &&
                   decl->get_family_id() == basic_family_id && !decl->is_associative());

    if (type_error) {
        std::ostringstream buffer;
        buffer << "Wrong number of arguments (" << num_args
               << ") passed to function " << mk_pp(decl, *this);
        throw ast_exception(buffer.str());
    }
    app * r = nullptr;
    if (num_args == 1 && decl->is_chainable() && decl->get_arity() == 2) {
        r = mk_true();
    }
    else if (num_args > 2 && !decl->is_flat_associative()) {
        if (decl->is_right_associative()) {
            unsigned j = num_args - 1;
            r = mk_app_core(decl, args[j-1], args[j]);
            -- j;
            while (j > 0) {
                --j;
                r = mk_app_core(decl, args[j], r);
            }
        }
        else if (decl->is_left_associative()) {
            r = mk_app_core(decl, args[0], args[1]);
            for (unsigned i = 2; i < num_args; i++) {
                r = mk_app_core(decl, r, args[i]);
            }
        }
        else if (decl->is_chainable()) {
            TRACE("chainable", tout << "chainable...\n";);
            ptr_buffer<expr> new_args;
            for (unsigned i = 1; i < num_args; i++) {
                new_args.push_back(mk_app_core(decl, args[i-1], args[i]));
            }
            r = mk_and(new_args.size(), new_args.data());
        }
    }
    if (r == nullptr) {
        r = mk_app_core(decl, num_args, args);
    }
    SASSERT(r != 0);
    TRACE("app_ground", tout << "ground: " << r->is_ground() << " id: " << r->get_id() << "\n" << mk_ll_pp(r, *this) << "\n";);
    return r;
}



func_decl * ast_manager::mk_fresh_func_decl(symbol const & prefix, symbol const & suffix, unsigned arity,
                                            sort * const * domain, sort * range, bool skolem) {
    func_decl_info info(null_family_id, null_decl_kind);
    info.m_skolem = skolem;
    SASSERT(skolem == info.is_skolem());
    func_decl * d;
    if (prefix == symbol::null && suffix == symbol::null) {
        d = mk_func_decl(symbol(m_fresh_id), arity, domain, range, &info);
    }
    else {
        string_buffer<64> buffer;
        if (prefix == symbol::null)
            buffer << "sk";
        else
            buffer << prefix;
        buffer << "!";
        if (suffix != symbol::null)
            buffer << suffix << "!";
        buffer << m_fresh_id;
        d = mk_func_decl(symbol(buffer.c_str()), arity, domain, range, &info);
    }
    m_fresh_id++;
    SASSERT(d->get_info());
    SASSERT(skolem == d->is_skolem());
    return d;
}

sort * ast_manager::mk_fresh_sort(char const * prefix) {
    string_buffer<32> buffer;
    buffer << prefix << "!" << m_fresh_id;
    m_fresh_id++;
    return mk_uninterpreted_sort(symbol(buffer.c_str()));
}

symbol ast_manager::mk_fresh_var_name(char const * prefix) {
    string_buffer<32> buffer;
    buffer << (prefix ? prefix : "var") << "!" << m_fresh_id;
    m_fresh_id++;
    return symbol(buffer.c_str());
}

var * ast_manager::mk_var(unsigned idx, sort * s) {
    unsigned sz     = var::get_obj_size();
    void * mem      = allocate_node(sz);
    var * new_node  = new (mem) var(idx, s);
    var * r         = register_node(new_node);

    if (m_trace_stream && r == new_node) {
        *m_trace_stream << "[mk-var] #" << r->get_id() << " " << idx << "\n";
    }
    return r;
}

app * ast_manager::mk_label(bool pos, unsigned num_names, symbol const * names, expr * n) {
    SASSERT(num_names > 0);
    SASSERT(n->get_sort() == m_bool_sort);
    buffer<parameter> p;
    p.push_back(parameter(static_cast<int>(pos)));
    for (unsigned i = 0; i < num_names; i++)
        p.push_back(parameter(names[i]));
    return mk_app(label_family_id, OP_LABEL, p.size(), p.data(), 1, &n);
}

app * ast_manager::mk_label(bool pos, symbol const & name, expr * n) {
    return mk_label(pos, 1, &name, n);
}

bool ast_manager::is_label(expr const * n, bool & pos, buffer<symbol> & names) const {
    if (!is_app_of(n, label_family_id, OP_LABEL)) {
        return false;
    }
    func_decl const * decl = to_app(n)->get_decl();
    pos  = decl->get_parameter(0).get_int() != 0;
    for (unsigned i = 1; i < decl->get_num_parameters(); i++)
        names.push_back(decl->get_parameter(i).get_symbol());
    return true;
}

app * ast_manager::mk_label_lit(unsigned num_names, symbol const * names) {
    SASSERT(num_names > 0);
    buffer<parameter> p;
    for (unsigned i = 0; i < num_names; i++)
        p.push_back(parameter(names[i]));
    return mk_app(label_family_id, OP_LABEL_LIT, p.size(), p.data(), 0, nullptr);
}

app * ast_manager::mk_label_lit(symbol const & name) {
    return mk_label_lit(1, &name);
}

bool ast_manager::is_label_lit(expr const * n, buffer<symbol> & names) const {
    if (!is_app_of(n, label_family_id, OP_LABEL_LIT)) {
        return false;
    }
    func_decl const * decl = to_app(n)->get_decl();
    for (parameter const& p : decl->parameters()) 
        names.push_back(p.get_symbol());
    return true;
}

app * ast_manager::mk_pattern(unsigned num_exprs, app * const * exprs) {
    for (unsigned i = 0; i < num_exprs; ++i) {
        if (!is_app(exprs[i])) throw default_exception("patterns cannot be variables or quantifiers");
    }
    return mk_app(pattern_family_id, OP_PATTERN, 0, nullptr, num_exprs, (expr*const*)exprs);
}

bool ast_manager::is_pattern(expr const * n) const {
    if (!is_app_of(n, pattern_family_id, OP_PATTERN)) {
        return false;
    }
    for (unsigned i = 0; i < to_app(n)->get_num_args(); ++i) {
        if (!is_app(to_app(n)->get_arg(i))) {
            return false;
         }
    }
    return true;
}


bool ast_manager::is_pattern(expr const * n, ptr_vector<expr> &args) {
    if (!is_app_of(n, pattern_family_id, OP_PATTERN)) {
        return false;
    }
    for (unsigned i = 0; i < to_app(n)->get_num_args(); ++i) {
        expr *arg = to_app(n)->get_arg(i);
        if (!is_app(arg)) {
            return false;
        }
        args.push_back(arg);
    }
    return true;
}

static void trace_quant(std::ostream& strm, quantifier* q) {
    strm << (is_lambda(q) ? "[mk-lambda]" : "[mk-quant]")
         << " #" << q->get_id() << " " << q->get_qid() << " " << q->get_num_decls();
    for (unsigned i = 0; i < q->get_num_patterns(); ++i) {
        strm << " #" << q->get_pattern(i)->get_id();
    }
    strm << " #" << q->get_expr()->get_id() << "\n";
}


quantifier * ast_manager::mk_quantifier(quantifier_kind k, unsigned num_decls, sort * const * decl_sorts, symbol const * decl_names,
                                        expr * body, int weight , symbol const & qid, symbol const & skid,
                                        unsigned num_patterns, expr * const * patterns,
                                        unsigned num_no_patterns, expr * const * no_patterns) {
    SASSERT(body);
    SASSERT(num_decls > 0);
    if (num_patterns != 0 && num_no_patterns != 0)
        throw ast_exception("simultaneous patterns and no-patterns not supported");
    DEBUG_CODE({
            for (unsigned i = 0; i < num_patterns; ++i) {
                TRACE("ast", tout << i << " " << mk_pp(patterns[i], *this) << "\n";);
                SASSERT(is_pattern(patterns[i]));
            }});
    unsigned sz               = quantifier::get_obj_size(num_decls, num_patterns, num_no_patterns);
    void * mem                = allocate_node(sz);

    sort* s = nullptr;
    if (k == lambda_k) {
        array_util autil(*this);
        s = autil.mk_array_sort(num_decls, decl_sorts, body->get_sort());
    }
    else {
        s = mk_bool_sort();
    }

    quantifier * new_node = new (mem) quantifier(k, num_decls, decl_sorts, decl_names, body, s,
                                                 weight, qid, skid, num_patterns, patterns,
                                                 num_no_patterns, no_patterns);
    quantifier * r = register_node(new_node);

    if (m_trace_stream && r == new_node) {
        trace_quant(*m_trace_stream, r);
        *m_trace_stream << "[attach-var-names] #" << r->get_id();
        for (unsigned i = 0; i < num_decls; ++i) {
            *m_trace_stream << " (|" << decl_names[num_decls - i - 1].str() << "| ; |" << decl_sorts[num_decls - i -1]->get_name().str() << "|)";
        }
        *m_trace_stream << "\n";
    }

    return r;
}

quantifier * ast_manager::mk_lambda(unsigned num_decls, sort * const * decl_sorts, symbol const * decl_names, expr * body) {
    SASSERT(body);
    unsigned sz               = quantifier::get_obj_size(num_decls, 0, 0);
    void * mem                = allocate_node(sz);
    array_util autil(*this);
    sort* s = autil.mk_array_sort(num_decls, decl_sorts, body->get_sort());
    quantifier * new_node = new (mem) quantifier(num_decls, decl_sorts, decl_names, body, s);
    quantifier * r = register_node(new_node);
    if (m_trace_stream && r == new_node) {
        trace_quant(*m_trace_stream, r);
    }
    return r;
}


// Return true if the patterns of q are the given ones.
static bool same_patterns(quantifier * q, unsigned num_patterns, expr * const * patterns) {
    if (num_patterns != q->get_num_patterns())
        return false;
    for (unsigned i = 0; i < num_patterns; i++)
        if (q->get_pattern(i) != patterns[i])
            return false;
    return true;
}

// Return true if the no patterns of q are the given ones.
static bool same_no_patterns(quantifier * q, unsigned num_no_patterns, expr * const * no_patterns) {
    if (num_no_patterns != q->get_num_no_patterns())
        return false;
    for (unsigned i = 0; i < num_no_patterns; i++)
        if (q->get_no_pattern(i) != no_patterns[i])
            return false;
    return true;
}

quantifier * ast_manager::update_quantifier(quantifier * q, unsigned num_patterns, expr * const * patterns, expr * body) {
    if (q->get_expr() == body && same_patterns(q, num_patterns, patterns))
        return q;
    return mk_quantifier(q->get_kind(),
                         q->get_num_decls(),
                         q->get_decl_sorts(),
                         q->get_decl_names(),
                         body,
                         q->get_weight(),
                         q->get_qid(),
                         q->get_skid(),
                         num_patterns,
                         patterns,
                         num_patterns == 0 ? q->get_num_no_patterns() : 0,
                         num_patterns == 0 ? q->get_no_patterns() : nullptr);
}

quantifier * ast_manager::update_quantifier(quantifier * q, unsigned num_patterns, expr * const * patterns, unsigned num_no_patterns, expr * const * no_patterns, expr * body) {
    if (q->get_expr() == body && same_patterns(q, num_patterns, patterns) && same_no_patterns(q, num_no_patterns, no_patterns))
        return q;
    return mk_quantifier(q->get_kind(),
                         q->get_num_decls(),
                         q->get_decl_sorts(),
                         q->get_decl_names(),
                         body,
                         q->get_weight(),
                         q->get_qid(),
                         q->get_skid(),
                         num_patterns,
                         patterns,
                         num_no_patterns,
                         no_patterns);
}

quantifier * ast_manager::update_quantifier(quantifier * q, expr * body) {
    if (q->get_expr() == body)
        return q;
    return mk_quantifier(q->get_kind(),
                         q->get_num_decls(),
                         q->get_decl_sorts(),
                         q->get_decl_names(),
                         body,
                         q->get_weight(),
                         q->get_qid(),
                         q->get_skid(),
                         q->get_num_patterns(),
                         q->get_patterns(),
                         q->get_num_no_patterns(),
                         q->get_no_patterns());
}

quantifier * ast_manager::update_quantifier_weight(quantifier * q, int w) {
    if (q->get_weight() == w)
        return q;
    TRACE("update_quantifier_weight", tout << "#" << q->get_id() << " " << q->get_weight() << " -> " << w << "\n";);
    return mk_quantifier(q->get_kind(),
                         q->get_num_decls(),
                         q->get_decl_sorts(),
                         q->get_decl_names(),
                         q->get_expr(),
                         w,
                         q->get_qid(),
                         q->get_skid(),
                         q->get_num_patterns(),
                         q->get_patterns(),
                         q->get_num_no_patterns(),
                         q->get_no_patterns());
}

quantifier * ast_manager::update_quantifier(quantifier * q, quantifier_kind k, expr * body) {    
    if (q->get_expr() == body && q->get_kind() == k)
        return q;
    return mk_quantifier(k,
                         q->get_num_decls(),
                         q->get_decl_sorts(),
                         q->get_decl_names(),
                         body,
                         q->get_weight(),
                         q->get_qid(),
                         q->get_skid(),
                         q->get_num_patterns(),
                         q->get_patterns(),
                         q->get_num_no_patterns(),
                         q->get_no_patterns());
}

quantifier * ast_manager::update_quantifier(quantifier * q, quantifier_kind k, unsigned num_patterns, expr * const * patterns, expr * body) {
    if (q->get_expr() == body && q->get_kind() == k && same_patterns(q, num_patterns, patterns))
        return q;
    return mk_quantifier(k,
                         q->get_num_decls(),
                         q->get_decl_sorts(),
                         q->get_decl_names(),
                         body,
                         q->get_weight(),
                         q->get_qid(),
                         q->get_skid(),
                         num_patterns,
                         patterns,
                         num_patterns == 0 ? q->get_num_no_patterns() : 0,
                         num_patterns == 0 ? q->get_no_patterns() : nullptr);
}

app * ast_manager::mk_distinct(unsigned num_args, expr * const * args) {
    return mk_app(basic_family_id, OP_DISTINCT, num_args, args);
}

app * ast_manager::mk_distinct_expanded(unsigned num_args, expr * const * args) {
    if (num_args < 2)
        return mk_true();
    if (num_args == 2)
        return mk_not(mk_eq(args[0], args[1]));
    ptr_buffer<expr> new_args;
    for (unsigned i = 0; i < num_args - 1; i++) {
        expr * a1 = args[i];
        for (unsigned j = i + 1; j < num_args; j++) {
            expr * a2 = args[j];
            new_args.push_back(mk_not(mk_eq(a1, a2)));
        }
    }
    app * r = mk_and(new_args.size(), new_args.data());
    TRACE("distinct", tout << "expanded distinct:\n" << mk_pp(r, *this) << "\n";);
    return r;
}

// -----------------------------------
//
// expr_dependency
//
// -----------------------------------

expr_dependency * ast_manager::mk_leaf(expr * t) {
    if (t == nullptr)
        return nullptr;
    else
        return m_expr_dependency_manager.mk_leaf(t);
}

expr_dependency * ast_manager::mk_join(unsigned n, expr * const * ts) {
    expr_dependency * d = nullptr;
    for (unsigned i = 0; i < n; i++)
        d = mk_join(d, mk_leaf(ts[i]));
    return d;
}

void ast_manager::linearize(expr_dependency * d, ptr_vector<expr> & ts) {
    m_expr_dependency_manager.linearize(d, ts);
    remove_duplicates(ts);
}

// -----------------------------------
//
// Values
//
// -----------------------------------

app * ast_manager::mk_model_value(unsigned idx, sort * s) {
    parameter p[2] = { parameter(idx), parameter(s) };
    return mk_app(model_value_family_id, OP_MODEL_VALUE, 2, p, 0, static_cast<expr * const *>(nullptr));
}

expr * ast_manager::get_some_value(sort * s, some_value_proc * p) {
    flet<some_value_proc*> l(m_some_value_proc, p);
    return get_some_value(s);
}

expr * ast_manager::get_some_value(sort * s) {
    expr * v = nullptr;
    if (m_some_value_proc)
        v = (*m_some_value_proc)(s);
    if (v != nullptr)
        return v;
    family_id fid = s->get_family_id();
    if (fid != null_family_id) {
        decl_plugin * p = get_plugin(fid);
        if (p != nullptr) {
            v = p->get_some_value(s);
            if (v != nullptr)
                return v;
        }
    }
    return mk_model_value(0, s);
}

bool ast_manager::is_fully_interp(sort * s) const {
    if (is_uninterp(s))
        return false;
    family_id fid = s->get_family_id();
    SASSERT(fid != null_family_id);
    decl_plugin * p = get_plugin(fid);
    if (p != nullptr)
        return p->is_fully_interp(s);
    return false;
}

// -----------------------------------
//
// Proof generation
//
// -----------------------------------

proof * ast_manager::mk_proof(family_id fid, decl_kind k, unsigned num_args, expr * const * args) {
    if (proofs_disabled())
        return nullptr;
    return mk_app(fid, k, num_args, args);
}

proof * ast_manager::mk_proof(family_id fid, decl_kind k, expr * arg) {
    return mk_proof(fid, k, 1, &arg);
}

proof * ast_manager::mk_proof(family_id fid, decl_kind k, expr * arg1, expr * arg2) {
    expr * args[2] = { arg1, arg2 };
    return mk_proof(fid, k, 2, args);
}

proof * ast_manager::mk_proof(family_id fid, decl_kind k, expr * arg1, expr * arg2, expr * arg3) {
    expr * args[3] = { arg1, arg2, arg3 };
    return mk_proof(fid, k, 2, args);
}

proof * ast_manager::mk_true_proof() {
    expr * f = mk_true();
    return mk_proof(basic_family_id, PR_TRUE, f);
}

proof * ast_manager::mk_asserted(expr * f) {
    CTRACE("mk_asserted_bug", !is_bool(f), tout << mk_ismt2_pp(f, *this) << "\nsort: " << mk_ismt2_pp(f->get_sort(), *this) << "\n";);
    SASSERT(is_bool(f));
    return mk_proof(basic_family_id, PR_ASSERTED, f);
}

proof * ast_manager::mk_goal(expr * f) {
    SASSERT(is_bool(f));
    return mk_proof(basic_family_id, PR_GOAL, f);
}

proof * ast_manager::mk_modus_ponens(proof * p1, proof * p2) {
    if (!p2 || !p1) return p1;
    SASSERT(has_fact(p1));
    SASSERT(has_fact(p2));
    CTRACE("mk_modus_ponens", !(is_implies(get_fact(p2)) || is_eq(get_fact(p2)) || is_oeq(get_fact(p2))),
           tout << mk_ll_pp(p1, *this) << "\n";
           tout << mk_ll_pp(p2, *this) << "\n";);
    SASSERT(is_implies(get_fact(p2)) || is_eq(get_fact(p2)) || is_oeq(get_fact(p2)));
    CTRACE("mk_modus_ponens", to_app(get_fact(p2))->get_arg(0) != get_fact(p1),
           tout << mk_pp(get_fact(p1), *this) << "\n" << mk_pp(get_fact(p2), *this) << "\n";);
    SASSERT(!proofs_enabled() || to_app(get_fact(p2))->get_arg(0) == get_fact(p1));
    CTRACE("mk_modus_ponens", !is_ground(p2) && !has_quantifiers(p2), tout << "Non-ground: " << mk_pp(p2, *this) << "\n";);
    CTRACE("mk_modus_ponens", !is_ground(p1) && !has_quantifiers(p1), tout << "Non-ground: " << mk_pp(p1, *this) << "\n";);
    if (is_reflexivity(p2))
        return p1;
    expr * f = to_app(get_fact(p2))->get_arg(1);
    if (is_oeq(get_fact(p2)))
        return mk_app(basic_family_id, PR_MODUS_PONENS_OEQ, p1, p2, f);
    return mk_app(basic_family_id, PR_MODUS_PONENS, p1, p2, f);
}

proof * ast_manager::mk_reflexivity(expr * e) {
    return mk_app(basic_family_id, PR_REFLEXIVITY, mk_eq(e, e));
}

proof * ast_manager::mk_oeq_reflexivity(expr * e) {
    return mk_app(basic_family_id, PR_REFLEXIVITY, mk_oeq(e, e));
}

proof * ast_manager::mk_commutativity(app * f) {
    SASSERT(f->get_num_args() == 2);
    app * f_prime = mk_app(f->get_decl(), f->get_arg(1), f->get_arg(0));
    return mk_app(basic_family_id, PR_COMMUTATIVITY, mk_eq(f, f_prime));
}

/**
   \brief Given a proof of p, return a proof of (p <=> true)
*/
proof * ast_manager::mk_iff_true(proof * pr) {
    if (!pr) return pr;
    SASSERT(has_fact(pr));
    SASSERT(is_bool(get_fact(pr)));
    return mk_app(basic_family_id, PR_IFF_TRUE, pr, mk_iff(get_fact(pr), mk_true()));
}

/**
   \brief Given a proof of (not p), return a proof of (p <=> false)
*/
proof * ast_manager::mk_iff_false(proof * pr) {
    if (!pr) return pr;
    SASSERT(has_fact(pr));
    SASSERT(is_not(get_fact(pr)));
    expr * p = to_app(get_fact(pr))->get_arg(0);
    return mk_app(basic_family_id, PR_IFF_FALSE, pr, mk_iff(p, mk_false()));
}

proof * ast_manager::mk_symmetry(proof * p) {
    if (!p) return p;
    if (is_reflexivity(p))
        return p;
    if (is_symmetry(p))
        return get_parent(p, 0);
    SASSERT(has_fact(p));
    SASSERT(is_app(get_fact(p)));
    SASSERT(to_app(get_fact(p))->get_num_args() == 2);
    return mk_app(basic_family_id, PR_SYMMETRY, p,
                  mk_app(to_app(get_fact(p))->get_decl(), to_app(get_fact(p))->get_arg(1), to_app(get_fact(p))->get_arg(0)));
}

proof * ast_manager::mk_transitivity(proof * p1, proof * p2) {
    if (!p1)
        return p2;
    if (!p2)
        return p1;
    if (proofs_disabled())
        return nullptr;
    SASSERT(has_fact(p1));
    SASSERT(has_fact(p2));
    SASSERT(is_app(get_fact(p1)));
    SASSERT(is_app(get_fact(p2)));
    SASSERT(to_app(get_fact(p1))->get_num_args() == 2);
    SASSERT(to_app(get_fact(p2))->get_num_args() == 2);
    CTRACE("mk_transitivity", to_app(get_fact(p1))->get_decl() != to_app(get_fact(p2))->get_decl(),
           tout << mk_pp(get_fact(p1), *this) << "\n\n" << mk_pp(get_fact(p2), *this) << "\n";
           tout << mk_pp(to_app(get_fact(p1))->get_decl(), *this) << "\n";
           tout << mk_pp(to_app(get_fact(p2))->get_decl(), *this) << "\n";);
    SASSERT(to_app(get_fact(p1))->get_decl() == to_app(get_fact(p2))->get_decl() ||
            ( (is_eq(get_fact(p1)) || is_oeq(get_fact(p1))) &&
              (is_eq(get_fact(p2)) || is_oeq(get_fact(p2)))));
    CTRACE("mk_transitivity", to_app(get_fact(p1))->get_arg(1) != to_app(get_fact(p2))->get_arg(0),
           tout << mk_pp(get_fact(p1), *this) << "\n\n" << mk_pp(get_fact(p2), *this) << "\n";
           tout << p1->get_id() << ": " << mk_bounded_pp(p1, *this, 5) << "\n\n";
           tout << p2->get_id() << ": " << mk_bounded_pp(p2, *this, 5) << "\n\n";
    );
    SASSERT(to_app(get_fact(p1))->get_arg(1) == to_app(get_fact(p2))->get_arg(0));
    if (is_reflexivity(p1))
        return p2;
    if (is_reflexivity(p2))
        return p1;
    // OEQ is compatible with EQ for transitivity.
    func_decl* f = to_app(get_fact(p1))->get_decl();
    if (is_oeq(get_fact(p2))) f = to_app(get_fact(p2))->get_decl();
    return  mk_app(basic_family_id, PR_TRANSITIVITY, p1, p2, mk_app(f, to_app(get_fact(p1))->get_arg(0), to_app(get_fact(p2))->get_arg(1)));

}

proof * ast_manager::mk_transitivity(proof * p1, proof * p2, proof * p3) {
    return mk_transitivity(mk_transitivity(p1,p2), p3);
}

proof * ast_manager::mk_transitivity(proof * p1, proof * p2, proof * p3, proof * p4) {
    return mk_transitivity(mk_transitivity(mk_transitivity(p1,p2), p3), p4);
}

proof * ast_manager::mk_transitivity(unsigned num_proofs, proof * const * proofs) {
    SASSERT(num_proofs > 0);
    proof * r = proofs[0];
    for (unsigned i = 1; i < num_proofs; i++)
        r = mk_transitivity(r, proofs[i]);
    return r;
}

proof * ast_manager::mk_transitivity(unsigned num_proofs, proof * const * proofs, expr * n1, expr * n2) {
    if (num_proofs == 0)
        return nullptr;
    if (num_proofs == 1)
        return proofs[0];
    DEBUG_CODE({
        for (unsigned i = 0; i < num_proofs; i++) {
            SASSERT(proofs[i]);
            SASSERT(!is_reflexivity(proofs[i]));
        }
    });
    ptr_buffer<expr> args;
    args.append(num_proofs, (expr**) proofs);
    args.push_back(mk_eq(n1,n2));
    return mk_app(basic_family_id, PR_TRANSITIVITY_STAR, args.size(), args.data());
}

proof * ast_manager::mk_monotonicity(func_decl * R, app * f1, app * f2, unsigned num_proofs, proof * const * proofs) {
    SASSERT(f1->get_num_args() == f2->get_num_args());
    SASSERT(f1->get_decl() == f2->get_decl());
    ptr_buffer<expr> args;
    args.append(num_proofs, (expr**) proofs);
    args.push_back(mk_app(R, f1, f2));
    proof* p = mk_app(basic_family_id, PR_MONOTONICITY, args.size(), args.data());
    return p;
}

proof * ast_manager::mk_congruence(app * f1, app * f2, unsigned num_proofs, proof * const * proofs) {
    SASSERT(f1->get_sort() == f2->get_sort());
    sort * s    = f1->get_sort();
    sort * d[2] = { s, s };
    return mk_monotonicity(mk_func_decl(basic_family_id, get_eq_op(f1), 0, nullptr, 2, d), f1, f2, num_proofs, proofs);
}

proof * ast_manager::mk_oeq_congruence(app * f1, app * f2, unsigned num_proofs, proof * const * proofs) {
    SASSERT(f1->get_sort() == f2->get_sort());
    sort * s    = f1->get_sort();
    sort * d[2] = { s, s };
    return mk_monotonicity(mk_func_decl(basic_family_id, OP_OEQ, 0, nullptr, 2, d), f1, f2, num_proofs, proofs);
}


proof * ast_manager::mk_bind_proof(quantifier * q, proof * p) {
    expr* b = mk_lambda(q->get_num_decls(), q->get_decl_sorts(), q->get_decl_names(), p);
    return mk_app(basic_family_id, PR_BIND, b);
}

proof * ast_manager::mk_quant_intro(quantifier * q1, quantifier * q2, proof * p) {
    if (!p) return nullptr;
    SASSERT(q1->get_num_decls() == q2->get_num_decls());
    SASSERT(has_fact(p));
    SASSERT(is_eq(get_fact(p)) || is_lambda(get_fact(p)));
    return mk_app(basic_family_id, PR_QUANT_INTRO, p, mk_iff(q1, q2));
}

proof * ast_manager::mk_oeq_quant_intro(quantifier * q1, quantifier * q2, proof * p) {
    if (!p) return nullptr;
    SASSERT(q1->get_num_decls() == q2->get_num_decls());
    SASSERT(has_fact(p));
    SASSERT(is_oeq(get_fact(p)) || is_lambda(get_fact(p)));
    return mk_app(basic_family_id, PR_QUANT_INTRO, p, mk_oeq(q1, q2));
}

proof * ast_manager::mk_distributivity(expr * s, expr * r) {
    return mk_app(basic_family_id, PR_DISTRIBUTIVITY, mk_eq(s, r));
}

proof * ast_manager::mk_rewrite(expr * s, expr * t) {
    if (proofs_disabled())
        return nullptr;
    return mk_app(basic_family_id, PR_REWRITE, mk_eq(s, t));
}

proof * ast_manager::mk_oeq_rewrite(expr * s, expr * t) {
    if (proofs_disabled())
        return nullptr;
    return mk_app(basic_family_id, PR_REWRITE, mk_oeq(s, t));
}

proof * ast_manager::mk_rewrite_star(expr * s, expr * t, unsigned num_proofs, proof * const * proofs) {
    if (proofs_disabled())
        return nullptr;
    ptr_buffer<expr> args;
    args.append(num_proofs, (expr**) proofs);
    args.push_back(mk_eq(s, t));
    return mk_app(basic_family_id, PR_REWRITE_STAR, args.size(), args.data());
}

proof * ast_manager::mk_pull_quant(expr * e, quantifier * q) {
    if (proofs_disabled())
        return nullptr;
    return mk_app(basic_family_id, PR_PULL_QUANT, mk_iff(e, q));
}

proof * ast_manager::mk_push_quant(quantifier * q, expr * e) {
    if (proofs_disabled())
        return nullptr;
    return mk_app(basic_family_id, PR_PUSH_QUANT, mk_iff(q, e));
}

proof * ast_manager::mk_elim_unused_vars(quantifier * q, expr * e) {
    if (proofs_disabled())
        return nullptr;
    return mk_app(basic_family_id, PR_ELIM_UNUSED_VARS, mk_iff(q, e));
}

proof * ast_manager::mk_der(quantifier * q, expr * e) {
    if (proofs_disabled())
        return nullptr;
    return mk_app(basic_family_id, PR_DER, mk_iff(q, e));
}

proof * ast_manager::mk_quant_inst(expr * not_q_or_i, unsigned num_bind, expr* const* binding) {
    if (proofs_disabled())
        return nullptr;
    vector<parameter> params;
    for (unsigned i = 0; i < num_bind; ++i) {
        params.push_back(parameter(binding[i]));
        SASSERT(params.back().is_ast());
    }
    return mk_app(basic_family_id, PR_QUANT_INST, num_bind, params.data(), 1, & not_q_or_i);
}

bool ast_manager::is_quant_inst(expr const* e, expr*& not_q_or_i, ptr_vector<expr>& binding) const {
    if (is_quant_inst(e)) {
        not_q_or_i = to_app(e)->get_arg(0);
        func_decl* d = to_app(e)->get_decl();
        SASSERT(binding.empty());
        for (parameter const& p : d->parameters()) {
            binding.push_back(to_expr(p.get_ast()));
        }
        return true;
    }
    return false;
}

bool ast_manager::is_rewrite(expr const* e, expr*& r1, expr*& r2) const {
    return is_rewrite(e) && is_eq(to_app(e)->get_arg(0), r1, r2);
}

proof * ast_manager::mk_def_axiom(expr * ax) {
    if (proofs_disabled())
        return nullptr;
    return mk_app(basic_family_id, PR_DEF_AXIOM, ax);
}

proof * ast_manager::mk_unit_resolution(unsigned num_proofs, proof * const * proofs) {
    SASSERT(num_proofs >= 2);
    DEBUG_CODE(for (unsigned i = 0; i < num_proofs; i++) SASSERT(has_fact(proofs[i])););
    ptr_buffer<expr> args;
    expr * fact;
    expr * f1 = get_fact(proofs[0]);

    bool found_complement = false;
    for (unsigned i = 1; !found_complement && i < num_proofs; ++i) {
        expr* f2 = get_fact(proofs[i]);
        if (is_complement(f1, f2)) {
            args.push_back(proofs[0]);
            args.push_back(proofs[i]);
            args.push_back(mk_false());
            found_complement = true;
        }
    }
    if (!found_complement) {
        args.append(num_proofs, (expr**)proofs);
        CTRACE("mk_unit_resolution_bug", !is_or(f1), tout << mk_ll_pp(f1, *this) << "\n";
               for (unsigned i = 1; i < num_proofs; ++i)
                   tout << mk_pp(proofs[i], *this) << "\n";
               );
        SASSERT(is_or(f1));
        ptr_buffer<expr> new_lits;
        app const * cls   = to_app(f1);
        unsigned num_args = cls->get_num_args();
#ifdef Z3DEBUG
        bool_vector found;
#endif
        ast_mark mark;
        for (unsigned i = 0; i < num_args; i++) {
            bool found_complement = false;
            expr * lit = cls->get_arg(i);
            for (unsigned j = 1; j < num_proofs; j++) {
                expr const * _fact = get_fact(proofs[j]);
                if (is_complement(lit, _fact)) {
                    found_complement = true;
                    DEBUG_CODE(found.setx(j, true, false); continue;);
                    break;
                }
            }
            if (!found_complement) {
                if (!mark.is_marked(lit)) {
                    new_lits.push_back(lit);
                    mark.mark(lit, true);
                }
            }
        }
        DEBUG_CODE({
                for (unsigned i = 1; proofs_enabled() && i < num_proofs; i++) {
                CTRACE("mk_unit_resolution_bug", !found.get(i, false),
                       for (unsigned j = 0; j < num_proofs; j++) {
                           if (j == i) tout << "Index " << i << " was not found:\n";
                           tout << mk_ll_pp(get_fact(proofs[j]), *this);
                       });
                SASSERT(found.get(i, false));
            }
        });
        switch (new_lits.size()) {
        case 0:
            fact = mk_false();
            break;
        case 1:
            fact = new_lits[0];
            break;
        default:
            fact = mk_or(new_lits.size(), new_lits.data());
            break;
        }
        args.push_back(fact);
    }
    
    proof * pr = mk_app(basic_family_id, PR_UNIT_RESOLUTION, args.size(), args.data());
    TRACE("unit_resolution", tout << "unit_resolution generating fact\n" << mk_ll_pp(pr, *this););
    return pr;
}

proof * ast_manager::mk_unit_resolution(unsigned num_proofs, proof * const * proofs, expr * new_fact) {
    TRACE("unit_bug",
          for (unsigned i = 0; i < num_proofs; i++) tout << mk_pp(get_fact(proofs[i]), *this) << "\n";
          tout << "===>\n";
          tout << mk_pp(new_fact, *this) << "\n";);

    ptr_buffer<expr> args;
    args.append(num_proofs, (expr**) proofs);
    args.push_back(new_fact);
#ifdef Z3DEBUG
    expr * f1 = get_fact(proofs[0]);
    expr const * f2 = get_fact(proofs[1]);
    if (num_proofs == 2 && is_complement(f1, f2)) {
        SASSERT(is_false(new_fact));
    }
    else {
        SASSERT(is_or(f1));
        app * cls            = to_app(f1);
        unsigned cls_sz      = cls->get_num_args();
        CTRACE("unit_bug", !(num_proofs == cls_sz || (num_proofs == cls_sz + 1 && is_false(new_fact))),
          for (unsigned i = 0; i < num_proofs; i++) tout << mk_pp(get_fact(proofs[i]), *this) << "\n";
          tout << "===>\n";
          tout << mk_pp(new_fact, *this) << "\n";);
        //
        // typically: num_proofs == cls_sz || (num_proofs == cls_sz + 1 && is_false(new_fact))
        // but formula could have repeated literals that are merged in the clausal representation.
        //
        unsigned num_matches = 0, num_occ = 0;
        for (unsigned i = 0; i < cls_sz; i++) {
            expr * lit = cls->get_arg(i);
            unsigned j = 1;
            for (; j < num_proofs; j++) {
                if (is_complement(lit, get_fact(proofs[j]))) {
                    num_matches++;
                    break;
                }
            }
            if (j == num_proofs) {
                CTRACE("unit_bug", new_fact != lit, tout << mk_pp(f1, *this) << "\n" << mk_ll_pp(new_fact, *this) << "\n" << mk_ll_pp(lit, *this) << "\n";);
                SASSERT(new_fact == lit);
                ++num_occ;
            }
        }
        SASSERT(num_matches == cls_sz || num_matches == cls_sz - num_occ);
        SASSERT(num_matches != cls_sz || is_false(new_fact));
    }
#endif
    proof * pr = mk_app(basic_family_id, PR_UNIT_RESOLUTION, args.size(), args.data());
    TRACE("unit_resolution", tout << "unit_resolution using fact\n" << mk_ll_pp(pr, *this););
    return pr;
}

proof * ast_manager::mk_hypothesis(expr * h) {
    return mk_app(basic_family_id, PR_HYPOTHESIS, h);
}

proof * ast_manager::mk_lemma(proof * p, expr * lemma) {
    if (!p) return p;
    SASSERT(has_fact(p));
    CTRACE("mk_lemma", !is_false(get_fact(p)), tout << mk_ll_pp(p, *this) << "\n";);
    SASSERT(is_false(get_fact(p)));
    return mk_app(basic_family_id, PR_LEMMA, p, lemma);
}

proof * ast_manager::mk_def_intro(expr * new_def) {
    SASSERT(is_bool(new_def));
    return mk_proof(basic_family_id, PR_DEF_INTRO, new_def);
}

proof * ast_manager::mk_apply_defs(expr * n, expr * def, unsigned num_proofs, proof * const * proofs) {
    if (proofs_disabled())
        return nullptr;
    ptr_buffer<expr> args;
    args.append(num_proofs, (expr**) proofs);
    args.push_back(mk_oeq(n, def));
    return mk_app(basic_family_id, PR_APPLY_DEF, args.size(), args.data());
}

proof * ast_manager::mk_iff_oeq(proof * p) {
    if (!p) return p;

    SASSERT(has_fact(p));
    SASSERT(is_eq(get_fact(p)) || is_oeq(get_fact(p)));
    if (is_oeq(get_fact(p)))
        return p;

    app * iff = to_app(get_fact(p));
    expr * lhs = iff->get_arg(0);
    expr * rhs = iff->get_arg(1);
    return mk_app(basic_family_id, PR_IFF_OEQ, p, mk_oeq(lhs, rhs));
}

bool ast_manager::check_nnf_proof_parents(unsigned num_proofs, proof * const * proofs) const {
    for (unsigned i = 0; i < num_proofs; i++) {
        if (!has_fact(proofs[i]))
            return false;
        if (!is_oeq(get_fact(proofs[i])))
            return false;
    }
    return true;
}

proof * ast_manager::mk_nnf_pos(expr * s, expr * t, unsigned num_proofs, proof * const * proofs) {
    if (proofs_disabled())
        return nullptr;
    check_nnf_proof_parents(num_proofs, proofs);
    ptr_buffer<expr> args;
    args.append(num_proofs, (expr**) proofs);
    args.push_back(mk_oeq(s, t));
    return mk_app(basic_family_id, PR_NNF_POS, args.size(), args.data());
}

proof * ast_manager::mk_nnf_neg(expr * s, expr * t, unsigned num_proofs, proof * const * proofs) {
    if (proofs_disabled())
        return nullptr;
    check_nnf_proof_parents(num_proofs, proofs);
    ptr_buffer<expr> args;
    args.append(num_proofs, (expr**) proofs);
    args.push_back(mk_oeq(mk_not(s), t));
    return mk_app(basic_family_id, PR_NNF_NEG, args.size(), args.data());
}

proof * ast_manager::mk_skolemization(expr * q, expr * e) {
    if (proofs_disabled())
        return nullptr;
    SASSERT(is_bool(q));
    SASSERT(is_bool(e));
    return mk_app(basic_family_id, PR_SKOLEMIZE, mk_oeq(q, e));
}

proof * ast_manager::mk_and_elim(proof * p, unsigned i) {
    if (proofs_disabled())
        return nullptr;
    SASSERT(has_fact(p));
    SASSERT(is_and(get_fact(p)));
    CTRACE("mk_and_elim", i >= to_app(get_fact(p))->get_num_args(), tout << "i: " << i << "\n" << mk_pp(get_fact(p), *this) << "\n";);
    SASSERT(i < to_app(get_fact(p))->get_num_args());
    expr * f = to_app(get_fact(p))->get_arg(i);
    return mk_app(basic_family_id, PR_AND_ELIM, p, f);
}

proof * ast_manager::mk_not_or_elim(proof * p, unsigned i) {
    if (proofs_disabled())
        return nullptr;
    SASSERT(has_fact(p));
    SASSERT(is_not(get_fact(p)));
    SASSERT(is_or(to_app(get_fact(p))->get_arg(0)));
    app * or_app = to_app(to_app(get_fact(p))->get_arg(0));
    SASSERT(i < or_app->get_num_args());
    expr * c     = or_app->get_arg(i);
    expr * f;
    if (is_not(c))
        f = to_app(c)->get_arg(0);
    else
        f = mk_not(c);
    return mk_app(basic_family_id, PR_NOT_OR_ELIM, p, f);
}

proof* ast_manager::mk_clause_trail_elem(proof *pr, expr* e, decl_kind k) {
    ptr_buffer<expr> args;
    if (pr) args.push_back(pr);
    args.push_back(e);
    return mk_app(basic_family_id, k, 0, nullptr, args.size(), args.data());
}

proof * ast_manager::mk_assumption_add(proof* pr, expr* e) {
    return mk_clause_trail_elem(pr, e, PR_ASSUMPTION_ADD);
}

proof * ast_manager::mk_lemma_add(proof* pr, expr* e) {
    return mk_clause_trail_elem(pr, e, PR_LEMMA_ADD);
}

proof * ast_manager::mk_th_assumption_add(proof* pr, expr* e) {
    return mk_clause_trail_elem(pr, e, PR_TH_ASSUMPTION_ADD);
}

proof * ast_manager::mk_th_lemma_add(proof* pr, expr* e) {
    return mk_clause_trail_elem(pr, e, PR_TH_LEMMA_ADD);
}

proof * ast_manager::mk_redundant_del(expr* e) {
    return mk_clause_trail_elem(nullptr, e, PR_REDUNDANT_DEL);
}

proof * ast_manager::mk_clause_trail(unsigned n, proof* const* ps) {    
    ptr_buffer<expr> args;
    args.append(n, (expr**) ps);
    return mk_app(basic_family_id, PR_CLAUSE_TRAIL, 0, nullptr, args.size(), args.data());
}

proof * ast_manager::mk_th_lemma(
    family_id tid,
    expr * fact, unsigned num_proofs, proof * const * proofs,
    unsigned num_params, parameter const* params
    )
{
    if (proofs_disabled())
        return nullptr;

    ptr_buffer<expr> args;
    vector<parameter> parameters;
    parameters.push_back(parameter(get_family_name(tid)));
    for (unsigned i = 0; i < num_params; ++i) {
        parameters.push_back(params[i]);
    }
    args.append(num_proofs, (expr**) proofs);
    args.push_back(fact);
    return mk_app(basic_family_id, PR_TH_LEMMA, num_params+1, parameters.data(), args.size(), args.data());
}

proof* ast_manager::mk_hyper_resolve(unsigned num_premises, proof* const* premises, expr* concl,
                                     svector<std::pair<unsigned, unsigned> > const& positions,
                                     vector<expr_ref_vector> const& substs) {
    ptr_vector<expr> fmls;
    SASSERT(positions.size() + 1 == substs.size());
    for (unsigned i = 0; i < num_premises; ++i) {
        TRACE("hyper_res", tout << mk_pp(premises[i], *this) << "\n";);
        fmls.push_back(get_fact(premises[i]));
    }
    SASSERT(is_bool(concl));
    vector<parameter> params;
    for (unsigned i = 0; i < substs.size(); ++i) {
        expr_ref_vector const& vec = substs[i];
        for (unsigned j = 0; j < vec.size(); ++j) {
            params.push_back(parameter(vec[j]));
        }
        if (i + 1 < substs.size()) {
            params.push_back(parameter(positions[i].first));
            params.push_back(parameter(positions[i].second));
        }
    }
    TRACE("hyper_res",
          for (unsigned i = 0; i < params.size(); ++i) {
              params[i].display(tout); tout << "\n";
          });
    ptr_vector<sort> sorts;
    ptr_vector<expr> args;
    for (unsigned i = 0; i < num_premises; ++i) {
        sorts.push_back(mk_proof_sort());
        args.push_back(premises[i]);
    }
    sorts.push_back(mk_bool_sort());
    args.push_back(concl);
    app* result = mk_app(basic_family_id, PR_HYPER_RESOLVE, params.size(), params.data(), args.size(), args.data());
    SASSERT(result->get_family_id() == basic_family_id);
    SASSERT(result->get_decl_kind() == PR_HYPER_RESOLVE);
    return result;
}

bool ast_manager::is_hyper_resolve(
    proof* p,
    proof_ref_vector& premises,
    expr_ref& conclusion,
    svector<std::pair<unsigned, unsigned> > & positions,
    vector<expr_ref_vector> & substs) {
    if (!is_hyper_resolve(p)) {
        return false;
    }
    unsigned sz = p->get_num_args();
    SASSERT(sz > 0);
    for (unsigned i = 0; i + 1 < sz; ++i) {
        premises.push_back(to_app(p->get_arg(i)));
    }
    conclusion = p->get_arg(sz-1);
    func_decl* d = p->get_decl();
    unsigned num_p = d->get_num_parameters();
    parameter const* params = d->get_parameters();

    substs.push_back(expr_ref_vector(*this));
    for (unsigned i = 0; i < num_p; ++i) {
        if (params[i].is_int()) {
            SASSERT(i + 1 < num_p);
            SASSERT(params[i+1].is_int());
            unsigned x = static_cast<unsigned>(params[i].get_int());
            unsigned y = static_cast<unsigned>(params[i+1].get_int());
            positions.push_back(std::make_pair(x, y));
            substs.push_back(expr_ref_vector(*this));
            ++i;
        }
        else {
            SASSERT(params[i].is_ast());
            ast* a = params[i].get_ast();
            SASSERT(is_expr(a));
            substs.back().push_back(to_expr(a));
        }
    }

    return true;
}


// -----------------------------------
//
// ast_mark
//
// -----------------------------------

bool ast_mark::is_marked(ast * n) const {
    if (is_decl(n))
        return m_decl_marks.is_marked(to_decl(n));
    else
        return m_expr_marks.is_marked(to_expr(n));
}

void ast_mark::mark(ast * n, bool flag) {
    if (is_decl(n))
        return m_decl_marks.mark(to_decl(n), flag);
    else
        return m_expr_marks.mark(to_expr(n), flag);
}

void ast_mark::reset() {
    m_decl_marks.reset();
    m_expr_marks.reset();
}

// -----------------------------------
//
// scoped_mark
//
// -----------------------------------

void scoped_mark::mark(ast * n, bool flag) {
    SASSERT(flag);
    mark(n);
}

void scoped_mark::mark(ast * n) {
    if (!ast_mark::is_marked(n)) {
        m_stack.push_back(n);
        ast_mark::mark(n, true);
    }
}

void scoped_mark::reset() {
    ast_mark::reset();
    m_stack.reset();
    m_lim.reset();
}

void scoped_mark::push_scope() {
    m_lim.push_back(m_stack.size());
}

void scoped_mark::pop_scope() {
    unsigned new_size = m_stack.size();
    unsigned old_size = m_lim.back();
    for (unsigned i = old_size; i < new_size; ++i) {
        ast_mark::mark(m_stack[i].get(), false);
    }
    m_lim.pop_back();
    m_stack.resize(old_size);
}

void scoped_mark::pop_scope(unsigned num_scopes) {
    for (unsigned i = 0; i < num_scopes; ++i) {
        pop_scope();
    }
}

// Added by KLM for use in GDB

// show an expr_ref on stdout

void prexpr(expr_ref &e){
    std::cout << mk_pp(e.get(), e.get_manager()) << std::endl;
}

void ast_manager::show_id_gen(){
    std::cout << "id_gen: " << m_expr_id_gen.show_hash() << " " << m_decl_id_gen.show_hash() << "\n";
}
