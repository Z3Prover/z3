/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    datatype_decl_plugin.cpp

Abstract:

    <abstract>

Author:

    Leonardo de Moura (leonardo) 2008-01-10.

Revision History:

--*/
#include"datatype_decl_plugin.h"
#include"warning.h"
#include"ast_smt2_pp.h"

/**
   \brief Auxiliary class used to declare inductive datatypes.
*/
class accessor_decl {
    symbol    m_name;
    type_ref  m_type;
public:
    accessor_decl(const symbol & n, type_ref r):m_name(n), m_type(r) {}
    symbol const & get_name() const { return m_name; }
    type_ref const & get_type() const { return m_type; }
};

accessor_decl * mk_accessor_decl(symbol const & n, type_ref const & t) {
    return alloc(accessor_decl, n, t);
}

void del_accessor_decl(accessor_decl * d) {
    dealloc(d);
}

void del_accessor_decls(unsigned num, accessor_decl * const * as) {
    for (unsigned i = 0; i < num; i++)
        del_accessor_decl(as[i]);
}

/**
   \brief Auxiliary class used to declare inductive datatypes.
*/
class constructor_decl {
    symbol                    m_name;
    symbol                    m_recogniser_name;
    ptr_vector<accessor_decl> m_accessors;
public:
    constructor_decl(const symbol & n, const symbol & r, unsigned num_accessors, accessor_decl * const * accessors):
        m_name(n), m_recogniser_name(r), m_accessors(num_accessors, accessors) {}
    ~constructor_decl() {
        std::for_each(m_accessors.begin(), m_accessors.end(), delete_proc<accessor_decl>());
    }
    symbol const & get_name() const { return m_name; }
    symbol const & get_recognizer_name() const { return m_recogniser_name; }
    ptr_vector<accessor_decl> const & get_accessors() const { return m_accessors; }
};

constructor_decl * mk_constructor_decl(symbol const & n, symbol const & r, unsigned num_accessors, accessor_decl * const * accessors) {
    return alloc(constructor_decl, n, r, num_accessors, accessors);
}

void del_constructor_decl(constructor_decl * d) {
    dealloc(d);
}

void del_constructor_decls(unsigned num, constructor_decl * const * cs) {
    for (unsigned i = 0; i < num; i++)
        del_constructor_decl(cs[i]);
}

/**
   \brief Auxiliary class used to declare inductive datatypes.
*/
class datatype_decl {
    symbol                       m_name;
    ptr_vector<constructor_decl> m_constructors;
public:
    datatype_decl(const symbol & n, unsigned num_constructors, constructor_decl * const * constructors):
        m_name(n), m_constructors(num_constructors, constructors) {
    }
    ~datatype_decl() {
        std::for_each(m_constructors.begin(), m_constructors.end(), delete_proc<constructor_decl>());
    }
    symbol const & get_name() const { return m_name; }
    ptr_vector<constructor_decl> const & get_constructors() const { return m_constructors; }
};

datatype_decl * mk_datatype_decl(symbol const & n, unsigned num_constructors, constructor_decl * const * cs) {
    return alloc(datatype_decl, n, num_constructors, cs);
}

void del_datatype_decl(datatype_decl * d) {
    dealloc(d);
}

void del_datatype_decls(unsigned num, datatype_decl * const * ds) {
    for (unsigned i = 0; i < num; i++)
        del_datatype_decl(ds[i]);
}

typedef buffer<bool, false, 256> bool_buffer;

struct invalid_datatype {};

static parameter const & read(unsigned num_parameters, parameter const * parameters, unsigned idx, bool_buffer & read_pos) {
    if (idx >= num_parameters) {
        throw invalid_datatype();
    }
    if (idx >= read_pos.size()) {
        read_pos.resize(idx+1, false);
    }
    read_pos[idx] = true;
    return parameters[idx];
}

static int read_int(unsigned num_parameters, parameter const * parameters, unsigned idx, bool_buffer & read_pos) {
    const parameter & r = read(num_parameters, parameters, idx, read_pos);
    if (!r.is_int()) {
        throw invalid_datatype();
    }
    return r.get_int();
}

static symbol read_symbol(unsigned num_parameters, parameter const * parameters, unsigned idx, bool_buffer & read_pos) {
    parameter const & r = read(num_parameters, parameters, idx, read_pos);
    if (!r.is_symbol()) {
        throw invalid_datatype();
    }
    return r.get_symbol();
}

enum status {
    WHITE,
    GRAY,
    BLACK
};

/**
   \brief Return true if the inductive datatype is recursive.
   Pre-condition: The given argument constains the parameters of an inductive datatype.
*/
static bool is_recursive_datatype(parameter const * parameters) {
    unsigned num_types          = parameters[0].get_int();
    unsigned top_tid            = parameters[1].get_int();
    buffer<status>    already_found(num_types, WHITE);
    buffer<unsigned>  todo;
    todo.push_back(top_tid);
    while (!todo.empty()) {
        unsigned tid = todo.back();
        if (already_found[tid] == BLACK) {
            todo.pop_back();
            continue;
        }
        already_found[tid] = GRAY;
        unsigned o                 = parameters[2 + 2*tid + 1].get_int(); // constructor offset
        unsigned num_constructors  = parameters[o].get_int();            
        bool     can_process       = true;
        for (unsigned s = 1; s <= num_constructors; s++) {
            unsigned k_i           = parameters[o + s].get_int();
            unsigned num_accessors = parameters[k_i + 2].get_int();
            for (unsigned r = 0; r < num_accessors; r++) {
                parameter const & a_type = parameters[k_i + 4 + 2*r];
                if (a_type.is_int()) {
                    unsigned tid_prime = a_type.get_int();
                    switch (already_found[tid_prime]) {
                    case WHITE:
                        todo.push_back(tid_prime);
                        can_process = false;
                        break;
                    case GRAY:
                        // type is recursive
                        return true;
                    case BLACK:
                        break;
                    }
                }
            }
        }
        if (can_process) {
            already_found[tid] = BLACK;
            todo.pop_back();
        }
    }
    return false;
}

/**
   \brief Return the size of the inductive datatype.
   Pre-condition: The given argument constains the parameters of an inductive datatype.
*/
static sort_size get_datatype_size(parameter const * parameters) {
    unsigned num_types          = parameters[0].get_int();
    unsigned top_tid            = parameters[1].get_int();
    buffer<sort_size> szs(num_types, sort_size());
    buffer<status>    already_found(num_types, WHITE);
    buffer<unsigned>  todo;
    todo.push_back(top_tid);
    while (!todo.empty()) {
        unsigned tid  = todo.back();
        if (already_found[tid] == BLACK) {
            todo.pop_back();
            continue;
        }
        already_found[tid] = GRAY;
        unsigned o                 = parameters[2 + 2*tid + 1].get_int(); // constructor offset
        unsigned num_constructors  = parameters[o].get_int();            
        bool     is_very_big       = false;
        bool     can_process       = true;
        for (unsigned s = 1; s <= num_constructors; s++) {
            unsigned k_i           = parameters[o+s].get_int();
            unsigned num_accessors = parameters[k_i+2].get_int();
            for (unsigned r = 0; r < num_accessors; r++) {
                parameter const & a_type = parameters[k_i+4 + 2*r];
                if (a_type.is_int()) {
                    int tid_prime = a_type.get_int();
                    switch (already_found[tid_prime]) {
                    case WHITE: 
                        todo.push_back(tid_prime);
                        can_process = false;
                        break;
                    case GRAY:
                        // type is recursive
                        return sort_size();
                    case BLACK:
                        break;
                    }
                }
                else { 
                    SASSERT(a_type.is_ast());
                    sort * ty = to_sort(a_type.get_ast());
                    if (ty->is_infinite()) {
                        // type is infinite
                        return sort_size();
                    }
                    else if (ty->is_very_big()) {
                        is_very_big = true;
                    }
                }
            }
        }
        if (can_process) {
            todo.pop_back();
            already_found[tid] = BLACK;
            if (is_very_big) {
                szs[tid] = sort_size::mk_very_big();
            }
            else {
                // the type is not infinite nor the number of elements is infinite...
                // computing the number of elements
                rational num;
                for (unsigned s = 1; s <= num_constructors; s++) {
                    unsigned k_i           = parameters[o+s].get_int();
                    unsigned num_accessors = parameters[k_i+2].get_int();
                    rational c_num(1); 
                    for (unsigned r = 0; r < num_accessors; r++) {
                        parameter const & a_type = parameters[k_i+4 + 2*r];
                        if (a_type.is_int()) {
                            int tid_prime = a_type.get_int();
                            SASSERT(!szs[tid_prime].is_infinite() && !szs[tid_prime].is_very_big());
                            c_num *= rational(szs[tid_prime].size(),rational::ui64());
                        }
                        else {
                            SASSERT(a_type.is_ast());
                            sort * ty = to_sort(a_type.get_ast());
                            SASSERT(!ty->is_infinite() && !ty->is_very_big());
                            c_num *= rational(ty->get_num_elements().size(), rational::ui64());
                        }
                    }
                    num += c_num;
                }
                szs[tid] = sort_size(num);
            }
        }
    }
    return szs[top_tid];
}

/**
   \brief Return true if the inductive datatype is well-founded.
   Pre-condition: The given argument constains the parameters of an inductive datatype.
*/
static bool is_well_founded(parameter const * parameters) {
    unsigned num_types        = parameters[0].get_int();
    buffer<bool> well_founded(num_types, false);
    unsigned num_well_founded = 0;
    bool changed;
    do {
        changed = false;
        for (unsigned tid = 0; tid < num_types; tid++) {
            if (!well_founded[tid]) {
                unsigned o                 = parameters[2 + 2*tid + 1].get_int(); // constructor offset
                unsigned num_constructors  = parameters[o].get_int();
                for (unsigned s = 1; s <= num_constructors; s++) {
                    unsigned k_i           = parameters[o + s].get_int();
                    unsigned num_accessors = parameters[k_i + 2].get_int();
                    unsigned r = 0;
                    for (; r < num_accessors; r++) {
                        parameter const & a_type = parameters[k_i + 4 + 2*r];
                        if (a_type.is_int() && !well_founded[a_type.get_int()]) {
                            break;
                        }
                    }
                    if (r ==  num_accessors) {
                        changed = true;
                        well_founded[tid] = true;
                        num_well_founded++;
                        break;
                    }
                }
            }
        }
    } while(changed && num_well_founded < num_types);
    unsigned tid = parameters[1].get_int();
    return well_founded[tid];
}

datatype_decl_plugin::~datatype_decl_plugin() {
    SASSERT(m_util.get() == 0);
}

void datatype_decl_plugin::finalize() {
    m_util = 0; // force deletion
}

datatype_util & datatype_decl_plugin::get_util() const {
    SASSERT(m_manager);
    if (m_util.get() == 0) {
        m_util = alloc(datatype_util, *m_manager);
    }
    return *(m_util.get());
}

        
sort * datatype_decl_plugin::mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) {
    try {
        if (k != DATATYPE_SORT) {
            throw invalid_datatype();
        }
        buffer<bool, false, 256> found;
        unsigned num_types = read_int(num_parameters, parameters, 0, found);
        if (num_types == 0) {
            throw invalid_datatype();
        }
        unsigned tid       = read_int(num_parameters, parameters, 1, found);
        for (unsigned j = 0; j < num_types; j++) {
            read_symbol(num_parameters, parameters, 2 + 2*j, found); // type name
            unsigned       o          = read_int(num_parameters, parameters, 2 + 2*j + 1, found);
            unsigned num_constructors = read_int(num_parameters, parameters, o, found);
            if (num_constructors == 0) {
                throw invalid_datatype();
            }
            for (unsigned s = 1; s <= num_constructors; s++) {
                unsigned k_i            = read_int(num_parameters, parameters, o + s, found);
                read_symbol(num_parameters, parameters, k_i, found);      // constructor name
                read_symbol(num_parameters, parameters, k_i + 1, found);  // recognizer name
                unsigned num_accessors  = read_int(num_parameters, parameters, k_i + 2, found); 
                unsigned first_accessor = k_i+3;
                for (unsigned r = 0; r < num_accessors; r++) {
                    read_symbol(num_parameters, parameters, first_accessor + 2*r, found); // accessor name
                    parameter const & a_type = read(num_parameters, parameters, first_accessor + 2*r + 1, found); // accessort type
                    if (!a_type.is_int() && !a_type.is_ast()) {
                        throw invalid_datatype();
                        if (a_type.is_ast() && !is_sort(a_type.get_ast())) {
                            throw invalid_datatype();
                        }
                    }
                }
            }
        }
        // check if there is no garbage
        if (found.size() != num_parameters || std::find(found.begin(), found.end(), false) != found.end()) {
            throw invalid_datatype();
        }

        if (!is_well_founded(parameters)) {
            m_manager->raise_exception("datatype is not well-founded");
            return 0;
        }
        
        // compute datatype size
        sort_size ts = get_datatype_size(parameters);
        symbol const & tname = parameters[2+2*tid].get_symbol();
        return m_manager->mk_sort(tname,
                                  sort_info(m_family_id, k, ts, num_parameters, parameters, true));
    }
    catch (invalid_datatype) {
        m_manager->raise_exception("invalid datatype");
        return 0;
    }
}

static sort * get_other_datatype(ast_manager & m, family_id datatype_fid, sort * source_datatype, unsigned tid) {
    SASSERT(source_datatype->get_family_id() == datatype_fid);
    SASSERT(source_datatype->get_decl_kind() == DATATYPE_SORT);
    if (tid == static_cast<unsigned>(source_datatype->get_parameter(1).get_int())) {
        return source_datatype;
    }
    buffer<parameter> p;
    unsigned n = source_datatype->get_num_parameters();
    for (unsigned i = 0; i < n; i++) {
        p.push_back(source_datatype->get_parameter(i));
    }
    p[1] = parameter(tid);
    return m.mk_sort(datatype_fid, DATATYPE_SORT, n, p.c_ptr());
}

static sort * get_type(ast_manager & m, family_id datatype_fid, sort * source_datatype, parameter const & p) {
    SASSERT(p.is_ast() || p.is_int());
    if (p.is_ast()) {
        return to_sort(p.get_ast());
    }
    else {
        return get_other_datatype(m, datatype_fid, source_datatype, p.get_int());
    }
}

func_decl * datatype_decl_plugin::mk_update_field(
    unsigned num_parameters, parameter const * parameters, 
    unsigned arity, sort * const * domain, sort * range) {
    decl_kind k = OP_DT_UPDATE_FIELD;
    ast_manager& m = *m_manager;

    if (num_parameters != 1 || !parameters[0].is_ast()) {
        m.raise_exception("invalid parameters for datatype field update");
        return 0;
    }
    if (arity != 2) {
        m.raise_exception("invalid number of arguments for datatype field update");
        return 0;
    }
    func_decl* acc = 0;
    if (is_func_decl(parameters[0].get_ast())) {
        acc = to_func_decl(parameters[0].get_ast());
    }
    if (acc && !get_util().is_accessor(acc)) {
        acc = 0;
    }
    if (!acc) {
        m.raise_exception("datatype field update requires a datatype accessor as the second argument");
        return 0;
    }
    sort* dom = acc->get_domain(0);
    sort* rng = acc->get_range();
    if (dom != domain[0]) {
        m.raise_exception("first argument to field update should be a data-type");
        return 0;
    }
    if (rng != domain[1]) {
        std::ostringstream buffer;
        buffer << "second argument to field update should be " << mk_ismt2_pp(rng, m) 
               << " instead of " << mk_ismt2_pp(domain[1], m);
        m.raise_exception(buffer.str().c_str());
        return 0;
    }
    range = domain[0];
    func_decl_info info(m_family_id, k, num_parameters, parameters);
    return m.mk_func_decl(symbol("update-field"), arity, domain, range, info);
}

func_decl * datatype_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters, 
                                             unsigned arity, sort * const * domain, sort * range) {

    if (k == OP_DT_UPDATE_FIELD) {
        return mk_update_field(num_parameters, parameters, arity, domain, range);
    }
    if (num_parameters < 2 || !parameters[0].is_ast() || !is_sort(parameters[0].get_ast())) {
        m_manager->raise_exception("invalid parameters for datatype operator");
        return 0;
    }
    sort * datatype = to_sort(parameters[0].get_ast());
    if (datatype->get_family_id() != m_family_id ||
        datatype->get_decl_kind() != DATATYPE_SORT) {
        m_manager->raise_exception("invalid parameters for datatype operator");
        return 0;
    }
    for (unsigned i = 1; i < num_parameters; i++) {
        if (!parameters[i].is_int()) {
            m_manager->raise_exception("invalid parameters for datatype operator");
            return 0;
        }
    }
    unsigned c_idx            = parameters[1].get_int();
    unsigned tid              = datatype->get_parameter(1).get_int();
    unsigned o                = datatype->get_parameter(2 + 2 * tid + 1).get_int();
    unsigned num_constructors = datatype->get_parameter(o).get_int();
    if (c_idx >= num_constructors) {
        m_manager->raise_exception("invalid parameters for datatype operator");
        return 0;
    }
    unsigned k_i              = datatype->get_parameter(o + 1 + c_idx).get_int();

    switch (k) {
    case OP_DT_CONSTRUCTOR:
        if (num_parameters != 2) { 
            m_manager->raise_exception("invalid parameters for datatype constructor");
            return 0;
        }
        else {


            symbol   c_name           = datatype->get_parameter(k_i).get_symbol();
            unsigned num_accessors    = datatype->get_parameter(k_i + 2).get_int();
            if (num_accessors != arity) {
                m_manager->raise_exception("invalid domain size for datatype constructor");
                return 0;
            }

            //
            // the reference count to domain could be 0.
            // we need to ensure that creating a temporary
            // copy of the same type causes a free.
            // 
            sort_ref_vector domain_check(*m_manager);

            for (unsigned r = 0; r < num_accessors; r++) {
                sort_ref ty(*m_manager);
                ty = get_type(*m_manager, m_family_id, datatype, datatype->get_parameter(k_i + 4 + 2*r));
                domain_check.push_back(ty);
                if (ty != domain[r]) {
                    m_manager->raise_exception("invalid domain for datatype constructor");
                    return 0;
                }

            }
            func_decl_info info(m_family_id, k, num_parameters, parameters);
            info.m_private_parameters = true;
            SASSERT(info.private_parameters());
            return m_manager->mk_func_decl(c_name, arity, domain, datatype, info);
        }
    case OP_DT_RECOGNISER:
        if (num_parameters != 2 || arity != 1 || domain[0] != datatype) { 
            m_manager->raise_exception("invalid parameters for datatype recogniser");
            return 0;
        }
        else {
            symbol   r_name = datatype->get_parameter(k_i + 1).get_symbol();
            sort *    b     = m_manager->mk_bool_sort();
            func_decl_info info(m_family_id, k, num_parameters, parameters);
            info.m_private_parameters = true;
            SASSERT(info.private_parameters());
            return m_manager->mk_func_decl(r_name, arity, domain, b, info);
        }
    case OP_DT_ACCESSOR:
        if (num_parameters != 3 || arity != 1 || domain[0] != datatype) { 
            m_manager->raise_exception("invalid parameters for datatype accessor");
            return 0;
        }
        else {
            unsigned a_idx            = parameters[2].get_int();
            unsigned num_accessors    = datatype->get_parameter(k_i + 2).get_int();
            if (a_idx >= num_accessors) {
                m_manager->raise_exception("invalid datatype accessor");
                return 0;
            }
            symbol a_name         = datatype->get_parameter(k_i + 3 + 2*a_idx).get_symbol();
            sort * a_type         = get_type(*m_manager, m_family_id, datatype, datatype->get_parameter(k_i + 4 + 2*a_idx));
            func_decl_info info(m_family_id, k, num_parameters, parameters);
            info.m_private_parameters = true;
            SASSERT(info.private_parameters());
            return m_manager->mk_func_decl(a_name, arity, domain, a_type, info);
        }
        break;
    case OP_DT_UPDATE_FIELD: 
        UNREACHABLE();
        return 0;
    default:
        m_manager->raise_exception("invalid datatype operator kind");
        return 0;
    }
}

bool datatype_decl_plugin::mk_datatypes(unsigned num_datatypes, datatype_decl * const * datatypes, sort_ref_vector & new_types) {
    buffer<parameter> p;
    p.push_back(parameter(num_datatypes));
    p.push_back(parameter(-1));
    for (unsigned i = 0; i < num_datatypes; i++) {
        p.push_back(parameter(datatypes[i]->get_name()));
        p.push_back(parameter(-1)); // offset is unknown at this point
    }
    for (unsigned i = 0; i < num_datatypes; i++) {
        p[3+2*i] = parameter(p.size()); // save offset to constructor table
        ptr_vector<constructor_decl> const & constructors = datatypes[i]->get_constructors();
        unsigned num_constructors = constructors.size();
        p.push_back(parameter(num_constructors));
        for (unsigned j = 0; j < num_constructors; j++) {
            p.push_back(parameter(-1)); // offset is unknown at this point
        }
    }
    for (unsigned i = 0; i < num_datatypes; i++) {
        unsigned       o          = p[3+2*i].get_int();
        ptr_vector<constructor_decl> const & constructors = datatypes[i]->get_constructors();
        unsigned num_constructors = constructors.size();
        for (unsigned j = 0; j < num_constructors; j++) {
            p[o+1+j] = parameter(p.size()); // save offset to constructor definition
            constructor_decl * c  = constructors[j];
            p.push_back(parameter(c->get_name()));
            p.push_back(parameter(c->get_recognizer_name()));
            ptr_vector<accessor_decl> const & accessors = c->get_accessors();
            unsigned num_accessors = accessors.size();
            p.push_back(parameter(num_accessors));
            for (unsigned k = 0; k < num_accessors; k++) {
                accessor_decl * a  = accessors[k];
                p.push_back(parameter(a->get_name()));
                type_ref const & ty = a->get_type(); 
                if (ty.is_idx()) {
                    if (static_cast<unsigned>(ty.get_idx()) >= num_datatypes) {
                        TRACE("datatype", tout << "Index out of bounds: " << ty.get_idx() << "\n";);
                        return false;
                    }
                    p.push_back(parameter(ty.get_idx()));
                }
                else {
                    p.push_back(parameter(ty.get_sort()));
                }
            }
        }
    }
    for (unsigned i = 0; i < num_datatypes; i++) {
        p[1] = parameter(i);
        TRACE("datatype", tout << "new datatype parameters:\n";
              for (unsigned j = 0; j < p.size(); j++) {
                  tout << "p[" << j << "] -> " << p[j] << "\n";
              });
        sort * ty = mk_sort(DATATYPE_SORT, p.size(), p.c_ptr());
        if (ty == 0) {
            TRACE("datatype", tout << "Failed to create datatype sort from parameters\n";);
            return false;
        }
        new_types.push_back(ty);
    }
    return true;
}

expr * datatype_decl_plugin::get_some_value(sort * s) {
    SASSERT(s->is_sort_of(m_family_id, DATATYPE_SORT));
    datatype_util & util = get_util();
    func_decl * c = util.get_non_rec_constructor(s);
    ptr_buffer<expr> args;
    for (unsigned i = 0; i < c->get_arity(); i++) {
        args.push_back(m_manager->get_some_value(c->get_domain(i)));
    }
    return m_manager->mk_app(c, args.size(), args.c_ptr());
}

bool datatype_decl_plugin::is_fully_interp(sort const * s) const {
    SASSERT(s->is_sort_of(m_family_id, DATATYPE_SORT));
    parameter const * parameters = s->get_parameters();
    unsigned num_types        = parameters[0].get_int();
    for (unsigned tid = 0; tid < num_types; tid++) {
        unsigned o                 = parameters[2 + 2*tid + 1].get_int(); // constructor offset
        unsigned num_constructors  = parameters[o].get_int();
        for (unsigned si = 1; si <= num_constructors; si++) {
            unsigned k_i           = parameters[o + si].get_int();
            unsigned num_accessors = parameters[k_i + 2].get_int();
            unsigned r = 0;
            for (; r < num_accessors; r++) {
                parameter const & a_type = parameters[k_i + 4 + 2*r];
                if (a_type.is_int())
                    continue;
                SASSERT(a_type.is_ast());
                sort * arg_s = to_sort(a_type.get_ast());
                if (!m_manager->is_fully_interp(arg_s))
                    return false;
            }
        }
    }
    return true;
}

bool datatype_decl_plugin::is_value_visit(expr * arg, ptr_buffer<app> & todo) const {
    if (!is_app(arg))
        return false;
    family_id fid = to_app(arg)->get_family_id();
    if (fid == m_family_id) {
        if (!get_util().is_constructor(to_app(arg)))
            return false;
        if (to_app(arg)->get_num_args() == 0)
            return true;
        todo.push_back(to_app(arg));
        return true;
    }
    else {
        return m_manager->is_value(arg);
    }
}

bool datatype_decl_plugin::is_value(app * e) const {
    TRACE("dt_is_value", tout << "checking\n" << mk_ismt2_pp(e, *m_manager) << "\n";);
    if (!get_util().is_constructor(e))
        return false;
    if (e->get_num_args() == 0)
        return true;
    // REMARK: if the following check is too expensive, we should
    // cache the values in the datatype_decl_plugin.
    ptr_buffer<app> todo;
    // potentially expensive check for common sub-expressions.
    for (unsigned i = 0; i < e->get_num_args(); i++) {
        if (!is_value_visit(e->get_arg(i), todo)) {
            TRACE("dt_is_value", tout << "not-value:\n" << mk_ismt2_pp(e->get_arg(i), *m_manager) << "\n";);
            return false;
        }
    }
    while (!todo.empty()) {
        app * curr = todo.back();
        SASSERT(get_util().is_constructor(curr));
        todo.pop_back();
        for (unsigned i = 0; i < curr->get_num_args(); i++) {
            if (!is_value_visit(curr->get_arg(i), todo)) {
                TRACE("dt_is_value", tout << "not-value:\n" << mk_ismt2_pp(curr->get_arg(i), *m_manager) << "\n";);
                return false;
            }
        }
    }
    return true;
}

void datatype_decl_plugin::get_op_names(svector<builtin_name> & op_names, symbol const & logic) {
    if (logic == symbol::null) {
        op_names.push_back(builtin_name("update-field", OP_DT_UPDATE_FIELD));
    }
}


datatype_util::datatype_util(ast_manager & m):
    m_manager(m),
    m_family_id(m.mk_family_id("datatype")),
    m_asts(m),
    m_start(0) {
}

datatype_util::~datatype_util() {
    std::for_each(m_vectors.begin(), m_vectors.end(), delete_proc<ptr_vector<func_decl> >());
}

func_decl * datatype_util::get_constructor(sort * ty, unsigned c_id) {
    unsigned tid           = ty->get_parameter(1).get_int();
    unsigned o             = ty->get_parameter(3 + 2*tid).get_int();
    unsigned k_i           = ty->get_parameter(o + c_id + 1).get_int();
    unsigned num_accessors = ty->get_parameter(k_i + 2).get_int();
    parameter p[2]         = { parameter(ty), parameter(c_id) };
    ptr_buffer<sort> domain;
    for (unsigned r = 0; r < num_accessors; r++) {
        domain.push_back(get_type(m_manager, m_family_id, ty, ty->get_parameter(k_i + 4 + 2*r)));
    }
    func_decl * d = m_manager.mk_func_decl(m_family_id, OP_DT_CONSTRUCTOR, 2, p, domain.size(), domain.c_ptr());
    SASSERT(d);
    return d;
}

ptr_vector<func_decl> const * datatype_util::get_datatype_constructors(sort * ty) {
    SASSERT(is_datatype(ty));
    ptr_vector<func_decl> * r = 0;
    if (m_datatype2constructors.find(ty, r))
        return r;
    r = alloc(ptr_vector<func_decl>);
    m_asts.push_back(ty);
    m_vectors.push_back(r);
    m_datatype2constructors.insert(ty, r);
    unsigned tid               = ty->get_parameter(1).get_int();
    unsigned o                 = ty->get_parameter(3 + 2*tid).get_int();
    unsigned num_constructors  = ty->get_parameter(o).get_int();
    for (unsigned c_id = 0; c_id < num_constructors; c_id++) {
        func_decl * c = get_constructor(ty, c_id);
        m_asts.push_back(c);
        r->push_back(c);
    }
    return r;
}

/**
   \brief Return a constructor mk(T_1, ... T_n)
   where each T_i is not a datatype or it is a datatype that contains 
   a constructor that will not contain directly or indirectly an element of the given sort.
*/
func_decl * datatype_util::get_non_rec_constructor(sort * ty) {
    SASSERT(is_datatype(ty));
    func_decl * r = 0;
    if (m_datatype2nonrec_constructor.find(ty, r))
        return r;
    r = 0;
    ptr_vector<sort> forbidden_set;
    forbidden_set.push_back(ty);
    r = get_non_rec_constructor_core(ty, forbidden_set);
    SASSERT(forbidden_set.back() == ty);
    SASSERT(r);
    m_asts.push_back(ty);
    m_asts.push_back(r);
    m_datatype2nonrec_constructor.insert(ty, r);
    return r;
}

/**
   \brief Return a constructor mk(T_1, ..., T_n) where
   each T_i is not a datatype or it is a datatype t not in forbidden_set,
   and get_non_rec_constructor_core(T_i, forbidden_set union { T_i })
*/
func_decl * datatype_util::get_non_rec_constructor_core(sort * ty, ptr_vector<sort> & forbidden_set) {
    // We must select a constructor c(T_1, ..., T_n):T such that
    //   1) T_i's are not recursive
    // If there is no such constructor, then we select one that 
    //   2) each type T_i is not recursive or contains a constructor that does not depend on T
    ptr_vector<func_decl> const * constructors = get_datatype_constructors(ty);
    // step 1)
    unsigned sz = constructors->size();
    ++m_start;
    for (unsigned j = 0; j < sz; ++j) {        
        func_decl * c = (*constructors)[(j + m_start) % sz];
        unsigned num_args = c->get_arity();
        unsigned i = 0;
        for (; i < num_args; i++) {
            sort * T_i = c->get_domain(i);
            if (is_datatype(T_i))
                break;
        }
        if (i == num_args)
            return c;
    }
    // step 2)
    for (unsigned j = 0; j < sz; ++j) {        
        func_decl * c = (*constructors)[(j + m_start) % sz];
        TRACE("datatype_util_bug", tout << "non_rec_constructor c: " << c->get_name() << "\n";);
        unsigned num_args = c->get_arity();
        unsigned i = 0;
        for (; i < num_args; i++) {
            sort * T_i = c->get_domain(i);
            TRACE("datatype_util_bug", tout << "c: " << c->get_name() << " i: " << i << " T_i: " << T_i->get_name() << "\n";);
            if (!is_datatype(T_i)) {
                TRACE("datatype_util_bug", tout << "T_i is not a datatype\n";);
                continue;
            }
            if (std::find(forbidden_set.begin(), forbidden_set.end(), T_i) != forbidden_set.end()) {
                TRACE("datatype_util_bug", tout << "T_i is in forbidden_set\n";);
                break;
            }
            forbidden_set.push_back(T_i);
            func_decl * nested_c = get_non_rec_constructor_core(T_i, forbidden_set);
            SASSERT(forbidden_set.back() == T_i);
            forbidden_set.pop_back();
            TRACE("datatype_util_bug", tout << "nested_c: " << nested_c->get_name() << "\n";);
            if (nested_c == 0)
                break;
        }
        if (i == num_args)
            return c;
    }
    return 0;
}

func_decl * datatype_util::get_constructor_recognizer(func_decl * constructor) {
    SASSERT(is_constructor(constructor));
    func_decl * d = 0;
    if (m_constructor2recognizer.find(constructor, d))
        return d;
    sort * datatype = constructor->get_range();
    d               = m_manager.mk_func_decl(m_family_id, OP_DT_RECOGNISER, 2, constructor->get_parameters(), 1, &datatype);
    SASSERT(d);
    m_asts.push_back(constructor);
    m_asts.push_back(d);
    m_constructor2recognizer.insert(constructor, d);
    return d;
}

ptr_vector<func_decl> const * datatype_util::get_constructor_accessors(func_decl * constructor) {
    SASSERT(is_constructor(constructor));
    ptr_vector<func_decl> * res = 0;
    if (m_constructor2accessors.find(constructor, res))
        return res;
    res = alloc(ptr_vector<func_decl>);
    m_asts.push_back(constructor);
    m_vectors.push_back(res);
    m_constructor2accessors.insert(constructor, res);
    unsigned c_id              = constructor->get_parameter(1).get_int();
    sort * datatype            = constructor->get_range();
    unsigned tid               = datatype->get_parameter(1).get_int();
    unsigned o                 = datatype->get_parameter(3 + 2*tid).get_int();
    unsigned k_i               = datatype->get_parameter(o + c_id + 1).get_int();
    unsigned num_accessors     = datatype->get_parameter(k_i+2).get_int();
    parameter p[3]             = { parameter(datatype), parameter(c_id), parameter(-1) };
    for (unsigned r = 0; r < num_accessors; r++) {
        p[2]           = parameter(r);
        func_decl * d  = m_manager.mk_func_decl(m_family_id, OP_DT_ACCESSOR, 3, p, 1, &datatype);
        SASSERT(d);
        m_asts.push_back(d);
        res->push_back(d);
    }
    return res;
}

func_decl * datatype_util::get_accessor_constructor(func_decl * accessor) { 
    SASSERT(is_accessor(accessor));
    func_decl * r = 0;
    if (m_accessor2constructor.find(accessor, r))
        return r;
    sort * datatype = to_sort(accessor->get_parameter(0).get_ast());
    unsigned c_id   = accessor->get_parameter(1).get_int();
    r = get_constructor(datatype, c_id);
    m_accessor2constructor.insert(accessor, r);
    m_asts.push_back(accessor);
    m_asts.push_back(r);
    return r;
}

func_decl * datatype_util::get_recognizer_constructor(func_decl * recognizer) {
    SASSERT(is_recognizer(recognizer));
    func_decl * r = 0;
    if (m_recognizer2constructor.find(recognizer, r))
        return r;
    sort * datatype = to_sort(recognizer->get_parameter(0).get_ast());
    unsigned c_id            = recognizer->get_parameter(1).get_int();
    r = get_constructor(datatype, c_id);
    m_recognizer2constructor.insert(recognizer, r);
    m_asts.push_back(recognizer);
    m_asts.push_back(r);
    return r;
}

bool datatype_util::is_recursive(sort * ty) {
    SASSERT(is_datatype(ty));
    bool r = false;
    if (m_is_recursive.find(ty, r))
        return r;
    r = is_recursive_datatype(ty->get_parameters());
    m_is_recursive.insert(ty, r);
    m_asts.push_back(ty);
    return r;
}


bool datatype_util::is_enum_sort(sort* s) {
	if (!is_datatype(s)) {
		return false;
	}
    bool r = false;
    if (m_is_enum.find(s, r))
        return r;
    ptr_vector<func_decl> const& cnstrs = *get_datatype_constructors(s);
    r = true;
    for (unsigned i = 0; r && i < cnstrs.size(); ++i) {
        r = cnstrs[i]->get_arity() == 0;
    }
    m_is_enum.insert(s, r);
    m_asts.push_back(s);
    return r;
}


void datatype_util::reset() {
    m_datatype2constructors.reset();
    m_datatype2nonrec_constructor.reset();
    m_constructor2accessors.reset();
    m_constructor2recognizer.reset();
    m_recognizer2constructor.reset();
    m_accessor2constructor.reset();
    m_is_recursive.reset();
    m_is_enum.reset();
    std::for_each(m_vectors.begin(), m_vectors.end(), delete_proc<ptr_vector<func_decl> >());
    m_vectors.reset();
    m_asts.reset();
    ++m_start;
}

/**
   \brief Two datatype sorts s1 and s2 are siblings if they were
   defined together in the same mutually recursive definition.
*/
bool datatype_util::are_siblings(sort * s1, sort * s2) {
    SASSERT(is_datatype(s1));
    SASSERT(is_datatype(s2));
    if (s1 == s2)
        return true;
    if (s1->get_num_parameters() != s2->get_num_parameters())
        return false;
    unsigned num_params = s1->get_num_parameters();
    if (s1->get_parameter(0) != s2->get_parameter(0))
        return false;
    // position 1 contains the IDX of the datatype in a mutually recursive definition.
    for (unsigned i = 2; i < num_params; i++) {
        if (s1->get_parameter(i) != s2->get_parameter(i))
            return false;
    }
    return true;
}

void datatype_util::display_datatype(sort *s0, std::ostream& strm) {
    ast_mark mark;
    ptr_buffer<sort> todo;
    SASSERT(is_datatype(s0));
    strm << s0->get_name() << " where\n";
    todo.push_back(s0);
    mark.mark(s0, true);
    while (!todo.empty()) {
        sort* s = todo.back();
        todo.pop_back();
        strm << s->get_name() << " =\n";

        ptr_vector<func_decl> const * cnstrs = get_datatype_constructors(s);
        for (unsigned i = 0; i < cnstrs->size(); ++i) {
            func_decl* cns = (*cnstrs)[i];
            func_decl* rec = get_constructor_recognizer(cns);
            strm << "  " << cns->get_name() << " :: " << rec->get_name() << " :: ";
            ptr_vector<func_decl> const * accs = get_constructor_accessors(cns);
            for (unsigned j = 0; j < accs->size(); ++j) {
                func_decl* acc = (*accs)[j];
                sort* s1 = acc->get_range();
                strm << "(" << acc->get_name() << ": " << s1->get_name() << ") "; 
                if (is_datatype(s1) && are_siblings(s1, s0) && !mark.is_marked(s1)) {
                        mark.mark(s1, true);
                        todo.push_back(s1);
                }          
            }
            strm << "\n";
        }
    }

}

bool datatype_util::is_func_decl(datatype_op_kind k, unsigned num_params, parameter const* params, func_decl* f) {
    bool eq = 
        f->get_decl_kind() == k &&
        f->get_family_id() == m_family_id &&
        f->get_num_parameters() == num_params;
    for (unsigned i = 0; eq && i < num_params; ++i) {
        eq = params[i] == f->get_parameter(i);
    }
    return eq;
}

bool datatype_util::is_constructor_of(unsigned num_params, parameter const* params, func_decl* f) {
    return 
        num_params == 2 &&
        m_family_id == f->get_family_id() &&
        OP_DT_CONSTRUCTOR == f->get_decl_kind() &&
        2 == f->get_num_parameters() &&
        params[0] == f->get_parameter(0) &&
        params[1] == f->get_parameter(1);
}

