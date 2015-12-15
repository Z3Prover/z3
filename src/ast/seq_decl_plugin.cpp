/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    dl_decl_plugin.h

Abstract:

    <abstract>

Author:

    Nikolaj Bjorner (nbjorner) 2011-14-11

Revision History:

--*/
#include "seq_decl_plugin.h"
#include "arith_decl_plugin.h"
#include "array_decl_plugin.h"
#include "ast_pp.h"
#include <sstream>

zstring::zstring(encoding enc): m_encoding(enc) {}

zstring::zstring(char const* s, encoding enc): m_encoding(enc) {
    // TBD: epply decoding
    while (*s) {
        m_buffer.push_back(*s);
        ++s;
    }
}

zstring::zstring(zstring const& other) {
    m_buffer = other.m_buffer;
    m_encoding = other.m_encoding;
}

zstring::zstring(unsigned num_bits, bool const* ch) {
    SASSERT(num_bits == 8 || num_bits == 16);
    m_encoding = (num_bits == 8)?ascii:unicode;
    unsigned n = 0;    
    for (unsigned i = 0; i < num_bits; ++i) {
        n |= (((unsigned)ch[i]) << num_bits);
    }
    m_buffer.push_back(n);
}

zstring::zstring(unsigned ch, encoding enc) {
    m_encoding = enc;
    m_buffer.push_back(ch & ((enc == ascii)?0x000000FF:0x0000FFFF));
}

zstring& zstring::operator=(zstring const& other) {
    m_encoding = other.m_encoding;
    m_buffer.reset();
    m_buffer.append(other.m_buffer);
    return *this;
}

zstring zstring::replace(zstring const& src, zstring const& dst) const {
    zstring result(m_encoding);
    if (length() < src.length()) {
        return zstring(*this);
    }
    bool found = false;
    for (unsigned i = 0; i <= length() - src.length(); ++i) {
        bool eq = !found;
        for (unsigned j = 0; eq && j < src.length(); ++j) {
            eq = m_buffer[i+j] == src[j];
        }
        if (eq) {
            result.m_buffer.append(dst.m_buffer);
            found = true;
        }
        else {
            result.m_buffer.push_back(m_buffer[i]);
        }
    }
    return result;
}

std::string zstring::encode() const {
    // TBD apply encodings.
    SASSERT(m_encoding == ascii);
    std::ostringstream strm;
    for (unsigned i = 0; i < m_buffer.size(); ++i) {
        strm << (char)(m_buffer[i]);
    }
    return strm.str();
}

bool zstring::suffixof(zstring const& other) const {
    if (length() > other.length()) return false;
    bool suffix = true;
    for (unsigned i = 0; suffix && i < length(); ++i) {
        suffix = m_buffer[length()-i-1] == other[other.length()-i-1];
    }
    return suffix;
}

bool zstring::prefixof(zstring const& other) const {
    if (length() > other.length()) return false;
    bool prefix = true;
    for (unsigned i = 0; prefix && i < length(); ++i) {
        prefix = m_buffer[i] == other[i];
    }
    return prefix;
}

bool zstring::contains(zstring const& other) const {
    if (other.length() > length()) return false;
    unsigned last = length() - other.length();
    bool cont = false;
    for (unsigned i = 0; !cont && i <= last; ++i) {
        cont = true;
        for (unsigned j = 0; cont && j < other.length(); ++j) {
            cont = other[j] == m_buffer[j+i];
        }
    }
    return cont;
}

int zstring::indexof(zstring const& other, int offset) const {
    SASSERT(offset >= 0);
    if (static_cast<unsigned>(offset) == length()) return -1;
    if (other.length() + offset > length()) return -1;
    unsigned last = length() - other.length();
    for (unsigned i = static_cast<unsigned>(offset); i <= last; ++i) {
        bool prefix = true;
        for (unsigned j = 0; prefix && j < other.length(); ++j) {
            prefix = m_buffer[i + j] == other[j];
        }    
        if (prefix) {
            return static_cast<int>(i);
        }
    }
    return -1;
}

zstring zstring::extract(int offset, int len) const {
    zstring result(m_encoding);
    SASSERT(0 <= offset && 0 <= len);
    int last = std::min(offset+len, static_cast<int>(length()));
    for (int i = offset; i < last; ++i) {
        result.m_buffer.push_back(m_buffer[i]);
    }
    return result;
}

zstring zstring::operator+(zstring const& other) const {
    SASSERT(m_encoding == other.m_encoding);
    zstring result(*this);
    result.m_buffer.append(other.m_buffer);
    return result;
}

std::ostream& zstring::operator<<(std::ostream& out) const {
    return out << encode();
}


seq_decl_plugin::seq_decl_plugin(): m_init(false), 
                                    m_stringc_sym("String"),
                                    m_string(0),
                                    m_char(0) {}

void seq_decl_plugin::finalize() {
    for (unsigned i = 0; i < m_sigs.size(); ++i) 
        dealloc(m_sigs[i]);
    m_manager->dec_ref(m_string);
    m_manager->dec_ref(m_char);
}

bool seq_decl_plugin::is_sort_param(sort* s, unsigned& idx) {
    return 
        s->get_name().is_numerical() &&
        (idx = s->get_name().get_num(), true);
}

bool seq_decl_plugin::match(ptr_vector<sort>& binding, sort* s, sort* sP) {
    ast_manager& m = *m_manager;
    if (s == sP) return true;
    unsigned i;
    if (is_sort_param(sP, i)) {
        if (binding.size() <= i) binding.resize(i+1);
        if (binding[i] && (binding[i] != s)) return false;
        TRACE("seq_verbose", tout << "setting binding @ " << i << " to " << mk_pp(s, m) << "\n";);
        binding[i] = s;
        return true;
    }

   
    if (s->get_family_id() == sP->get_family_id() &&
        s->get_decl_kind() == sP->get_decl_kind() &&
        s->get_num_parameters() == sP->get_num_parameters()) {
        for (unsigned i = 0; i < s->get_num_parameters(); ++i) {
            parameter const& p = s->get_parameter(i);
            if (p.is_ast() && is_sort(p.get_ast())) {
                parameter const& p2 = sP->get_parameter(i);
                if (!match(binding, to_sort(p.get_ast()), to_sort(p2.get_ast()))) return false;
            }
        }
        return true;
    }
    else {
        TRACE("seq", tout << "Could not match " << mk_pp(s, m) << " and " << mk_pp(sP, m) << "\n";);
        return false;
    }
}

/*
  \brief match left associative operator.
*/
void seq_decl_plugin::match_left_assoc(psig& sig, unsigned dsz, sort *const* dom, sort* range, sort_ref& range_out) {
    ptr_vector<sort> binding;
    ast_manager& m = *m_manager;
    TRACE("seq_verbose", 
          tout << sig.m_name << ": ";
          for (unsigned i = 0; i < dsz; ++i) tout << mk_pp(dom[i], m) << " ";
          if (range) tout << " range: " << mk_pp(range, m);
          tout << "\n";);
    if (dsz == 0) {
        std::ostringstream strm;
        strm << "Unexpected number of arguments to '" << sig.m_name << "' ";
        strm << "at least one argument expected " << dsz << " given";
        m.raise_exception(strm.str().c_str());
    }
    bool is_match = true;
    for (unsigned i = 0; is_match && i < dsz; ++i) {
        SASSERT(dom[i]);
        is_match = match(binding, dom[i], sig.m_dom[0].get());
    }
    if (range && is_match) {
        is_match = match(binding, range, sig.m_range);
    }
    if (!is_match) {
        std::ostringstream strm;
        strm << "Sort of function '" << sig.m_name << "' ";
        strm << "does not match the declared type";
        m.raise_exception(strm.str().c_str());
    }
    range_out = apply_binding(binding, sig.m_range);
    SASSERT(range_out);
    TRACE("seq_verbose", tout << mk_pp(range_out, m) << "\n";);
}

void seq_decl_plugin::match(psig& sig, unsigned dsz, sort *const* dom, sort* range, sort_ref& range_out) {
    ptr_vector<sort> binding;
    ast_manager& m = *m_manager;
    if (sig.m_dom.size() != dsz) {
        std::ostringstream strm;
        strm << "Unexpected number of arguments to '" << sig.m_name << "' ";
        strm << sig.m_dom.size() << " arguments expected " << dsz << " given";
        m.raise_exception(strm.str().c_str());
    }
    bool is_match = true;
    for (unsigned i = 0; is_match && i < dsz; ++i) {
        is_match = match(binding, dom[i], sig.m_dom[i].get());
    }
    if (range && is_match) {
        is_match = match(binding, range, sig.m_range);
    }
    if (!is_match) {
        std::ostringstream strm;
        strm << "Sort of polymorphic function '" << sig.m_name << "' ";
        strm << "does not match the declared type";
        m.raise_exception(strm.str().c_str());
    }
    if (!range && dsz == 0) {
        std::ostringstream strm;
        strm << "Sort of polymorphic function '" << sig.m_name << "' ";
        strm << "is ambiguous. Function takes no arguments and sort of range has not been constrained";
        m.raise_exception(strm.str().c_str());
    }
    range_out = apply_binding(binding, sig.m_range);
    SASSERT(range_out);
}

sort* seq_decl_plugin::apply_binding(ptr_vector<sort> const& binding, sort* s) {
    unsigned i;
    if (is_sort_param(s, i)) {
        if (binding.size() <= i || !binding[i]) {
            m_manager->raise_exception("Expecting type parameter to be bound");
        }
        return binding[i];
    }
    if (is_sort_of(s, m_family_id, SEQ_SORT) || is_sort_of(s, m_family_id, RE_SORT)) {
        SASSERT(s->get_num_parameters() == 1);
        SASSERT(s->get_parameter(0).is_ast());
        SASSERT(is_sort(s->get_parameter(0).get_ast()));
        sort* p = apply_binding(binding, to_sort(s->get_parameter(0).get_ast()));
        parameter param(p);
        return mk_sort(s->get_decl_kind(), 1, &param);
    }
    return s;
}


void seq_decl_plugin::init() {
    if(m_init) return;
    ast_manager& m = *m_manager;
    m_init = true;
    sort* A = m.mk_uninterpreted_sort(symbol((unsigned)0));
    sort* strT = m_string;
    parameter paramA(A);
    parameter paramS(strT);
    sort* seqA = m.mk_sort(m_family_id, SEQ_SORT, 1, &paramA);
    sort* reA  = m.mk_sort(m_family_id, RE_SORT, 1, &paramA);
    sort* reT  = m.mk_sort(m_family_id, RE_SORT, 1, &paramS);
    sort* boolT = m.mk_bool_sort();
    sort* intT  = arith_util(m).mk_int();
    sort* predA = array_util(m).mk_array_sort(A, boolT);
    sort* seqAseqA[2] = { seqA, seqA };
    sort* seqAreA[2] = { seqA, reA };
    sort* reAreA[2] = { reA, reA };
    sort* seqAint2T[3] = { seqA, intT, intT };
    sort* seq2AintT[3] = { seqA, seqA, intT };
    sort* str2T[2] = { strT, strT };
    sort* str3T[3] = { strT, strT, strT };
    sort* strTint2T[3] = { strT, intT, intT };
    sort* strTreT[2] = { strT, reT };
    sort* str2TintT[3] = { strT, strT, intT };
    sort* seqAintT[2] = { seqA, intT };
    sort* seq3A[3] = { seqA, seqA, seqA };
    m_sigs.resize(LAST_SEQ_OP);
    // TBD: have (par ..) construct and load parameterized signature from premable.
    m_sigs[OP_SEQ_UNIT]      = alloc(psig, m, "seq.unit",     1, 1, &A, seqA);
    m_sigs[OP_SEQ_EMPTY]     = alloc(psig, m, "seq.empty",    1, 0, 0, seqA); 
    m_sigs[OP_SEQ_CONCAT]    = alloc(psig, m, "seq.++",       1, 2, seqAseqA, seqA);
    m_sigs[OP_SEQ_PREFIX]    = alloc(psig, m, "seq.prefixof", 1, 2, seqAseqA, boolT);
    m_sigs[OP_SEQ_SUFFIX]    = alloc(psig, m, "seq.suffixof", 1, 2, seqAseqA, boolT);
    m_sigs[OP_SEQ_CONTAINS]  = alloc(psig, m, "seq.contains", 1, 2, seqAseqA, boolT);
    m_sigs[OP_SEQ_EXTRACT]   = alloc(psig, m, "seq.extract",  1, 3, seqAint2T, seqA);
    m_sigs[OP_SEQ_REPLACE]   = alloc(psig, m, "seq.replace",  1, 3, seq3A, seqA);
    m_sigs[OP_SEQ_INDEX]     = alloc(psig, m, "seq.indexof",  1, 3, seq2AintT, intT);
    m_sigs[OP_SEQ_AT]        = alloc(psig, m, "seq.at",       1, 2, seqAintT, seqA);
    m_sigs[OP_SEQ_LENGTH]    = alloc(psig, m, "seq.len",      1, 1, &seqA, intT);
    m_sigs[OP_RE_PLUS]       = alloc(psig, m, "re.+",         1, 1, &reA, reA);
    m_sigs[OP_RE_STAR]       = alloc(psig, m, "re.*",         1, 1, &reA, reA);
    m_sigs[OP_RE_OPTION]     = alloc(psig, m, "re.opt",       1, 1, &reA, reA);
    m_sigs[OP_RE_RANGE]      = alloc(psig, m, "re.range",     1, 2, seqAseqA,  reA);
    m_sigs[OP_RE_CONCAT]     = alloc(psig, m, "re.++",        1, 2, reAreA, reA);
    m_sigs[OP_RE_UNION]      = alloc(psig, m, "re.union",     1, 2, reAreA, reA);
    m_sigs[OP_RE_INTERSECT]  = alloc(psig, m, "re.inter",     1, 2, reAreA, reA);
    m_sigs[OP_RE_LOOP]           = alloc(psig, m, "re-loop",    1, 1, &reA, reA);
    m_sigs[OP_RE_EMPTY_SET]      = alloc(psig, m, "re-empty-set", 1, 0, 0, reA);
    m_sigs[OP_RE_FULL_SET]       = alloc(psig, m, "re-full-set", 1, 0, 0, reA);
    m_sigs[OP_RE_OF_PRED]        = alloc(psig, m, "re-of-pred", 1, 1, &predA, reA);
    m_sigs[OP_SEQ_TO_RE]         = alloc(psig, m, "seq.to.re",  1, 1, &seqA, reA);
    m_sigs[OP_SEQ_IN_RE]         = alloc(psig, m, "seq.in.re", 1, 2, seqAreA, boolT);
    m_sigs[OP_STRING_CONST]      = 0;
    m_sigs[_OP_STRING_STRIDOF]   = alloc(psig, m, "str.indexof", 0, 3, str2TintT, intT);
    m_sigs[_OP_STRING_STRREPL]   = alloc(psig, m, "str.replace", 0, 3, str3T, strT);
    m_sigs[OP_STRING_ITOS]       = alloc(psig, m, "int.to.str", 0, 1, &intT, strT);
    m_sigs[OP_STRING_STOI]       = alloc(psig, m, "str.to.int", 0, 1, &strT, intT);
    m_sigs[OP_REGEXP_LOOP]       = alloc(psig, m, "re.loop", 0, 2, strTint2T, reT); // maybe 3 arguments.
    m_sigs[_OP_STRING_CONCAT]    = alloc(psig, m, "str.++", 1, 2, str2T, strT);
    m_sigs[_OP_STRING_LENGTH]    = alloc(psig, m, "str.len", 0, 1, &strT, intT);
    m_sigs[_OP_STRING_STRCTN]    = alloc(psig, m, "str.contains", 0, 2, str2T, boolT);
    m_sigs[_OP_STRING_CHARAT]    = alloc(psig, m, "str.at", 0, 2, strTint2T, strT);
    m_sigs[_OP_STRING_PREFIX]    = alloc(psig, m, "str.prefixof", 0, 2, str2T, boolT);
    m_sigs[_OP_STRING_SUFFIX]    = alloc(psig, m, "str.suffixof", 0, 2, str2T, boolT);
    m_sigs[_OP_STRING_IN_REGEXP]  = alloc(psig, m, "str.in.re", 0, 2, strTreT, boolT);
    m_sigs[_OP_STRING_TO_REGEXP]  = alloc(psig, m, "str.to.re", 0, 1, &strT, reT);
    m_sigs[_OP_STRING_SUBSTR]     = alloc(psig, m, "str.substr", 0, 3, strTint2T, strT);
}

void seq_decl_plugin::set_manager(ast_manager* m, family_id id) {
    decl_plugin::set_manager(m, id);
    m_char = m->mk_sort(symbol("Char"), sort_info(m_family_id, _CHAR_SORT, 0, (parameter const*)0));
    m->inc_ref(m_char);
    parameter param(m_char);
    m_string = m->mk_sort(symbol("String"), sort_info(m_family_id, SEQ_SORT, 1, &param));
    m->inc_ref(m_string);
}

sort * seq_decl_plugin::mk_sort(decl_kind k, unsigned num_parameters, parameter const * parameters) {
    init();
    ast_manager& m = *m_manager;
    switch (k) {
    case SEQ_SORT:
        if (num_parameters != 1) {
            m.raise_exception("Invalid sequence sort, expecting one parameter");
        }
        if (!parameters[0].is_ast() || !is_sort(parameters[0].get_ast())) {
            m.raise_exception("invalid sequence sort, parameter is not a sort");
        }
        if (parameters[0].get_ast() == m_char) {
            return m_string;
        }
        return m.mk_sort(symbol("Seq"), sort_info(m_family_id, SEQ_SORT, num_parameters, parameters));
    case RE_SORT:
        if (num_parameters != 1) {
            m.raise_exception("Invalid regex sort, expecting one parameter");
        }
        if (!parameters[0].is_ast() || !is_sort(parameters[0].get_ast())) {
            m.raise_exception("invalid regex sort, parameter is not a sort");
        }
        return m.mk_sort(symbol("RegEx"), sort_info(m_family_id, RE_SORT, num_parameters, parameters));
    case _STRING_SORT:
        return m_string;
    case _CHAR_SORT:
        return m_char;
    default:
        UNREACHABLE();
        return 0;
    }
}

func_decl* seq_decl_plugin::mk_seq_fun(decl_kind k, unsigned arity, sort* const* domain, sort* range, decl_kind k_string) {
    ast_manager& m = *m_manager;
    sort_ref rng(m);
    match(*m_sigs[k], arity, domain, range, rng);
    return m.mk_func_decl(m_sigs[(domain[0] == m_string)?k_string:k]->m_name, arity, domain, rng, func_decl_info(m_family_id, k));
}


func_decl* seq_decl_plugin::mk_str_fun(decl_kind k, unsigned arity, sort* const* domain, sort* range, decl_kind k_seq) {
    ast_manager& m = *m_manager;
    sort_ref rng(m);
    match(*m_sigs[k], arity, domain, range, rng);
    return m.mk_func_decl(m_sigs[k]->m_name, arity, domain, rng, func_decl_info(m_family_id, k_seq));
}

func_decl* seq_decl_plugin::mk_assoc_fun(decl_kind k, unsigned arity, sort* const* domain, sort* range, decl_kind k_seq, decl_kind k_string) {
    ast_manager& m = *m_manager;
    sort_ref rng(m);
    if (arity == 0) {
        m.raise_exception("Invalid function application. At least one argument expected");
    }
    match_left_assoc(*m_sigs[k], arity, domain, range, rng);
    func_decl_info info(m_family_id, k_seq);
    info.set_left_associative();
    return m.mk_func_decl(m_sigs[(rng == m_string)?k_string:k_seq]->m_name, rng, rng, rng, info);    
}

func_decl * seq_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters, 
                                          unsigned arity, sort * const * domain, sort * range) {
    init();
    ast_manager& m = *m_manager;
    sort_ref rng(m);
    switch(k) {
    case OP_SEQ_EMPTY:
        match(*m_sigs[k], arity, domain, range, rng);
        if (rng == m_string) {
            parameter param(symbol(""));
            return mk_func_decl(OP_STRING_CONST, 1, &param, 0, 0, m_string);
        }
        return m.mk_func_decl(m_sigs[k]->m_name, arity, domain, rng, func_decl_info(m_family_id, k));
        
    case OP_SEQ_UNIT:
    case OP_RE_PLUS:
    case OP_RE_STAR:
    case OP_RE_OPTION:
    case OP_RE_RANGE:
    case OP_RE_EMPTY_SET:
    case OP_RE_OF_PRED:
    case OP_STRING_ITOS:
    case OP_STRING_STOI:
    case OP_REGEXP_LOOP:
        match(*m_sigs[k], arity, domain, range, rng);
        return m.mk_func_decl(m_sigs[k]->m_name, arity, domain, rng, func_decl_info(m_family_id, k));

    case OP_RE_LOOP:
        match(*m_sigs[k], arity, domain, range, rng);
        if (num_parameters != 2 || !parameters[0].is_int() || !parameters[1].is_int()) {
            m.raise_exception("Expecting two numeral parameters to function re-loop");
        }
        return m.mk_func_decl(m_sigs[k]->m_name, arity, domain, rng, func_decl_info(m_family_id, k, num_parameters, parameters));   

    case OP_STRING_CONST:
        if (!(num_parameters == 1 && arity == 0 && parameters[0].is_symbol())) {
            m.raise_exception("invalid string declaration");
        } 
        return m.mk_const_decl(m_stringc_sym, m_string,
                               func_decl_info(m_family_id, OP_STRING_CONST, num_parameters, parameters));
        
    case OP_RE_UNION:
        return mk_assoc_fun(k, arity, domain, range, k, k);

    case OP_RE_CONCAT:  
        return mk_assoc_fun(k, arity, domain, range, k, k);

    case OP_SEQ_CONCAT: 
        return mk_assoc_fun(k, arity, domain, range, k, _OP_STRING_CONCAT);

    case _OP_STRING_CONCAT: 
        return mk_assoc_fun(k, arity, domain, range, OP_SEQ_CONCAT, k);

    case OP_SEQ_REPLACE:
        return mk_seq_fun(k, arity, domain, range, _OP_STRING_STRREPL);
    case _OP_STRING_STRREPL:
        return mk_str_fun(k, arity, domain, range, OP_SEQ_REPLACE);

    case OP_SEQ_INDEX:
        if (arity == 2) {
            sort* dom[3] = { domain[0], domain[1], arith_util(m).mk_int() };
            sort_ref rng(m);
            match(*m_sigs[k], 3, dom, range, rng);
            return m.mk_func_decl(m_sigs[(dom[0] == m_string)?_OP_STRING_STRIDOF:k]->m_name, arity, domain, rng, func_decl_info(m_family_id, k));
        }
        return mk_seq_fun(k, arity, domain, range, _OP_STRING_STRIDOF);
    case _OP_STRING_STRIDOF:
        if (arity == 2) {
            sort* dom[3] = { domain[0], domain[1], arith_util(m).mk_int() };
            sort_ref rng(m);
            match(*m_sigs[k], 3, dom, range, rng);
            return m.mk_func_decl(m_sigs[k]->m_name, arity, domain, rng, func_decl_info(m_family_id, OP_SEQ_INDEX));
        }
        return mk_str_fun(k, arity, domain, range, OP_SEQ_INDEX);

    case OP_SEQ_PREFIX:
        return mk_seq_fun(k, arity, domain, range, _OP_STRING_PREFIX);
    case _OP_STRING_PREFIX:
        return mk_str_fun(k, arity, domain, range, OP_SEQ_PREFIX);

    case OP_SEQ_SUFFIX:
        return mk_seq_fun(k, arity, domain, range, _OP_STRING_SUFFIX);
    case _OP_STRING_SUFFIX:
        return mk_str_fun(k, arity, domain, range, OP_SEQ_SUFFIX);

    case OP_SEQ_LENGTH:
        return mk_seq_fun(k, arity, domain, range, _OP_STRING_LENGTH);
    case _OP_STRING_LENGTH:
        return mk_str_fun(k, arity, domain, range, OP_SEQ_LENGTH);

    case OP_SEQ_CONTAINS:
        return mk_seq_fun(k, arity, domain, range, _OP_STRING_STRCTN);
    case _OP_STRING_STRCTN:
        return mk_str_fun(k, arity, domain, range, OP_SEQ_CONTAINS);

    case OP_SEQ_TO_RE:
        return mk_seq_fun(k, arity, domain, range, _OP_STRING_TO_REGEXP);
    case _OP_STRING_TO_REGEXP:
        return mk_str_fun(k, arity, domain, range, OP_SEQ_TO_RE);

    case OP_SEQ_IN_RE:
        return mk_seq_fun(k, arity, domain, range, _OP_STRING_IN_REGEXP);
    case _OP_STRING_IN_REGEXP:
        return mk_str_fun(k, arity, domain, range, OP_SEQ_IN_RE);

    case OP_SEQ_AT:
        return mk_seq_fun(k, arity, domain, range, _OP_STRING_CHARAT);
    case _OP_STRING_CHARAT:
        return mk_str_fun(k, arity, domain, range, OP_SEQ_AT);

    case OP_SEQ_EXTRACT:
        return mk_seq_fun(k, arity, domain, range, _OP_STRING_SUBSTR);
    case _OP_STRING_SUBSTR:
        return mk_str_fun(k, arity, domain, range, OP_SEQ_EXTRACT);

    case _OP_SEQ_SKOLEM: {
        if (num_parameters != 1 || !parameters[0].is_symbol()) {
            m.raise_exception("one symbol parameter expected to skolem symbol");
        }
        symbol s = parameters[0].get_symbol();
        return m.mk_func_decl(s, arity, domain, range, func_decl_info(m_family_id, k, num_parameters, parameters));
    }
    default:
        UNREACHABLE();
        return 0;
    }
}

void seq_decl_plugin::get_op_names(svector<builtin_name> & op_names, symbol const & logic) {
    init();
    for (unsigned i = 0; i < m_sigs.size(); ++i) {
        if (m_sigs[i]) {
            op_names.push_back(builtin_name(m_sigs[i]->m_name.str().c_str(), i));
        }
    }
}

void seq_decl_plugin::get_sort_names(svector<builtin_name> & sort_names, symbol const & logic) {
    init();
    sort_names.push_back(builtin_name("Seq",   SEQ_SORT));
    sort_names.push_back(builtin_name("RegEx", RE_SORT));
    sort_names.push_back(builtin_name("String", _STRING_SORT));
}

app* seq_decl_plugin::mk_string(symbol const& s) {
    parameter param(s);
    func_decl* f = m_manager->mk_const_decl(m_stringc_sym, m_string,
                                   func_decl_info(m_family_id, OP_STRING_CONST, 1, &param));
    return m_manager->mk_const(f);
}

app* seq_decl_plugin::mk_string(zstring const& s) {
    symbol sym(s.encode().c_str());
    parameter param(sym);
    func_decl* f = m_manager->mk_const_decl(m_stringc_sym, m_string,
                                   func_decl_info(m_family_id, OP_STRING_CONST, 1, &param));
    return m_manager->mk_const(f);
}

bool seq_decl_plugin::is_value(app* e) const {
    return is_app_of(e, m_family_id, OP_STRING_CONST);
}

app* seq_util::mk_skolem(symbol const& name, unsigned n, expr* const* args, sort* range) {
    SASSERT(range);
    parameter param(name);
    func_decl* f = m.mk_func_decl(get_family_id(), _OP_SEQ_SKOLEM, 1, &param, n, args, range);
    return m.mk_app(f, n, args);
}

app* seq_util::str::mk_string(zstring const& s) { return u.seq.mk_string(s); }


app*  seq_util::str::mk_char(zstring const& s, unsigned idx) {
    bv_util bvu(m);
    return bvu.mk_numeral(s[idx], s.num_bits());
}


bool seq_util::str::is_string(expr const* n, zstring& s) const {
    if (is_string(n)) {
        s = zstring(to_app(n)->get_decl()->get_parameter(0).get_symbol().bare_str());
        return true;
    }
    else {
        return false;
    }
}


void seq_util::str::get_concat(expr* e, ptr_vector<expr>& es) const {
    expr* e1, *e2;
    while (is_concat(e, e1, e2)) {
        get_concat(e1, es);
        e = e2;
    }    
    es.push_back(e);
}
