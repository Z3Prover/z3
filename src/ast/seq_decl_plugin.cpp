/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    seq_decl_plugin.h

Abstract:

    decl_plugin for the theory of sequences

Author:

    Nikolaj Bjorner (nbjorner) 2011-14-11

Revision History:

--*/
#include "ast/seq_decl_plugin.h"
#include "ast/arith_decl_plugin.h"
#include "ast/array_decl_plugin.h"
#include "ast/ast_pp.h"
#include <sstream>


seq_decl_plugin::seq_decl_plugin(): m_init(false),
                                    m_stringc_sym("String"),
                                    m_string(nullptr),
                                    m_char(nullptr),
                                    m_reglan(nullptr),
                                    m_has_re(false),
                                    m_has_seq(false) {
}

void seq_decl_plugin::finalize() {
    for (psig* s : m_sigs) 
        dealloc(s);
    m_manager->dec_ref(m_string);
    m_manager->dec_ref(m_char);
    m_manager->dec_ref(m_reglan);
}

bool seq_decl_plugin::is_sort_param(sort* s, unsigned& idx) {
    return
        s->get_name().is_numerical() &&
        (idx = s->get_name().get_num(), true);
}

bool seq_decl_plugin::match(ptr_vector<sort>& binding, sort* s, sort* sP) {
    if (s == sP) return true;
    unsigned idx;
    if (is_sort_param(sP, idx)) {
        if (binding.size() <= idx) binding.resize(idx+1);
        if (binding[idx] && (binding[idx] != s)) return false;
        binding[idx] = s;
        return true;
    }


    if (s->get_family_id() == sP->get_family_id() &&
        s->get_decl_kind() == sP->get_decl_kind() &&
        s->get_num_parameters() == sP->get_num_parameters()) {
        for (unsigned i = 0, sz = s->get_num_parameters(); i < sz; ++i) {
            parameter const& p = s->get_parameter(i);
            if (p.is_ast() && is_sort(p.get_ast())) {
                parameter const& p2 = sP->get_parameter(i);
                if (!match(binding, to_sort(p.get_ast()), to_sort(p2.get_ast()))) return false;
            }
        }
        return true;
    }
    else {
        TRACE("seq", tout << "Could not match " << mk_pp(s, *m_manager) << " and " << mk_pp(sP, *m_manager) << "\n";);
        return false;
    }
}

/*
  \brief match right associative operator.
*/
void seq_decl_plugin::match_assoc(psig& sig, unsigned dsz, sort *const* dom, sort* range, sort_ref& range_out) {
    ptr_vector<sort> binding;
    ast_manager& m = *m_manager;
    if (dsz == 0) {
        std::ostringstream strm;
        strm << "Unexpected number of arguments to '" << sig.m_name << "' ";
        strm << "at least one argument expected " << dsz << " given";
        m.raise_exception(strm.str());
    }
    bool is_match = true;
    for (unsigned i = 0; is_match && i < dsz; ++i) {
        SASSERT(dom[i]);
        is_match = match(binding, dom[i], sig.m_dom.get(0));
    }
    if (range && is_match) {
        is_match = match(binding, range, sig.m_range);
    }
    if (!is_match) {
        std::ostringstream strm;
        strm << "Sort of function '" << sig.m_name << "' ";
        strm << "does not match the declared type. Given domain: ";
        for (unsigned i = 0; i < dsz; ++i) {
            strm << mk_pp(dom[i], m) << " ";
        }
        if (range) {
            strm << " and range: " << mk_pp(range, m);
        }
        m.raise_exception(strm.str());
    }
    range_out = apply_binding(binding, sig.m_range);
    SASSERT(range_out);
}

void seq_decl_plugin::match(psig& sig, unsigned dsz, sort *const* dom, sort* range, sort_ref& range_out) {
    m_binding.reset();
    ast_manager& m = *m_manager;
    if (sig.m_dom.size() != dsz) {
        std::ostringstream strm;
        strm << "Unexpected number of arguments to '" << sig.m_name << "' ";
        strm << sig.m_dom.size() << " arguments expected " << dsz << " given";
        m.raise_exception(strm.str());
    }
    bool is_match = true;
    for (unsigned i = 0; is_match && i < dsz; ++i) {
        is_match = match(m_binding, dom[i], sig.m_dom[i].get());
    }
    if (range && is_match) {
        is_match = match(m_binding, range, sig.m_range);
    }
    if (!is_match) {
        std::ostringstream strm;
        strm << "Sort of polymorphic function '" << sig.m_name << "' ";
        strm << "does not match the declared type. ";
        strm << "\nGiven domain: ";
        for (unsigned i = 0; i < dsz; ++i) {
            strm << mk_pp(dom[i], m) << " ";
        }
        if (range) {
            strm << " and range: " << mk_pp(range, m);
        }
        strm << "\nExpected domain: ";
        for (unsigned i = 0; i < dsz; ++i) {
            strm << mk_pp(sig.m_dom[i].get(), m) << " ";
        }

        m.raise_exception(strm.str());
    }
    if (!range && dsz == 0) {
        std::ostringstream strm;
        strm << "Sort of polymorphic function '" << sig.m_name << "' ";
        strm << "is ambiguous. Function takes no arguments and sort of range has not been constrained";
        m.raise_exception(strm.str());
    }
    range_out = apply_binding(m_binding, sig.m_range);
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
        if (p == m_char && s->get_decl_kind() == SEQ_SORT)
            return m_string;
        if (p == m_string && s->get_decl_kind() == RE_SORT)
            return mk_reglan();
        return mk_sort(s->get_decl_kind(), 1, &param);
    }
    return s;
}


void seq_decl_plugin::init() {
    if (m_init) return;
    ast_manager& m = *m_manager;
    m_init = true;
    sort* A = m.mk_uninterpreted_sort(symbol(0u));
    sort* strT = m_string;
    parameter paramA(A);
    parameter paramS(strT);
    sort* seqA = m.mk_sort(m_family_id, SEQ_SORT, 1, &paramA);
    parameter paramSA(seqA);
    sort* reA  = m.mk_sort(m_family_id, RE_SORT, 1, &paramSA);
    sort* reT  = m.mk_sort(m_family_id, RE_SORT, 1, &paramS);
    sort* boolT = m.mk_bool_sort();
    sort* intT  = arith_util(m).mk_int();
    sort* predA = array_util(m).mk_array_sort(A, boolT);
    sort* seqAseqAseqA[3] = { seqA, seqA, seqA };
    sort* seqAreAseqA[3] = { seqA, reA, seqA };
    sort* seqAseqA[2] = { seqA, seqA };
    sort* seqAreA[2] = { seqA, reA };
    sort* reAreA[2] = { reA, reA };
    sort* AreA[2] = { A, reA };
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
    m_sigs[OP_SEQ_EMPTY]     = alloc(psig, m, "seq.empty",    1, 0, nullptr, seqA);
    m_sigs[OP_SEQ_CONCAT]    = alloc(psig, m, "seq.++",       1, 2, seqAseqA, seqA);
    m_sigs[OP_SEQ_PREFIX]    = alloc(psig, m, "seq.prefixof", 1, 2, seqAseqA, boolT);
    m_sigs[OP_SEQ_SUFFIX]    = alloc(psig, m, "seq.suffixof", 1, 2, seqAseqA, boolT);
    m_sigs[OP_SEQ_CONTAINS]  = alloc(psig, m, "seq.contains", 1, 2, seqAseqA, boolT);
    m_sigs[OP_SEQ_EXTRACT]   = alloc(psig, m, "seq.extract",  1, 3, seqAint2T, seqA);
    m_sigs[OP_SEQ_REPLACE]   = alloc(psig, m, "seq.replace",  1, 3, seq3A, seqA);
    m_sigs[OP_SEQ_INDEX]     = alloc(psig, m, "seq.indexof",  1, 3, seq2AintT, intT);
    m_sigs[OP_SEQ_LAST_INDEX] = alloc(psig, m, "seq.last_indexof",  1, 2, seqAseqA, intT);
    m_sigs[OP_SEQ_AT]        = alloc(psig, m, "seq.at",       1, 2, seqAintT, seqA);
    m_sigs[OP_SEQ_NTH]       = alloc(psig, m, "seq.nth",      1, 2, seqAintT, A);
    m_sigs[OP_SEQ_NTH_I]     = alloc(psig, m, "seq.nth_i",    1, 2, seqAintT, A);
    m_sigs[OP_SEQ_NTH_U]     = alloc(psig, m, "seq.nth_u",    1, 2, seqAintT, A);
    m_sigs[OP_SEQ_LENGTH]    = alloc(psig, m, "seq.len",      1, 1, &seqA, intT);
    m_sigs[OP_RE_PLUS]       = alloc(psig, m, "re.+",         1, 1, &reA, reA);
    m_sigs[OP_RE_STAR]       = alloc(psig, m, "re.*",         1, 1, &reA, reA);
    m_sigs[OP_RE_OPTION]     = alloc(psig, m, "re.opt",       1, 1, &reA, reA);
    m_sigs[OP_RE_RANGE]      = alloc(psig, m, "re.range",     1, 2, seqAseqA,  reA);
    m_sigs[OP_RE_CONCAT]     = alloc(psig, m, "re.++",        1, 2, reAreA, reA);
    m_sigs[OP_RE_UNION]      = alloc(psig, m, "re.union",     1, 2, reAreA, reA);
    m_sigs[OP_RE_INTERSECT]  = alloc(psig, m, "re.inter",     1, 2, reAreA, reA);
    m_sigs[OP_RE_DIFF]       = alloc(psig, m, "re.diff",      1, 2, reAreA, reA);
    m_sigs[OP_RE_LOOP]           = alloc(psig, m, "re.loop",    1, 1, &reA, reA);
    m_sigs[OP_RE_POWER]          = alloc(psig, m, "re.^", 1, 1, &reA, reA);
    m_sigs[OP_RE_COMPLEMENT]     = alloc(psig, m, "re.comp", 1, 1, &reA, reA);
    m_sigs[OP_RE_EMPTY_SET]      = alloc(psig, m, "re.empty", 1, 0, nullptr, reA);
    m_sigs[OP_RE_FULL_SEQ_SET]   = alloc(psig, m, "re.all", 1, 0, nullptr, reA);
    m_sigs[OP_RE_FULL_CHAR_SET]  = alloc(psig, m, "re.allchar", 1, 0, nullptr, reA);
    m_sigs[OP_RE_OF_PRED]        = alloc(psig, m, "re.of.pred", 1, 1, &predA, reA);
    m_sigs[OP_RE_REVERSE]        = alloc(psig, m, "re.reverse", 1, 1, &reA, reA);
    m_sigs[OP_RE_DERIVATIVE]     = alloc(psig, m, "re.derivative", 1, 2, AreA, reA);
    m_sigs[_OP_RE_ANTIMOROV_UNION] = alloc(psig, m, "re.union", 1, 2, reAreA, reA);
    m_sigs[OP_SEQ_TO_RE]         = alloc(psig, m, "seq.to.re",  1, 1, &seqA, reA);
    m_sigs[OP_SEQ_IN_RE]         = alloc(psig, m, "seq.in.re", 1, 2, seqAreA, boolT);
    m_sigs[OP_SEQ_REPLACE_RE_ALL] = alloc(psig, m, "str.replace_re_all", 1, 3, seqAreAseqA, seqA);
    m_sigs[OP_SEQ_REPLACE_RE]    = alloc(psig, m, "str.replace_re", 1, 3, seqAreAseqA, seqA);
    m_sigs[OP_SEQ_REPLACE_ALL]   = alloc(psig, m, "str.replace_all", 1, 3, seqAseqAseqA, seqA);
    m_sigs[OP_STRING_CONST]      = nullptr;
    m_sigs[_OP_STRING_STRIDOF]   = alloc(psig, m, "str.indexof", 0, 3, str2TintT, intT);
    m_sigs[_OP_STRING_STRREPL]   = alloc(psig, m, "str.replace", 0, 3, str3T, strT);
    m_sigs[_OP_STRING_FROM_CHAR] = alloc(psig, m, "char", 1, 0, nullptr, strT);
    m_sigs[OP_STRING_ITOS]       = alloc(psig, m, "str.from_int", 0, 1, &intT, strT);
    m_sigs[OP_STRING_STOI]       = alloc(psig, m, "str.to_int", 0, 1, &strT, intT);
    m_sigs[OP_STRING_LT]         = alloc(psig, m, "str.<", 0, 2, str2T, boolT);
    m_sigs[OP_STRING_LE]         = alloc(psig, m, "str.<=", 0, 2, str2T, boolT);
    m_sigs[OP_STRING_IS_DIGIT]   = alloc(psig, m, "str.is_digit", 0, 1, &strT, boolT);
    m_sigs[OP_STRING_TO_CODE]    = alloc(psig, m, "str.to_code", 0, 1, &strT, intT);
    m_sigs[OP_STRING_FROM_CODE]  = alloc(psig, m, "str.from_code", 0, 1, &intT, strT);
    m_sigs[_OP_STRING_CONCAT]    = alloc(psig, m, "str.++", 1, 2, str2T, strT);
    m_sigs[_OP_STRING_LENGTH]    = alloc(psig, m, "str.len", 0, 1, &strT, intT);
    m_sigs[_OP_STRING_STRCTN]    = alloc(psig, m, "str.contains", 0, 2, str2T, boolT);
    m_sigs[_OP_STRING_CHARAT]    = alloc(psig, m, "str.at", 0, 2, strTint2T, strT);
    m_sigs[_OP_STRING_PREFIX]    = alloc(psig, m, "str.prefixof", 0, 2, str2T, boolT);
    m_sigs[_OP_STRING_SUFFIX]    = alloc(psig, m, "str.suffixof", 0, 2, str2T, boolT);
    m_sigs[_OP_STRING_IN_REGEXP]  = alloc(psig, m, "str.in_re", 0, 2, strTreT, boolT);
    m_sigs[_OP_STRING_TO_REGEXP]  = alloc(psig, m, "str.to_re", 0, 1, &strT, reT);
    m_sigs[_OP_REGEXP_EMPTY]      = alloc(psig, m, "re.none", 0, 0, nullptr, reT);
    m_sigs[_OP_REGEXP_FULL_CHAR]  = alloc(psig, m, "re.allchar", 0, 0, nullptr, reT);
    m_sigs[_OP_STRING_SUBSTR]     = alloc(psig, m, "str.substr", 0, 3, strTint2T, strT);
}

sort* seq_decl_plugin::mk_reglan() {
    if (!m_reglan) {
        ast_manager& m = *m_manager;
        parameter paramS(m_string);
        m_reglan = m.mk_sort(symbol("RegEx"), sort_info(m_family_id, RE_SORT, 1, &paramS));
        m.inc_ref(m_reglan);
    }
    return m_reglan;
}

void seq_decl_plugin::set_manager(ast_manager* m, family_id id) {
    decl_plugin::set_manager(m, id);
    m_char_plugin = static_cast<char_decl_plugin*>(m_manager->get_plugin(m_manager->mk_family_id("char")));
    m_char = get_char_plugin().char_sort();
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
    case RE_SORT: {
        if (num_parameters != 1) {
            m.raise_exception("Invalid regex sort, expecting one parameter");
        }
        if (!parameters[0].is_ast() || !is_sort(parameters[0].get_ast())) {
            m.raise_exception("invalid regex sort, parameter is not a sort");
        }
        return m.mk_sort(symbol("RegEx"), sort_info(m_family_id, RE_SORT, num_parameters, parameters));
    }
    case _STRING_SORT:
        return m_string;
    case _REGLAN_SORT:
        return mk_reglan();
    default:
        UNREACHABLE();
        return nullptr;
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
    return mk_assoc_fun(k, arity, domain, range, k_seq, k_string, true);
}

func_decl* seq_decl_plugin::mk_left_assoc_fun(decl_kind k, unsigned arity, sort* const* domain, sort* range, decl_kind k_seq, decl_kind k_string) {
    return mk_assoc_fun(k, arity, domain, range, k_seq, k_string, false);
}

func_decl* seq_decl_plugin::mk_ubv2s(unsigned arity, sort* const* domain) {
    ast_manager& m = *m_manager;
    if (arity != 1)
        m.raise_exception("Invalid str.from_ubv expects one bit-vector argument");
    bv_util bv(m);
    if (!bv.is_bv_sort(domain[0]))
        m.raise_exception("Invalid str.from_ubv expects one bit-vector argument");
    sort* rng = m_string;
    return m.mk_func_decl(symbol("str.from_ubv"), arity, domain, rng, func_decl_info(m_family_id, OP_STRING_UBVTOS));    
}

func_decl* seq_decl_plugin::mk_assoc_fun(decl_kind k, unsigned arity, sort* const* domain, sort* range, decl_kind k_seq, decl_kind k_string, bool is_right) {
    ast_manager& m = *m_manager;
    sort_ref rng(m);
    if (arity == 0) {
        m.raise_exception("Invalid function application. At least one argument expected");
    }
    match_assoc(*m_sigs[k], arity, domain, range, rng);
    func_decl_info info(m_family_id, k_seq);
    if (is_right)
        info.set_right_associative(true);
    info.set_left_associative(true);
    return m.mk_func_decl(m_sigs[(rng == m_string)?k_string:k_seq]->m_name, rng, rng, rng, info);
}


func_decl * seq_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters,
                                          unsigned arity, sort * const * domain, sort * range) {
    init();
    m_has_seq = true;
    ast_manager& m = *m_manager;
    sort_ref rng(m);
    switch(k) {
    case OP_SEQ_EMPTY:
        match(*m_sigs[k], arity, domain, range, rng);
        if (rng == m_string) {
            parameter param(zstring(""));
            return mk_func_decl(OP_STRING_CONST, 1, &param, 0, nullptr, m_string);
        }
        else {
            parameter param(rng.get());
            func_decl_info info(m_family_id, k, 1, &param);
            return m.mk_func_decl(m_sigs[k]->m_name, arity, domain, rng, info);
        }

    case OP_RE_PLUS:
    case OP_RE_STAR:
    case OP_RE_OPTION:
    case OP_RE_RANGE:
    case OP_RE_OF_PRED:
    case OP_RE_COMPLEMENT:
    case OP_RE_REVERSE:
    case OP_RE_DERIVATIVE:
    case _OP_RE_ANTIMOROV_UNION:
        m_has_re = true;
        // fall-through
    case OP_SEQ_UNIT:
    case OP_STRING_ITOS:
    case OP_STRING_STOI:
    case OP_STRING_LT:
    case OP_STRING_LE:
    case OP_STRING_IS_DIGIT:
    case OP_STRING_TO_CODE:
    case OP_STRING_FROM_CODE:
        match(*m_sigs[k], arity, domain, range, rng);
        return m.mk_func_decl(m_sigs[k]->m_name, arity, domain, rng, func_decl_info(m_family_id, k));
    case OP_STRING_UBVTOS:
        return mk_ubv2s(arity, domain);        

    case _OP_REGEXP_FULL_CHAR:
        m_has_re = true;
        if (!range) range = mk_reglan();
        match(*m_sigs[k], arity, domain, range, rng);
        return m.mk_func_decl(symbol("re.allchar"), arity, domain, rng, func_decl_info(m_family_id, OP_RE_FULL_CHAR_SET));

    case OP_RE_FULL_CHAR_SET:
        m_has_re = true;
        if (!range) range = mk_reglan();
        if (range == mk_reglan()) {
            match(*m_sigs[k], arity, domain, range, rng);
            return m.mk_func_decl(symbol("re.allchar"), arity, domain, rng, func_decl_info(m_family_id, k));
        }
        return m.mk_func_decl(m_sigs[k]->m_name, arity, domain, range, func_decl_info(m_family_id, k));

    case OP_RE_FULL_SEQ_SET:
        m_has_re = true;
        if (!range) range = mk_reglan();
        return m.mk_func_decl(m_sigs[k]->m_name, arity, domain, range, func_decl_info(m_family_id, k));        

    case _OP_REGEXP_EMPTY:
        m_has_re = true;
        if (!range) range = mk_reglan();
        match(*m_sigs[k], arity, domain, range, rng);
        return m.mk_func_decl(symbol("re.none"), arity, domain, rng, func_decl_info(m_family_id, OP_RE_EMPTY_SET));

    case OP_RE_EMPTY_SET:
        m_has_re = true;
        if (!range) range = mk_reglan();
        if (range == mk_reglan()) {
            match(*m_sigs[k], arity, domain, range, rng);
            return m.mk_func_decl(symbol("re.none"), arity, domain, rng, func_decl_info(m_family_id, k));
        }
        return m.mk_func_decl(m_sigs[k]->m_name, arity, domain, range, func_decl_info(m_family_id, k));

    case OP_RE_LOOP:
        m_has_re = true;
        switch (arity) {
        case 1:
            match(*m_sigs[k], arity, domain, range, rng);
            if (num_parameters == 0 || num_parameters > 2 || !parameters[0].is_int() || (num_parameters == 2 && !parameters[1].is_int())) {
                m.raise_exception("Expecting two numeral parameters to function re-loop");
            }
            return m.mk_func_decl(m_sigs[k]->m_name, arity, domain, rng, func_decl_info(m_family_id, k, num_parameters, parameters));
        case 2:
            if (mk_reglan() != domain[0] || !arith_util(m).is_int(domain[1])) {
                m.raise_exception("Incorrect type of arguments passed to re.loop. Expecting regular expression and two integer parameters");
            }
            return m.mk_func_decl(m_sigs[k]->m_name, arity, domain, domain[0], func_decl_info(m_family_id, k, num_parameters, parameters));
        case 3:
            if (mk_reglan() != domain[0] || !arith_util(m).is_int(domain[1]) || !arith_util(m).is_int(domain[2])) {
                m.raise_exception("Incorrect type of arguments passed to re.loop. Expecting regular expression and two integer parameters");
            }
            return m.mk_func_decl(m_sigs[k]->m_name, arity, domain, domain[0], func_decl_info(m_family_id, k, num_parameters, parameters));
        default:
            m.raise_exception("Incorrect number of arguments passed to loop. Expected 1 regular expression and two integer parameters");
        }
    case OP_RE_POWER:
        m_has_re = true;
        if (num_parameters == 1 && parameters[0].is_int() && arity == 1 && parameters[0].get_int() >= 0) {
            rng = domain[0];
            return m.mk_func_decl(m_sigs[k]->m_name, arity, domain, rng, func_decl_info(m_family_id, k, num_parameters, parameters));
        }
        m.raise_exception("Incorrect arguments used for re.^. Expected one non-negative integer parameter");

    case OP_STRING_CONST:
        if (!(num_parameters == 1 && arity == 0 && parameters[0].is_zstring())) {
            m.raise_exception("invalid string declaration");
        }
        return m.mk_const_decl(m_stringc_sym, m_string,
                               func_decl_info(m_family_id, OP_STRING_CONST, num_parameters, parameters));

    case OP_RE_UNION:
    case OP_RE_CONCAT:
    case OP_RE_INTERSECT:
    case OP_RE_DIFF:
        m_has_re = true;
        return mk_left_assoc_fun(k, arity, domain, range, k, k);

    case OP_SEQ_REPLACE_RE_ALL:
    case OP_SEQ_REPLACE_RE:
        m_has_re = true;
    case OP_SEQ_REPLACE_ALL:
        return mk_str_fun(k, arity, domain, range, k);        

    case OP_SEQ_CONCAT:
        return mk_assoc_fun(k, arity, domain, range, k, _OP_STRING_CONCAT);

    case _OP_STRING_CONCAT:
        return mk_assoc_fun(k, arity, domain, range, OP_SEQ_CONCAT, k);

    case _OP_STRING_FROM_CHAR: {
        if (!(num_parameters == 1 && parameters[0].is_int())) 
            m.raise_exception("character literal expects integer parameter");
        zstring zs(parameters[0].get_int());        
        parameter p(zs);
        return m.mk_const_decl(m_stringc_sym, m_string,func_decl_info(m_family_id, OP_STRING_CONST, 1, &p));
    }
        
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
    case OP_SEQ_LAST_INDEX:
        if (arity != 2) {
            m.raise_exception("two arguments expected tin last_indexof");
        }
        else {
            return mk_seq_fun(k, arity, domain, range, OP_SEQ_LAST_INDEX);
        }
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
        m_has_re = true;
        return mk_seq_fun(k, arity, domain, range, _OP_STRING_TO_REGEXP);
    case _OP_STRING_TO_REGEXP:
        m_has_re = true;
        return mk_str_fun(k, arity, domain, range, OP_SEQ_TO_RE);

    case OP_SEQ_IN_RE:
        m_has_re = true;
        return mk_seq_fun(k, arity, domain, range, _OP_STRING_IN_REGEXP);
    case _OP_STRING_IN_REGEXP:
        m_has_re = true;
        return mk_str_fun(k, arity, domain, range, OP_SEQ_IN_RE);

    case OP_SEQ_AT:
        return mk_seq_fun(k, arity, domain, range, _OP_STRING_CHARAT);
    case _OP_STRING_CHARAT:
        return mk_str_fun(k, arity, domain, range, OP_SEQ_AT);

    case OP_SEQ_NTH:
    case OP_SEQ_NTH_I:
    case OP_SEQ_NTH_U:
        match(*m_sigs[k], arity, domain, range, rng);
        return m.mk_func_decl(m_sigs[k]->m_name, arity, domain, rng, func_decl_info(m_family_id, k));

    case OP_SEQ_EXTRACT:
        return mk_seq_fun(k, arity, domain, range, _OP_STRING_SUBSTR);
    case _OP_STRING_SUBSTR:
        return mk_str_fun(k, arity, domain, range, OP_SEQ_EXTRACT);

    case _OP_SEQ_SKOLEM: {
        if (num_parameters == 0 || !parameters[0].is_symbol()) {
            m.raise_exception("first parameter to skolem symbol should be a parameter");
        }
        symbol s = parameters[0].get_symbol();
        return m.mk_func_decl(s, arity, domain, range, func_decl_info(m_family_id, k, num_parameters, parameters));
    }
    default:
        UNREACHABLE();
        return nullptr;
    }
}

void seq_decl_plugin::get_op_names(svector<builtin_name> & op_names, symbol const & logic) {
    init();
    for (unsigned i = 0; i < m_sigs.size(); ++i) {
        if (m_sigs[i]) {
            op_names.push_back(builtin_name(m_sigs[i]->m_name.str(), i));
        }
    }
    op_names.push_back(builtin_name("str.in.re", _OP_STRING_IN_REGEXP));
    op_names.push_back(builtin_name("str.in-re", _OP_STRING_IN_REGEXP));
    op_names.push_back(builtin_name("str.to.re", _OP_STRING_TO_REGEXP));
    op_names.push_back(builtin_name("str.to-re", _OP_STRING_TO_REGEXP));
    op_names.push_back(builtin_name("str.to-int", OP_STRING_STOI));
    op_names.push_back(builtin_name("str.to.int", OP_STRING_STOI));
    op_names.push_back(builtin_name("str.from-int", OP_STRING_ITOS));
    op_names.push_back(builtin_name("int.to.str", OP_STRING_ITOS));
    op_names.push_back(builtin_name("re.nostr",  _OP_REGEXP_EMPTY));
    op_names.push_back(builtin_name("re.complement", OP_RE_COMPLEMENT));
    op_names.push_back(builtin_name("str.from_ubv", OP_STRING_UBVTOS));
}

void seq_decl_plugin::get_sort_names(svector<builtin_name> & sort_names, symbol const & logic) {
    init();
    sort_names.push_back(builtin_name("Seq",   SEQ_SORT));
    sort_names.push_back(builtin_name("RegEx", RE_SORT));

    // SMTLIB 2.6 RegLan, String
    sort_names.push_back(builtin_name("RegLan", _REGLAN_SORT));
    sort_names.push_back(builtin_name("String", _STRING_SORT));

    // SMTLIB 2.5 compatibility
    sort_names.push_back(builtin_name("StringSequence", _STRING_SORT));
}

app* seq_decl_plugin::mk_string(zstring const& s) {
    parameter param(s);
    func_decl* f = m_manager->mk_const_decl(m_stringc_sym, m_string,
                                            func_decl_info(m_family_id, OP_STRING_CONST, 1, &param));
    return m_manager->mk_const(f);
}

app* seq_decl_plugin::mk_char(unsigned u) {
    return get_char_plugin().mk_char(u);
}

bool seq_decl_plugin::is_considered_uninterpreted(func_decl * f) {
    seq_util util(*m_manager);
    return util.str.is_nth_u(f);
}

bool seq_decl_plugin::is_unique_value(app* e) const {
    return false;
}

bool seq_decl_plugin::is_value(app* e) const {
    while (true) {
        if (is_app_of(e, m_family_id, OP_SEQ_EMPTY)) 
            return true;
        if (is_app_of(e, m_family_id, OP_STRING_CONST)) 
            return true;
        if (is_app_of(e, m_family_id, OP_SEQ_UNIT) &&
            m_manager->is_value(e->get_arg(0))) 
            return true;
        if (is_app_of(e, m_family_id, OP_SEQ_CONCAT)) {
            bool first = true;
            for (expr* arg : *e) {
                if (first) {
                    first = false;
                }
                else if (is_app(arg) && !is_value(to_app(arg))) {
                    return false;
                }
            }
            if (!is_app(e->get_arg(0))) return false;            
            e = to_app(e->get_arg(0));
            continue;
        }
        return false;
    }
}

bool seq_decl_plugin::are_equal(app* a, app* b) const {
    if (a == b) return true;
    // handle concatenations
    return false;
}

bool seq_decl_plugin::are_distinct(app* a, app* b) const {
    if (a == b) 
        return false;
    if (is_app_of(a, m_family_id, OP_STRING_CONST) &&
        is_app_of(b, m_family_id, OP_STRING_CONST)) 
        return true;
    if (is_app_of(a, m_family_id, OP_SEQ_UNIT) && 
        is_app_of(b, m_family_id, OP_SEQ_UNIT)) 
        return m_manager->are_distinct(a->get_arg(0), b->get_arg(0));
    if (is_app_of(a, m_family_id, OP_SEQ_EMPTY) && 
        is_app_of(b, m_family_id, OP_SEQ_UNIT)) 
        return true;
    if (is_app_of(b, m_family_id, OP_SEQ_EMPTY) && 
        is_app_of(a, m_family_id, OP_SEQ_UNIT)) 
        return true;
    return false;
}


expr* seq_decl_plugin::get_some_value(sort* s) {
    seq_util util(*m_manager);
    if (util.is_seq(s)) {
        return util.str.mk_empty(s);
    }
    sort* seq;
    if (util.is_re(s, seq)) {
        return util.re.mk_to_re(util.str.mk_empty(seq));
    }
    UNREACHABLE();
    return nullptr;
}


app* seq_util::mk_skolem(symbol const& name, unsigned n, expr* const* args, sort* range) {
    SASSERT(range);    
    parameter param(name);
    func_decl* f = m.mk_func_decl(get_family_id(), _OP_SEQ_SKOLEM, 1, &param, n, args, range);
    return m.mk_app(f, n, args);
}

app* seq_util::str::mk_string(zstring const& s) const { 
    return u.seq.mk_string(s); 
}

app* seq_util::str::mk_char(zstring const& s, unsigned idx) const {
    return u.mk_char(s[idx]);
}

app* seq_util::str::mk_char(unsigned ch) const {
    return u.mk_char(ch);
}

app* seq_util::str::mk_char_bit(expr* e, unsigned idx) {
    return u.mk_char_bit(e, idx);
}

app* seq_util::mk_char_bit(expr* e, unsigned i) {
    parameter params[2] = { parameter(symbol("char.bit")), parameter(i) };
    sort* range = m.mk_bool_sort();
    func_decl* f = m.mk_func_decl(get_family_id(), _OP_SEQ_SKOLEM, 2, params, 1, &e, range);
    return m.mk_app(f, 1, &e);
}

unsigned seq_util::max_plus(unsigned x, unsigned y) const {
    if (x + y < x || x + y < y)
        return UINT_MAX;
    return x + y;
}

unsigned seq_util::max_mul(unsigned x, unsigned y) const {
    uint64_t r = ((uint64_t)x)*((uint64_t)y);
    return (r > UINT_MAX) ? UINT_MAX : (unsigned)r;
}


bool seq_util::is_const_char(expr* e, unsigned& c) const {
    return ch.is_const_char(e, c);
}

bool seq_util::is_char_le(expr const* e) const {
    return ch.is_le(e);
}

bool seq_util::is_char2int(expr const* e) const {
    return ch.is_to_int(e);
}

app* seq_util::mk_char(unsigned ch) const {
    return seq.mk_char(ch);
}

app* seq_util::mk_le(expr* ch1, expr* ch2) const {
    return ch.mk_le(ch1, ch2);
}

app* seq_util::mk_lt(expr* ch1, expr* ch2) const {
    return m.mk_not(mk_le(ch2, ch1));
}

bool seq_util::str::is_string(func_decl const* f, zstring& s) const {
    if (is_string(f)) {
        s = f->get_parameter(0).get_zstring();
        return true;
    }
    else {
        return false;
    }
}

bool seq_util::str::is_string(expr const* n, zstring& s) const {
    return is_app(n) && is_string(to_app(n)->get_decl(), s);
}

bool seq_util::str::is_nth_i(expr const* n, expr*& s, unsigned& idx) const {
    expr* i = nullptr;
    if (!is_nth_i(n, s, i)) return false;
    return arith_util(m).is_unsigned(i, idx);
}

app* seq_util::str::mk_nth_i(expr* s, unsigned i) const {
    return mk_nth_i(s, arith_util(m).mk_int(i));
}

void seq_util::str::get_concat(expr* e, expr_ref_vector& es) const {
    expr* e1, *e2;
    while (is_concat(e, e1, e2)) {
        get_concat(e1, es);
        e = e2;
    }
    if (!is_empty(e)) {
        es.push_back(e);
    }
}

void seq_util::str::get_concat_units(expr* e, expr_ref_vector& es) const {
    expr* e1, *e2;
    while (is_concat(e, e1, e2)) {
        get_concat_units(e1, es);
        e = e2;
    }
    zstring s;
    if (is_string(e, s)) {
        unsigned sz = s.length();
        for (unsigned j = 0; j < sz; ++j) {
            es.push_back(mk_unit(mk_char(s, j)));
        }        
    }
    else if (!is_empty(e)) {
        es.push_back(e);
    }
}

app* seq_util::str::mk_is_empty(expr* s) const {
    return m.mk_eq(s, mk_empty(s->get_sort()));
}



unsigned seq_util::str::min_length(expr* s) const {
    SASSERT(u.is_seq(s));
    unsigned result = 0;
    expr* s1 = nullptr, *s2 = nullptr;
    auto get_length = [&](expr* s1) {
        zstring st;
        if (is_unit(s1))
            return 1u;
        else if (is_string(s1, st))
            return st.length();
        else
            return 0u;
    };
    while (is_concat(s, s1, s2)) {
        result += get_length(s1);
        s = s2;
    }
    result += get_length(s);
    return result;
}

unsigned seq_util::str::max_length(expr* s) const {
    SASSERT(u.is_seq(s));
    unsigned result = 0;
    expr* s1 = nullptr, *s2 = nullptr, *s3 = nullptr;
    unsigned n = 0;
    zstring st;
    auto get_length = [&](expr* s1) {
        if (is_empty(s1))
            return 0u;
        else if (is_unit(s1))
            return 1u;
        else if (is_at(s1))
            return 1u;
        else if (is_extract(s1, s1, s2, s3)) 
            return (arith_util(m).is_unsigned(s3, n)) ? n : UINT_MAX;
        else if (is_string(s1, st))
            return st.length();
        else
            return UINT_MAX;
    };
    while (is_concat(s, s1, s2)) {
        result = u.max_plus(get_length(s), result);
        s = s2;
    }
    result = u.max_plus(get_length(s), result);
    return result;
}

unsigned seq_util::rex::min_length(expr* r) const {
    SASSERT(u.is_re(r));
    return get_info(r).min_length;
}

unsigned seq_util::rex::max_length(expr* r) const {
    SASSERT(u.is_re(r));
    expr* r1 = nullptr, *r2 = nullptr, *s = nullptr;
    unsigned lo = 0, hi = 0;
    if (is_empty(r))
        return 0;
    if (is_concat(r, r1, r2))
        return u.max_plus(max_length(r1), max_length(r2));
    if (is_union(r, r1, r2) || m.is_ite(r, s, r1, r2))
        return std::max(max_length(r1), max_length(r2));
    if (is_intersection(r, r1, r2))
        return std::min(max_length(r1), max_length(r2));
    if (is_diff(r, r1, r2) || is_reverse(r, r1) || is_opt(r, r1))
        return max_length(r1);
    if (is_loop(r, r1, lo, hi))
        return u.max_mul(hi, max_length(r1));
    if (is_to_re(r, s))
        return u.str.max_length(s);
    if (is_range(r) || is_of_pred(r) || is_full_char(r))
        return 1;
    // Else: star, plus, complement, full_seq, loop(r,r1,lo), derivative
    return UINT_MAX;
}

sort* seq_util::rex::to_seq(sort* re) {
    (void)u;
    SASSERT(u.is_re(re));
    return to_sort(re->get_parameter(0).get_ast());
}

app* seq_util::rex::mk_loop(expr* r, unsigned lo) {
    parameter param(lo);
    return m.mk_app(m_fid, OP_RE_LOOP, 1, &param, 1, &r);
}

app* seq_util::rex::mk_loop(expr* r, unsigned lo, unsigned hi) {
    parameter params[2] = { parameter(lo), parameter(hi) };
    return m.mk_app(m_fid, OP_RE_LOOP, 2, params, 1, &r);
}

app* seq_util::rex::mk_loop(expr* r, expr* lo) {
    expr* rs[2] = { r, lo };
    return m.mk_app(m_fid, OP_RE_LOOP, 0, nullptr, 2, rs);
}

app* seq_util::rex::mk_loop(expr* r, expr* lo, expr* hi) {
    expr* rs[3] = { r, lo, hi };
    return m.mk_app(m_fid, OP_RE_LOOP, 0, nullptr, 3, rs);
}

app* seq_util::rex::mk_full_char(sort* s) {
    return m.mk_app(m_fid, OP_RE_FULL_CHAR_SET, 0, nullptr, 0, nullptr, s);
}

app* seq_util::rex::mk_full_seq(sort* s) {
    return m.mk_app(m_fid, OP_RE_FULL_SEQ_SET, 0, nullptr, 0, nullptr, s);
}

app* seq_util::rex::mk_empty(sort* s) {    
    return m.mk_app(m_fid, OP_RE_EMPTY_SET, 0, nullptr, 0, nullptr, s);
}

app* seq_util::rex::mk_of_pred(expr* p) {
    return m.mk_app(m_fid, OP_RE_OF_PRED, 0, nullptr, 1, &p);
}

bool seq_util::rex::is_loop(expr const* n, expr*& body, unsigned& lo, unsigned& hi) const {
    if (is_loop(n)) {
        app const* a = to_app(n);
        if (a->get_num_args() == 1 && a->get_decl()->get_num_parameters() == 2) {
            body = a->get_arg(0);
            lo = a->get_decl()->get_parameter(0).get_int();
            hi = a->get_decl()->get_parameter(1).get_int();
            return true;
        }
    }
    return false;
}

bool seq_util::rex::is_loop(expr const* n, expr*& body, unsigned& lo) const {
    if (is_loop(n)) {
        app const* a = to_app(n);
        if (a->get_num_args() == 1 && a->get_decl()->get_num_parameters() == 1) {
            body = a->get_arg(0);
            lo = a->get_decl()->get_parameter(0).get_int();
            return true;
        }
    }
    return false;
}

bool seq_util::rex::is_loop(expr const* n, expr*& body, expr*& lo, expr*& hi) const {
    if (is_loop(n)) {
        app const* a = to_app(n);
        if (a->get_num_args() == 3) {
            body = a->get_arg(0);
            lo = a->get_arg(1);
            hi = a->get_arg(2);
            return true;
        }
    }
    return false;
}

bool seq_util::rex::is_loop(expr const* n, expr*& body, expr*& lo) const {
    if (is_loop(n)) {
        app const* a = to_app(n);
        if (a->get_num_args() == 2) {
            body = a->get_arg(0);
            lo = a->get_arg(1);
            return true;
        }
    }
    return false;
}

/**
   Returns true iff e is the epsilon regex.
 */
bool seq_util::rex::is_epsilon(expr* r) const {
    expr* s;
    return is_to_re(r, s) && u.str.is_empty(s);
}
/**
   Makes the epsilon regex for a given sequence sort.
 */
app* seq_util::rex::mk_epsilon(sort* seq_sort) {
    return mk_to_re(u.str.mk_empty(seq_sort));
}

/*
  Produces compact view of concrete concatenations such as (abcd).
*/
std::ostream& seq_util::rex::pp::compact_helper_seq(std::ostream& out, expr* s) const {
    SASSERT(re.u.is_seq(s));
    if (re.u.str.is_empty(s))
        out << "()";
    else if (re.u.str.is_unit(s))
        seq_unit(out, s);
    else if (re.u.str.is_concat(s)) {
        expr_ref_vector es(re.m);
        re.u.str.get_concat(s, es);
        for (expr* e : es)
            compact_helper_seq(out, e);
    }
    //using braces to indicate 'full' output
    //for example an uninterpreted constant X will be printed as {X}
    //while a unit sequence "X" will be printed as X
    //thus for example (concat "X" "Y" Z "W") where Z is uninterpreted is printed as XY{Z}W
    else out << "{" << mk_pp(s, re.m) << "}";
    return out;
}

/*
  Produces output such as [a-z] for a range.
*/
std::ostream& seq_util::rex::pp::compact_helper_range(std::ostream& out, expr* s1, expr* s2) const {
    out << "[";
    seq_unit(out, s1) << "-";
    seq_unit(out, s2) << "]";
    return out;
}

/*
  Checks if parenthesis can be omitted in some cases in a loop body or in complement.
*/
bool seq_util::rex::pp::can_skip_parenth(expr* r) const {
    expr* s;
    return ((re.is_to_re(r, s) && re.u.str.is_unit(s)) || re.is_range(r) || re.is_empty(r) || re.is_epsilon(r) || re.is_full_char(r));
}

/*
  Specialize output for a unit sequence converting to visible ASCII characters if possible.
*/
std::ostream& seq_util::rex::pp::seq_unit(std::ostream& out, expr* s) const {
    expr* e;
    unsigned n = 0;
    if (re.u.str.is_unit(s, e) && re.u.is_const_char(e, n)) {
        char c = (char)n;
        if (c == '\n')
            out << "\\n";
        else if (c == '\r')
            out << "\\r";
        else if (c == '\f')
            out << "\\f";
        else if (c == ' ')
            out << "\\s";
        else if (c == '(' || c == ')' || c == '{' || c == '}' || c == '[' || c == ']' || c == '.' || c == '\\')
            out << "\\" << c;
        else if (32 < n && n < 127) {
            if (html_encode) {
                if (c == '<')
                    out << "&lt;";
                else if (c == '>')
                    out << "&gt;";
                else if (c == '&')
                    out << "&amp;";
                else if (c == '\"')
                    out << "&quot;";
                else
                    out << "\\x" << std::hex << n;
            }
            else
                out << c;
        }
        else if (n <= 0xF)
            out << "\\x0" << std::hex << n;
        else if (n <= 0xFF)
            out << "\\x" << std::hex << n;
        else if (n <= 0xFFF)
            out << "\\u0" << std::hex << n;
        else 
            out << "\\u" << std::hex << n;
    }
    else
        out << "{" << mk_pp(s, re.m) << "}";
    return out;
}

/*
  Pretty prints the regex r into the out stream
*/
std::ostream& seq_util::rex::pp::display(std::ostream& out) const {
    expr* r1 = nullptr, * r2 = nullptr, * s = nullptr, * s2 = nullptr;
    unsigned lo = 0, hi = 0;
    if (re.is_full_char(e))
        return out << ".";
    else if (re.is_full_seq(e))
        return out << ".*";
    else if (re.is_to_re(e, s))
        return compact_helper_seq(out, s);
    else if (re.is_range(e, s, s2)) 
        return compact_helper_range(out, s, s2);
    else if (re.is_epsilon(e))
        return out << "()";
    else if (re.is_empty(e))
        return out << "[]";
    else if (re.is_concat(e, r1, r2)) 
        return out << pp(re, r1) << pp(re, r2);
    else if (re.is_union(e, r1, r2)) 
        return out << pp(re, r1) << "|" << pp(re, r2);
    else if (re.is_intersection(e, r1, r2)) 
        return out << "(" << pp(re, r1) << (html_encode ? ")&amp;(": ")&(" ) << pp(re, r2) << ")";
    else if (re.is_complement(e, r1)) {
        if (can_skip_parenth(r1))
            return out << "~" << pp(re, r1);
        else 
            return out << "~(" << pp(re, r1) << ")";
    }
    else if (re.is_plus(e, r1)) {
        if (can_skip_parenth(r1)) 
            return out << pp(re, r1) << "+";
        else 
            return out << "(" << pp(re, r1) << ")+";
    }
    else if (re.is_star(e, r1)) {
        if (can_skip_parenth(r1))
            return out << pp(re, r1) << "*";
        else
            return out << "(" << pp(re, r1) << ")*";
    }
    else if (re.is_loop(e, r1, lo)) {
        if (can_skip_parenth(r1))
            return out << pp(re, r1) << "{" << lo << ",}";
        else 
            return out << "(" << pp(re, r1) << "){" << lo << ",}";
    }
    else if (re.is_loop(e, r1, lo, hi)) {
        if (can_skip_parenth(r1)) {
            if (lo == hi)
                return out << pp(re, r1) << "{" << lo << "}";
            else 
                return out << pp(re, r1) << "{" << lo << "," << hi << "}";
        }
        else {
            if (lo == hi)
                return out << "(" << pp(re, r1) << "){" << lo << "}";
            else
                return out << "(" << pp(re, r1) << "){" << lo << "," << hi << "}";
        }
    }
    else if (re.is_diff(e, r1, r2)) 
        return out << "(" << pp(re, r1) << ")\\(" << pp(re, r2) << ")";
    else if (re.m.is_ite(e, s, r1, r2)) 
        return out << "if(" << mk_pp(s, re.m) << "," << pp(re, r1) << "," << pp(re, r2) << ")";
    else if (re.is_opt(e, r1)) {
        if (can_skip_parenth(r1)) 
            return out << pp(re, r1) << "?";
        else 
            return out << "(" << pp(re, r1) << ")?";
    }
    else if (re.is_reverse(e, r1)) 
        return out << "reverse(" << pp(re, r1) << ")";
    else
        // Else: derivative or is_of_pred
        return out << "{" << mk_pp(e, re.m) << "}";
}

/*
  Pretty prints the regex r into the output string
*/
std::string seq_util::rex::to_str(expr* r) const {
    std::ostringstream out;
    out << pp(u.re, r);
    return out.str();
}

/*
  Returns true iff info has been computed for the regex r
*/
bool seq_util::rex::has_valid_info(expr* r) const {
    return r->get_id() < m_infos.size() && m_infos[r->get_id()].is_valid();
}

/*
  Returns the info in the cache if the info is valid. Returns invalid_info otherwise.
*/
seq_util::rex::info seq_util::rex::get_cached_info(expr* e) const {
    if (has_valid_info(e))
        return m_infos[e->get_id()];
    else
        return invalid_info;
}

/*
  Get the information value associated with the regular expression e
*/
seq_util::rex::info seq_util::rex::get_info(expr* e) const
{
    SASSERT(u.is_re(e));
    auto result = get_cached_info(e);
    if (result.is_valid())
        return result;
    m_info_pinned.push_back(e);
    return get_info_rec(e);
}

/*
  Gets the info value for the given regex e, possibly making a new info recursively over the structure of e.
*/
seq_util::rex::info seq_util::rex::get_info_rec(expr* e) const {
    auto result = get_cached_info(e);
    if (result.is_valid())
        return result;
    if (!is_app(e))
        result = unknown_info;
    else 
        result = mk_info_rec(to_app(e));
    m_infos.setx(e->get_id(), result, invalid_info);
    STRACE("re_info", tout << "compute_info(" << pp(u.re, e) << ")=" << result << std::endl;);
    return result;
}

/*
  Computes the info value for the given regex e recursively over the structure of e.
  The regex e does not yet have an entry in the cache.
*/
seq_util::rex::info seq_util::rex::mk_info_rec(app* e) const {
    info i1, i2;
    lbool nullable(l_false);
    unsigned min_length(0), lower_bound(0), upper_bound(UINT_MAX);
    bool is_value(false);
    if (e->get_family_id() == u.get_family_id()) {
        switch (e->get_decl()->get_decl_kind()) {
        case OP_RE_EMPTY_SET:
            return info(true, true, true, true, true, true, false, l_false, UINT_MAX, 0);
        case OP_RE_FULL_SEQ_SET:
            return info(true, true, true, true, true, true, false, l_true, 0, 1);
        case OP_RE_STAR:
            i1 = get_info_rec(e->get_arg(0));
            return i1.star();
        case OP_RE_OPTION:
            i1 = get_info_rec(e->get_arg(0));
            return i1.opt();
        case OP_RE_RANGE: 
        case OP_RE_FULL_CHAR_SET:
        case OP_RE_OF_PRED:
            //TBD: check if the character predicate contains uninterpreted symbols or is nonground or is unsat
            //TBD: check if the range is unsat
            return info(true, true, true, true, true, true, true, l_false, 1, 0);
        case OP_RE_CONCAT:
            i1 = get_info_rec(e->get_arg(0));
            i2 = get_info_rec(e->get_arg(1));
            return i1.concat(i2, u.re.is_concat(e->get_arg(0)));
        case OP_RE_UNION:
            i1 = get_info_rec(e->get_arg(0));
            i2 = get_info_rec(e->get_arg(1));
            return i1.disj(i2);
        case OP_RE_INTERSECT:
            i1 = get_info_rec(e->get_arg(0));
            i2 = get_info_rec(e->get_arg(1));
            return i1.conj(i2);
        case OP_SEQ_TO_RE:
            min_length = u.str.min_length(e->get_arg(0));
            is_value = m.is_value(e->get_arg(0));
            nullable = (is_value && min_length == 0 ? l_true : (min_length > 0 ? l_false : l_undef));
            return info(true, true, is_value, true, true, true, (min_length == 1 && u.str.max_length(e->get_arg(0)) == 1), nullable, min_length, 0);
        case OP_RE_REVERSE:
            return get_info_rec(e->get_arg(0));
        case OP_RE_PLUS:
            i1 = get_info_rec(e->get_arg(0));
            return i1.plus();
        case OP_RE_COMPLEMENT:
            i1 = get_info_rec(e->get_arg(0));
            return i1.complement();
        case OP_RE_LOOP:
            i1 = get_info_rec(e->get_arg(0));
            if (e->get_decl()->get_num_parameters() >= 1)
                lower_bound = e->get_decl()->get_parameter(0).get_int();
            if (e->get_decl()->get_num_parameters() == 2)
                upper_bound = e->get_decl()->get_parameter(1).get_int();
            return i1.loop(lower_bound, upper_bound);
        case OP_RE_DIFF:
            i1 = get_info_rec(e->get_arg(0));
            i2 = get_info_rec(e->get_arg(1));
            return i1.diff(i2);
        }
        return unknown_info;
    }
    expr* c, * t, * f;
    if (u.m.is_ite(e, c, t, f)) {
        i1 = get_info_rec(t);
        i2 = get_info_rec(f);
        return i1.orelse(i2);
    }
    return unknown_info;
}

std::ostream& seq_util::rex::info::display(std::ostream& out) const {
    if (is_known()) {
        out << "info("
            << "nullable=" << (nullable == l_true ? "T" : (nullable == l_false ? "F" : "U")) << ", "
            << "classical=" << (classical ? "T" : "F") << ", "
            << "standard=" << (standard ? "T" : "F") << ", "
            << "nonbranching=" << (nonbranching ? "T" : "F") << ", "
            << "normalized=" << (normalized ? "T" : "F") << ", "
            << "monadic=" << (monadic ? "T" : "F") << ", "
            << "singleton=" << (singleton ? "T" : "F") << ", "
            << "min_length=" << min_length << ", "
            << "star_height=" << star_height << ")";
    }
    else if (is_valid())
        out << "UNKNOWN";
    else
        out << "INVALID";
    return out;
}

/*
  String representation of the info.
*/
std::string seq_util::rex::info::str() const {
    std::ostringstream out;
    display(out);
    return out.str();
}

seq_util::rex::info seq_util::rex::info::star() const {
    //if is_known() is false then all mentioned properties will remain false
    return seq_util::rex::info(classical, classical, interpreted, nonbranching, normalized, monadic, false, l_true, 0, star_height + 1);
}

seq_util::rex::info seq_util::rex::info::plus() const {
    if (is_known()) {
        //plus never occurs in a normalized regex
        return info(classical, classical, interpreted, nonbranching, false, monadic, false, nullable, min_length, star_height + 1);
    }
    else
        return *this;
}

seq_util::rex::info seq_util::rex::info::opt() const {
    // if is_known() is false then all mentioned properties will remain false
    // optional construct never occurs in a normalized regex
    return seq_util::rex::info(classical, classical, interpreted, nonbranching, false, monadic, false, l_true, 0, star_height);
}

seq_util::rex::info seq_util::rex::info::complement() const {
    if (is_known()) {
        lbool compl_nullable = (nullable == l_true ? l_false : (nullable == l_false ? l_true : l_undef));
        unsigned compl_min_length = (compl_nullable == l_false ? 1 : 0);
        return info(false, standard, interpreted, nonbranching, normalized, monadic, false, compl_nullable, compl_min_length, star_height);
    }
    else
        return *this;
}

seq_util::rex::info seq_util::rex::info::concat(seq_util::rex::info const& rhs, bool lhs_is_concat) const {
    if (is_known()) {
        if (rhs.is_known()) {
            unsigned m = min_length + rhs.min_length;
            if (m < min_length || m < rhs.min_length)
                m = UINT_MAX;
            return info(classical & rhs.classical,
                classical && rhs.classical, //both args of concat must be classical for it to be standard
                interpreted && rhs.interpreted,
                nonbranching && rhs.nonbranching,
                (normalized && !lhs_is_concat && rhs.normalized),
                monadic && rhs.monadic,
                false,
                ((nullable == l_false || rhs.nullable == l_false) ? l_false : ((nullable == l_true && rhs.nullable == l_true) ? l_true : l_undef)),
                m,
                std::max(star_height, rhs.star_height));
        }
        else
            return rhs;
    }
    else
        return *this;
}

seq_util::rex::info seq_util::rex::info::disj(seq_util::rex::info const& rhs) const {
    if (is_known() || rhs.is_known()) {
        //works correctly if one of the arguments is unknown
        return info(classical & rhs.classical,
            standard && rhs.standard,
            interpreted && rhs.interpreted,
            nonbranching && rhs.nonbranching,
            normalized && rhs.normalized,
            monadic && rhs.monadic,
            singleton && rhs.singleton,
            ((nullable == l_true || rhs.nullable == l_true) ? l_true : ((nullable == l_false && rhs.nullable == l_false) ? l_false : l_undef)),
            std::min(min_length, rhs.min_length),
            std::max(star_height, rhs.star_height));
    }
    else
        return rhs;
}

seq_util::rex::info seq_util::rex::info::conj(seq_util::rex::info const& rhs) const {
    if (is_known()) {
        if (rhs.is_known()) {
            return info(false,
                standard && rhs.standard,
                interpreted && rhs.interpreted,
                nonbranching && rhs.nonbranching,
                normalized && rhs.normalized,
                monadic && rhs.monadic,
                singleton && rhs.singleton,
                ((nullable == l_true && rhs.nullable == l_true) ? l_true : ((nullable == l_false || rhs.nullable == l_false) ? l_false : l_undef)),
                std::max(min_length, rhs.min_length),
                std::max(star_height, rhs.star_height));
        }
        else
            return rhs;
    }
    else
        return *this;
}

seq_util::rex::info seq_util::rex::info::diff(seq_util::rex::info const& rhs) const {
    if (is_known()) {
        if (rhs.is_known()) {
            return info(false,
                standard & rhs.standard,
                interpreted & rhs.interpreted,
                nonbranching & rhs.nonbranching,
                normalized & rhs.normalized,
                monadic & rhs.monadic,
                false,
                ((nullable == l_true && rhs.nullable == l_false) ? l_true : ((nullable == l_false || rhs.nullable == l_false) ? l_false : l_undef)),
                std::max(min_length, rhs.min_length),
                std::max(star_height, rhs.star_height));
        }
        else
            return rhs;
    }
    else
        return *this;
}

seq_util::rex::info seq_util::rex::info::orelse(seq_util::rex::info const& i) const {
    if (is_known()) {
        if (i.is_known()) {
            // unsigned ite_min_length = std::min(min_length, i.min_length);
            // lbool ite_nullable = (nullable == i.nullable ? nullable : l_undef);
            // TBD: whether ite is interpreted or not depends on whether the condition is interpreted and both branches are interpreted
            return info(false, false, false, false, normalized && i.normalized, monadic && i.monadic, singleton && i.singleton, nullable, std::min(min_length, i.min_length), std::max(star_height, i.star_height));
        }
        else
            return i;
    }
    else
        return *this;
}

seq_util::rex::info seq_util::rex::info::loop(unsigned lower, unsigned upper) const {
    if (is_known()) {
        unsigned m = min_length * lower;
        // Code review: this is not a complete overflow check. 
        if (m > 0 && (m < min_length || m < lower))
            m = UINT_MAX;
        lbool loop_nullable = (nullable == l_true || lower == 0 ? l_true : nullable);
        if (upper == UINT_MAX) {
            // this means the loop is r{lower,*} and is therefore not normalized
            // normalized regex would be r{lower,lower}r* and would in particular not use r{0,} for r*
            return info(classical, classical, interpreted, nonbranching, false, singleton, false, loop_nullable, m, star_height + 1);
        }
        else {
            bool loop_normalized = normalized;
            // r{lower,upper} is not normalized if r is nullable but lower > 0
            // r{0,1} is not normalized: it should be ()|r
            // r{1,1} is not normalized: it should be r
            // r{lower,upper} is not normalized if lower > upper it should then be [] (empty)
            if ((nullable == l_true && lower > 0) || upper == 1 || lower > upper)
                loop_normalized = false;
            return info(classical, classical, interpreted, nonbranching, loop_normalized, singleton, false, loop_nullable, m, star_height);
        }
    }
    else
        return *this;
}


