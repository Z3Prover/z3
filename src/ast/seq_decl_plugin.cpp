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
        TRACE("seq", tout << "setting binding @ " << i << " to " << mk_pp(s, m) << "\n";);
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
    TRACE("seq", 
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
    TRACE("seq", tout << mk_pp(range_out, m) << "\n";);
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
    sort* B = m.mk_uninterpreted_sort(symbol((unsigned)1));
    sort* strT = m_string;
    parameter paramA(A);
    parameter paramS(strT);
    sort* seqA = m.mk_sort(m_family_id, SEQ_SORT, 1, &paramA);
    sort* reA  = m.mk_sort(m_family_id, RE_SORT, 1, &paramA);
    sort* reT  = m.mk_sort(m_family_id, RE_SORT, 1, &paramS);
    sort* boolT = m.mk_bool_sort();
    sort* intT  = arith_util(m).mk_int();
    sort* predA = array_util(m).mk_array_sort(A, boolT);
    sort* u16T = 0;
    sort* u32T = 0;
    sort* seqAseqA[2] = { seqA, seqA };
    sort* seqAB[2] = { seqA, B };
    sort* seqAreA[2] = { seqA, reA };
    sort* reAreA[2] = { reA, reA };
    sort* AA[2] = { A, A };
    sort* seqABB[3] = { seqA, B, B };
    sort* str2T[2] = { strT, strT };
    sort* str3T[3] = { strT, strT, strT };
    sort* strTint2T[3] = { strT, intT, intT };
    sort* re2T[2] = { reT, reT };
    sort* strTreT[2] = { strT, reT };
    sort* str2TintT[3] = { strT, strT, intT };
    m_sigs.resize(LAST_SEQ_OP);
    // TBD: have (par ..) construct and load parameterized signature from premable.
    m_sigs[OP_SEQ_UNIT]      = alloc(psig, m, "seq.unit",   1, 1, &A, seqA);
    m_sigs[OP_SEQ_EMPTY]     = alloc(psig, m, "seq.empty",  1, 0, 0, seqA); 
    m_sigs[OP_SEQ_CONCAT]    = alloc(psig, m, "seq.++", 1, 2, seqAseqA, seqA);
    m_sigs[OP_SEQ_PREFIX_OF] = alloc(psig, m, "seq.prefixof", 1, 2, seqAseqA, boolT);
    m_sigs[OP_SEQ_SUFFIX_OF] = alloc(psig, m, "seq.suffixof", 1, 2, seqAseqA, boolT);
    m_sigs[OP_SEQ_SUBSEQ_OF] = alloc(psig, m, "seq-subseq-of", 1, 2, seqAseqA, boolT);
    m_sigs[OP_SEQ_EXTRACT]   = alloc(psig, m, "seq-extract", 2, 3, seqABB, seqA);
    m_sigs[OP_SEQ_NTH]       = alloc(psig, m, "seq-nth", 2, 2, seqAB, A);
    m_sigs[OP_SEQ_LENGTH]    = alloc(psig, m, "seq-length", 1, 1, &seqA, intT);
    m_sigs[OP_RE_PLUS]       = alloc(psig, m, "re.+",    1, 1, &reA, reA);
    m_sigs[OP_RE_STAR]       = alloc(psig, m, "re.*",    1, 1, &reA, reA);
    m_sigs[OP_RE_OPTION]     = alloc(psig, m, "re.opt",  1, 1, &reA, reA);
    m_sigs[OP_RE_RANGE]      = alloc(psig, m, "re.range",   1, 2, seqAseqA,  reA);
    m_sigs[OP_RE_CONCAT]     = alloc(psig, m, "re.++",  1, 2, reAreA, reA);
    m_sigs[OP_RE_UNION]      = alloc(psig, m, "re.union",   1, 2, reAreA, reA);
    m_sigs[OP_RE_INTERSECT]  = alloc(psig, m, "re.inter",   1, 2, reAreA, reA);
    m_sigs[OP_RE_LOOP]           = alloc(psig, m, "re-loop",    1, 1, &reA, reA);
    m_sigs[OP_RE_EMPTY_SEQ]      = alloc(psig, m, "re-empty-seq", 1, 0, 0, reA);
    m_sigs[OP_RE_EMPTY_SET]      = alloc(psig, m, "re-empty-set", 1, 0, 0, reA);
    m_sigs[OP_RE_FULL_SET]       = alloc(psig, m, "re-full-set", 1, 0, 0, reA);
    m_sigs[OP_RE_OF_SEQ]         = alloc(psig, m, "re-of-seq",  1, 1, &seqA, reA);
    m_sigs[OP_RE_OF_PRED]        = alloc(psig, m, "re-of-pred", 1, 1, &predA, reA);
    m_sigs[OP_RE_MEMBER]         = alloc(psig, m, "re-member", 1, 2, seqAreA, boolT);
    m_sigs[OP_STRING_CONST]      = 0;
    m_sigs[_OP_STRING_CONCAT]    = alloc(psig, m, "str.++", 1, 2, str2T, strT);
    m_sigs[OP_STRING_LENGTH]     = alloc(psig, m, "str.len", 0, 1, &strT, intT);
    m_sigs[OP_STRING_SUBSTR]     = alloc(psig, m, "str.substr", 0, 3, strTint2T, boolT);
    m_sigs[OP_STRING_STRCTN]     = alloc(psig, m, "str.contains", 0, 2, str2T, boolT);
    m_sigs[OP_STRING_CHARAT]     = alloc(psig, m, "str.at", 0, 2, strTint2T, strT);
    m_sigs[OP_STRING_STRIDOF]    = alloc(psig, m, "str.indexof", 0, 3, str2TintT, intT);
    m_sigs[OP_STRING_STRREPL]    = alloc(psig, m, "str.replace", 0, 3, str3T, strT);
    m_sigs[OP_STRING_PREFIX]     = alloc(psig, m, "str.prefixof", 0, 2, str2T, boolT);
    m_sigs[OP_STRING_SUFFIX]     = alloc(psig, m, "str.suffixof", 0, 2, str2T, boolT);
    m_sigs[OP_STRING_ITOS]       = alloc(psig, m, "int.to.str", 0, 1, &intT, strT);
    m_sigs[OP_STRING_STOI]       = alloc(psig, m, "str.to.int", 0, 1, &strT, intT);
    m_sigs[OP_STRING_IN_REGEXP]  = alloc(psig, m, "str.in.re", 0, 2, strTreT, boolT);
    m_sigs[OP_STRING_TO_REGEXP]  = alloc(psig, m, "str.to.re", 0, 1, &strT, reT);
    m_sigs[OP_REGEXP_LOOP]       = alloc(psig, m, "re.loop", 0, 2, strTint2T, reT); // maybe 3 arguments.
}

void seq_decl_plugin::set_manager(ast_manager* m, family_id id) {
    decl_plugin::set_manager(m, id);
    m_char = m->mk_sort(symbol("Char"), sort_info(m_family_id, CHAR_SORT, 0, (parameter const*)0));
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
    case STRING_SORT:
        return m_string;
    case CHAR_SORT:
        return m_char;
    default:
        UNREACHABLE();
        return 0;
    }
}

func_decl * seq_decl_plugin::mk_func_decl(decl_kind k, unsigned num_parameters, parameter const * parameters, 
                                          unsigned arity, sort * const * domain, sort * range) {
    init();
    ast_manager& m = *m_manager;
    sort_ref rng(m);
    switch(k) {
    case OP_SEQ_UNIT:
    case OP_SEQ_EMPTY:
    case OP_SEQ_PREFIX_OF:
    case OP_SEQ_SUFFIX_OF:
    case OP_SEQ_SUBSEQ_OF:
    case OP_SEQ_LENGTH:
    case OP_RE_PLUS:
    case OP_RE_STAR:
    case OP_RE_OPTION:
    case OP_RE_RANGE:
    case OP_RE_UNION:
    case OP_RE_EMPTY_SEQ:
    case OP_RE_EMPTY_SET:
    case OP_RE_OF_SEQ:   
    case OP_RE_OF_PRED:
    case OP_RE_MEMBER:
        match(*m_sigs[k], arity, domain, range, rng);
        return m.mk_func_decl(m_sigs[k]->m_name, arity, domain, rng, func_decl_info(m_family_id, k));
    case OP_SEQ_EXTRACT:
    case OP_SEQ_NTH:
        // TBD check numeric arguments for being BVs or integers.
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
        
    case OP_SEQ_CONCAT: {
        match_left_assoc(*m_sigs[k], arity, domain, range, rng);
        
        func_decl_info info(m_family_id, k);
        info.set_left_associative();
        if (rng == m_string) {
            return m.mk_func_decl(m_sigs[_OP_STRING_CONCAT]->m_name, rng, rng, rng, info);
        }
        return m.mk_func_decl(m_sigs[k]->m_name, rng, rng, rng, info);
    } 
    case OP_RE_CONCAT:  {
        match_left_assoc(*m_sigs[k], arity, domain, range, rng);
        func_decl_info info(m_family_id, k);
        info.set_left_associative();
        return m.mk_func_decl(m_sigs[k]->m_name, rng, rng, rng, info);
    }
    case _OP_STRING_CONCAT: {
        match_left_assoc(*m_sigs[k], arity, domain, range, rng);
        func_decl_info info(m_family_id, OP_SEQ_CONCAT);
        info.set_left_associative();
        return m.mk_func_decl(m_sigs[k]->m_name, rng, rng, rng, info);
    }

    case OP_STRING_LENGTH:
    case OP_STRING_SUBSTR:
    case OP_STRING_STRCTN:
    case OP_STRING_CHARAT:
    case OP_STRING_STRIDOF:
    case OP_STRING_STRREPL:
    case OP_STRING_PREFIX:
    case OP_STRING_SUFFIX:
    case OP_STRING_ITOS:
    case OP_STRING_STOI:
    case OP_STRING_IN_REGEXP:
    case OP_STRING_TO_REGEXP:
    case OP_REGEXP_LOOP:
        match(*m_sigs[k], arity, domain, range, rng);
        return m.mk_func_decl(m_sigs[k]->m_name, arity, domain, rng, func_decl_info(m_family_id, k));

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
    sort_names.push_back(builtin_name("String", STRING_SORT));
}

app* seq_decl_plugin::mk_string(symbol const& s) {
    parameter param(s);
    func_decl* f = m_manager->mk_const_decl(m_stringc_sym, m_string,
                                   func_decl_info(m_family_id, OP_STRING_CONST, 1, &param));
    return m_manager->mk_const(f);
}

bool seq_decl_plugin::is_value(app* e) const {
    return is_app_of(e, m_family_id, OP_STRING_CONST);
}

app* seq_util::str::mk_string(symbol const& s) {
    return u.seq.mk_string(s);
}

void seq_util::str::get_concat(expr* e, ptr_vector<expr>& es) const {
    expr* e1, *e2;
    while (is_concat(e, e1, e2)) {
        get_concat(e1, es);
        e = e2;
    }    
    es.push_back(e);
}
