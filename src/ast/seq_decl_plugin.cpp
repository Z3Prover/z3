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
#include <sstream>

seq_decl_plugin::seq_decl_plugin(): m_init(false) {}

void seq_decl_plugin::finalize() {
    for (unsigned i = 0; i < m_sigs.size(); ++i) 
        dealloc(m_sigs[i]);
}

bool seq_decl_plugin::is_sort_param(sort* s, unsigned& idx) {
    return 
        s->get_name().is_numerical() &&
        (idx = s->get_name().get_num(), true);
}

bool seq_decl_plugin::match(ptr_vector<sort>& binding, sort* s, sort* sP) {
    if (s == sP) return true;
    unsigned i;
    if (is_sort_param(sP, i)) {
        if (binding.size() <= i) binding.resize(i+1);
        if (binding[i] && (binding[i] != s)) return false;
        binding[i] = s;
        return true;
    }
   
    if (s->get_family_id() == sP->get_family_id() &&
        s->get_decl_kind() == sP->get_decl_kind() &&
        s->get_name() == sP->get_name()) {
            SASSERT(s->get_num_parameters() == sP->get_num_parameters());
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
        return false;
    }
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
    parameter paramA(A);
    sort* seqA = m.mk_sort(m_family_id, SEQ_SORT, 1, &paramA);
    sort* reA  = m.mk_sort(m_family_id, RE_SORT, 1, &paramA);
    sort* seqAseqA[2] = { seqA, seqA };
    sort* seqAA[2] = { seqA, A };
    sort* seqAB[2] = { seqA, B };
    sort* seqAreA[2] = { seqA, reA };
    sort* AseqA[2] = { A, seqA };
    sort* reAreA[2] = { reA, reA };
    sort* AA[2] = { A, A };
    sort* seqABB[3] = { seqA, B, B };
    sort* boolT = m.mk_bool_sort();
    sort* intT  = arith_util(m).mk_int();
    sort* predA = array_util(m).mk_array_sort(A, boolT);
    m_sigs.resize(LAST_SEQ_OP);
    // TBD: have (par ..) construct and load parameterized signature from premable.
    m_sigs[OP_SEQ_UNIT]      = alloc(psig, m, "seq-unit",   1, 1, &A, seqA);
    m_sigs[OP_SEQ_EMPTY]     = alloc(psig, m, "seq-empty",  1, 0, 0, seqA); 
    m_sigs[OP_SEQ_CONCAT]    = alloc(psig, m, "seq-concat", 1, 2, seqAseqA, seqA);
    m_sigs[OP_SEQ_CONS]      = alloc(psig, m, "seq-cons",   1, 2, AseqA, seqA);
    m_sigs[OP_SEQ_REV_CONS]  = alloc(psig, m, "seq-rev-cons",   1, 2, seqAA, seqA);
    m_sigs[OP_SEQ_HEAD]      = alloc(psig, m, "seq-head",   1, 1, &seqA, A);
    m_sigs[OP_SEQ_TAIL]      = alloc(psig, m, "seq-tail",   1, 1, &seqA, seqA);
    m_sigs[OP_SEQ_LAST]      = alloc(psig, m, "seq-last",   1, 1, &seqA, A);
    m_sigs[OP_SEQ_FIRST]     = alloc(psig, m, "seq-first",  1, 1, &seqA, seqA);
    m_sigs[OP_SEQ_PREFIX_OF] = alloc(psig, m, "seq-prefix-of", 1, 2, seqAseqA, boolT);
    m_sigs[OP_SEQ_SUFFIX_OF] = alloc(psig, m, "seq-suffix-of", 1, 2, seqAseqA, boolT);
    m_sigs[OP_SEQ_SUBSEQ_OF] = alloc(psig, m, "seq-subseq-of", 1, 2, seqAseqA, boolT);
    m_sigs[OP_SEQ_EXTRACT]   = alloc(psig, m, "seq-extract", 2, 3, seqABB, seqA);
    m_sigs[OP_SEQ_NTH]       = alloc(psig, m, "seq-nth", 2, 2, seqAB, A);
    m_sigs[OP_SEQ_LENGTH]    = alloc(psig, m, "seq-length", 1, 1, &seqA, intT);
    m_sigs[OP_RE_PLUS]       = alloc(psig, m, "re-plus",    1, 1, &reA, reA);
    m_sigs[OP_RE_STAR]       = alloc(psig, m, "re-star",    1, 1, &reA, reA);
    m_sigs[OP_RE_OPTION]     = alloc(psig, m, "re-option",  1, 1, &reA, reA);
    m_sigs[OP_RE_RANGE]      = alloc(psig, m, "re-range",   1, 2, AA,  reA);
    m_sigs[OP_RE_CONCAT]     = alloc(psig, m, "re-concat",  1, 2, reAreA, reA);
    m_sigs[OP_RE_UNION]      = alloc(psig, m, "re-union",   1, 2, reAreA, reA);
    m_sigs[OP_RE_INTERSECT]  = alloc(psig, m, "re-intersect",   1, 2, reAreA, reA);
    m_sigs[OP_RE_DIFFERENCE] = alloc(psig, m, "re-difference",   1, 2, reAreA, reA);
    m_sigs[OP_RE_COMPLEMENT] = alloc(psig, m, "re-complement",   1, 1, &reA, reA);
    m_sigs[OP_RE_LOOP]       = alloc(psig, m, "re-loop",    1, 1, &reA, reA);
    m_sigs[OP_RE_EMPTY_SEQ]      = alloc(psig, m, "re-empty-seq", 1, 0, 0, reA);
    m_sigs[OP_RE_EMPTY_SET]    = alloc(psig, m, "re-empty-set", 1, 0, 0, reA);
    m_sigs[OP_RE_FULL_SET]    = alloc(psig, m, "re-full-set", 1, 0, 0, reA);
    m_sigs[OP_RE_OF_SEQ]     = alloc(psig, m, "re-of-seq",  1, 1, &seqA, reA);
    m_sigs[OP_RE_OF_PRED]    = alloc(psig, m, "re-of-pred", 1, 1, &predA, reA);
    m_sigs[OP_RE_MEMBER]     = alloc(psig, m, "re-member", 1, 2, seqAreA, boolT);
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
        return m.mk_sort(symbol("Seq"), sort_info(m_family_id, SEQ_SORT, num_parameters, parameters));
    case RE_SORT:
        if (num_parameters != 1) {
            m.raise_exception("Invalid regex sort, expecting one parameter");
        }
        if (!parameters[0].is_ast() || !is_sort(parameters[0].get_ast())) {
            m.raise_exception("invalid regex sort, parameter is not a sort");
        }
        return m.mk_sort(symbol("RegEx"), sort_info(m_family_id, RE_SORT, num_parameters, parameters));
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
    case OP_SEQ_CONCAT:
    case OP_SEQ_CONS:
    case OP_SEQ_REV_CONS:
    case OP_SEQ_HEAD:
    case OP_SEQ_TAIL:
    case OP_SEQ_LAST:
    case OP_SEQ_FIRST:
    case OP_SEQ_PREFIX_OF:
    case OP_SEQ_SUFFIX_OF:
    case OP_SEQ_SUBSEQ_OF:
    case OP_SEQ_LENGTH:
    case OP_RE_PLUS:
    case OP_RE_STAR:
    case OP_RE_OPTION:
    case OP_RE_RANGE:
    case OP_RE_CONCAT:
    case OP_RE_UNION:
    case OP_RE_INTERSECT:
    case OP_RE_DIFFERENCE:
    case OP_RE_COMPLEMENT:
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
    default:
        UNREACHABLE();
        return 0;
    }
}

void seq_decl_plugin::get_op_names(svector<builtin_name> & op_names, symbol const & logic) {
    init();
    for (unsigned i = 0; i < m_sigs.size(); ++i) {
        op_names.push_back(builtin_name(m_sigs[i]->m_name.str().c_str(), i));
    }
}

void seq_decl_plugin::get_sort_names(svector<builtin_name> & sort_names, symbol const & logic) {
    init();
    sort_names.push_back(builtin_name("Seq",   SEQ_SORT));
    sort_names.push_back(builtin_name("RegEx", RE_SORT));
}

bool seq_decl_plugin::is_value(app* e) const {
    // TBD: empty sequence is a value.
    return false;
}
