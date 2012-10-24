/*++
Copyright (c) 2007 Microsoft Corporation

Module Name:

    Microsoft.Z3V3.cpp

Abstract:

    Z3 Managed API.

Author:

    Nikolaj Bjorner (nbjorner)
    Leonardo de Moura (leonardo) 2007-06-8

Notes:
    
--*/

//#include "stdafx.h"
#include "Microsoft.Z3V3.h"
#include "..\lib\util.h"
#include "..\lib\z3_private.h"
#include <sstream>
#include <strstream>
#include <vcclr.h>
#include "../lib/rational.h"
#include "../lib/z3_private.h"


using namespace System::Text;
using namespace Microsoft::Z3V3;

// -------------------------------
// ref_context

ref_context* ref_context::mk(Z3_context ctx, bool owned, bool scoped) { 
    return alloc(ref_context, ctx, owned, scoped); 
}

void ref_context::dec_ref() { 
    --m_count;
    if (0 == m_count) {
        if (m_owned) {
            if (m_dl) {
                Z3_fixedpoint_dec_ref(m_ctx, m_dl);
            }
            Z3_del_context(m_ctx); 
        }
        dealloc(this);
    }
}

void ref_context::inc_ref() { 
    ++m_count;
}

Z3_fixedpoint ref_context::dl() {
    if (!m_dl) {
        m_dl = Z3_mk_fixedpoint(m_ctx);
        Z3_fixedpoint_inc_ref(m_ctx, m_dl);
    }
    return m_dl;
}


// -------------------------------
// static functions


static std::string
CreateString(
    String^ string
    )
{
    std::string s;
    array<Byte>^ bytes = 
        Encoding::Convert(
            Encoding::Unicode, 
            Encoding::ASCII, 
            Encoding::Unicode->GetBytes(string)
            );

    for (int i = 0; i < bytes->Length; ++i) {
        s += bytes[i];
    }
    return s;
}

bool Z3Log::Open(String^ filename) {
    m_open = true;
    return Z3_TRUE == Z3_open_log(CreateString(filename).c_str());
}

void Z3Log::Append(String^ s) {
    Z3_append_log(CreateString(s).c_str());
}

void Z3Log::Close() {
    m_open = false;
    Z3_close_log();
}

template<class T>
class scoped_array {
public:
    scoped_array(unsigned length)
        : m_length(length),
          m_data(new T[length])
    {
    }

    scoped_array(array<T>^ a) 
    {
        m_length = a?a->Length:0;
        m_data = a?(new T[m_length]):0;
        for (unsigned i = 0; i < m_length; ++i) {
            m_data[i] = a[i];
        }
    }

    virtual ~scoped_array() {
        delete[] m_data;
    }

    T* c_ptr() { return m_data; }

    T const* c_ptr() const { return m_data; }

    T& operator[](int i) { return m_data[i]; }

    unsigned size() { return m_length; }
protected:
    unsigned m_length;
    T*       m_data;
};

template<typename T>
class scoped_Z3_ast_array : public scoped_array<T> {
public:
    scoped_Z3_ast_array(array<IntPtr>^ asts)
        : scoped_array((!asts)?0:asts->Length)
    {
        for (unsigned i = 0; i < m_length; ++i) {
            c_ptr()[i] = static_cast<T>(asts[i].ToPointer());
        }
    }
    scoped_Z3_ast_array(int length)
        : scoped_array(length) {}
};


class scoped_Z3_symbol_array : public scoped_array<Z3_symbol> {
public:
    scoped_Z3_symbol_array(array<Symbol^>^ symbols)
        : scoped_array((!symbols)?0:symbols->Length)
    {
        for (unsigned i = 0; i < m_length; ++i) {
            c_ptr()[i] = symbols[i]->get();
        }
    }

    scoped_Z3_symbol_array(Z3_context ctx, array<String^>^ symbols)
        : scoped_array((!symbols)?0:symbols->Length)
    {
        for (unsigned i = 0; i < m_length; ++i) {
            c_ptr()[i] = Z3_mk_string_symbol(ctx, CreateString(symbols[i]).c_str());
        }
    }

    scoped_Z3_symbol_array(unsigned n): scoped_array(n) {}
};

static void CopyFuncDecl(scoped_Z3_ast_array<Z3_func_decl>& src,
                         array<FuncDeclPtr>^ dst) {
    SASSERT(dst->Length == src.size());
    for (unsigned i = 0; i < src.size(); ++i) {
        dst[i] = FuncDeclPtr(src[i]);
    }
}

static array<TermPtr>^ MkArray(unsigned n, Z3_ast const* args) {
    array<TermPtr>^ result = gcnew array<TermPtr>(n);
    for (unsigned i = 0; i < n; ++i) {
        result[i] = TermPtr(args[i]);
    }
    return result;
}

static SearchFailureExplanation ConvertExplanation(Z3_search_failure f) {
    switch(f) {
    case Z3_NO_FAILURE:
        return SearchFailureExplanation::NoFailure;
    case Z3_UNKNOWN:
        return SearchFailureExplanation::Unknown;
    case Z3_TIMEOUT:
        return SearchFailureExplanation::TimeOut;
    case Z3_MEMOUT_WATERMARK:
        return SearchFailureExplanation::MemOut;
    case Z3_CANCELED:      
        return SearchFailureExplanation::UserCanceled;
    case Z3_NUM_CONFLICTS: 
        return SearchFailureExplanation::MaxConflicts;
    case Z3_THEORY: 
        return SearchFailureExplanation::Theory;
    case Z3_QUANTIFIERS: 
        return SearchFailureExplanation::Quantifiers;
    }
    return SearchFailureExplanation::Unknown;
}

//----------------------------------------
// Config

Config::Config() { m_config = Z3_mk_config(); }

Config::~Config() { 
    if (m_config) { 
        Z3_del_config(m_config); 
        m_config = 0;
    } 
}

Config::!Config() { 
    if (m_config) {
        if (RawContext::m_error_handler ) {
            RawContext::m_error_handler->Handler(ErrorCode::NonDisposedConfig);
        }
        else {
            verbose_stream() << "WARNING: configuration was not disposed\n";
        }
    }
}


void Config::SetParamValue(String^ param_id, String^ param_value) {    
    Z3_set_param_value(m_config, CreateString(param_id).c_str(), CreateString(param_value).c_str());
}


//----------------------------------------
// Model

RawModel::~RawModel() { 
    Reset();
}

RawModel::!RawModel() { 
    if (m_model) {
        if (RawContext::m_error_handler ) {
            RawContext::m_error_handler->Handler(ErrorCode::NonDisposedModel);
        }
        else {
            verbose_stream() << "WARNING: model was not disposed\n";
        }
    }
}

void RawModel::Reset() {
    if (m_model != 0) { 
        Z3_del_model(m_context(), m_model); 
        m_context.dec_ref();
        m_model = 0;
    } 
}

array<FuncDeclPtr>^ RawModel::GetModelConstants() {
    unsigned num_consts = Z3_get_model_num_constants(m_context(), m_model);
    array<FuncDeclPtr>^ result = gcnew array<FuncDeclPtr>(num_consts);
    for (unsigned i = 0; i < num_consts; ++i) {
        result[i] = FuncDeclPtr(Z3_get_model_constant(m_context(), m_model, i));
    }
    return result;
}


String^ RawContext::GetNumeralString(TermPtr v) {
    return gcnew String(Z3_get_numeral_string(ctx(), get_ast(v)));
}

int RawContext::GetNumeralInt(TermPtr v) {
    int result = 0;
    if (!Z3_get_numeral_int(ctx(), get_ast(v), &result)) {
        throw gcnew System::ArgumentException("Expecting value of integer type");
    }
    return result;
}

bool RawContext::TryGetNumeralInt(TermPtr v, int% i) {
    int result = 0;
    if (!Z3_get_numeral_int(ctx(), get_ast(v), &result)) {
        return false;
    }
    i = result;
    return true;
}

unsigned RawContext::GetNumeralUInt(TermPtr v) {
    unsigned result = 0;
    if (!Z3_get_numeral_uint(ctx(), get_ast(v), &result)) {
        throw gcnew System::ArgumentException("Expecting TermPtr of unsigned integer type");
    }
    return result;
}

bool RawContext::TryGetNumeralUInt(TermPtr v, unsigned% u) {
    unsigned result = 0;
    if (!Z3_get_numeral_uint(ctx(), get_ast(v), &result)) {
        return false;
    }
    u = result;
    return true;
}


__int64 RawContext::GetNumeralInt64(TermPtr v) {
    __int64 result = 0;
    if (!Z3_get_numeral_int64(ctx(), get_ast(v), &result)) {
        throw gcnew System::ArgumentException("Expecting value of signed 64 bit integer type");
    }
    return result;
}

bool RawContext::TryGetNumeralInt64(TermPtr v, __int64% i) {
    __int64 result = 0;
    if (!Z3_get_numeral_int64(ctx(), get_ast(v), &result)) {
        return false;
    }
    i = result;
    return true;
}


unsigned __int64 RawContext::GetNumeralUInt64(TermPtr v) {
    unsigned __int64 result = 0;
    if (!Z3_get_numeral_uint64(ctx(), get_ast(v), &result)) {
        throw gcnew System::ArgumentException("Expecting value of unsigned 64 bit integer type");
    }
    return result;
}

bool RawContext::TryGetNumeralUInt64(TermPtr v, unsigned __int64% u) {
    unsigned __int64 result = 0;
    if (!Z3_get_numeral_uint64(ctx(), get_ast(v), &result)) {
        return false;
    }
    u = result;
    return true;
}

bool RawContext::TryGetNumeral(TermPtr v, [Out] __int64% num, [Out] __int64% den) {
    __int64 _num, _den;
    if (!Z3_get_numeral_rational_int64(ctx(), get_ast(v), &_num, &_den)) {
        return false;
    }
    num = _num;
    den = _den;
    return true;
}


void RawContext::GetNumeral(TermPtr v, [Out] System::Numerics::BigInteger% num, [Out] System::Numerics::BigInteger% den) {
    rational r;
    if (!Z3_get_numeral_rational(ctx(), get_ast(v), r)) {
        Z3_error_handler(Z3_INVALID_ARG);
        return;
    }
    rational d = denominator(r);
    rational n = numerator(r);
    rational ten(10);
    bool is_neg = false;
    SASSERT(!d.is_neg());
    if (n.is_neg()) {
        is_neg = true;
        n = -n;
    }
    num = 0;
    System::Numerics::BigInteger mul = 1;
    while (n.is_pos()) {
        num += mul * mod(n,ten).get_unsigned();
        n = div(n,ten);
        mul *= 10;
    }
    if (is_neg) {
        num = -num;
    }
    den = 0;
    mul = 1;
    while (d.is_pos()) {
        den += mul * mod(d,ten).get_unsigned();
        d = div(d,ten);
        mul *= 10;
    }
}


LBool RawContext::GetBoolValue(TermPtr a) {
    switch (Z3_get_bool_value(ctx(), get_ast(a))) {
    case Z3_L_FALSE: return LBool::False;
    case Z3_L_UNDEF: return LBool::Undef;
    case Z3_L_TRUE:  return LBool::True;
    default:
        UNREACHABLE();
        return LBool::Undef;
    }
}


bool RawModel::TryGetArrayValue(TermPtr v, RawArrayValue^% av) {
    unsigned num_entries;
    if (!Z3_is_array_value(m_context(), m_model, get_ast(v), & num_entries)) {
        return false;
    }
    scoped_Z3_ast_array<Z3_ast> _indices(num_entries);
    scoped_Z3_ast_array<Z3_ast> _values(num_entries);
    Z3_ast else_value;
    Z3_get_array_value(m_context(), m_model, get_ast(v), num_entries, _indices.c_ptr(), _values.c_ptr(), &else_value);   
    av = gcnew RawArrayValue();
    av->Domain = gcnew array<TermPtr>(num_entries);
    av->Range = gcnew array<TermPtr>(num_entries);
    av->ElseCase = TermPtr(else_value);
    for (unsigned i = 0; i < num_entries; ++i) {
        av->Domain[i] = TermPtr(_indices[i]);
        av->Range[i] = TermPtr(_values[i]);
    }
    return true;
}

TermPtr RawContext::GetAssignments() {
    return TermPtr(Z3_get_context_assignment(ctx())); 
}


TermPtr RawContext::UpdateTerm(TermPtr t, array<TermPtr>^ new_args) {
    scoped_Z3_ast_array<Z3_ast> _new_args(new_args);
    return TermPtr(Z3_update_term(ctx(), get_ast(t), 
                                  _new_args.size(), _new_args.c_ptr()));
}

Dictionary<FuncDeclPtr, RawFunctionGraph^>^ RawModel::GetFunctionGraphs() {
    if (m_graphs) {
        return m_graphs;
    }
    SASSERT(m_model);
    unsigned _num_funs = Z3_get_model_num_funcs(m_context(), m_model);

    Dictionary<FuncDeclPtr, RawFunctionGraph^>^ graphs = 
        gcnew Dictionary<FuncDeclPtr, RawFunctionGraph^>();

    for (unsigned i = 0; i < _num_funs; ++i) {        
        unsigned num_entries = Z3_get_model_func_num_entries(m_context(), m_model, i);
        FuncDeclPtr decl = FuncDeclPtr(Z3_get_model_func_decl(m_context(), m_model, i));
        RawFunctionGraph^ graph = gcnew RawFunctionGraph();
        graphs[decl] = graph;
        graph->Declaration = decl;
        graph->Else = TermPtr(Z3_get_model_func_else(m_context(), m_model, i));
        graph->Entries = gcnew array<RawFunctionEntry^>(num_entries);

        for (unsigned j = 0; j < num_entries; ++j) {
            unsigned num_args = Z3_get_model_func_entry_num_args(m_context(), m_model, i, j);
            graph->Entries[j] = gcnew RawFunctionEntry();
            graph->Entries[j]->Arguments = gcnew array<TermPtr>(num_args);
            for (unsigned k = 0; k < num_args; ++k) {
                graph->Entries[j]->Arguments[k] = TermPtr(Z3_get_model_func_entry_arg(m_context(), m_model, i, j, k));
            }
            graph->Entries[j]->Result = TermPtr(Z3_get_model_func_entry_value(m_context(), m_model, i, j));
        }
    }
    m_graphs = graphs;
    return graphs;
}

TermPtr RawModel::Eval(TermPtr t) {
    Z3_ast v = 0;
    if (!Z3_eval(m_context(), m_model, get_ast(t), &v)) {
        return IntPtr::Zero; 
    }
    return TermPtr(v);
}

TermPtr RawModel::Eval(FuncDeclPtr decl, array<TermPtr>^ args) {
    Z3_ast v = 0;
    scoped_Z3_ast_array<Z3_ast> _args(args);
    
    if (!Z3_eval_decl(m_context(), m_model, get_func_decl(decl), 
                      _args.size(), _args.c_ptr(), &v)) {
        return IntPtr::Zero;
    }
    return TermPtr(v);
}

String^ RawModel::ToString() {
    return gcnew String(Z3_model_to_string(m_context(), m_model));
}

void RawModel::Display(System::IO::TextWriter^ w) {
    w->Write(ToString());
}

RawTheory^ RawContext::MkTheory(String^ name) {
    return gcnew RawTheory(*m_context, name);
}


void RawContext::RegisterRelation(FuncDeclPtr r) {
    Z3_fixedpoint_register_relation(ctx(), dl(), get_func_decl(r));
}

void RawContext::AddRule(TermPtr term, Symbol^ name) {
    Z3_fixedpoint_add_rule(ctx(), dl(), get_ast(term), name?name->get():0);
}

LBool RawContext::Query(TermPtr query) {
    switch(Z3_fixedpoint_query(ctx(), dl(), get_ast(query))) {
    case Z3_L_FALSE: return LBool::False;
    case Z3_L_TRUE:  return LBool::True;
    default: return LBool::Undef;
    }
}

String^ RawContext::GetQueryStatus() {
    return gcnew String(Z3_fixedpoint_get_reason_unknown(ctx(),dl()));
}

TermPtr RawContext::GetQueryAnswer() {
    return TermPtr(Z3_fixedpoint_get_answer(ctx(),dl()));
}

static void fixedpoint_assign_callback(void* c, Z3_func_decl f, unsigned n, Z3_ast const* _args, unsigned m, Z3_ast const* outs) {
    RawContext::fixedpoint_assign_callback(c, f, n, _args, m, outs);
}

static void fixedpoint_apply_callback(void* c, Z3_func_decl f, unsigned n, Z3_ast const* _args, Z3_ast* out) {
    RawContext::fixedpoint_apply_callback(c, f, n, _args, out);
}

void RawContext::init_fixedpoint_callbacks() {
    if (contexts == nullptr) {
        contexts = gcnew Dictionary<GCHandle, RawContext^>();
    }
    if (m_fixedpoint_gch == IntPtr::Zero) {        
        int id = contexts->Count;
        GCHandle h = GCHandle::Alloc(id, GCHandleType::Pinned);
        contexts[h] = this;
        m_fixedpoint_gch = GCHandle::ToIntPtr(h);        
        Z3_fixedpoint_init(ctx(), dl(), m_fixedpoint_gch.ToPointer());    
        Z3_fixedpoint_set_reduce_assign_callback(ctx(), dl(), ::fixedpoint_assign_callback);
        Z3_fixedpoint_set_reduce_app_callback(ctx(), dl(), ::fixedpoint_apply_callback);
    }
}


void RawContext::fixedpoint_assign_callback(void* ud, Z3_func_decl f, unsigned n, Z3_ast const* args, unsigned m, Z3_ast const* outs) {
    RawContext^ ctx = contexts[GCHandle::FromIntPtr(IntPtr(ud))];
    if (ctx->m_fixedpoint_assign != nullptr) {
        array<TermPtr>^ _args = MkArray(n, args);
        array<TermPtr>^ _outs = MkArray(m, outs);
        ctx->m_fixedpoint_assign(TermPtr(f), _args, _outs);
    }
}

void RawContext::fixedpoint_apply_callback(void* ud, Z3_func_decl f, unsigned n, Z3_ast const* args, Z3_ast* out) {
    RawContext^ ctx = contexts[GCHandle::FromIntPtr(IntPtr(ud))];
    if (ctx->m_fixedpoint_apply != nullptr) {
        array<TermPtr>^ _args = MkArray(n, args);
        TermPtr r = ctx->m_fixedpoint_apply(TermPtr(f), _args);
        if (out) *out = get_ast(r);
    }    
}

String^ RawContext::FixedpointToString(array<TermPtr>^ queries) {
    scoped_Z3_ast_array<Z3_ast> _queries(queries);
    return gcnew String(Z3_fixedpoint_to_string(
                            ctx(), dl(), 
                            _queries.size(), _queries.c_ptr()));
}

array<TermPtr>^ RawContext::SimplifyFixedpointRules(array<TermPtr>^ rules, array<FuncDeclPtr>^ output_predicates) {
    scoped_Z3_ast_array<Z3_ast> _rules(rules);
    scoped_Z3_ast_array<Z3_func_decl> _outputs(output_predicates);
    Z3_ast_vector new_rules = Z3_fixedpoint_simplify_rules(
        ctx(), dl(), _rules.size(), _rules.c_ptr(), 
        _outputs.size(), _outputs.c_ptr());
    unsigned num_rules = Z3_ast_vector_size(ctx(), new_rules);
    Z3_ast_vector_inc_ref(ctx(), new_rules);
    array<TermPtr>^ result = gcnew array<TermPtr>(num_rules);
    for (unsigned i = 0; i < num_rules; ++i) {
        result[i] = TermPtr(Z3_ast_vector_get(ctx(), new_rules, i));
    }
    Z3_ast_vector_dec_ref(ctx(), new_rules);
    return result;
}

//----------------------------------------
// RawContext

static void error_handler(Z3_context ctx, Z3_error_code c) {
    ErrorCode code;
    switch(c) {
    case Z3_OK: code = ErrorCode::Ok; break;
    case Z3_SORT_ERROR: code = ErrorCode::TypeError; break;
    case Z3_IOB: code = ErrorCode::IndexOutOfBounds; break;
    case Z3_INVALID_ARG: code = ErrorCode::InvalidArgument; break;
    case Z3_PARSER_ERROR: code = ErrorCode::ParserError; break;
    case Z3_NO_PARSER: code = ErrorCode::NoParser; break;
    case Z3_INVALID_PATTERN: code = ErrorCode::InvalidPattern; break;
    case Z3_MEMOUT_FAIL: throw gcnew OutOfMemoryException();
    case Z3_INTERNAL_FATAL: code = ErrorCode::InternalFatal; break;
    case Z3_INVALID_USAGE: code = ErrorCode::InvalidUsage; break;
    case Z3_FILE_ACCESS_ERROR: code = ErrorCode::FileAccessError; break;
    default:
        UNREACHABLE();
        code = ErrorCode::InvalidArgument; break;
    }
    if (RawContext::m_error_handler ) {
        RawContext::m_error_handler->Handler(code);
    }
    // we throw if you don't
    throw gcnew Z3Error(code);
}


// -----------------------------
// LabeledLiterals


LabeledLiterals::!LabeledLiterals() { 
    if (m_labels) {
        if (RawContext::m_error_handler ) {
            RawContext::m_error_handler->Handler(ErrorCode::NonDisposedLiterals);
        }
        else {
            verbose_stream() << "WARNING: labeled literals have not been disposed\n"; 
        }
    }
}

// -----------------------------
// RawTheory

void RawTheory::static_delete_callback(Z3_theory th)
{
    RawTheory^ theory = GetTheory(th);
    if (theory->delete_handler) {
        theory->delete_handler();
    }
    Z3_theory_data td = Z3_theory_get_ext_data(th);
    theories->Remove(GCHandle::FromIntPtr(IntPtr(td)));
    GCHandle::FromIntPtr(IntPtr(td)).Free();
}

static void static_delete_callback(Z3_theory th) {
    RawTheory::static_delete_callback(th);
}

RawTheory::RawTheory(ref_context& ctx, String^ name): m_context(ctx), m_name(name)
{
    if (!theories) theories = gcnew Dictionary<GCHandle, RawTheory^>();
    int id = theories->Count;
    GCHandle h = GCHandle::Alloc(id, GCHandleType::Pinned);
    theories[h] = this;
    IntPtr gch = GCHandle::ToIntPtr(h);
    m_theory = Z3_mk_theory(ctx(), CreateString(name).c_str(), gch.ToPointer());
    m_context.inc_ref();
    Z3_set_delete_callback(m_theory, ::static_delete_callback);
}

RawTheory::~RawTheory() {
    m_context.dec_ref();
}

Z3_bool RawTheory::reduce_eq_callback(Z3_theory th, Z3_ast a, Z3_ast b, Z3_ast* r) {
    RawTheory^ theory = GetTheory(th);
    TermPtr res = theory->reduce_eq(TermPtr(a), TermPtr(b));
    if (res != TermPtr::Zero) {
        *r = get_ast(res);
    }
    return res != TermPtr::Zero;
}

static Z3_bool reduce_eq_callback(Z3_theory th, Z3_ast a, Z3_ast b, Z3_ast* r) {
    return RawTheory::reduce_eq_callback(th, a, b, r);
}

void RawTheory::set_reduce_eq(Func2<TermPtr, TermPtr, TermPtr>^ value) {
    reduce_eq = value;
    Z3_set_reduce_eq_callback(m_theory, ::reduce_eq_callback);
}

Z3_bool RawTheory::reduce_app_callback(Z3_theory th, Z3_func_decl f, unsigned num_args, Z3_ast const args[], Z3_ast* r) {
    RawTheory^ theory = GetTheory(th);
    array<TermPtr>^ argv = MkArray(num_args, args);
    TermPtr res = theory->reduce_app(TermPtr(f), argv);
    if (r && res != TermPtr::Zero) {
        *r = get_ast(res);
    }
    return res != TermPtr::Zero;
}

static Z3_bool reduce_app_callback(Z3_theory th, Z3_func_decl f, unsigned num_args, Z3_ast const args[], Z3_ast* r) {
    return RawTheory::reduce_app_callback(th, f, num_args, args, r);
}

void RawTheory::set_reduce_app(Func2<FuncDeclPtr, array<TermPtr>^, TermPtr>^ value) {
    reduce_app = value;
    Z3_set_reduce_app_callback(m_theory, ::reduce_app_callback);
}

Z3_bool RawTheory::reduce_distinct_callback(Z3_theory th, unsigned n, Z3_ast const args[], Z3_ast* r) {
    RawTheory^ theory = GetTheory(th);
    TermPtr res = theory->reduce_distinct(MkArray(n, args));
    if (r && res != TermPtr::Zero) {
        *r = get_ast(res);
    }
    return res != TermPtr::Zero;
}

static Z3_bool reduce_distinct_callback(Z3_theory th, unsigned n, Z3_ast const args[], Z3_ast* r) {
    return RawTheory::reduce_distinct_callback(th, n, args, r);
}

void RawTheory::set_reduce_distinct(Func1<array<TermPtr>^, TermPtr>^ value) {
    reduce_distinct = value;
    Z3_set_reduce_distinct_callback(m_theory, ::reduce_distinct_callback);
}

static void new_relevant_callback(Z3_theory t, Z3_ast a) {
    RawTheory::GetTheory(t)->new_relevant(TermPtr(a));
}

void RawTheory::set_new_relevant(Action<TermPtr>^ value) {
    new_relevant = value;
    Z3_set_new_relevant_callback(m_theory, ::new_relevant_callback);
}

static void new_app_callback(Z3_theory t, Z3_ast a) {
    RawTheory::GetTheory(t)->new_app(TermPtr(a));
}

void RawTheory::set_new_app(Action<TermPtr>^ value) {
    new_app = value;
    Z3_set_new_app_callback(m_theory, ::new_app_callback);
}


static void new_elem_callback(Z3_theory t, Z3_ast a) {
    RawTheory::GetTheory(t)->new_elem(TermPtr(a));
}

void RawTheory::set_new_elem(Action<TermPtr>^ value) {
    new_elem = value;
    Z3_set_new_elem_callback(m_theory, ::new_elem_callback);
}

static void init_search_callback(Z3_theory t) {
    RawTheory::GetTheory(t)->init_search();
}

void RawTheory::set_init_search(Action0^ value) {
    init_search = value;
    Z3_set_init_search_callback(m_theory, ::init_search_callback);
}

static void push_callback(Z3_theory t) {
    RawTheory::GetTheory(t)->push();
}

void RawTheory::set_push(Action0^ value) {
    push = value;
    Z3_set_push_callback(m_theory, ::push_callback);
}


static void pop_callback(Z3_theory t) {
    RawTheory::GetTheory(t)->pop();
}

void RawTheory::set_pop(Action0^ value) {
    pop = value;
    Z3_set_pop_callback(m_theory, ::pop_callback);
}


static void reset_callback(Z3_theory t) {
    RawTheory::GetTheory(t)->reset();
}

void RawTheory::set_reset(Action0^ value) {
    reset = value;
    Z3_set_reset_callback(m_theory, ::reset_callback);
}


static void restart_callback(Z3_theory t) {
    RawTheory::GetTheory(t)->restart();
}

void RawTheory::set_restart(Action0^ value) {
    restart = value;
    Z3_set_restart_callback(m_theory, ::restart_callback);
}


static Z3_bool final_check_callback(Z3_theory t) {
    return RawTheory::GetTheory(t)->final_check();
}

void RawTheory::set_final_check(Func0<bool>^ value) {
    final_check = value;
    Z3_set_final_check_callback(m_theory, ::final_check_callback);
}

static void new_eq_callback(Z3_theory t, Z3_ast a, Z3_ast b) {
    RawTheory::GetTheory(t)->new_eq(TermPtr(a), TermPtr(b));
}

void RawTheory::set_new_eq(Action2<TermPtr, TermPtr>^ value) {
    new_eq = value;
    Z3_set_new_eq_callback(m_theory, ::new_eq_callback);
}


static void new_diseq_callback(Z3_theory t, Z3_ast a, Z3_ast b) {
    RawTheory::GetTheory(t)->new_diseq(TermPtr(a), TermPtr(b));
}

void RawTheory::set_new_diseq(Action2<TermPtr, TermPtr>^ value) {
    new_diseq = value;
    Z3_set_new_diseq_callback(m_theory, ::new_diseq_callback);
}

static void new_assignment_callback(Z3_theory t, Z3_ast a, Z3_bool b)
{
    RawTheory::GetTheory(t)->new_assignment(TermPtr(a), b?true:false);
}

void RawTheory::set_new_assignment(Action2<TermPtr, bool>^ value) {
    new_assignment = value;
    Z3_set_new_assignment_callback(m_theory, ::new_assignment_callback);
}

FuncDeclPtr RawTheory::MkFuncDecl(Symbol^ n, array<SortPtr>^ domain, SortPtr range) {
    scoped_Z3_ast_array<Z3_sort> _domain(domain);
    return FuncDeclPtr(Z3_theory_mk_func_decl(m_context(), m_theory, n->get(), 
                                              _domain.size(), _domain.c_ptr(), get_sort(range)));
}


SortPtr RawTheory::MkSort(String^ s) {
    return SortPtr(Z3_theory_mk_sort(m_context(), m_theory, Z3_mk_string_symbol(m_context(), CreateString(s).c_str())));
}
        
TermPtr RawTheory::MkValue(String^ s, SortPtr srt) {
    Z3_symbol sym = Z3_mk_string_symbol(m_context(), CreateString(s).c_str());
    return TermPtr(Z3_theory_mk_value(m_context(), m_theory, sym, get_sort(srt)));
}

TermPtr RawTheory::MkConstant(String^ s, SortPtr srt) {
    Z3_symbol sym = Z3_mk_string_symbol(m_context(), CreateString(s).c_str());
    return TermPtr(Z3_theory_mk_constant(m_context(), m_theory, sym, get_sort(srt)));
}

FuncDeclPtr RawTheory::MkFuncDecl(String^ s, array<SortPtr>^ domain, SortPtr range) {
    Z3_symbol sym = Z3_mk_string_symbol(m_context(), CreateString(s).c_str());
    scoped_Z3_ast_array<Z3_sort> _domain(domain);
    return FuncDeclPtr(Z3_theory_mk_func_decl(m_context(), m_theory, sym, 
                                              _domain.size(), _domain.c_ptr(), get_sort(range)));

}


// -----------------------------
// Constructor

Constructor::Constructor(
    ref_context& context,
    String^ name,
    String^ tester,
    array<String^>^  field_names,
    array<SortPtr>^  field_sorts,
    array<unsigned>^ field_refs
    ): 
    m_context(context),
    m_constructor(0),
    m_name(name),
    m_tester_name(tester),
    m_field_names(field_names),
    m_field_sorts(field_sorts),
    m_field_refs(field_refs),
    m_constructor_decl(FuncDeclPtr()),
    m_tester(FuncDeclPtr()),
    m_accessors(nullptr)
{
    m_context.inc_ref();
}


Z3_constructor Constructor::Get() 
{
    if (m_constructor) {
        return m_constructor;
    }
    Z3_symbol _name = Z3_mk_string_symbol(m_context(), CreateString(m_name).c_str());
    Z3_symbol _tester = Z3_mk_string_symbol(m_context(), CreateString(m_tester_name).c_str());
    unsigned num_fields = (!m_field_names)?0:m_field_names->Length;
    scoped_Z3_symbol_array _field_names(m_context(), m_field_names); 
    scoped_Z3_ast_array<Z3_sort> _field_sorts(m_field_sorts);
    scoped_array<unsigned> _field_refs(m_field_refs);
    SASSERT(_field_names.size() == _field_sorts.size());
    SASSERT(_field_names.size() == _field_refs.size());
    m_constructor = Z3_mk_constructor(m_context(), _name, _tester, num_fields, 
                                      _field_names.c_ptr(), _field_sorts.c_ptr(), _field_refs.c_ptr());
    return m_constructor;
}

Z3_constructor Constructor::Query() {
    Z3_constructor result = 0;
    if (!m_accessors) {
        SASSERT(m_constructor);
        result = m_constructor;
        unsigned num_fields = (!m_field_names)?0:m_field_names->Length;
        m_accessors = gcnew array<FuncDeclPtr>(num_fields);
        Z3_func_decl constructor_decl, tester_decl;
        scoped_array<Z3_func_decl> accs(num_fields);
        Z3_query_constructor(m_context(), 
                             m_constructor,
                             num_fields,
                             &constructor_decl,
                             &tester_decl,
                             accs.c_ptr());
        m_constructor_decl = FuncDeclPtr(constructor_decl);
        m_tester = FuncDeclPtr(tester_decl);
        for (unsigned i = 0; i < num_fields; ++i) {
            m_accessors[i] = FuncDeclPtr(accs[i]);
        }
        m_constructor = 0;
    }
    SASSERT(!m_constructor);
    return result;
}

Constructor::!Constructor() {
    SASSERT(!m_constructor);
}


Constructor::~Constructor() {
    SASSERT(!m_constructor); 
    m_context.dec_ref();
}


FuncDeclPtr Constructor::GetConstructor() {
    if (!m_constructor && !m_accessors) {
        throw gcnew Z3Error(ErrorCode::InvalidUsage);
    }
    Z3_constructor c = Query();
    SASSERT(!c);
    return FuncDeclPtr(m_constructor_decl);
}

FuncDeclPtr Constructor::GetTester() {
    if (!m_constructor && !m_accessors) {
        throw gcnew Z3Error(ErrorCode::InvalidUsage);
    }
    Z3_constructor c = Query();
    SASSERT(!c);
    return FuncDeclPtr(m_tester);
}

array<FuncDeclPtr>^ Constructor::GetAccessors() {
    if (!m_constructor && !m_accessors) {
        throw gcnew Z3Error(ErrorCode::InvalidUsage);
    }
    Z3_constructor c = Query();
    SASSERT(!c);
    return m_accessors;
}




// -----------------------------
// RawContext


void RawContext::Init() {
    m_disposed = false;
    s_nonempty = false;
    if (s_todec == nullptr) {
        s_todec = gcnew List<KeyValuePair<IntPtr, RawContext^> >();
        s_monitor = gcnew IntPtr(0);
    }
    Z3_set_error_handler(ctx(), error_handler);
}

RawContext::RawContext(Config^ config) { 
    m_context = ref_context::mk(Z3_mk_context(config->get()), true, true);
    Init();
}

RawContext::RawContext(Config^ config, ReferenceCounted^ rc) { 
    m_context = ref_context::mk(Z3_mk_context_rc(config->get()), true, false); 
    Init();
}

RawContext::RawContext() {
    m_context = ref_context::mk(Z3_mk_context(0), true, true);
    Init();
}

void RawContext::SetContext(Z3_context ctx) {
    Reset();
    m_context = ref_context::mk(ctx, false, true);
}

RawContext::!RawContext() { 
    if (!m_disposed) {
        if (RawContext::m_error_handler ) {
            RawContext::m_error_handler->Handler(ErrorCode::NonDisposedContext);
        }
        else {
            verbose_stream() << "WARNING: context was not disposed\n";
        }
    }
}


void
RawContext::Reset() {
    System::Threading::Monitor::Enter(s_monitor);
    if (!m_disposed) {
        m_context->dec_ref();
        m_disposed = true;
    } 
    System::Threading::Monitor::Exit(s_monitor);
}

RawContext::~RawContext() { 
    Reset();
}

#include "..\lib\vector.h"
#include "..\lib\trace.h"

void RawContext::EnableDebugTrace(String^ tag) {
    static vector<std::string*> pinned;
    std::string s = CreateString(tag);
    pinned.push_back(new std::string(s));
    enable_trace(pinned.back()->c_str());
}

void RawContext::ToggleWarningMessages(bool enabled) {
    Z3_toggle_warning_messages(enabled);
}

void RawContext::UpdateParamValue(String^ p, String^ v) {
    Z3_update_param_value(ctx(), CreateString(p).c_str(), CreateString(v).c_str());
}

String^ RawContext::GetParamValue(String^ p) {
    Z3_string vl = "";
    if (!Z3_get_param_value(ctx(), CreateString(p).c_str(), &vl)) {
        throw gcnew Z3Error(ErrorCode::InvalidArgument);
    }
    return gcnew String(vl);
}

bool RawContext::SetLogic(String^ l) {
    return Z3_TRUE == Z3_set_logic(ctx(), CreateString(l).c_str());
}

Symbol^ RawContext::MkSymbol(String^ s) {    
    return gcnew Symbol(ctx(), Z3_mk_string_symbol(ctx(), CreateString(s).c_str()));
}
Symbol^ RawContext::MkSymbol(int i) { 
    return gcnew Symbol(ctx(), Z3_mk_int_symbol(ctx(), i)); 
}        

SortPtr RawContext::MkSort(Symbol^ s) {
    return SortPtr(Z3_mk_uninterpreted_sort(ctx(), s->get()));
}

SortPtr RawContext::MkSort(String^ s) {
    return SortPtr(Z3_mk_uninterpreted_sort(ctx(), Z3_mk_string_symbol(ctx(), CreateString(s).c_str())));
}

SortPtr RawContext::MkSort(int i) {
    return SortPtr(Z3_mk_uninterpreted_sort(ctx(), Z3_mk_int_symbol(ctx(), i)));
}

SortPtr RawContext::MkBoolSort() { return SortPtr(Z3_mk_bool_sort(ctx())); }

SortPtr RawContext::MkIntSort() { return SortPtr(Z3_mk_int_sort(ctx())); }

SortPtr RawContext::MkRealSort() { return SortPtr(Z3_mk_real_sort(ctx())); }

SortPtr RawContext::MkBvSort(unsigned sz) { return SortPtr(Z3_mk_bv_sort(ctx(), sz)); }

SortPtr RawContext::MkArraySort(SortPtr domain, SortPtr range) {
    return SortPtr(Z3_mk_array_sort(ctx(), get_sort(domain), get_sort(range)));
}

SortPtr RawContext::MkFiniteDomainSort(String^ s, unsigned __int64 domain_size) {
    return SortPtr(Z3_mk_finite_domain_sort(ctx(), Z3_mk_string_symbol(ctx(), CreateString(s).c_str()), domain_size));
}

SortPtr RawContext::MkTupleSort(
    Symbol^             mk_tuple_name, 
    array<Symbol^>^     field_names,
    array<SortPtr>^     field_types,
    FuncDeclPtr%        mk_tuple_decl,
    array<FuncDeclPtr>^ proj_decls
    )
{
    if (!field_names ||
        !field_types ||
        !proj_decls ||
        field_names->Length != field_types->Length ||
        field_names->Length != proj_decls->Length) {
        throw gcnew Z3Error(ErrorCode::InvalidArgument);
    }
    scoped_Z3_symbol_array syms(field_names);
    scoped_Z3_ast_array<Z3_sort> types(field_types);
    scoped_Z3_ast_array<Z3_func_decl> projs(field_names->Length);
    Z3_func_decl decl;

    Z3_sort ty = 
        Z3_mk_tuple_sort(
            ctx(), 
            mk_tuple_name->get(),
            syms.size(),
            syms.c_ptr(),
            types.c_ptr(),
            &decl,
            projs.c_ptr()
            );
   
    mk_tuple_decl = FuncDeclPtr(decl);
    CopyFuncDecl(projs, proj_decls);
    return SortPtr(ty);
}

SortPtr RawContext::MkTupleSort(
    String^              mk_tuple_name, 
    array<String^>^      field_names,
    array<SortPtr>^      field_types,
    FuncDeclPtr%         mk_tuple_decl,
    array<FuncDeclPtr>^  proj_decls
    )
{
    Symbol^ tn = MkSymbol(mk_tuple_name);
    array<Symbol^>^ fields = gcnew array<Symbol^>(field_names->Length);
    for (int i = 0; i < fields->Length; ++i) {
        fields[i] = MkSymbol(field_names[i]);
    }
    return MkTupleSort(tn, fields, field_types, mk_tuple_decl, proj_decls);
    
}

SortPtr RawContext::MkEnumerationSort(
    String^             name,
    array<String^>^     enum_names,
    array<FuncDeclPtr>^ enum_consts,
    array<FuncDeclPtr>^ enum_testers) {
    
    Z3_symbol _name(Z3_mk_string_symbol(ctx(), CreateString(name).c_str()));
    scoped_Z3_symbol_array _enum_names(ctx(), enum_names); 
    scoped_Z3_ast_array<Z3_func_decl> _enum_consts(enum_consts);
    scoped_Z3_ast_array<Z3_func_decl> _enum_testers(enum_testers);
    unsigned sz = _enum_names.size();
    SASSERT(sz == _enum_consts.size());
    SASSERT(sz == _enum_testers.size());
    Z3_sort s = Z3_mk_enumeration_sort(ctx(), _name, sz, _enum_names.c_ptr(), _enum_consts.c_ptr(), _enum_testers.c_ptr());
    CopyFuncDecl(_enum_consts, enum_consts);
    CopyFuncDecl(_enum_testers, enum_testers);
    return SortPtr(s);
}

SortPtr RawContext::MkListSort(
    String^ name,
    SortPtr elem_sort,
    FuncDeclPtr% nil_decl,
    FuncDeclPtr% is_nil_decl,
    FuncDeclPtr% cons_decl,
    FuncDeclPtr% is_cons_decl,
    FuncDeclPtr% head_decl,
    FuncDeclPtr% tail_decl
    )
{
    Z3_func_decl _nil_decl, _is_nil_decl, _cons_decl, _is_cons_decl, _head_decl, _tail_decl;
    Z3_symbol _name = Z3_mk_string_symbol(ctx(), CreateString(name).c_str());
    Z3_sort _elem_sort = get_sort(elem_sort);
    
    Z3_sort s = Z3_mk_list_sort(ctx(), _name, _elem_sort, 
                                &_nil_decl, &_is_nil_decl, &_cons_decl,
                                &_is_cons_decl, &_head_decl, &_tail_decl);

    is_nil_decl  = FuncDeclPtr(_is_nil_decl);
    nil_decl     = FuncDeclPtr(_nil_decl);
    is_cons_decl = FuncDeclPtr(_is_cons_decl);
    cons_decl    = FuncDeclPtr(_cons_decl);
    head_decl    = FuncDeclPtr(_head_decl);
    tail_decl    = FuncDeclPtr(_tail_decl);
    return SortPtr(s);
}



Constructor^ RawContext::MkConstructor(
    String^ name,
    String^ tester,
    array<String^>^  field_names,
    array<SortPtr>^  field_sorts,
    array<unsigned>^ field_refs
    )
{

    int l1 = (!field_names)?0:field_names->Length;
    int l2 = (!field_sorts)?0:field_sorts->Length;
    int l3 = (!field_refs)?0:field_refs->Length;
    if (l1 != l2 || l1 != l3) {
        throw gcnew Z3Error(ErrorCode::InvalidArgument);
    }
    return gcnew Constructor(*m_context, name, tester, 
                             field_names, field_sorts, field_refs);
}


SortPtr RawContext::MkDataType(
    String^ name,
    array<Constructor^>^ constructors
    )
{
    Z3_symbol _name = Z3_mk_string_symbol(ctx(), CreateString(name).c_str());
    scoped_array<Z3_constructor> _cons(constructors->Length);
    for (int i = 0; i < constructors->Length; ++i) {
        _cons[i] = constructors[i]->Get();
    }
    Z3_sort s = Z3_mk_datatype(ctx(), _name, _cons.size(), _cons.c_ptr());
    for (int i = 0; i < constructors->Length; ++i) {
        Z3_constructor c = constructors[i]->Query();        
        Z3_del_constructor(ctx(), c);
    }
    return SortPtr(s);
}

array<SortPtr>^ RawContext::MkDataTypes(
    array<String^>^ names,
    array<array<Constructor^>^>^ constructors_list
    )
{
    if (!names ||
        !constructors_list || 
        names->Length != constructors_list->Length) {
        throw gcnew Z3Error(ErrorCode::InvalidArgument);

    }
    unsigned num_sorts = names->Length;
    scoped_array<Z3_symbol> sort_names(num_sorts);
    scoped_array<Z3_constructor_list> clist(num_sorts);
    scoped_array<Z3_sort> sort_sorts(num_sorts);
    array<SortPtr>^ result = gcnew array<SortPtr>(num_sorts);
    unsigned num_constructors = 0;
    for (unsigned j = 0; j < num_sorts; ++j) {
        num_constructors += constructors_list[j]->Length;
    }
    scoped_array<Z3_constructor> constructor_vec(num_constructors);
    svector<Z3_constructor> constructors_q;
    unsigned constructor_idx = 0;
    
    for (unsigned j = 0; j < num_sorts; ++j) {
        String^ name = names[j];
        array<Constructor^>^ constructors = constructors_list[j];        
        
        // add sort name
        Z3_symbol _name = Z3_mk_string_symbol(ctx(), CreateString(name).c_str());
        sort_names[j] = _name;

        // create constructor_list
        scoped_array<Z3_constructor> _cons(constructors->Length);
        for (int i = 0; i < constructors->Length; ++i) {
            _cons[i] = constructors[i]->Get();
            constructor_vec[constructor_idx++] = _cons[i];
        }
        Z3_constructor_list cl = Z3_mk_constructor_list(ctx(), _cons.size(), _cons.c_ptr());
        clist[j] = cl;        
    }
    Z3_mk_datatypes(ctx(), num_sorts, sort_names.c_ptr(), sort_sorts.c_ptr(), clist.c_ptr());

    for (unsigned j = 0; j < num_sorts; ++j) {
        Z3_del_constructor_list(ctx(), clist[j]);
        result[j] = SortPtr(sort_sorts[j]);
        // populate the constructors
        array<Constructor^>^ constructors = constructors_list[j];        
        for (int i = 0; i < constructors->Length; ++i) {
            constructors_q.push_back(constructors[i]->Query());
        }
    }
    for (unsigned i = 0; i < constructors_q.size(); ++i) {
        Z3_constructor c = constructors_q[i];
        if (c) {
            Z3_del_constructor(ctx(), c);
        }
    }
    return result;
}



FuncDeclPtr RawContext::MkFuncDecl(Symbol^ s, array<SortPtr>^ domain, SortPtr range) {
    scoped_Z3_ast_array<Z3_sort> types(domain);
    return FuncDeclPtr(Z3_mk_func_decl(ctx(), s->get(), types.size(), types.c_ptr(), get_sort(range))); 
}

FuncDeclPtr RawContext::MkFuncDecl(String^ s, array<SortPtr>^ domain, SortPtr range) {
    scoped_Z3_ast_array<Z3_sort> types(domain);
    Z3_symbol sym = Z3_mk_string_symbol(ctx(), CreateString(s).c_str());
    return FuncDeclPtr(Z3_mk_func_decl(ctx(), sym, types.size(), types.c_ptr(), get_sort(range))); 
}

FuncDeclPtr RawContext::MkFuncDecl(Symbol^ s, SortPtr domain, SortPtr range) {
    Z3_sort dom[1] = { get_sort(domain) };
    return FuncDeclPtr(Z3_mk_func_decl(ctx(), s->get(), 1, dom, get_sort(range))); 
}

FuncDeclPtr RawContext::MkFuncDecl(Symbol^ s, SortPtr d1, SortPtr d2, SortPtr range) {
    Z3_sort dom[2] = { get_sort(d1), get_sort(d2) };
    return FuncDeclPtr(Z3_mk_func_decl(ctx(), s->get(), 2, dom, get_sort(range))); 
}

FuncDeclPtr RawContext::MkFuncDecl(String^ s, SortPtr domain, SortPtr range) {
    Z3_sort dom[1] = { get_sort(domain) };
    Z3_symbol sym = Z3_mk_string_symbol(ctx(), CreateString(s).c_str());
    return FuncDeclPtr(Z3_mk_func_decl(ctx(), sym, 1, dom, get_sort(range))); 
}

FuncDeclPtr RawContext::MkFuncDecl(String^ s, SortPtr d1, SortPtr d2, SortPtr range) {
    Z3_symbol sym = Z3_mk_string_symbol(ctx(), CreateString(s).c_str());
    Z3_sort dom[2] = { get_sort(d1), get_sort(d2) };
    return FuncDeclPtr(Z3_mk_func_decl(ctx(), sym, 2, dom, get_sort(range))); 
}

TermPtr RawContext::MkApp(FuncDeclPtr d, array<TermPtr>^ args) {
    scoped_Z3_ast_array<Z3_ast> z3_args(args);
    return TermPtr(Z3_mk_app(ctx(), get_func_decl(d), z3_args.size(), z3_args.c_ptr()));
}

TermPtr RawContext::MkApp(FuncDeclPtr d, TermPtr arg) {
    Z3_ast args[1] = { get_ast(arg) };
    return TermPtr(Z3_mk_app(ctx(), get_func_decl(d), 1, args));
}

TermPtr RawContext::MkApp(FuncDeclPtr d, TermPtr arg1, TermPtr arg2) {
    Z3_ast args[2] = { get_ast(arg1), get_ast(arg2) };
    return TermPtr(Z3_mk_app(ctx(), get_func_decl(d), 2, args));
}

TermPtr RawContext::MkApp(FuncDeclPtr d, TermPtr arg1, TermPtr arg2, TermPtr arg3) {
    Z3_ast args[3] = { get_ast(arg1), get_ast(arg2), get_ast(arg3) };
    return TermPtr(Z3_mk_app(ctx(), get_func_decl(d), 3, args));
}


TermPtr RawContext::MkConst(FuncDeclPtr d) {
    return TermPtr(Z3_mk_app(ctx(),get_func_decl(d), 0, 0));
}

TermPtr RawContext::MkConst(String^ s, SortPtr ty) {
    Z3_symbol sym = Z3_mk_string_symbol(ctx(),CreateString(s).c_str());
    Z3_func_decl d = Z3_mk_func_decl(ctx(), sym, 0, 0, get_sort(ty));
    return TermPtr(Z3_mk_app(ctx(), d, 0, 0));
}

TermPtr RawContext::MkConst(Symbol^ s, SortPtr ty) {
    Z3_func_decl d = Z3_mk_func_decl(ctx(), s->get(), 0, 0, get_sort(ty));
    return TermPtr(Z3_mk_app(ctx(), d, 0, 0));
}

FuncDeclPtr RawContext::MkFreshFuncDecl(String^ prefix, array<SortPtr>^ domain, SortPtr range) {
    scoped_Z3_ast_array<Z3_sort> types(domain);
    return FuncDeclPtr(Z3_mk_fresh_func_decl(ctx(), CreateString(prefix).c_str(), types.size(), types.c_ptr(), get_sort(range))); 
}

TermPtr RawContext::MkFreshConst(String^ prefix, SortPtr ty) {
    return TermPtr(Z3_mk_fresh_const(ctx(), CreateString(prefix).c_str(), get_sort(ty))); 
}

TermPtr RawContext::MkLabel(Symbol^ name, bool pos, TermPtr fml) {
    return TermPtr(Z3_mk_label(ctx(), name->get(), pos, get_ast(fml)));
}


TermPtr RawContext::MkEq(TermPtr l, TermPtr r) {
    return TermPtr(Z3_mk_eq(ctx(), get_ast(l), get_ast(r)));
}

TermPtr RawContext::MkDistinct(array<TermPtr>^ _args) {
    scoped_Z3_ast_array<Z3_ast> args(_args);
    return TermPtr(Z3_mk_distinct(ctx(), args.size(), args.c_ptr()));
}

TermPtr RawContext::MkNot(TermPtr arg) {
    return TermPtr(Z3_mk_not(ctx(), get_ast(arg)));
}
    
TermPtr RawContext::MkIte(TermPtr t1, TermPtr t2, TermPtr t3) {
    return TermPtr(Z3_mk_ite(ctx(), get_ast(t1), get_ast(t2), get_ast(t3)));
}

#define MK_BINARY(fn, t1, t2) return TermPtr(Z3_mk_ ## fn (ctx(), get_ast(t1), get_ast(t2)))

#define MK_UNARY(fn, t1) return TermPtr(Z3_mk_ ## fn (ctx(), get_ast(t1)))

#define MK_NARY(fn, _args_) { scoped_Z3_ast_array<Z3_ast> my_args(_args_); return TermPtr(Z3_mk_ ## fn (ctx(), my_args.size(), my_args.c_ptr())); }

TermPtr RawContext::MkIff(TermPtr t1, TermPtr t2) {
    MK_BINARY(iff, t1, t2);
}

TermPtr RawContext::MkImplies(TermPtr t1, TermPtr t2) {
    MK_BINARY(implies, t1, t2);
}
    
TermPtr RawContext::MkXor(TermPtr t1, TermPtr t2) {
    MK_BINARY(xor, t1, t2);
}
    
TermPtr RawContext::MkAnd(array<TermPtr>^ args) {
    MK_NARY(and, args);
}

TermPtr RawContext::MkAnd(TermPtr arg1, TermPtr arg2) {
    Z3_ast args[2] = { get_ast(arg1), get_ast(arg2) };
    return TermPtr(Z3_mk_and(ctx(), 2, args));
}
    
TermPtr RawContext::MkOr(array<TermPtr>^ args) {
    MK_NARY(or, args);
}

TermPtr RawContext::MkOr(TermPtr arg1, TermPtr arg2) {
    Z3_ast args[2] = { get_ast(arg1), get_ast(arg2) };
    return TermPtr(Z3_mk_or(ctx(), 2, args));
}

TermPtr RawContext::MkAdd(array<TermPtr>^ args) {
    MK_NARY(add, args);
}

TermPtr RawContext::MkAdd(TermPtr arg1, TermPtr arg2) {
    Z3_ast args[2] = { get_ast(arg1), get_ast(arg2) };
    return TermPtr(Z3_mk_add(ctx(), 2, args));
}

TermPtr RawContext::MkMul(array<TermPtr>^ args) {
    MK_NARY(mul, args);
}

TermPtr RawContext::MkMul(TermPtr arg1, TermPtr arg2) {
    Z3_ast args[2] = { get_ast(arg1), get_ast(arg2) };
    return TermPtr(Z3_mk_mul(ctx(), 2, args));
}

TermPtr RawContext::MkSub(array<TermPtr>^ args) {
    MK_NARY(sub, args);
}

TermPtr RawContext::MkSub(TermPtr arg1, TermPtr arg2) {
    Z3_ast args[2] = { get_ast(arg1), get_ast(arg2) };
    return TermPtr(Z3_mk_sub(ctx(), 2, args));
}

TermPtr RawContext::MkUnaryMinus(TermPtr arg) {
    MK_UNARY(unary_minus, arg);
}

TermPtr RawContext::MkDiv(TermPtr arg1, TermPtr arg2) {
    MK_BINARY(div, arg1, arg2);
}

TermPtr RawContext::MkMod(TermPtr arg1, TermPtr arg2) {
    MK_BINARY(mod, arg1, arg2);
}

TermPtr RawContext::MkRem(TermPtr arg1, TermPtr arg2) {
    MK_BINARY(rem, arg1, arg2);
}

TermPtr RawContext::MkToReal(TermPtr arg) {
    MK_UNARY(int2real, arg);
}


TermPtr RawContext::MkToInt(TermPtr arg) {
    MK_UNARY(real2int, arg);
}

TermPtr RawContext::MkIsInt(TermPtr arg) {
    MK_UNARY(is_int, arg);
}

TermPtr RawContext::MkLt(TermPtr arg1, TermPtr arg2) {
    MK_BINARY(lt, arg1, arg2);
}

TermPtr RawContext::MkLe(TermPtr arg1, TermPtr arg2) {
    MK_BINARY(le, arg1, arg2);
}

TermPtr RawContext::MkGt(TermPtr arg1, TermPtr arg2) {
    MK_BINARY(gt, arg1, arg2);    
}

TermPtr RawContext::MkGe(TermPtr arg1, TermPtr arg2) {
    MK_BINARY(ge, arg1, arg2);    
}

TermPtr RawContext::MkBvNot(TermPtr t1) {
    MK_UNARY(bvnot, t1);
}

TermPtr RawContext::MkBvReduceAnd(TermPtr t1) {
    MK_UNARY(bvredand, t1);
}

TermPtr RawContext::MkBvReduceOr(TermPtr t1) {
    MK_UNARY(bvredor, t1);
}

TermPtr RawContext::MkBvAnd(TermPtr t1, TermPtr t2) {
    MK_BINARY(bvand, t1, t2);
}

TermPtr RawContext::MkBvOr(TermPtr t1, TermPtr t2) {
    MK_BINARY(bvor, t1, t2);
}

TermPtr RawContext::MkBvXor(TermPtr t1, TermPtr t2) {
    MK_BINARY(bvxor, t1, t2);
}

TermPtr RawContext::MkBvNand(TermPtr t1, TermPtr t2) {
    MK_BINARY(bvnand, t1, t2);
}

TermPtr RawContext::MkBvNor(TermPtr t1, TermPtr t2) {
    MK_BINARY(bvnor, t1, t2);
}

TermPtr RawContext::MkBvXnor(TermPtr t1, TermPtr t2) {
    MK_BINARY(bvxnor, t1, t2);
}

TermPtr RawContext::MkBvNeg(TermPtr t1) {
    MK_UNARY(bvneg, t1);
}

TermPtr RawContext::MkBvAdd(TermPtr t1, TermPtr t2) {
    MK_BINARY(bvadd, t1, t2);
}

TermPtr RawContext::MkBvSub(TermPtr t1, TermPtr t2) {
    MK_BINARY(bvsub, t1, t2);
}
    
TermPtr RawContext::MkBvMul(TermPtr t1, TermPtr t2) {
    MK_BINARY(bvmul, t1, t2);
}

TermPtr RawContext::MkBvUdiv(TermPtr t1, TermPtr t2) {
    MK_BINARY(bvudiv, t1, t2);
}

TermPtr RawContext::MkBvSdiv(TermPtr t1, TermPtr t2) {
    MK_BINARY(bvsdiv, t1, t2);
}

TermPtr RawContext::MkBvUrem(TermPtr t1, TermPtr t2) {
    MK_BINARY(bvurem, t1, t2);
}
TermPtr RawContext::MkBvSrem(TermPtr t1, TermPtr t2) {
    MK_BINARY(bvsrem, t1, t2);
}

TermPtr RawContext::MkBvSmod(TermPtr t1, TermPtr t2) {
    MK_BINARY(bvsmod, t1, t2);
}

TermPtr RawContext::MkBvUlt(TermPtr t1, TermPtr t2) {
    MK_BINARY(bvult, t1, t2);
}

TermPtr RawContext::MkBvSlt(TermPtr t1, TermPtr t2) {
    MK_BINARY(bvslt, t1, t2);
}

TermPtr RawContext::MkBvUle(TermPtr t1, TermPtr t2) {
    MK_BINARY(bvule, t1, t2);
}

TermPtr RawContext::MkBvSle(TermPtr t1, TermPtr t2) {
    MK_BINARY(bvsle, t1, t2);
}

TermPtr RawContext::MkBvUge(TermPtr t1, TermPtr t2) {
    MK_BINARY(bvuge, t1, t2);
}

TermPtr RawContext::MkBvSge(TermPtr t1, TermPtr t2) {
    MK_BINARY(bvsge, t1, t2);
}

TermPtr RawContext::MkBvUgt(TermPtr t1, TermPtr t2) {
    MK_BINARY(bvugt, t1, t2);
}

TermPtr RawContext::MkBvSgt(TermPtr t1, TermPtr t2) {
    MK_BINARY(bvsgt, t1, t2);
}

TermPtr RawContext::MkBvConcat(TermPtr t1, TermPtr t2) {
    MK_BINARY(concat, t1, t2);
}
    
TermPtr RawContext::MkBvExtract(unsigned high, unsigned low, TermPtr t) {
    return TermPtr(Z3_mk_extract(ctx(), high, low, get_ast(t)));
}

TermPtr RawContext::MkBvSignExt(unsigned i, TermPtr t) {
    return TermPtr(Z3_mk_sign_ext(ctx(), i, get_ast(t)));
}

TermPtr RawContext::MkBvZeroExt(unsigned i, TermPtr t) {
    return TermPtr(Z3_mk_zero_ext(ctx(), i, get_ast(t)));    
}

TermPtr RawContext::MkBvRepeat(unsigned i, TermPtr t) {
    return TermPtr(Z3_mk_repeat(ctx(), i, get_ast(t)));    
}

TermPtr RawContext::MkBvShl(TermPtr t1, TermPtr t2) {
    MK_BINARY(bvshl, t1, t2);
}

TermPtr RawContext::MkBvLshr(TermPtr t1, TermPtr t2) {
    MK_BINARY(bvlshr, t1, t2);
}

TermPtr RawContext::MkBvAshr(TermPtr t1, TermPtr t2) {
    MK_BINARY(bvashr, t1, t2);
}
    
TermPtr RawContext::MkBvRotateLeft(unsigned i, TermPtr t1) {
    return TermPtr(Z3_mk_rotate_left(ctx(), i, get_ast(t1)));    
}
    
TermPtr RawContext::MkBvRotateRight(unsigned i, TermPtr t1) {
    return TermPtr(Z3_mk_rotate_right(ctx(), i, get_ast(t1)));    
}

TermPtr RawContext::MkBvRotateLeft(TermPtr t1, TermPtr t2) {
    return TermPtr(Z3_mk_ext_rotate_left(ctx(), get_ast(t1), get_ast(t2)));    
}
    
TermPtr RawContext::MkBvRotateRight(TermPtr t1, TermPtr t2) {
    return TermPtr(Z3_mk_ext_rotate_right(ctx(), get_ast(t1), get_ast(t2)));
}

TermPtr RawContext::MkInt2Bv(unsigned i, TermPtr t1) {
    return TermPtr(Z3_mk_int2bv(ctx(), i, get_ast(t1)));    
}

TermPtr RawContext::MkBv2Int(TermPtr t1, bool is_signed) {
    return TermPtr(Z3_mk_bv2int(ctx(), get_ast(t1), is_signed));
}

TermPtr RawContext::MkBvAddNoOverflow(TermPtr t1, TermPtr t2, bool is_signed) {
    return TermPtr(Z3_mk_bvadd_no_overflow(ctx(), get_ast(t1), get_ast(t2), is_signed));
}

TermPtr RawContext::MkBvAddNoUnderflow(TermPtr t1, TermPtr t2) {
    return TermPtr(Z3_mk_bvadd_no_underflow(ctx(), get_ast(t1), get_ast(t2)));
}

TermPtr RawContext::MkBvSubNoOverflow(TermPtr t1, TermPtr t2) {
    return TermPtr(Z3_mk_bvsub_no_overflow(ctx(), get_ast(t1), get_ast(t2)));
}

TermPtr RawContext::MkBvSubNoUnderflow(TermPtr t1, TermPtr t2, bool is_signed) {
    return TermPtr(Z3_mk_bvsub_no_underflow(ctx(), get_ast(t1), get_ast(t2), is_signed));
}

TermPtr RawContext::MkBvSDivNoOverflow(TermPtr t1, TermPtr t2) {
    return TermPtr(Z3_mk_bvsdiv_no_overflow(ctx(), get_ast(t1), get_ast(t2)));
}

TermPtr RawContext::MkBvNegNoOverflow(TermPtr t1) {
    return TermPtr(Z3_mk_bvneg_no_overflow(ctx(), get_ast(t1)));
}

TermPtr RawContext::MkBvMulNoOverflow(TermPtr t1, TermPtr t2, bool is_signed) {
    return TermPtr(Z3_mk_bvmul_no_overflow(ctx(), get_ast(t1), get_ast(t2), is_signed));
}

TermPtr RawContext::MkBvMulNoUnderflow(TermPtr t1, TermPtr t2) {
    return TermPtr(Z3_mk_bvmul_no_underflow(ctx(), get_ast(t1), get_ast(t2)));
}

TermPtr RawContext::MkArraySelect(TermPtr a, TermPtr i) {
    return TermPtr(Z3_mk_select(ctx(), get_ast(a), get_ast(i)));
}

TermPtr RawContext::MkArrayStore(TermPtr a, TermPtr i, TermPtr v) {
    return TermPtr(Z3_mk_store(ctx(), get_ast(a), get_ast(i), get_ast(v)));
}

TermPtr RawContext::MkArrayMap(FuncDeclPtr d, array<TermPtr>^ args) {
    scoped_Z3_ast_array<Z3_ast> _args(args);
    return TermPtr(Z3_mk_map(ctx(), get_func_decl(d), _args.size(), _args.c_ptr()));
}

TermPtr RawContext::MkArrayConst(SortPtr domain, TermPtr v) {
    return TermPtr(Z3_mk_const_array(ctx(), get_sort(domain), get_ast(v)));
}

TermPtr RawContext::MkArrayDefault(TermPtr a) {
    return TermPtr(Z3_mk_array_default(ctx(), get_ast(a)));
}

TermPtr RawContext::MkSetUnion(array<TermPtr>^ sets) {
    scoped_Z3_ast_array<Z3_ast> _sets(sets);
    return TermPtr(Z3_mk_set_union(ctx(), _sets.size(), _sets.c_ptr()));
}

TermPtr RawContext::MkSetUnion(TermPtr set1, TermPtr set2) {
    Z3_ast args[2] = { get_ast(set1), get_ast(set2) };
    return TermPtr(Z3_mk_set_union(ctx(), 2, args));
}

TermPtr RawContext::MkSetIntersect(array<TermPtr>^ sets) {
    scoped_Z3_ast_array<Z3_ast> _sets(sets);
    return TermPtr(Z3_mk_set_intersect(ctx(), _sets.size(), _sets.c_ptr()));
}

TermPtr RawContext::MkSetIntersect(TermPtr set1, TermPtr set2) {
    Z3_ast args[2] = { get_ast(set1), get_ast(set2) };
    return TermPtr(Z3_mk_set_intersect(ctx(), 2, args));
}

FuncDeclPtr RawContext::MkInjectiveFunction(String^ name, array<SortPtr>^ domain, SortPtr range) {
    scoped_Z3_ast_array<Z3_sort> types(domain);
    Z3_symbol sym = Z3_mk_string_symbol(ctx(), CreateString(name).c_str());
    return FuncDeclPtr(Z3_mk_injective_function(ctx(), sym, types.size(), types.c_ptr(), get_sort(range)));
}

FuncDeclPtr RawContext::MkInjectiveFunction(Symbol^ name, array<SortPtr>^ domain, SortPtr range) {
    scoped_Z3_ast_array<Z3_sort> types(domain);
    return FuncDeclPtr(Z3_mk_injective_function(ctx(), name->get(), types.size(), types.c_ptr(), get_sort(range)));
}


TermPtr RawContext::MkNumeral(String^ numeral, SortPtr ty) {
    return TermPtr(Z3_mk_numeral(ctx(), CreateString(numeral).c_str(), get_sort(ty)));
}

TermPtr RawContext::MkNumeral(int n, SortPtr ty) {
    return TermPtr(Z3_mk_int(ctx(), n, get_sort(ty)));
}

TermPtr RawContext::MkNumeral(unsigned n, SortPtr ty) {
    return TermPtr(Z3_mk_unsigned_int(ctx(), n, get_sort(ty)));
}

TermPtr RawContext::MkNumeral(__int64 n, SortPtr ty) {
    return TermPtr(Z3_mk_int64(ctx(), n, get_sort(ty)));
}

TermPtr RawContext::MkNumeral(unsigned __int64 n, SortPtr ty) {
    return TermPtr(Z3_mk_unsigned_int64(ctx(), n, get_sort(ty)));
}

PatternPtr RawContext::MkPattern(array<TermPtr>^ terms) {
    scoped_Z3_ast_array<Z3_ast> args(terms);
    return PatternPtr(Z3_mk_pattern(ctx(), args.size(), args.c_ptr()));
}

TermPtr RawContext::MkBound(unsigned index, SortPtr ty) {
    return TermPtr(Z3_mk_bound(ctx(), index, get_sort(ty)));
}

TermPtr RawContext::MkForall(
    unsigned weight,
    array<PatternPtr>^ patterns,
    array<SortPtr>^ types,
    array<Symbol^>^ names,
    TermPtr body
    ) 
{
    scoped_Z3_ast_array<Z3_pattern> _patterns(patterns);
    scoped_Z3_ast_array<Z3_sort> _types(types);
    scoped_Z3_symbol_array _names(names); 
    return TermPtr(
        Z3_mk_forall(
            ctx(), 
            weight,
            _patterns.size(),
            _patterns.c_ptr(),
            _types.size(),
            _types.c_ptr(),
            _names.c_ptr(),
            get_ast(body)
            )
        );
}

TermPtr RawContext::MkForall(
    unsigned weight,
    array<PatternPtr>^ patterns,
    array<SortPtr>^ types,
    array<String^>^ names,
    TermPtr body
    ) 
{
    if (!names) {
        throw gcnew Z3Error(ErrorCode::InvalidArgument);
    }
    array<Symbol^>^ nameSymbols = gcnew array<Symbol^>(names->Length);
    for (int i = 0; i < nameSymbols->Length; ++i) {
        nameSymbols[i] = MkSymbol(names[i]);
    }
    return MkForall(weight, patterns, types, nameSymbols, body);
}

TermPtr RawContext::MkForall(
    unsigned           weight,
    array<AppPtr>^   bound,
    array<PatternPtr>^ patterns,
    TermPtr            body
    )
{
    scoped_Z3_ast_array<Z3_app> _bound(bound);
    scoped_Z3_ast_array<Z3_pattern> _patterns(patterns);
    return TermPtr(
        Z3_mk_forall_const(
            ctx(), 
            weight,
            _bound.size(),
            _bound.c_ptr(),
            _patterns.size(),
            _patterns.c_ptr(),
            get_ast(body)
            ));
}

TermPtr RawContext::MkExists(
    unsigned weight,
    array<PatternPtr>^ patterns,
    array<SortPtr>^ types,
    array<Symbol^>^ names,
    TermPtr body
    )
{
    scoped_Z3_ast_array<Z3_pattern> _patterns(patterns);
    scoped_Z3_ast_array<Z3_sort> _types(types);
    scoped_Z3_symbol_array _names(names); 
    return TermPtr(
        Z3_mk_exists(
            ctx(), 
            weight,
            _patterns.size(),
            _patterns.c_ptr(),
            _types.size(),
            _types.c_ptr(),
            _names.c_ptr(),
            get_ast(body)
            )
        );
}

TermPtr RawContext::MkExists(
    unsigned weight,
    array<PatternPtr>^ patterns,
    array<SortPtr>^ types,
    array<String^>^ names,
    TermPtr body
    ) 
{
    if (!names) {
        throw gcnew Z3Error(ErrorCode::InvalidArgument);
    }
    array<Symbol^>^ nameSymbols = gcnew array<Symbol^>(names->Length);
    for (int i = 0; i < nameSymbols->Length; ++i) {
        nameSymbols[i] = MkSymbol(names[i]);
    }
    return MkExists(weight, patterns, types, nameSymbols, body);
}

TermPtr RawContext::MkExists(
    unsigned           weight,
    array<AppPtr>^   bound,
    array<PatternPtr>^ patterns,
    TermPtr            body
    )
{
    scoped_Z3_ast_array<Z3_app> _bound(bound);
    scoped_Z3_ast_array<Z3_pattern> _patterns(patterns);
    return TermPtr(
        Z3_mk_exists_const(
            ctx(), 
            weight,
            _bound.size(),
            _bound.c_ptr(),
            _patterns.size(),
            _patterns.c_ptr(),
            get_ast(body)
            ));
}

TermPtr RawContext::MkQuantifier(
    bool                  is_forall,
    unsigned              weight,
    Symbol^               quantifier_id,
    Symbol^               skolem_id,
    array<PatternPtr>^ patterns,
    array<TermPtr>^    no_patterns,
    array<SortPtr>^    types,
    array<Symbol^>^       names,
    TermPtr            body
    )
{
    scoped_Z3_ast_array<Z3_pattern> _patterns(patterns);
    scoped_Z3_ast_array<Z3_ast> _no_patterns(no_patterns);
    scoped_Z3_ast_array<Z3_sort> _types(types);
    scoped_Z3_symbol_array _names(names); 
    return TermPtr(
        Z3_mk_quantifier_ex(
            ctx(),
            is_forall,
            weight,
            quantifier_id?quantifier_id->get():0,
            skolem_id?skolem_id->get():0,
            _patterns.size(),
            _patterns.c_ptr(),
            _no_patterns.size(),
            _no_patterns.c_ptr(),
            _types.size(),
            _types.c_ptr(),
            _names.c_ptr(),
            get_ast(body)
            )
        );
}

TermPtr RawContext::MkQuantifier(
    bool                  is_forall,
    unsigned              weight,
    Symbol^               quantifier_id,
    Symbol^               skolem_id,
    array<PatternPtr>^    patterns,
    array<TermPtr>^       no_patterns,
    array<TermPtr>^       bound,
    TermPtr               body
    )
{
    scoped_Z3_ast_array<Z3_pattern> _patterns(patterns);
    scoped_Z3_ast_array<Z3_ast> _no_patterns(no_patterns);
    scoped_Z3_ast_array<Z3_app> _bound(bound);
    return TermPtr(
        Z3_mk_quantifier_const_ex(
            ctx(),
            is_forall,
            weight,
            quantifier_id?quantifier_id->get():0,
            skolem_id?skolem_id->get():0,
            _bound.size(), _bound.c_ptr(),
            _patterns.size(),
            _patterns.c_ptr(),
            _no_patterns.size(),
            _no_patterns.c_ptr(),
            get_ast(body)
            )
        );
}

unsigned RawContext::GetTermId(TermPtr t) {
    return Z3_get_ast_id(ctx(), get_ast(t));
}

unsigned RawContext::GetFuncDeclId(FuncDeclPtr t) {
    return Z3_get_func_decl_id(ctx(), get_func_decl(t));
}

unsigned RawContext::GetSortId(SortPtr t) {
    return Z3_get_sort_id(ctx(), get_sort(t));
}

SymbolKind RawContext::GetSymbolKind(Symbol^ s) {
    switch(Z3_get_symbol_kind(ctx(), s->get())) {
    case Z3_INT_SYMBOL: 
        return SymbolKind::Int;
    case Z3_STRING_SYMBOL: 
        return SymbolKind::String;
    default:
        UNREACHABLE();
    }
    return SymbolKind::Int;
}

int RawContext::GetSymbolInt(Symbol^ s) {
    return Z3_get_symbol_int(ctx(), s->get());
}

String^ Symbol::ToString() {
    return gcnew String(Z3_get_symbol_string(m_ctx, m_symbol));
}

String^ RawContext::GetSymbolString(Symbol^ s) {
    return gcnew String(Z3_get_symbol_string(ctx(), s->get()));
}

bool RawContext::IsEq(TermPtr t1, TermPtr t2) {
    return Z3_TRUE == Z3_is_eq_ast(ctx(), get_ast(t1), get_ast(t2));
}

bool RawContext::IsWellSorted(TermPtr t) {
    return Z3_is_well_sorted(ctx(), get_ast(t)) == Z3_TRUE;
}

TermKind RawContext::GetTermKind(TermPtr a) {
    switch(Z3_get_ast_kind(ctx(), get_ast(a))) {
    case Z3_NUMERAL_AST: 
        return TermKind::Numeral;
    case Z3_APP_AST: 
        return TermKind::App;
    case Z3_VAR_AST: 
        return TermKind::Var;
    case Z3_QUANTIFIER_AST: 
        return TermKind::Quantifier;
    case Z3_UNKNOWN_AST: 
        return TermKind::Unknown;
    }
    UNREACHABLE();
    return TermKind::Unknown;
}

DeclKind RawContext::GetDeclKind(FuncDeclPtr d) {
    switch(Z3_get_decl_kind(ctx(), get_func_decl(d))) {
    case Z3_OP_TRUE: return DeclKind::True;
    case Z3_OP_FALSE: return DeclKind::False;
    case Z3_OP_EQ: return DeclKind::Eq;
    case Z3_OP_DISTINCT: return DeclKind::Distinct;
    case Z3_OP_ITE: return DeclKind::Ite;
    case Z3_OP_AND: return DeclKind::And;
    case Z3_OP_OR: return DeclKind::Or;
    case Z3_OP_IFF: return DeclKind::Iff;
    case Z3_OP_XOR: return DeclKind::Xor;
    case Z3_OP_NOT: return DeclKind::Not;
    case Z3_OP_IMPLIES: return DeclKind::Implies;
    case Z3_OP_ANUM: return DeclKind::ArithNum;
    case Z3_OP_LE: return DeclKind::Le;
    case Z3_OP_GE: return DeclKind::Ge;
    case Z3_OP_LT: return DeclKind::Lt;
    case Z3_OP_GT: return DeclKind::Gt;
    case Z3_OP_ADD: return DeclKind::Add;
    case Z3_OP_SUB: return DeclKind::Sub;
    case Z3_OP_UMINUS: return DeclKind::Uminus;
    case Z3_OP_MUL: return DeclKind::Mul;
    case Z3_OP_DIV: return DeclKind::Div;
    case Z3_OP_IDIV: return DeclKind::IDiv;
    case Z3_OP_REM: return DeclKind::Rem;
    case Z3_OP_MOD: return DeclKind::Mod;
    case Z3_OP_TO_REAL: return DeclKind::ToReal;
    case Z3_OP_TO_INT: return DeclKind::ToInt;
    case Z3_OP_IS_INT: return DeclKind::IsInt;
    case Z3_OP_STORE: return DeclKind::Store;
    case Z3_OP_SELECT: return DeclKind::Select;
    case Z3_OP_CONST_ARRAY: return DeclKind::ConstArray;
    case Z3_OP_ARRAY_DEFAULT: return DeclKind::DefaultArray;
    case Z3_OP_ARRAY_MAP: return DeclKind::MapArray;
    case Z3_OP_SET_UNION: return DeclKind::Union;
    case Z3_OP_SET_INTERSECT: return DeclKind::Intersect;
    case Z3_OP_SET_DIFFERENCE: return DeclKind::Difference;
    case Z3_OP_SET_COMPLEMENT: return DeclKind::Complement;
    case Z3_OP_SET_SUBSET: return DeclKind::Subset;
    case Z3_OP_AS_ARRAY: return DeclKind::AsArray;
    case Z3_OP_BNUM: return DeclKind::BitNum;
    case Z3_OP_BIT1: return DeclKind::Bit1 ;
    case Z3_OP_BIT0: return DeclKind::Bit0 ;
    case Z3_OP_BNEG: return DeclKind::BNeg ;
    case Z3_OP_BADD: return DeclKind::BAdd ;
    case Z3_OP_BSUB: return DeclKind::BSub ;
    case Z3_OP_BMUL: return DeclKind::BMul ;
    
    case Z3_OP_BSDIV: return DeclKind::BSDiv ;
    case Z3_OP_BUDIV: return DeclKind::BUDiv ;
    case Z3_OP_BSREM: return DeclKind::BSRem ;
    case Z3_OP_BUREM: return DeclKind::BURem ;
    case Z3_OP_BSMOD: return DeclKind::BSMod ;

    // special functions to record the division by 0 cases
    // these are internal functions 
    case Z3_OP_BSDIV0: return DeclKind::BSDiv0 ; 
    case Z3_OP_BUDIV0: return DeclKind::BUDiv0 ;
    case Z3_OP_BSREM0: return DeclKind::BSRem0 ;
    case Z3_OP_BUREM0: return DeclKind::BURem0 ;
    case Z3_OP_BSMOD0: return DeclKind::BSMod0 ;
    
    case Z3_OP_ULEQ: return DeclKind::BULeq ;
    case Z3_OP_SLEQ: return DeclKind::BSLeq ;
    case Z3_OP_UGEQ: return DeclKind::BUGeq ;
    case Z3_OP_SGEQ: return DeclKind::BSGeq ;
    case Z3_OP_ULT: return DeclKind::BULt ;
    case Z3_OP_SLT: return DeclKind::BSLt ;
    case Z3_OP_UGT: return DeclKind::BUGt ;
    case Z3_OP_SGT: return DeclKind::BSGt ;

    case Z3_OP_BAND: return DeclKind::BAnd ;
    case Z3_OP_BOR: return DeclKind::BOr ;
    case Z3_OP_BNOT: return DeclKind::BNot;
    case Z3_OP_BXOR: return DeclKind::BXor ;
    case Z3_OP_BNAND: return DeclKind::BNand ;
    case Z3_OP_BNOR: return DeclKind::BNor ;
    case Z3_OP_BXNOR: return DeclKind::BXnor ;

    case Z3_OP_CONCAT: return DeclKind::BConcat ;
    case Z3_OP_SIGN_EXT: return DeclKind::BSignExt ;
    case Z3_OP_ZERO_EXT: return DeclKind::BZeroExt ;
    case Z3_OP_EXTRACT: return DeclKind::BExtract ;
    case Z3_OP_REPEAT: return DeclKind::BRepeat ;

    case Z3_OP_BREDOR: return DeclKind::BRedOr ;
    case Z3_OP_BREDAND: return DeclKind::BRedAnd ;
    case Z3_OP_BCOMP: return DeclKind::BComp ;

    case Z3_OP_BSHL: return DeclKind::BShl ;
    case Z3_OP_BLSHR: return DeclKind::BLShr ;
    case Z3_OP_BASHR: return DeclKind::BAShr ;
    case Z3_OP_ROTATE_LEFT: return DeclKind::BRotateLeft ;
    case Z3_OP_ROTATE_RIGHT: return DeclKind::BRotateRight ;
    case Z3_OP_EXT_ROTATE_LEFT: return DeclKind::BExtRotateLeft ;
    case Z3_OP_EXT_ROTATE_RIGHT: return DeclKind::BExtRotateRight ;

    case Z3_OP_INT2BV: return DeclKind::BInt2Bv ;
    case Z3_OP_BV2INT: return DeclKind::BBv2Int ;
    case Z3_OP_CARRY:  return DeclKind::BCarry;
    case Z3_OP_XOR3:   return DeclKind::BXor3;

    case Z3_OP_PR_ASSERTED: return DeclKind::PrAsserted ; 
    case Z3_OP_PR_GOAL: return DeclKind::PrGoal ; 
    case Z3_OP_PR_MODUS_PONENS: return DeclKind::PrModusPonens ; 
    case Z3_OP_PR_REFLEXIVITY: return DeclKind::PrReflexivity ; 
    case Z3_OP_PR_SYMMETRY: return DeclKind::PrSymmetry ; 
    case Z3_OP_PR_TRANSITIVITY: return DeclKind::PrTransitivity ; 
    case Z3_OP_PR_TRANSITIVITY_STAR: return DeclKind::PrTransitivityStar ; 
    case Z3_OP_PR_MONOTONICITY: return DeclKind::PrMonotonicity ; 
    case Z3_OP_PR_QUANT_INTRO: return DeclKind::PrQuantIntro ;
    case Z3_OP_PR_DISTRIBUTIVITY: return DeclKind::PrDistributivity ; 
    case Z3_OP_PR_AND_ELIM: return DeclKind::PrAndElim ; 
    case Z3_OP_PR_NOT_OR_ELIM: return DeclKind::PrNotOrElim ; 
    case Z3_OP_PR_REWRITE: return DeclKind::PrRewrite ; 
    case Z3_OP_PR_REWRITE_STAR: return DeclKind::PrRewriteStar ; 
    case Z3_OP_PR_PULL_QUANT: return DeclKind::PrPullQuant ; 
    case Z3_OP_PR_PULL_QUANT_STAR: return DeclKind::PrPullQuantStar ; 
    case Z3_OP_PR_PUSH_QUANT: return DeclKind::PrPushQuant ; 
    case Z3_OP_PR_ELIM_UNUSED_VARS: return DeclKind::PrElimUnusedVars ; 
    case Z3_OP_PR_DER: return DeclKind::PrDer ; 
    case Z3_OP_PR_QUANT_INST: return DeclKind::PrQuantInst ;
    case Z3_OP_PR_HYPOTHESIS: return DeclKind::PrHypothesis ; 
    case Z3_OP_PR_LEMMA: return DeclKind::PrLemma ; 
    case Z3_OP_PR_UNIT_RESOLUTION: return DeclKind::PrUnitResolution ; 
    case Z3_OP_PR_IFF_TRUE: return DeclKind::PrIffTrue ; 
    case Z3_OP_PR_IFF_FALSE: return DeclKind::PrIffFalse ; 
    case Z3_OP_PR_COMMUTATIVITY: return DeclKind::PrCommutativity ; 
    case Z3_OP_PR_DEF_AXIOM: return DeclKind::PrDefAxiom ;
    case Z3_OP_PR_DEF_INTRO: return DeclKind::PrDefIntro ; 
    case Z3_OP_PR_APPLY_DEF: return DeclKind::PrApplyDef ; 
    case Z3_OP_PR_IFF_OEQ: return DeclKind::PrIffOeq ; 
    case Z3_OP_PR_NNF_POS: return DeclKind::PrNnfPos ; 
    case Z3_OP_PR_NNF_NEG: return DeclKind::PrNnfNeg ; 
    case Z3_OP_PR_NNF_STAR: return DeclKind::PrNnfStar ; 
    case Z3_OP_PR_SKOLEMIZE: return DeclKind::PrSkolemize ; 
    case Z3_OP_PR_CNF_STAR: return DeclKind::PrCnfStar ; 
    case Z3_OP_PR_MODUS_PONENS_OEQ: return DeclKind::PrModusPonensOeq ; 
    case Z3_OP_PR_TH_LEMMA: return DeclKind::PrThLemma ; 
    case Z3_OP_LABEL: return DeclKind::Label;
    case Z3_OP_LABEL_LIT: return DeclKind::LabelLit;
    case Z3_OP_RA_STORE: return DeclKind::RaStore;
    case Z3_OP_RA_EMPTY: return DeclKind::RaEmpty;
    case Z3_OP_RA_IS_EMPTY: return DeclKind::RaIsEmpty;
    case Z3_OP_RA_JOIN: return DeclKind::RaJoin;
    case Z3_OP_RA_UNION: return DeclKind::RaUnion;
    case Z3_OP_RA_WIDEN: return DeclKind::RaWiden;
    case Z3_OP_RA_PROJECT: return DeclKind::RaProject;
    case Z3_OP_RA_FILTER: return DeclKind::RaFilter;
    case Z3_OP_RA_NEGATION_FILTER: return DeclKind::RaNegationFilter;
    case Z3_OP_RA_RENAME: return DeclKind::RaRename;
    case Z3_OP_RA_COMPLEMENT: return DeclKind::RaComplement;
    case Z3_OP_RA_SELECT: return DeclKind::RaSelect;
    case Z3_OP_RA_CLONE: return DeclKind::RaClone;

    case Z3_OP_UNINTERPRETED: return DeclKind::Uninterpreted;
    default:
        UNREACHABLE();
        return DeclKind::Uninterpreted;
    }
}

array<IRawParameter^>^ RawContext::GetDeclParameters(FuncDeclPtr d) {
    Z3_func_decl fd = get_func_decl(d);
    unsigned num_params = Z3_get_decl_num_parameters(ctx(), fd);
    array<IRawParameter^>^ params = gcnew array<IRawParameter^>(num_params);
    for (unsigned i = 0; i < num_params; ++i) {
        switch(Z3_get_decl_parameter_kind(ctx(), fd, i)) {
        case Z3_PARAMETER_INT:
            params[i] = gcnew IntParameter(Z3_get_decl_int_parameter(ctx(), fd, i));
            break;
        case Z3_PARAMETER_DOUBLE:
            params[i] = gcnew DoubleParameter(Z3_get_decl_double_parameter(ctx(), fd, i));
            break;
        case Z3_PARAMETER_RATIONAL: {
            Z3_string s = Z3_get_decl_rational_parameter(ctx(), fd, i);
            params[i] = gcnew RationalParameter(gcnew String(s));
            break;
        }
        case Z3_PARAMETER_SYMBOL: {
            Z3_symbol s = Z3_get_decl_symbol_parameter(ctx(), fd, i);
            params[i] = gcnew SymbolParameter(gcnew Symbol(ctx(), s));
            break;
        }
        case Z3_PARAMETER_SORT:
            params[i] = gcnew SortPtrParameter(SortPtr(Z3_get_decl_sort_parameter(ctx(), fd, i)));
            break;
        case Z3_PARAMETER_AST:
            params[i] = gcnew TermPtrParameter(TermPtr(Z3_get_decl_ast_parameter(ctx(), fd, i)));
            break;
        case Z3_PARAMETER_FUNC_DECL:
            params[i] = gcnew FuncDeclPtrParameter(FuncDeclPtr(Z3_get_decl_func_decl_parameter(ctx(), fd, i)));
            break;
        default:
            UNREACHABLE();
            break;
        }
    }
    return params;
}

FuncDeclPtr RawContext::GetAppDecl(AppPtr a) {
    if (GetTermKind(a) != TermKind::App) {
        throw gcnew Z3Error(ErrorCode::InvalidArgument);
    }
    return FuncDeclPtr(Z3_get_app_decl(ctx(), get_const_ast(a)));
}

array<TermPtr>^ RawContext::GetAppArgs(AppPtr a) {
    if (GetTermKind(a) != TermKind::App) {
        throw gcnew Z3Error(ErrorCode::InvalidArgument);
    }

    unsigned num_args = Z3_get_app_num_args(ctx(), get_const_ast(a));
    array<TermPtr>^ result = gcnew array<TermPtr>(num_args);
    for (unsigned i = 0; i < num_args; ++i) {
        result[i] = TermPtr(Z3_get_app_arg(ctx(), get_const_ast(a), i));
    }
    return result;
}

RawQuantifier^ RawContext::GetQuantifier(TermPtr a) {
    if (GetTermKind(a) != TermKind::Quantifier) {
        throw gcnew Z3Error(ErrorCode::InvalidArgument);
    }
    RawQuantifier^ t = gcnew RawQuantifier();
    Z3_ast ast = get_ast(a);
    t->IsForall = Z3_TRUE == Z3_is_quantifier_forall(ctx(), ast);
    t->Weight   = Z3_get_quantifier_weight(ctx(), ast);
    t->Patterns = gcnew array<PatternPtr>(Z3_get_quantifier_num_patterns(ctx(), ast));
    t->NoPatterns = gcnew array<TermPtr>(Z3_get_quantifier_num_no_patterns(ctx(), ast));
    t->Sorts    = gcnew array<SortPtr>(Z3_get_quantifier_num_bound(ctx(), ast));
    t->Names    = gcnew array<Symbol^>(Z3_get_quantifier_num_bound(ctx(), ast));
    t->Body     = TermPtr(Z3_get_quantifier_body(ctx(), ast));
    for (int i = 0; i < t->Sorts->Length; ++i) {
        t->Sorts[i] = SortPtr(Z3_get_quantifier_bound_sort(ctx(), ast, i));
        t->Names[i] = gcnew Symbol(ctx(), Z3_get_quantifier_bound_name(ctx(), ast, i));
    }
    for (int i = 0; i < t->Patterns->Length; ++i) {
        t->Patterns[i] = PatternPtr(Z3_get_quantifier_pattern_ast(ctx(), ast, i));
    }
    for (int i = 0; i < t->NoPatterns->Length; ++i) {
        t->NoPatterns[i] = TermPtr(Z3_get_quantifier_no_pattern_ast(ctx(), ast, i));
    }
    return t;
};
 
array<TermPtr>^ RawContext::GetPatternTerms(PatternPtr p) {
    unsigned np = Z3_get_pattern_num_terms(ctx(), get_pattern(p));
    array<TermPtr>^ result = gcnew array<TermPtr>(np);
    for (unsigned i = 0; i < np; ++i) {
        result[i] = TermPtr(Z3_get_pattern(ctx(), get_pattern(p), i));
    }
    return result;
}

Symbol^ RawContext::GetDeclName(FuncDeclPtr d) {
    return gcnew Symbol(ctx(), Z3_get_decl_name(ctx(), get_func_decl(d)));
}

Symbol^ RawContext::GetSortName(SortPtr ty) {
    return gcnew Symbol(ctx(), Z3_get_sort_name(ctx(), get_sort(ty)));
}

SortPtr RawContext::GetSort(TermPtr a) {
    return SortPtr(Z3_get_sort(ctx(), get_ast(a)));
}

array<SortPtr>^ RawContext::GetDomain(FuncDeclPtr d) {
    unsigned num_args = Z3_get_domain_size(ctx(), get_func_decl(d));
    array<SortPtr>^ result = gcnew array<SortPtr>(num_args);
    for (unsigned i = 0; i < num_args; ++i) {
        result[i] = TermPtr(Z3_get_domain(ctx(), get_func_decl(d), i));
    }
    return result;
}


SortPtr RawContext::GetRange(FuncDeclPtr d) {
    return SortPtr(Z3_get_range(ctx(), get_func_decl(d)));
}

SortKind RawContext::GetSortKind(SortPtr t) {
    switch(Z3_get_sort_kind(ctx(), get_sort(t))) {
    case Z3_UNINTERPRETED_SORT: return SortKind::Uninterpreted;
    case Z3_BOOL_SORT: return SortKind::Bool;
    case Z3_INT_SORT: return SortKind::Int;
    case Z3_REAL_SORT: return SortKind::Real;
    case Z3_BV_SORT: return SortKind::BitVector;
    case Z3_ARRAY_SORT: return SortKind::Array;
    case Z3_DATATYPE_SORT: return SortKind::Datatype;
    case Z3_UNKNOWN_SORT: return SortKind::Unknown;
    default: UNREACHABLE(); return SortKind::Unknown;
    }
}

SearchFailureExplanation RawContext::GetSearchFailureExplanation() {
    return ConvertExplanation(Z3_get_search_failure(ctx()));
}

unsigned RawContext::GetBvSortSize(SortPtr t) {
    return Z3_get_bv_sort_size(ctx(), get_sort(t));
}

SortPtr RawContext::GetArraySortDomain(SortPtr t) {
    return SortPtr(Z3_get_array_sort_domain(ctx(), get_sort(t)));
}

SortPtr RawContext::GetArraySortRange(SortPtr t) {
    return SortPtr(Z3_get_array_sort_range(ctx(), get_sort(t)));
}

FuncDeclPtr RawContext::GetTupleConstructor(SortPtr t) {
    return FuncDeclPtr(Z3_get_tuple_sort_mk_decl(ctx(), get_sort(t)));
}

array<FuncDeclPtr>^ RawContext::GetTupleFields(SortPtr t) {
    unsigned num_args = Z3_get_tuple_sort_num_fields(ctx(), get_sort(t));
    array<FuncDeclPtr>^ result = gcnew array<FuncDeclPtr>(num_args);
    for (unsigned i = 0; i < num_args; ++i) {
        result[i] = FuncDeclPtr(Z3_get_tuple_sort_field_decl(ctx(), get_sort(t), i));
    }
    return result;
}

void RawContext::Push() {
    Z3_push(ctx());
}
    
void RawContext::Pop(unsigned num_scopes) {
    Z3_pop(ctx(), num_scopes);
}

unsigned RawContext::GetNumScopes() {
    return Z3_get_num_scopes(ctx());
}

void RawContext::PersistTerm(TermPtr t, unsigned num_scopes) {
    Z3_persist_ast(ctx(), get_ast(t), num_scopes);
}

void RawContext::IncRef(IntPtr ast) {
    Z3_inc_ref(ctx(), get_ast(ast));
    // decrement reference counts of whatever is gc'ed.
    if (s_nonempty) {
        System::Threading::Monitor::Enter(s_monitor);
        for (int i = 0; i < s_todec->Count; ++i) {            
            AstPtr a = s_todec[i].Key;
            RawContext^ c = s_todec[i].Value;
            SASSERT(c->ref_context().is_ref_counted());
            Z3_dec_ref(c->ctx(), get_ast(a));
            c->ref_context().dec_ref();
        }
        s_todec->Clear();
        s_nonempty = false;
        System::Threading::Monitor::Exit(s_monitor);        
    }
}

void RawContext::EnqueueDecRef(IntPtr ast) {
    System::Threading::Monitor::Enter(s_monitor);
    s_todec->Add(KeyValuePair<AstPtr,RawContext^>(ast, this));
    s_nonempty = true;
    System::Threading::Monitor::Exit(s_monitor);
}

void RawContext::AssertCnstr(TermPtr a) {
    Z3_assert_cnstr(ctx(), get_ast(a));
}
    
LBool RawContext::CheckAndGetModel(RawModel^% m) {
    m = nullptr;
    Z3_model model = 0;
    Z3_lbool lb = Z3_check_and_get_model(ctx(), & model);

    if (model) {
        m = gcnew RawModel(*m_context, model);
    }
    else {
        m = nullptr;
    }
    return ToLBool(lb);
}

LBool RawContext::Check() {
    Z3_lbool lb = Z3_check(ctx());
    return ToLBool(lb);
}

LBool RawContext::CheckAssumptions(RawModel^% m, array<TermPtr>^ assumptions, TermPtr% proof, array<TermPtr>^% core) {
    scoped_Z3_ast_array<Z3_ast> _assumptions(assumptions);
    scoped_Z3_ast_array<Z3_ast> _core(assumptions);
    unsigned core_size = 0;
    Z3_ast _proof = 0;
    Z3_model model = 0;
    Z3_lbool lb = Z3_check_assumptions(
        ctx(),
        _assumptions.size(),
        _assumptions.c_ptr(),
        &model,
        &_proof,
        &core_size, 
        _core.c_ptr());

    core = gcnew array<TermPtr>(core_size);
    for (unsigned i = 0; i < core_size; ++i) {
        core[i] = TermPtr(_core[i]);
    }
    if(_proof) {
        proof = TermPtr(_proof);
    }
    if (model) {
        m = gcnew RawModel(*m_context, model);
    }
    return ToLBool(lb);    
}

void RawContext::SoftCheckCancel() {
    Z3_soft_check_cancel(ctx());
}

LBool RawContext::GetImpliedEqualities(
    [In]  array<TermPtr>^ terms,
    [Out] array<unsigned>^% class_ids) {
    scoped_Z3_ast_array<Z3_ast> _terms(terms);
    scoped_array<unsigned> _class_ids(_terms.size());
    Z3_lbool lb = Z3_get_implied_equalities(ctx(), _terms.size(), _terms.c_ptr(), _class_ids.c_ptr());
    class_ids = gcnew array<unsigned>(_terms.size());
    for (unsigned i = 0; i < _terms.size(); ++i) {
        class_ids[i] = _class_ids[i];
    }
    return ToLBool(lb);    
}

LabeledLiterals^ RawContext::GetRelevantLabels() {    
    Z3_literals lbls = Z3_get_relevant_labels(ctx());
    return gcnew LabeledLiterals(*m_context, lbls); 
}

LabeledLiterals^ RawContext::GetRelevantLiterals() {    
    Z3_literals lbls = Z3_get_relevant_literals(ctx());
    return gcnew LabeledLiterals(*m_context, lbls); 
}

LabeledLiterals^ RawContext::GetGuessedLiterals() {    
    Z3_literals lbls = Z3_get_guessed_literals(ctx());
    return gcnew LabeledLiterals(*m_context, lbls); 
}

void RawContext::BlockLiterals(LabeledLiterals^ lbls) {
    Z3_block_literals(ctx(), lbls->Get());
}

TermPtr RawContext::Simplify(TermPtr a) {    
    return TermPtr(Z3_simplify(ctx(), get_ast(a)));
}


String^ RawContext::ToString() {
    return gcnew String(Z3_context_to_string(ctx()));
}

void RawContext::SetPrintMode(PrintMode mode) {
    Z3_ast_print_mode m = Z3_PRINT_SMTLIB_FULL;
    switch(mode) {
    case PrintMode::SmtlibFull:
        m = Z3_PRINT_SMTLIB_FULL;
        break;
    case PrintMode::LowLevel:
        m = Z3_PRINT_LOW_LEVEL;
        break;
    case PrintMode::Smtlib2Compliant:
        m = Z3_PRINT_SMTLIB2_COMPLIANT;
        break;
    case PrintMode::SmtlibCompliant:
        m = Z3_PRINT_SMTLIB_COMPLIANT;
        break;
    default:
        UNREACHABLE();
        break;
    }
    Z3_set_ast_print_mode(ctx(), m);
}

void RawContext::Display(System::IO::TextWriter^ w) {
    w->Write(ToString());
}

String^ RawContext::BenchmarkToSmtlib(
    String^ name,
    String^ logic,
    String^ status,
    String^ attributes,
    array<TermPtr>^ assumptions,
    TermPtr formula) {
    scoped_Z3_ast_array<Z3_ast> _assumptions(assumptions);
    return gcnew String(Z3_benchmark_to_smtlib_string(
                            ctx(), 
                            (name )?CreateString(name).c_str():0,
                            (logic )?CreateString(logic).c_str():0,
                            (status )?CreateString(status).c_str():0,
                            (attributes )?CreateString(attributes).c_str():0,
                            _assumptions.size(),
                            _assumptions.c_ptr(),
                            get_ast(formula)));                                               
}


void RawContext::ParseSmtlibString(
    String^ string,
    [In]  array<SortPtr>^     sorts,
    [In]  array<FuncDeclPtr>^ old_decls,
    [Out] array<TermPtr>^%    assumptions,            
    [Out] array<TermPtr>^%    formulas,
    [Out] array<FuncDeclPtr>^% new_decls,
    [Out] array<SortPtr>^%    new_sorts,
    [Out] String^% parser_out
    )
{
    scoped_Z3_ast_array<Z3_sort> _types(sorts);
    scoped_Z3_ast_array<Z3_func_decl> _decls(old_decls);
    scoped_Z3_symbol_array _sort_names(_types.size());
    scoped_Z3_symbol_array _decl_names(_decls.size());
    for (unsigned i = 0; i < _sort_names.size(); ++i) {
        _sort_names[i] = Z3_get_sort_name(ctx(), _types[i]);
    }
    for (unsigned i = 0; i < _decl_names.size(); ++i) {
        _decl_names[i] = Z3_get_decl_name(ctx(), _decls[i]);
    }

    try {
      Z3_parse_smtlib_string(
        ctx(),
        CreateString(string).c_str(),
        _types.size(),
        _sort_names.c_ptr(),
        _types.c_ptr(),        
        _decls.size(),
        _decl_names.c_ptr(),
        _decls.c_ptr()
        );
    }
    catch(...) {
        parser_out = gcnew String(Z3_get_smtlib_error(ctx()));
        throw;
    }
    parser_out = gcnew String(Z3_get_smtlib_error(ctx()));

    unsigned count = Z3_get_smtlib_num_formulas(ctx());
    formulas = gcnew array<TermPtr>(count);
    for (unsigned i = 0; i < count; ++i) {
        formulas[i] = TermPtr(Z3_get_smtlib_formula(ctx(), i));
    }

    count = Z3_get_smtlib_num_assumptions(ctx());
    assumptions = gcnew array<TermPtr>(count);
    for (unsigned i = 0; i < count; ++i) {
        assumptions[i] = TermPtr(Z3_get_smtlib_assumption(ctx(), i));
    }

    count = Z3_get_smtlib_num_decls(ctx());
    new_decls = gcnew array<FuncDeclPtr>(count);
    for (unsigned i = 0; i < count; ++i) {
        new_decls[i] = FuncDeclPtr(Z3_get_smtlib_decl(ctx(), i));
    }    
    count = Z3_get_smtlib_num_sorts(ctx());
    new_sorts = gcnew array<SortPtr>(count);
    for (unsigned i = 0; i < count; ++i) {
        new_sorts[i] = SortPtr(Z3_get_smtlib_sort(ctx(), i));
    }    
}

void RawContext::ParseSmtlibFile(
    String^             file,
    [In]  array<SortPtr>^     sorts,
    [In]  array<FuncDeclPtr>^ old_decls,
    [Out] array<TermPtr>^%    assumptions,            
    [Out] array<TermPtr>^%    formulas,
    [Out] array<FuncDeclPtr>^% new_decls,
    [Out] array<SortPtr>^%    new_sorts,
    [Out] String^% parser_out
    )
{
    scoped_Z3_ast_array<Z3_sort> _sorts(sorts);
    scoped_Z3_ast_array<Z3_func_decl> _decls(old_decls);
    scoped_Z3_symbol_array _sort_names(_sorts.size());
    scoped_Z3_symbol_array _decl_names(_decls.size());
    for (unsigned i = 0; i < _sort_names.size(); ++i) {
        _sort_names[i] = Z3_get_sort_name(ctx(), _sorts[i]);
    }
    for (unsigned i = 0; i < _decl_names.size(); ++i) {
        _decl_names[i] = Z3_get_decl_name(ctx(), _decls[i]);
    }

    try {
        Z3_parse_smtlib_file(
            ctx(),
            CreateString(file).c_str(),
            _sorts.size(),
            _sort_names.c_ptr(),
            _sorts.c_ptr(),
            _decls.size(),
            _decl_names.c_ptr(),
            _decls.c_ptr()
            );
    }
    catch(...) {
        parser_out = gcnew String(Z3_get_smtlib_error(ctx()));
        throw;
    }
    parser_out = gcnew String(Z3_get_smtlib_error(ctx()));

    unsigned count = Z3_get_smtlib_num_formulas(ctx());
    formulas = gcnew array<TermPtr>(count);
    for (unsigned i = 0; i < count; ++i) {
        formulas[i] = TermPtr(Z3_get_smtlib_formula(ctx(), i));
    }

    count = Z3_get_smtlib_num_assumptions(ctx());
    assumptions = gcnew array<TermPtr>(count);
    for (unsigned i = 0; i < count; ++i) {
        assumptions[i] = TermPtr(Z3_get_smtlib_assumption(ctx(), i));
    }

    count = Z3_get_smtlib_num_decls(ctx());
    new_decls = gcnew array<FuncDeclPtr>(count);
    for (unsigned i = 0; i < count; ++i) {
        new_decls[i] = FuncDeclPtr(Z3_get_smtlib_decl(ctx(), i));
    }
    count = Z3_get_smtlib_num_sorts(ctx());
    new_sorts = gcnew array<SortPtr>(count);
    for (unsigned i = 0; i < count; ++i) {
        new_sorts[i] = SortPtr(Z3_get_smtlib_sort(ctx(), i));
    }    
}





TermPtr RawContext::ParseZ3String(String^ s) {
    return TermPtr(Z3_parse_z3_string(ctx(), CreateString(s).c_str()));    
}

TermPtr RawContext::ParseZ3File(String^ file) {
    return TermPtr(Z3_parse_z3_file(ctx(), CreateString(file).c_str()));
}


#define PROCESS_SMTLIB2(_fn) \
    scoped_Z3_ast_array<Z3_sort> _sorts(sorts);         \
    scoped_Z3_ast_array<Z3_func_decl> _decls(decls);    \
    scoped_Z3_symbol_array _sort_names(_sorts.size());  \
    scoped_Z3_symbol_array _decl_names(_decls.size());  \
    for (unsigned i = 0; i < _sort_names.size(); ++i) {                 \
        _sort_names[i] = Z3_get_sort_name(ctx(), _sorts[i]);        \
                std::cout << Z3_get_symbol_string(ctx(), _sort_names[i]) << "\n"; \
    }                                                                   \
    for (unsigned i = 0; i < _decl_names.size(); ++i) {                 \
        _decl_names[i] = Z3_get_decl_name(ctx(), _decls[i]);        \
            std::cout << Z3_get_symbol_string(ctx(), _decl_names[i]) << "\n"; \
    }                                                                   \
    return TermPtr(_fn(ctx(), CreateString(s).c_str(), \
                       _sorts.size(), _sort_names.c_ptr(), _sorts.c_ptr(), \
                       _decls.size(), _decl_names.c_ptr(), _decls.c_ptr())); \
    

TermPtr RawContext::ParseSmtlib2String(String^ s, array<SortPtr>^ sorts, array<FuncDeclPtr>^ decls) {
    PROCESS_SMTLIB2(Z3_parse_smtlib2_string);
}

TermPtr RawContext::ParseSmtlib2File(String^ s, array<SortPtr>^ sorts, array<FuncDeclPtr>^ decls) {
    PROCESS_SMTLIB2(Z3_parse_smtlib2_file);
}

TermPtr RawContext::ExecSmtlib2String(String^ s, array<SortPtr>^ sorts, array<FuncDeclPtr>^ decls) {
    PROCESS_SMTLIB2(Z3_exec_smtlib2_string);
}

TermPtr RawContext::ExecSmtlib2File(String^ s, array<SortPtr>^ sorts, array<FuncDeclPtr>^ decls) {
    PROCESS_SMTLIB2(Z3_exec_smtlib2_file);
}

void RawContext::SetErrorHandler(IErrorHandler^ h) {
    m_error_handler = h;
}


String^ RawContext::GetErrorMessage(ErrorCode h) {
    Z3_error_code code;
    switch(h) {
    case ErrorCode::Ok: code = Z3_OK; break;
    case ErrorCode::TypeError: code = Z3_SORT_ERROR; break;
    case ErrorCode::IndexOutOfBounds: code = Z3_IOB; break;
    case ErrorCode::InvalidArgument: code = Z3_INVALID_ARG; break;
    case ErrorCode::ParserError: code = Z3_PARSER_ERROR; break;
    case ErrorCode::NoParser: code = Z3_NO_PARSER; break;
    case ErrorCode::InvalidUsage: code = Z3_INVALID_USAGE; break;
    case ErrorCode::InternalFatal:
    case ErrorCode::FileAccessError:
        code = Z3_INVALID_ARG;
        break;
    default:
        UNREACHABLE();
        code = Z3_INVALID_ARG;
    }
    return gcnew String(Z3_get_error_msg(code));
}

void RawContext::ResetMemory() {
    Z3_reset_memory();
}

String^ RawContext::ToString(AstPtr a) {
    return gcnew String(Z3_ast_to_string(ctx(), get_ast(a)));
}

void RawContext::Display(System::IO::TextWriter^ w, AstPtr a) {
    w->Write(ToString(a));
}

                                    
void RawContext::GetVersion(unsigned% major, unsigned% minor, unsigned% build_number, unsigned% version_number) {
    unsigned ma, mi, bn, vn;
    Z3_get_version(&ma,&mi,&bn,&vn);
    major = ma;
    minor = mi;
    build_number = bn;
    version_number = vn;
}

// -----------------------------
// Ast

Ast::Ast(RawContext^ c, AstPtr a) : m_ast(a), m_ctx(c) {
    SASSERT(m_ast != IntPtr(0));
    if (c->ref_context().is_ref_counted()) {    
        c->IncRef(a);
        c->ref_context().inc_ref();
    }
}

Ast::!Ast() {
    if (m_ctx->ref_context().is_ref_counted()) {
        m_ctx->EnqueueDecRef(m_ast);
    }
}

Ast::~Ast() {}

bool Ast::Equals(Object^ obj) {
    if (!obj) {
        return false;
    }
    Ast^ a = dynamic_cast<Ast^>(obj);
    if (!a) {
        return false;
    }
    return a->GetPtr() == GetPtr();
}

int Ast::GetHashCode() {
    return GetId();
}

String^ Ast::ToString() {
    return m_ctx->ToString(m_ast);
}

int Ast::CompareTo(Object^ other) {
    Ast^ a = dynamic_cast<Ast^>(other);
    if (!a) {
        return -1;
    }
    return GetId() - a->GetId();
}

#if 0
bool Ast::operator==(Object^ other) {
    return this->Equals(other);
}

bool Ast::operator!=(Object^ other) {
    return !this->Equals(other);
}
#endif

String^ Sort::GetName() {
    return m_ctx->GetSymbolString(m_ctx->GetSortName(m_ast));
}

String^ FuncDecl::GetDeclName() {
    return m_ctx->GetSymbolString(m_ctx->GetDeclName(m_ast));
}

DeclKind FuncDecl::GetKind() {
    return m_ctx->GetDeclKind(m_ast);
}

// ----------------------------
// Term
// Assumption: contexts are equal
// Note: overloading && and || is possible, 
// but C# does not seem to perform the 
// correct type inference when they are used.

Term^ Term::operator!(Term^ t) {
    return gcnew Term(t->m_ctx, t->m_ctx->MkNot(t()));
}

Term^ Term::operator+(Term^ t1, Term^ t2) {    
    return gcnew Term(t1->m_ctx, t1->m_ctx->MkAdd(t1(), t2()));
}

Term^ Term::operator^(Term^ t1, Term^ t2) {    
    return gcnew Term(t1->m_ctx, t1->m_ctx->MkXor(t1(), t2()));
}

Term^ Term::operator&(Term^ t1, Term^ t2) {    
    return gcnew Term(t1->m_ctx, t1->m_ctx->MkAnd(t1(), t2()));
}

Term^ Term::operator|(Term^ t1, Term^ t2) {    
    return gcnew Term(t1->m_ctx, t1->m_ctx->MkOr(t1(), t2()));
}
Term^ Term::operator*(Term^ t1, Term^ t2) {
    return gcnew Term(t1->m_ctx, t1->m_ctx->MkMul(t1(), t2()));
}

Term^ Term::operator-(Term^ t1, Term^ t2) {
    return gcnew Term(t1->m_ctx, t1->m_ctx->MkSub(t1(), t2()));
}

Term^ Term::operator/(Term^ t1, Term^ t2) {
    return gcnew Term(t1->m_ctx, t1->m_ctx->MkDiv(t1(), t2()));
}

Term^ Term::operator<(Term^ t1, Term^ t2) {
    return gcnew Term(t1->m_ctx, t1->m_ctx->MkLt(t1(), t2()));
}

Term^ Term::operator<=(Term^ t1, Term^ t2) {
    return gcnew Term(t1->m_ctx, t1->m_ctx->MkLe(t1(), t2()));
}

Term^ Term::operator>(Term^ t1, Term^ t2) {
    return gcnew Term(t1->m_ctx, t1->m_ctx->MkGt(t1(), t2()));
}

Term^ Term::operator>=(Term^ t1, Term^ t2) {
    return gcnew Term(t1->m_ctx, t1->m_ctx->MkGe(t1(), t2()));
}

Term^ Term::operator[](Term^ index) {
    return gcnew Term(m_ctx, m_ctx->MkArraySelect(m_ast, index()));
}

TermKind Term::GetKind() {
    return m_ctx->GetTermKind(m_ast);
}

FuncDecl^ Term::GetAppDecl() {
    return gcnew FuncDecl(m_ctx, m_ctx->GetAppDecl(m_ast));
}

array<Term^>^ Term::GetAppArgs() {
    return Context::CopyTermArray(m_ctx, m_ctx->GetAppArgs(m_ast));
}

Sort^ Term::GetSort() {
    return gcnew Sort(m_ctx, m_ctx->GetSort(m_ast));
}

String^ Term::GetNumeralString() {
    return m_ctx->GetNumeralString(m_ast);
}

unsigned Term::GetVarIndex() {
    return m_ctx->GetVarIndex(m_ast);
}

Quantifier^ Term::GetQuantifier() {
    return Context::GetQuantifier(m_ctx, this);
}
// -----------------------------
// Context


LBool Context::CheckAndGetModel(Model^% m) {
    RawModel^ md = nullptr;
    LBool is_sat = m_ctx->CheckAndGetModel(md); 
    if (md ) {
        m = gcnew Model(md, this);
    }
    else {
        md = nullptr;
    }
    return is_sat;
}

LBool Context::CheckAssumptions(
    Model^% m, array<Term^>^ assumptions, Term^% proof, array<Term^>^% core) {
    RawModel^ md = nullptr;
    array<TermPtr>^ _core = nullptr;
    TermPtr _proof;
    LBool is_sat = m_ctx->CheckAssumptions(md, CopyArray(assumptions), _proof, _core); 
    core  = nullptr;
    proof = nullptr;
    m = nullptr;
    if (md ) {
        m = gcnew Model(md, this);
    }
    if (_proof != TermPtr()) {
        proof = gcnew Term(m_ctx, _proof);
    }
    if (_core ) {
        core = CopyTermArray(_core);
    }
    return is_sat;
}

void Context::SoftCheckCancel() {
    m_ctx->SoftCheckCancel();
}


LBool Context::GetImpliedEqualities(
    [In]  array<Term^>^ terms,
    [Out] array<unsigned>^% class_ids) {
    return m_ctx->GetImpliedEqualities(CopyArray(terms), class_ids);
}



Quantifier^ Context::GetQuantifier(RawContext^ ctx, Term^ t) {
    RawQuantifier^ q0 = ctx->GetQuantifier(t());
    Quantifier^ q = gcnew Quantifier();
    q->IsForall = q0->IsForall;
    q->Weight = q0->Weight;    
    q->Patterns = gcnew array<Pattern^>(q0->Patterns->Length);
    for (int i = 0; i < q0->Patterns->Length; ++i) {
        q->Patterns[i] = gcnew Pattern(ctx, q0->Patterns[i]);
    }
    q->NoPatterns = gcnew array<Term^>(q0->NoPatterns->Length);
    for (int i = 0; i < q0->NoPatterns->Length; ++i) {
        q->NoPatterns[i] = gcnew Term(ctx, q0->Patterns[i]);
    }
    q->Names = q0->Names;
    q->Body = gcnew Term(ctx, q0->Body);
    q->Sorts = CopySortArray(ctx, q0->Sorts);
    return q;
}


Sort^ Context::MkTupleSort(
    Symbol^               mk_tuple_name, 
    array<Symbol^>^       field_names,
    array<Sort^>^       field_types,
    FuncDecl^%         mk_tuple_decl,
    array<FuncDecl^>^  proj_decl
    ) {
    array<SortPtr>^ ftypes = gcnew array<SortPtr>(field_types->Length);
    for (int i = 0; i < field_types->Length; ++i) {
        ftypes[i] = field_types[i]();
    }
    array<FuncDeclPtr>^ pdecls = gcnew array<FuncDeclPtr>(proj_decl->Length);
    FuncDeclPtr mk_tupled;
    SortPtr res = m_ctx->MkTupleSort(mk_tuple_name, field_names, ftypes, mk_tupled, pdecls);
    for (int i = 0; i < pdecls->Length; ++i) {
        proj_decl[i] = gcnew FuncDecl(m_ctx,pdecls[i]);
    }
    mk_tuple_decl = gcnew FuncDecl(m_ctx,mk_tupled);
    return gcnew Sort(m_ctx,res);
}

Sort^ Context::MkTupleSort(
    String^               mk_tuple_name, 
    array<String^>^       field_names,
    array<Sort^>^       field_types,
    FuncDecl^%         mk_tuple_decl,
    array<FuncDecl^>^  proj_decl
    ) {
    array<SortPtr>^ ftypes = gcnew array<SortPtr>(field_types->Length);
    for (int i = 0; i < field_types->Length; ++i) {
        ftypes[i] = field_types[i]();
    }
    array<FuncDeclPtr>^ pdecls = gcnew array<FuncDeclPtr>(proj_decl->Length);
    FuncDeclPtr mk_tupled;
    SortPtr res = m_ctx->MkTupleSort(mk_tuple_name, field_names, ftypes, mk_tupled, pdecls);
    for (int i = 0; i < pdecls->Length; ++i) {
        proj_decl[i] = gcnew FuncDecl(m_ctx,pdecls[i]);
    }
    mk_tuple_decl = gcnew FuncDecl(m_ctx,mk_tupled);
    return gcnew Sort(m_ctx,res);
}

Sort^ Context::MkEnumerationSort(
    String^           name,
    array<String^>^   enum_names,
    array<FuncDecl^>^ enum_consts,
    array<FuncDecl^>^ enum_testers) {

    array<FuncDeclPtr>^ _enum_consts  = CopyArray(enum_consts);
    array<FuncDeclPtr>^ _enum_testers = CopyArray(enum_testers);

    SortPtr s = m_ctx->MkEnumerationSort(name, enum_names, _enum_consts, _enum_testers);

    for (int i = 0; i < enum_consts->Length; ++i) {
        enum_consts[i] = gcnew FuncDecl(m_ctx, _enum_consts[i]);
        enum_testers[i] = gcnew FuncDecl(m_ctx, _enum_testers[i]);
    }
    return gcnew Sort(m_ctx, s);
}

Sort^ Context::MkListSort(
    String^ name,
    Sort^ elem_sort,
    FuncDecl^% nil_decl,
    FuncDecl^% is_nil_decl,
    FuncDecl^% cons_decl,
    FuncDecl^% is_cons_decl,
    FuncDecl^% head_decl,
    FuncDecl^% tail_decl
    ) {
    FuncDeclPtr a, b, c, d, e, f;
    SortPtr s = m_ctx->MkListSort(name, elem_sort(), a, b, c, d, e, f);
    nil_decl = gcnew FuncDecl(m_ctx, a);
    is_nil_decl = gcnew FuncDecl(m_ctx, b);
    cons_decl = gcnew FuncDecl(m_ctx, c);
    is_cons_decl = gcnew FuncDecl(m_ctx, d);
    head_decl = gcnew FuncDecl(m_ctx, e);
    tail_decl = gcnew FuncDecl(m_ctx, f);
    return gcnew Sort(m_ctx, s);
}
        
Constructor^ Context::MkConstructor(
    String^ name,
    String^ tester,
    array<String^>^ field_names,
    array<Sort^>^ field_sorts,
    array<unsigned>^ field_refs
    ) {
    return m_ctx->MkConstructor(name, tester, field_names, CopyArray(field_sorts), field_refs);
}

        
FuncDecl^ Context::GetConstructor(Constructor^ c) { 
    return gcnew FuncDecl(m_ctx, m_ctx->GetConstructor(c)); 
}

FuncDecl^ Context::GetTester(Constructor^ c) { 
    return gcnew FuncDecl(m_ctx, m_ctx->GetTester(c)); 
}

array<FuncDecl^>^ Context::GetAccessors(Constructor^ c) { 
    array<FuncDeclPtr>^ result = m_ctx->GetAccessors(c);
    return CopyAstArray<FuncDecl, FuncDeclPtr>(result);
}


bool Model::TryGetArrayValue(Term^ v, ArrayValue^% av) {
    RawArrayValue^ _av = nullptr;
    if (m_model->TryGetArrayValue(v(), _av)) {
        av = gcnew ArrayValue();
        av->ElseCase = gcnew Term(m_ctx->GetContext, _av->ElseCase);
        av->Domain = m_ctx->CopyAstArray<Term>(_av->Domain);
        av->Range = m_ctx->CopyAstArray<Term>(_av->Range);
        return true;
    }
    else {
        return false;
    }
}

array<IParameter^>^ Context::GetDeclParameters(FuncDecl^ d) {
    Z3_context ctx = m_ctx->ctx();
    Z3_func_decl fd = get_func_decl(d());
    unsigned num_params = Z3_get_decl_num_parameters(ctx, fd);
    array<IParameter^>^ params = gcnew array<IParameter^>(num_params);
    for (unsigned i = 0; i < num_params; ++i) {
        switch(Z3_get_decl_parameter_kind(ctx, fd, i)) {
        case Z3_PARAMETER_INT:
            params[i] = gcnew IntParameter(Z3_get_decl_int_parameter(ctx, fd, i));
            break;
        case Z3_PARAMETER_DOUBLE:
            params[i] = gcnew DoubleParameter(Z3_get_decl_double_parameter(ctx, fd, i));
            break;
        case Z3_PARAMETER_RATIONAL: {
            Z3_string s = Z3_get_decl_rational_parameter(ctx, fd, i);
            params[i] = gcnew RationalParameter(gcnew String(s));
            break;
        }
        case Z3_PARAMETER_SYMBOL: {
            Z3_symbol s = Z3_get_decl_symbol_parameter(ctx, fd, i);
            params[i] = gcnew SymbolParameter(gcnew Symbol(ctx, s));
            break;
        }
        case Z3_PARAMETER_SORT:
            params[i] = gcnew SortParameter(gcnew Sort(m_ctx,SortPtr(Z3_get_decl_sort_parameter(ctx, fd, i))));
            break;
        case Z3_PARAMETER_AST:
            params[i] = gcnew TermParameter(gcnew Term(m_ctx,TermPtr(Z3_get_decl_ast_parameter(ctx, fd, i))));
            break;
        case Z3_PARAMETER_FUNC_DECL:
            params[i] = gcnew FuncDeclParameter(gcnew FuncDecl(m_ctx, FuncDeclPtr(Z3_get_decl_func_decl_parameter(ctx, fd, i))));
            break;
        default:
            UNREACHABLE();
            break;
        }
    }
    return params;
}

String^ Context::BenchmarkToSmtlib(
    String^ name,
    String^ logic,
    String^ status,
    String^ attributes,
    array<Term^>^ assumptions,
    Term^ formula) {
    return m_ctx->BenchmarkToSmtlib(name, logic, status, attributes, CopyArray(assumptions), formula());
 }

void Context::ParseSmtlibString(
    String^            string,
    [In]  array<Sort^>^     types,
    [In]  array<FuncDecl^>^ old_decls,
    [Out] array<Term^>^%    assumptions,            
    [Out] array<Term^>^%    formulas,
    [Out] array<FuncDecl^>^% new_decls,
    [Out] array<Sort^>^%     new_sorts,
    [Out] String^%           parser_out
    ) {
    array<TermPtr>^ _assumptions = nullptr;
    array<TermPtr>^ _formulas = nullptr;
    array<FuncDeclPtr>^ _new_decls = nullptr;
    array<SortPtr>^ _new_sorts = nullptr;
    m_ctx->ParseSmtlibString(string, CopyArray(types), CopyArray(old_decls), 
                             _assumptions, _formulas, _new_decls, _new_sorts, parser_out);
    assumptions = CopyTermArray(_assumptions);
    formulas = CopyTermArray(_formulas);
    new_decls = CopyAstArray<FuncDecl, FuncDeclPtr>(_new_decls);
    new_sorts = CopyAstArray<Sort, SortPtr>(_new_sorts);
}


void Context::ParseSmtlibFile(
    String^ file,
    [In]  array<Sort^>^      types,
    [In]  array<FuncDecl^>^  old_decls,
    [Out] array<Term^>^%     assumptions,            
    [Out] array<Term^>^%     formulas,
    [Out] array<FuncDecl^>^% new_decls,
    [Out] array<Sort^>^%     new_sorts,
    [Out] String^%           parser_out
    ) {
    array<TermPtr>^ _assumptions = nullptr;
    array<TermPtr>^ _formulas = nullptr;
    array<FuncDeclPtr>^ _new_decls = nullptr;
    array<SortPtr>^ _new_sorts = nullptr;
    m_ctx->ParseSmtlibFile(file, CopyArray(types), CopyArray(old_decls),
                           _assumptions, _formulas, _new_decls, _new_sorts, parser_out);
    assumptions = CopyAstArray<Term,TermPtr>(_assumptions);
    formulas    = CopyAstArray<Term,TermPtr>(_formulas);
    new_decls   = CopyAstArray<FuncDecl, FuncDeclPtr>(_new_decls);
    new_sorts   = CopyAstArray<Sort, SortPtr>(_new_sorts);
}

// -----------------------------
// Model

ArrayValue^ Model::Mk(RawArrayValue^ av) {
    ArrayValue^ res = gcnew ArrayValue();
    res->Domain = m_ctx->CopyTermArray(av->Domain);
    res->Range = m_ctx->CopyTermArray(av->Range);
    res->ElseCase = gcnew Term(m_ctx->GetContext, av->ElseCase);
    return res;
}

FunctionEntry^ Model::Mk(RawFunctionEntry^ fe) {
    FunctionEntry^ res = gcnew FunctionEntry();
    res->Arguments = m_ctx->CopyTermArray(fe->Arguments);
    res->Result = gcnew Term(m_ctx->GetContext, fe->Result);
    return res;
}

FunctionGraph^ Model::Mk(RawFunctionGraph^ fg) {
    FunctionGraph^ res = gcnew FunctionGraph();
    res->Declaration = gcnew FuncDecl(m_ctx->GetContext, fg->Declaration);
    res->Entries = gcnew array<FunctionEntry^>(fg->Entries->Length);
    for (int i = 0; i < fg->Entries->Length; ++i) {
        res->Entries[i] = Mk(fg->Entries[i]);
    }
    res->Else = gcnew Term(m_ctx->GetContext, fg->Else);
    return res;
}

Dictionary<FuncDecl^, FunctionGraph^>^ Model::Mk(Dictionary<FuncDeclPtr, RawFunctionGraph^>^ fgs) {
    Dictionary<FuncDecl^, FunctionGraph^>^ res =
        gcnew Dictionary<FuncDecl^, FunctionGraph^>();
    
    Dictionary<FuncDeclPtr, RawFunctionGraph^>::Enumerator e = fgs->GetEnumerator();
    while(e.MoveNext()) {
        KeyValuePair<FuncDeclPtr, RawFunctionGraph^>^ kv = e.Current;
        res->Add(gcnew FuncDecl(m_ctx->GetContext, kv->Key), Mk(kv->Value));
    }
    return res;
}

Theory^ Context::MkTheory(String^ name) {
    return gcnew Theory(this, name);
}
