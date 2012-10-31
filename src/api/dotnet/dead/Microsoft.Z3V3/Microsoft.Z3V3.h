/*++
Copyright (c) 2007 Microsoft Corporation

Module Name:

    Microsoft.Z3V3.h

Abstract:

    Z3 Managed API.

Author:

    Nikolaj Bjorner (nbjorner)
    Leonardo de Moura (leonardo) 2007-06-8

Notes:

    This API is deprecated and support for this is discontinued.
    It is superseeded by the new Microsoft.Z3 API.
    
--*/

#ifndef _MICROSOFT_Z3V3_H__
#define _MICROSOFT_Z3V3_H__

struct _Z3_model {};
struct _Z3_config {};
struct _Z3_context {};
struct _Z3_func_decl {};
struct _Z3_app {};
struct _Z3_sort {};
struct _Z3_symbol {};
struct _Z3_ast {};
struct _Z3_literals {};
struct _Z3_pattern {};
struct _Z3_constructor {};
struct _Z3_constructor_list {};
typedef _Z3_literals *Z3_literals;
struct _Z3_theory {};
struct _Z3_ast_vector {};
struct _Z3_fixedpoint {};

using namespace System;
using namespace System::Collections::Generic;
using namespace System::Runtime::InteropServices;
using namespace System::Numerics;


#include "..\lib\z3.h"

namespace Microsoft {
namespace Z3V3 {

    class ref_context {
        unsigned   m_count;
        bool       m_owned;
        bool       m_scoped;
        Z3_context m_ctx;
        Z3_fixedpoint m_dl;
    ref_context(Z3_context ctx, bool owned, bool scoped): m_count(1), m_owned(owned), m_scoped(scoped), m_ctx(ctx), m_dl(0) {}
    public:
        static ref_context* mk(Z3_context ctx, bool owned, bool scoped);
        void dec_ref();
        void inc_ref();
        Z3_context operator()() { return m_ctx; }
        ~ref_context() {}
        bool is_ref_counted() const { return !is_scoped(); }
        bool is_scoped() const { return m_scoped; }
        Z3_fixedpoint dl();
    };

/**
   \defgroup mapi Managed (.NET) API
*/
/*@{*/

    public ref class Z3Log {
        static bool m_open = false;
    public:
        /**
           \brief Log assertions to a file.
           
           \sa Close
           
           Returns \c true if the open succeeds, otherwise \c false.
        */
        static bool Open(String^ filename);

        /**
           \brief Return true if the log is open.
        */
        static bool IsOpen() { return m_open; }
        
        /**
           \brief Append user comment to log.
           
           \sa Open
        */
        static void Append(String^ string);
        
        /**
           \brief Close file with logged API calls.
           
           \sa Open
        */
        static void Close();
    };
    
    /** 
        \brief Symbol.

        Wrapper class for string or integer symbols.
        This class remains unsafe. You cannot access the ToString()
        method after the owning context has been deleted.
        We don't use dispose pattern here. I believe it would be too 
        awkward to manage.
    */
    public ref class Symbol {
        Z3_context   m_ctx;
        Z3_symbol    m_symbol;
    internal:
        Symbol(Z3_context c, Z3_symbol s) : m_ctx(c), m_symbol(s) { }
        Z3_symbol get() { return m_symbol; }      
    public:
        virtual String^ ToString() override;
    };

    /**
       \brief Lifted Booleans.

       The result of m_context->Check() is a lifted Boolean. When Z3 is unable to 
       decide whether the result is satisfiable or unsatisfiable it returns
       Undef.
    */
    
    public enum class LBool
    {
        True,
        False,
        Undef
    };

    /**
       \brief Z3 error codes.
   
       - Ok,            
       - TypeError:             User tried to build an invalid (type incorrect) AST.
       - IndexOutOfBounds:      Index out of bounds 
       - InvalidArgument::      Invalid argument was provided
       - ParserError:           An error occurred when parsing a string or file.
       - NoParser:              Parser output is not available, that is, user didn't invoke ParseSmtlibString or ParseSmtlibFile.
       - InvalidPattern:        An invalid pattern was used to build a quantifier.
       - InternalFatal:         An internal fatal error was encountered.
       - InvalidUsage:          The API was used in an invalid context.
       - FileAccessError:       File access failed for an inaccessible file.
       - NonDisposedConfig      A configuration was not disposed explictly.
       - NonDisposedContext:    A context was not disposed explictly.
       - NonDisposedLiterals:   A conflict literal set was not disposed explicitly.
       - NonDisposedModel:      A model was not disposed of explicitly.

       There is no error code for out of memory errors.
       Z3 will throw the library exception <tt>OutOfMemoryException</tt>
       if memory allocation fails. Users should call ResetMemory() 
       to reclaim all allocated resources.
       
    */

    public enum class ErrorCode 
    {
        Ok,
        TypeError,
        IndexOutOfBounds,
        InvalidArgument,
        ParserError,
        NoParser,
        InvalidPattern,
        InternalFatal,
        InvalidUsage,
        FileAccessError,
        NonDisposedConfig,
        NonDisposedContext,
        NonDisposedLiterals,
        NonDisposedModel
    };

    /**
       \brief Z3 pretty printing modes used when pretty printing terms.

       - SmtlibFull:    Print AST nodes in SMTLIB verbose format.
       - LowLevel:      Print AST nodes using a low-level format.
       - SmtlibCompliant Print AST in SMTLIB 1.x compliant format.
       - Smtlib2Compliant Print AST in SMTLIB 1.x compliant format.
    */
    public enum class PrintMode 
    {
        SmtlibFull,
        LowLevel,
        SmtlibCompliant,
        Smtlib2Compliant
    };

    /**
        \brief Z3 error exceptions contain an \c ErrorCode.

        A \c Z3Error exception gets raised on errors caused by
        malformed calls into the #Context.
    */
    public ref class Z3Error : Exception {
    public:
        Z3Error(ErrorCode c) { Code = c; InternalCode = 0; }
        Z3Error(int i) { Code = ErrorCode::Ok; InternalCode = i; }
        ErrorCode Code;
        int       InternalCode;
    };

    
    /// @cond 0
    typedef IntPtr AstPtr;
    typedef IntPtr SortPtr;
    typedef IntPtr FuncDeclPtr;
    typedef IntPtr TermPtr;
    typedef IntPtr PatternPtr;
    typedef IntPtr AppPtr;


    Z3_func_decl get_func_decl(FuncDeclPtr t) { 
        if (t == IntPtr::Zero) {
            throw gcnew Z3Error(ErrorCode::InvalidArgument);
        }
        return static_cast<Z3_func_decl>(t.ToPointer()); 
    }
    Z3_ast get_ast(TermPtr t) { 
        if (t == IntPtr::Zero) {
            throw gcnew Z3Error(ErrorCode::InvalidArgument);
        }
        return static_cast<Z3_ast>(t.ToPointer()); 
    }
    Z3_sort get_sort(SortPtr t) { 
        if (t == IntPtr::Zero) {
            throw gcnew Z3Error(ErrorCode::InvalidArgument);
        }
        return static_cast<Z3_sort>(t.ToPointer()); 
    }
    Z3_app get_const_ast(AppPtr c) { 
        if (c == IntPtr::Zero) {
            throw gcnew Z3Error(ErrorCode::InvalidArgument);
        }
        return static_cast<Z3_app>(c.ToPointer()); 
    }
    Z3_pattern get_pattern(PatternPtr p) { 
        if (p == IntPtr::Zero) {
            throw gcnew Z3Error(ErrorCode::InvalidArgument);
        }
        return static_cast<Z3_pattern>(p.ToPointer()); 
    }

    /// @endcond


    
    /**
       \brief In Z3, a symbol can be represented using integers and strings (See #GetSymbolKind).

       \sa MkIntSymbol
       \sa MkStringSymbol
    */
    public enum class SymbolKind 
    {
        Int, 
        String
    };

    /**
       \brief The different kinds of Z3 sorts (See #GetSortKind).
    */
    public enum class SortKind 
    {
        Uninterpreted,
        Bool,
        Int,
        Real,
        BitVector,
        Array,
        Datatype,
        Unknown
    };

    /**
       \brief Different failure kinds.

        - NoFailure  
        - Unknown:
        - TimeOut:
        - MemOut:
        - UserCanceled:
        - MaxConflicts:
        - Theory:
        - Quantifiers:

    */
    public enum class SearchFailureExplanation
    {
        NoFailure,
        Unknown,
        TimeOut,
        MemOut,
        UserCanceled,
        MaxConflicts,
        Theory,
        Quantifiers
    };

    /**
       \brief The different kinds of Z3 Terms. 

       - Numeral:        numerals 
       - App:            constant and applications 
       - Var:            bound variables 
       - Quantifier:     quantifiers 
       - Unknown:        internal 
    */
    public enum class TermKind 
    {
        Numeral,
        App,
        Var,
        Quantifier,
        Unknown
    };
    

    /** \brief Different kinds of Z3 built-in declarations (See #GetDeclKind)

    */
    public enum class DeclKind 
    {
        // Basic operators
        True,
        False,
        Eq,
        Distinct,
        Ite,
        And,
        Or,
        Iff,
        Xor,
        Not,
        Implies,
        // Arithmetic
        ArithNum,
        Le,
        Ge,
        Lt,
        Gt,
        Add,
        Sub,
        Uminus,
        Mul,
        Div,
        IDiv,
        Rem,
        Mod,
        ToReal,
        ToInt,
        IsInt,
        // Arrays
        Store,
        Select,
        ConstArray,
        DefaultArray,
        MapArray,
        Union,
        Intersect,
        Difference,
        Complement,
        Subset,
        AsArray,
        // Bit-vectors.            

        BitNum,
        Bit1,
        Bit0,
        BNeg,
        BAdd,
        BSub,
        BMul,
        BSDiv,
        BUDiv,
        BSRem,
        BURem,
        BSMod,

        BSDiv0,
        BUDiv0,
        BSRem0,
        BURem0,
        BSMod0,
        BULeq,
        BSLeq,
        BUGeq,
        BSGeq,
        BULt,
        BSLt,
        BUGt,
        BSGt,
        BAnd,
        BOr,
        BNot,
        BXor,
        BNand,
        BNor,
        BXnor,
        BConcat,
        BSignExt,
        BZeroExt,
        BExtract,
        BRepeat,
        BRedOr,
        BRedAnd,
        BComp,

        BShl,
        BLShr,
        BAShr,
        BRotateLeft,
        BRotateRight,
        BExtRotateLeft,
        BExtRotateRight,
        BInt2Bv,
        BBv2Int,
        BCarry,
        BXor3,

        PrAsserted,
        PrGoal,
        PrModusPonens,
        PrReflexivity,
        PrTransitivity,
        PrTransitivityStar,
        PrSymmetry,
        PrMonotonicity,
        PrQuantIntro,
        PrDistributivity,
        PrAndElim,
        PrNotOrElim,
        PrRewrite,
        PrRewriteStar,
        PrPullQuant,
        PrPullQuantStar,
        PrPushQuant,
        PrElimUnusedVars,
        PrDer,
        PrQuantInst,
        PrHypothesis,
        PrLemma,
        PrUnitResolution,
        PrIffTrue,
        PrIffFalse,
        PrCommutativity,
        PrDefAxiom,
        PrDefIntro,
        PrApplyDef,
        PrIffOeq,            
        PrNnfPos,
        PrNnfNeg,
        PrNnfStar,
        PrSkolemize,
        PrCnfStar,
        PrModusPonensOeq,
        PrThLemma,

        RaStore,
        RaEmpty,
        RaIsEmpty,
        RaJoin,
        RaUnion,
        RaWiden,
        RaProject,
        RaFilter,
        RaNegationFilter,
        RaRename,
        RaComplement,
        RaSelect,
        RaClone,

        Label,
        LabelLit,
        Uninterpreted            
    };


    /** 
        \brief IErrorHandler is an abstract (interface) class for passing
        an error handler.

        The \c Handler method takes as argument an \c ErrorCode and processes
        it.
    */
    public interface class IErrorHandler 
    {
    public:
        virtual void Handler(ErrorCode code) = 0;
    };

    /// @cond 0
    LBool ToLBool(Z3_lbool b) {
        switch(b) {
        case Z3_L_FALSE: return LBool::False; 
        case Z3_L_TRUE:  return LBool::True; 
        default:         return LBool::Undef; 
        }
    }
    /// @endcond

    /**
       \brief Container for labeled literals.
      
       A satisfiable state can be queried for a set of labeled literals that are satisfied.
       
    */

    public ref class LabeledLiterals {
        ref_context& m_context;
        Z3_literals  m_labels;
    internal:
        LabeledLiterals(ref_context& ctx, Z3_literals lbls): m_context(ctx), m_labels(lbls) { ctx.inc_ref(); }
        Z3_literals Get() { return m_labels; }
        TermPtr GetLiteral(unsigned idx) { return TermPtr(Z3_get_literal(m_context(), m_labels, idx)); }
    protected:
        !LabeledLiterals(); 
    public:
        ~LabeledLiterals() { if (m_labels) { Z3_del_literals(m_context(), m_labels); } m_labels = 0; m_context.dec_ref(); }
        unsigned GetNumLabels() { return Z3_get_num_literals(m_context(), m_labels); }
        void Disable(unsigned idx) { Z3_disable_literal(m_context(), m_labels, idx); }
        Symbol^ GetLabel(unsigned idx) { return gcnew Symbol(m_context(), Z3_get_label_symbol(m_context(), m_labels, idx)); }
    };


    /**
       \brief Container for constructor declarations.

    */

    public ref class Constructor {
        ref_context&          m_context;
        Z3_constructor      m_constructor;
        FuncDeclPtr         m_constructor_decl;
        FuncDeclPtr         m_tester;
        array<FuncDeclPtr>^ m_accessors;

        !Constructor();

    internal:
        String^          m_name;
        String^          m_tester_name;
        array<String^>^  m_field_names;
        array<SortPtr>^  m_field_sorts;
        array<unsigned>^ m_field_refs;

        Constructor(
            ref_context&     context,
            String^          name,
            String^          tester,
            array<String^>^  field_names,
            array<SortPtr>^  field_sorts,
            array<unsigned>^ field_refs
            );

        Z3_constructor Query();
        Z3_constructor Get();
        FuncDeclPtr GetConstructor();
        FuncDeclPtr GetTester();
        array<FuncDeclPtr>^ GetAccessors();
    public:    
        ~Constructor();   
    };

    

    /**
       \brief Configuration

       Configuration can be set prior to creating an instance 
       of the Z3 Context.

       To set a parameter create an instance of the Params class
       and call the SetParamValue() method.

       The set of legal parameters can be found by executing z3.exe /ini?
    */
    public ref class Config
    {
        /// @cond 0
        Z3_config m_config;
        /// @endcond
    internal:
        /// @cond 0
        Z3_config get() { return m_config; }
        /// @endcond

    protected:
        !Config();

    public:
        /**
           \brief Create configuration context.

           Create a configuration context to supply configurations to the 
           Z3 #Context. Callers must explicitly close the configuration 
           in order to collect the resources allocated in the configuration.
        */
        Config();

        /// \brief Configuration destructor.
        ~Config();
        
        /**
           \brief Set parameter to specified value.

           The list of all configuration parameters can be obtained using the Z3 executable:

           \verbatim
           z3.exe /ini?
           \endverbatim
        */
        void SetParamValue(String^ name, String^ value);
    };


    /**
       \brief Z3 Parameter values.
    */
    public interface class IRawParameter {  };
    public interface class IParameter {  };

    public ref class IntParameter : public IRawParameter, public IParameter { 
        int m_value;
    internal:
        IntParameter(int i) : m_value(i) {}
    public:
        property int Int { int get() { return m_value; } }
        virtual String^ ToString() override { return m_value.ToString(); }
    };

    public ref class DoubleParameter : public IRawParameter, public IParameter  { 
        double m_value;
    internal:
        DoubleParameter(double i) : m_value(i) {}
    public:
        property double Double { double get() { return m_value; } }
        virtual String^ ToString() override { return m_value.ToString(); }
    };

    public ref class RationalParameter : public IRawParameter, public IParameter  { 
        String^ m_value;
    internal:
        RationalParameter(String^ s): m_value(s) {}
    public:
        property  String^ GetRational {  String^ get() { return m_value; } }
        virtual String^ ToString() override { return m_value; }
    };

    public ref class SymbolParameter : public IRawParameter, public IParameter  { 
        Symbol^ m_value;
    internal:
        SymbolParameter(Symbol^ s): m_value(s) {}
    public:
        property  Symbol^ GetSymbol {  Symbol^ get() { return m_value; } }
    };

    public ref class TermPtrParameter : public IRawParameter  { 
        TermPtr m_value;
    internal:
        TermPtrParameter(TermPtr t) : m_value(t) {}
    public:
        property TermPtr GetTerm {  TermPtr get() { return m_value; } }
    };

    public ref class SortPtrParameter : public IRawParameter  { 
        SortPtr m_value;
    internal:
        SortPtrParameter(SortPtr t) : m_value(t) {}
    public:
        property  SortPtr GetSort {  SortPtr get() { return m_value; } }
    };

    public ref class FuncDeclPtrParameter : public IRawParameter  { 
        FuncDeclPtr m_value;
    internal:
        FuncDeclPtrParameter(FuncDeclPtr t) : m_value(t) {}
    public:
        property  FuncDeclPtr GetFuncDecl {  FuncDeclPtr get() { return m_value; } }
    };




    /** 
        \brief Z3 Array Value object.
    */
    public ref class RawArrayValue {
    public:
        array<TermPtr>^   Domain; 
        array<TermPtr>^   Range;
        TermPtr           ElseCase;
    };

    /** 
        \brief Z3 Function entry object.

        A FunctionEntry object summarizes what a function maps to
        based on a given set of argument values.
    */
    public ref class RawFunctionEntry {
    public:
        array<TermPtr>^ Arguments;
        TermPtr         Result;
    };

    /** 
        \brief Z3 Function graph object.

        The finite function graph of an uninterpreted function
        is represented as a list of #FunctionEntry entries, together
        with a default value. The domain values not listed in the
        #FunctionEntry array map to the default value \c Else.

        \param Declaration contains the function declaration Ast.
        \param Entries contains the array of entries where the function 
        is defined explicitly.
        \param Contains the default value of the function; where the function
        maps to a default value.
    */
    public ref class RawFunctionGraph {
    public:
        FuncDeclPtr               Declaration;
        array<RawFunctionEntry^>^ Entries;
        TermPtr                   Else;
    };

    public ref class RawQuantifier {
    public:
        bool               IsForall;
        unsigned           Weight;
        array<PatternPtr>^ Patterns;
        array<TermPtr>^    NoPatterns;
        array<SortPtr>^    Sorts;
        array<Symbol^>^    Names;
        TermPtr            Body;
    };

    ref class RawModel;

    public delegate void Action0();

    generic<typename T, typename S>
        public delegate void Action2(
            T obj1, 
            S obj2
            );
    generic<typename T, typename S, typename U>
        public delegate void Action3(
            T obj1, 
            S obj2,
            U obj3
            );


    generic<typename T>
        public delegate T Func0();
    
    generic<typename T, typename S>
        public delegate S Func1(
            T obj
            );
    
    generic<typename T, typename S, typename U>
        public delegate U Func2(
            T obj1,
            S obj2
            );


    /** 
        \brief Z3 RawModel object.
    */
    public ref class RawModel {
        ref_context& m_context;
        Z3_model     m_model;
        Dictionary<FuncDeclPtr, RawFunctionGraph^>^ m_graphs;
    internal:           
        RawModel(ref_context& c, Z3_model m) : m_context(c), m_model(m), m_graphs(nullptr) { c.inc_ref(); }

        void Reset();
    protected:
        !RawModel();
    public:
        ~RawModel();


        /**
           \brief Return the constants assigned by the given model.       
        */        
        array<FuncDeclPtr>^ GetModelConstants();
           
        /**
           \brief Return the function interpretations in the given model.
       
           A function interpretation is represented as a finite map and an 'else' value.
           Each entry in the finite map represents the value of a function given a set of arguments.       
        */
        Dictionary<FuncDeclPtr, RawFunctionGraph^>^ GetFunctionGraphs();

        /**
           \brief Evaluate the AST node \c t in the given model. 

           Return the result as a non-zero value. The
           returned value is null if the term does not evaluate to a fixed value
           in the current model.
           term to a value.
       

           The evaluation may fail for the following reasons:

           - \c t contains a quantifier or bound variable. 

           - the model \c m is partial, that is, it doesn't have a complete interpretation for free functions. 
             That is, the option <tt>PARTIAL_MODELS=true</tt> was used.

           - the evaluator doesn't have support for some interpreted operator.

           - \c t is type incorrect (see #TypeCheck).

           - The result of an intepreted operator in \c t is undefined (e.g. division by zero).
        */
        TermPtr Eval(TermPtr);

        TermPtr Eval(FuncDeclPtr, array<TermPtr>^ args);

        
        /**
           \brief Return decomposed sequence of stores as an array value.
        */
        bool TryGetArrayValue(TermPtr a,[Out] RawArrayValue^% av);

        /**
           \brief Convert the given model into a string.
        */
        virtual String^ ToString() override;

        /**
           \brief Display model to TextWriter
        */
        void Display(System::IO::TextWriter^ w);
    };

    public ref class ReferenceCounted {};

    public ref class TermProofPtr {
        TermPtr m_term;
        TermPtr m_proof; // proof is optional, use IntPtr::Zero for absence of proofs.
    public:
        TermProofPtr(TermPtr term, TermPtr proof): m_term(term), m_proof(proof) {}
        property TermPtr GetTerm { TermPtr get() { return m_term; } }
        property TermPtr Proof { TermPtr get() { return m_proof; } }
    };

    ref class RawTheory;
    /**
       \brief Z3 API object.
    */
    public ref class RawContext : public MarshalByRefObject
    {        
        ref_context* m_context;        
        bool         m_disposed;
        static List<KeyValuePair<AstPtr,RawContext^> >^  s_todec;
        static IntPtr^ s_monitor;
        static bool    s_nonempty;

        void Init();
    internal:
        static IErrorHandler^ m_error_handler = nullptr;

        Z3_context ctx() { return (*m_context)(); }
        Z3_fixedpoint dl() { return m_context->dl(); }
        ref_context& ref_context() { return *m_context; }

        /**
            \brief Increment and decrement reference counters on 
            terms, sorts and declarations.

            These methods are required when the context is created
            using the ReferenceCounted argument.
        */
        void IncRef(AstPtr ast);

        void EnqueueDecRef(AstPtr ast);

    protected:

        !RawContext();
    public: 
        /**
           \brief Create a logical context using the given configuration. 
    
           After a context is created, the configuration cannot be changed.
           All main interaction with Z3 happens in the context of a \c Context.

           All contexts that are created must be disposed (call Dispose).
           Failure to dispose contexts cause memory leaks.
           Garbage collection will not free resources allocated in contexts.
        */

        RawContext(Config^ config); 

        /**
           \brief Create a logical context using the given configuration. 

           This constructor is similar to the default RawContext constructor.
           Reference counts to terms, functions, and sorts that are created
           over the API have to be handled explicitly by the caller, however.
            
           Terms (sorts, declarations) created by the context have initially 
           reference count 0, and the caller has to explicitly manage the reference counts.
           This mode is more flexible, but also very error prone.

           Use the metheods AddRef and DecRef on terms, sorts, declarations to
           control the reference counts.

           All contexts that are created must be disposed (call Dispose).
           Failure to dispose contexts cause memory leaks.
           Garbage collection will not free resources allocated in contexts.
        */
        RawContext(Config^ config, ReferenceCounted^ rc);

        RawContext();

        void SetContext(Z3_context ctx);

        void Reset();

        ~RawContext();

        /**
           @name Tracing and logging
        */
        /*@{*/
        
        /**
           \brief Enable low-level debug tracing. 

           This method only works with debug builds.
        */
        void EnableDebugTrace(String^ tag);

        /**
           \brief Enable or disable warning messages sent to the console out/error.

           Warnings are printed after passing \c true, warning messages are
           suppressed after calling this method with \c false.
        */
        void ToggleWarningMessages(bool enabled);

        /**
           \brief Update a mutable configuration parameter.
           
           The list of all configuration parameters can be obtained using the Z3 executable:
           
           \verbatim
           z3.exe -ini?
           \endverbatim
           
           Only a few configuration parameters are mutable once the context is created.
           The error handler is invoked when trying to modify an immutable parameter.
           
           \sa SetParamValue
        */
        void UpdateParamValue(String^ param_id, String^ value);

        /**
           \brief Get a configuration parameter.
       
           \sa Z3_mk_config
           \sa Z3_set_param_value
        */
        String^ GetParamValue(String^ param_id);

        /**
           \brief Configure the SMTLIB logic to be used in the given logical context.
        */

        bool SetLogic(String^ logic);

        /*@}*/


        /**
           @name Symbols
        */
        /*@{*/
        /**
           \brief Create a Z3 symbol using an intege or a string.
           
           Symbols are used to name several term and type constructors.
           
        */
        Symbol^ MkSymbol(int i);

        Symbol^ MkSymbol(String^ s);
        /*@}*/

        /**
           @name Types
        */
        /*@{*/
        
        /**
           \brief Create a free (uninterpreted) type using the given name (symbol).
       
           Two free types are considered the same iff the have the same name.
        */
        SortPtr MkSort(Symbol^ s);

        SortPtr MkSort(String^ s); 

        SortPtr MkSort(int i);


        /**
           \brief Create the boolean type. 

           This type is used to create propositional variables and predicates.
        */
        SortPtr MkBoolSort();

        /**
           \brief Create an integer type.
           
           This type is not the int type found in programming languages.
           A machine integer can be represented using bit-vectors. The function
           #MkBvType creates a bit-vector type.

           \sa MkBvType
        */
        SortPtr MkIntSort();

        /**
           \brief Create a real type. 
           
           This type is not a floating point number.
           Z3 does not have support for floating point numbers yet.
        */
        SortPtr MkRealSort();


        /**
           \brief Create a bit-vector type of the given size.
           
           This type can also be seen as a machine integer.
           
           \remark The size of the bitvector type must be greater than zero.
        */
        SortPtr MkBvSort(unsigned sz);

        /**
           \brief Create an array type. 
           
           We usually represent the array type as: <tt>[domain -> range]</tt>.
           Arrays are usually used to model the heap/memory in software verification.
           
           \sa MkArraySelect
           \sa MkArrayStore
           \sa MkArrayMap
           \sa MkConstArray
        */

        SortPtr MkArraySort(SortPtr domain, SortPtr range);

        /**
           \brief Create a named finite domain sort.

           To create constants that belong to the finite domain, 
           use MkNumeral for creating numerals and pass a numeric
           constant together with the sort returned by this call.
        */
        SortPtr MkFiniteDomainSort(String^ name, unsigned __int64 domain_size);


        /**
           \brief Create a tuple type.
       

           A tuple with \c n fields has a constructor and \c n projections.
           This function will also declare the constructor and projection functions.

           \param mk_tuple_name name of the constructor function associated with the tuple type.
           \param field_names name of the projection functions.
           \param field_types type of the tuple fields.
           \param mk_tuple_decl output parameter that will contain the constructor declaration.
           \param proj_decl output parameter that will contain the projection function declarations. 
                  This field must be a buffer of size \c num_fields allocated by the user.
        */
        SortPtr MkTupleSort(
            Symbol^               mk_tuple_name, 
            array<Symbol^>^       field_names,
            array<SortPtr>^       field_types,
            [Out] FuncDeclPtr%         mk_tuple_decl,
            [In] [Out] array<FuncDeclPtr>^  proj_decl
            );

        SortPtr MkTupleSort(
            String^               mk_tuple_name, 
            array<String^>^       field_names,
            array<SortPtr>^       field_types,
            [Out] FuncDeclPtr%         mk_tuple_decl,
            [In, Out] array<FuncDeclPtr>^  proj_decl
            );

        /** 
            \brief create an enumeration type.

            \param name - name of enumeration sort.
            \param enum_names - names of enumerated elements.
            \param enum_consts - output function declarations for enumerated elements.
            \param enum_testers - output function declarations for enumeration testers.

        */
        SortPtr MkEnumerationSort(
            String^             name,
            array<String^>^     enum_names,
            array<FuncDeclPtr>^ enum_consts,
            array<FuncDeclPtr>^ enum_testers);

        /**
           \brief create list sort.

           \param name of resulting list type.
           \param elem_sort sort of elements.
           \param nil_decl function declaration for nil.
           \param is_nil_decl function declaration for nil tester.
           \param cons_decl function declaration for cons constructor.
           \param is_cons_decl function declaration for cons tester.
           \param head_decl function declaration for head accessor.
           \param tail_decl function declaration for tail accessor.

        */
        SortPtr MkListSort(
            String^ name,
            SortPtr elem_sort,
            [Out] FuncDeclPtr% nil_decl,
            [Out] FuncDeclPtr% is_nil_decl,
            [Out] FuncDeclPtr% cons_decl,
            [Out] FuncDeclPtr% is_cons_decl,
            [Out] FuncDeclPtr% head_decl,
            [Out] FuncDeclPtr% tail_decl
            );
        

        /**
           \brief create constructor object for datatype declarations.
           The object must be disposed with manually.
           
           Use the methods #GetConstructor, #GetTester, and #GetAccessors to
           retrieve the function declarations for constructors, tester and accessors
           after the datatype has been declared.

           A field_ref is the index of the (mutually) recursive datatype.
           For example, if you declare a single recursive datatype, then 
           a reference to the recursive datatype that is being declared is 
           the number 0. If you declare two mutually recursive datatypes, then
           the reference to the second recursive datatype is 1.

        */

        Constructor^ MkConstructor(
            String^ name,
            String^ tester,
            array<String^>^ field_names,
            array<SortPtr>^ field_sorts,
            array<unsigned>^ field_refs
            );

        /**
           \brief retrieve constructor function declaration.
        */        
        FuncDeclPtr GetConstructor(Constructor^ c) { return c->GetConstructor(); }

        /**
           \brief retrieve test function for constructor.
        */
        FuncDeclPtr GetTester(Constructor^ c) { return c->GetTester(); }

        /**
           \brief retrieve accessors for datatype.
        */
        array<FuncDeclPtr>^ GetAccessors(Constructor^ c) { return c->GetAccessors(); }

        /**
           \brief create datatype sort.
        */
        SortPtr MkDataType(
            String^ name,
            array<Constructor^>^ constructors
            );

        
        /**
           \brief create datatype sorts.

           \param names array of names for the recursive datatypes.
           \param constructors array of arrays of constructors.
        */
        array<SortPtr>^ MkDataTypes(
            array<String^>^ names,
            array<array<Constructor^>^>^ constructors
            );

    /*@}*/

    /**
       @name Constants and Applications
    */

    /*@{*/

    /**
       \brief Declare a constant or function.

       \param s name of the constant or function.
       \param domain array containing the type of each argument. 
              The array must contain domain_size elements. It is 0 whe declaring a constant.
       \param range type of the constant or the return type of the function.

       After declaring a constant or function, the function
       #MkApp can be used to create a constant or function
       application.

       \sa MkApp
    */
        FuncDeclPtr MkFuncDecl(Symbol^ s, array<SortPtr>^ domain, SortPtr range);

        FuncDeclPtr MkFuncDecl(String^ s, array<SortPtr>^ domain, SortPtr range);

        FuncDeclPtr MkConstDecl(Symbol^ s, SortPtr ty) {
            return MkFuncDecl(s, gcnew array<SortPtr>(0), ty);
        }
        FuncDeclPtr MkFuncDecl(Symbol^ s, SortPtr domain, SortPtr range);

        FuncDeclPtr MkFuncDecl(Symbol^ s, SortPtr d1, SortPtr d2, SortPtr range);

        FuncDeclPtr MkConstDecl(String^ s, SortPtr ty) {
            return MkFuncDecl(s, gcnew array<SortPtr>(0), ty);
        }
        FuncDeclPtr MkFuncDecl(String^ s, SortPtr domain, SortPtr range);

        FuncDeclPtr MkFuncDecl(String^ s, SortPtr d1, SortPtr d2, SortPtr range);

    
    /**
       \brief Create a constant or function application.

       \sa MkFuncDecl
    */
        AppPtr MkApp(FuncDeclPtr d, array<TermPtr>^ args);
        AppPtr MkApp(FuncDeclPtr d, TermPtr arg);
        AppPtr MkApp(FuncDeclPtr d, TermPtr arg1, TermPtr arg2);
        AppPtr MkApp(FuncDeclPtr d, TermPtr arg1, TermPtr arg2, TermPtr arg3);

    /**
       \brief Declare and create a constant.
              
       \sa MkApp
       \sa MkFuncDecl
    */
        AppPtr MkConst(FuncDeclPtr d);
        AppPtr MkConst(String^ s, SortPtr ty);
        AppPtr MkConst(Symbol^ s, SortPtr ty);


        /**
           \brief Declare a fresh constant or function.
           
           Z3 will generate an unique name for this function declaration.
           
           \sa MkFuncDecl
        */
        FuncDeclPtr MkFreshFuncDecl(String^ prefix, array<SortPtr>^ domain, SortPtr range);
    
        /**
           \brief Declare and create a fresh constant.
           
           \sa MkFuncDecl
           \sa MkApp
        */
        TermPtr MkFreshConst(String^ prefix, SortPtr ty);

        /** 
            \brief Create labeled formula.

        */
        TermPtr MkLabel(Symbol^ name, bool pos, TermPtr fml);
    
        /** 
            \brief Create an AST node representing \c true.
        */
        TermPtr MkTrue() { return TermPtr(Z3_mk_true(ctx())); }


        /** 
            \brief Create an AST node representing \c false.
        */
        TermPtr MkFalse() { return TermPtr(Z3_mk_false(ctx())); }

    
        /** 
            \brief Create an AST node representing <tt>l = r</tt>.
            
            The nodes \c l and \c r must have the same type. 
        */
        TermPtr MkEq(TermPtr l, TermPtr r);


        /**
           \brief Create an AST node representing <tt>distinct(args[0], ..., args[args.Length-1])</tt>.

           The \c distinct construct is used for declaring the arguments pairwise distinct. 
           That is, <tt>Forall 0 <= i < j < args.Length. not args[i] = args[j]</tt>.
       
           All arguments must have the same type.

           \remark The number of arguments of a distinct construct must be greater than one.
        */
        TermPtr MkDistinct(array<TermPtr>^ args);


        /** 
            \brief Create an AST node representing <tt>not(a)</tt>.
        
            The node \c a must have Boolean type.
        */
        virtual TermPtr MkNot(TermPtr arg);
    
        /**
           \brief 
           Create an AST node representing an if-then-else: <tt>ite(t1, t2, t3)</tt>.

           The node \c t1 must have Boolean type, \c t2 and \c t3 must have the same type.
           The type of the new node is equal to the type of \c t2 and \c t3.
        */
        TermPtr MkIte(TermPtr t1, TermPtr t2, TermPtr t3);

        /**
           \brief Create an AST node representing <tt>t1 iff t2</tt>.
           
           The nodes \c t1 and \c t2 must have Boolean type.
        */
        TermPtr MkIff(TermPtr t1, TermPtr t2);

        /**
           \brief Create an AST node representing <tt>t1 implies t2</tt>.

           The nodes \c t1 and \c t2 must have Boolean type.
        */
        TermPtr MkImplies(TermPtr t1, TermPtr t2);
    
        /**
           \brief Create an AST node representing <tt>t1 xor t2</tt>.

           The nodes \c t1 and \c t2 must have Boolean type.
        */
        TermPtr MkXor(TermPtr t1, TermPtr t2);
    
        /**
           \brief Create an AST node representing <tt>args[0] and ... and args[args.Length-1]</tt>.

           All arguments must have Boolean type.
       
           \remark The number of arguments must be greater than zero.
        */
        TermPtr MkAnd(array<TermPtr>^ args);
        TermPtr MkAnd(TermPtr arg1, TermPtr arg2);
    
        /**
           \brief Create an AST node representing <tt>args[0] or ... or args[args.Length-1]</tt>.

           All arguments must have Boolean type.

           \remark The number of arguments must be greater than zero.
        */
        TermPtr MkOr(array<TermPtr>^ args);
        TermPtr MkOr(TermPtr arg1, TermPtr arg2);

        /**
           \brief Create an AST node representing <tt>args[0] + ... + args[args.Length-1]</tt>.

           All arguments must have int or real type.
           
           \remark The number of arguments must be greater than zero.
        */
        TermPtr MkAdd(array<TermPtr>^ args);
        TermPtr MkAdd(TermPtr arg1, TermPtr arg2);

        /**
           \brief Create an AST node representing <tt>args[0] * ... * args[args.Length-1]</tt>.

           All arguments must have int or real type.
       
           \remark Z3 has limited support for non-linear arithmetic.
           \remark The number of arguments must be greater than zero.
        */
        TermPtr MkMul(array<TermPtr>^ args);
        TermPtr MkMul(TermPtr arg1, TermPtr arg2);
    
        /**
           \brief Create an AST node representing <tt>args[0] - ... - args[args.Length - 1]</tt>.

           All arguments must have int or real type.

           \remark The number of arguments must be greater than zero.
        */
        TermPtr MkSub(array<TermPtr>^ args);
        TermPtr MkSub(TermPtr arg1, TermPtr arg2);

        /**
           \brief Create an AST node representing <tt>- arg</tt>.

           The argument must have int or real type.
        */
        TermPtr MkUnaryMinus(TermPtr arg);

        /** 
            \brief Create integer or real division.

            The nodes \c arg1 and \c arg2 must have the same type, and must be int or real.
        */
        TermPtr MkDiv(TermPtr arg1, TermPtr arg2);

        /** 
            \brief Create integer modulus

            The nodes \c arg1 and \c arg2 must have integer type.
        */
        TermPtr MkMod(TermPtr arg1, TermPtr arg2);

        /** 
            \brief Create integer remainder

            The nodes \c arg1 and \c arg2 must have integer type.
        */
        TermPtr MkRem(TermPtr arg1, TermPtr arg2);

        /** 
            \brief Create coercion from integer to real

            The node \c arg must have integer type.
        */
        TermPtr MkToReal(TermPtr arg);

        /** 
            \brief Create coercion from real to integer (floor)

            The node \c arg must have real type.
        */
        TermPtr MkToInt(TermPtr arg);

        /** 
            \brief Check if real is an integer value.

            The node \c arg must have real type.
        */
        TermPtr MkIsInt(TermPtr arg);



        /** 
            \brief Create less than.

            The nodes \c arg1 and \c arg2 must have the same type, and must be int or real.
        */
        TermPtr MkLt(TermPtr arg1, TermPtr arg2);

        /** 
            \brief Create less than or equal to.
        
            The nodes \c arg1 and \c arg2 must have the same type, and must be int or real.
        */
        TermPtr MkLe(TermPtr arg1, TermPtr arg2);

        /** 
            \brief Create greater than.
        
            The nodes \c arg1 and \c arg2 must have the same type, and must be int or real.
        */
        TermPtr MkGt(TermPtr arg1, TermPtr arg2);

        /** 
            \brief Create greater than or equal to.
        
            The nodes \c arg1 and \c arg2 must have the same type, and must be int or real.
        */
        TermPtr MkGe(TermPtr arg1, TermPtr arg2);

        /**
           \brief Bitwise negation.

           The node \c arg1 must have a bit-vector type.
        */
        TermPtr MkBvNot(TermPtr t1);

        /**
           \brief Take conjunction of bits in vector.

           The node \c arg1 must have a bit-vector type.
        */
        TermPtr MkBvReduceAnd(TermPtr t1);

        /**
           \brief Take disjunction of bits in vector.

           The node \c arg1 must have a bit-vector type.
        */
        TermPtr MkBvReduceOr(TermPtr t1);

        /**
           \brief Bitwise and.
       
           The nodes \c t1 and \c t2 must have the same bit-vector type.
        */
        TermPtr MkBvAnd(TermPtr t1, TermPtr t2);

        /**
           \brief Bitwise or.

           The nodes \c t1 and \c t2 must have the same bit-vector type.
        */
        TermPtr MkBvOr(TermPtr t1, TermPtr t2);

        /**
           \brief Bitwise exclusive-or.
           
           The nodes \c t1 and \c t2 must have the same bit-vector type.
        */
        TermPtr MkBvXor(TermPtr t1, TermPtr t2);

        /**
           \brief Bitwise nand. 

           The nodes \c t1 and \c t2 must have the same bit-vector type.
        */
        TermPtr MkBvNand(TermPtr t1, TermPtr t2);

        /**
           \brief Bitwise nor. 

           The nodes \c t1 and \c t2 must have the same bit-vector type.
        */
        TermPtr MkBvNor(TermPtr t1, TermPtr t2);

        /**
           \brief Bitwise xnor. 
       
           The nodes \c t1 and \c t2 must have the same bit-vector type.
        */
        TermPtr MkBvXnor(TermPtr t1, TermPtr t2);

        /**
           \brief Standard two's complement unary minus. 

           The node \c t1 must have bit-vector type.
        */
        TermPtr MkBvNeg(TermPtr t1);
    
        /** 
            \brief Standard two's complement addition.
        
            The nodes \c t1 and \c t2 must have the same bit-vector type.
        */
        TermPtr MkBvAdd(TermPtr t1, TermPtr t2);

        /** 
            \brief Standard two's complement subtraction.
        
            The nodes \c t1 and \c t2 must have the same bit-vector type.
        */
        TermPtr MkBvSub(TermPtr t1, TermPtr t2);
    
        /** 
            \brief Standard two's complement multiplication.
        
            The nodes \c t1 and \c t2 must have the same bit-vector type.
        */
        TermPtr MkBvMul(TermPtr t1, TermPtr t2);

        /** 
            \brief Unsigned division. 

            It is defined as the \c floor of <tt>t1/t2</tt> if \c t2 is
            different from zero. If <tt>t2</tt> is zero, then the result
            is undefined.
        
            The nodes \c t1 and \c t2 must have the same bit-vector type.
        */
        TermPtr MkBvUdiv(TermPtr t1, TermPtr t2);

        /** 
            \brief Two's complement signed division. 
            
            It is defined in the following way:
            
            - The \c floor of <tt>t1/t2</tt> if \c t2 is different from zero, and <tt>t1*t2 >= 0</tt>.
            
            - The \c ceiling of <tt>t1/t2</tt> if \c t2 is different from zero, and <tt>t1*t2 < 0</tt>.
            
            If <tt>t2</tt> is zero, then the result is undefined.
            
            The nodes \c t1 and \c t2 must have the same bit-vector type.
        */
        TermPtr MkBvSdiv(TermPtr t1, TermPtr t2);

        /**
           \brief Unsigned remainder.

           It is defined as <tt>t1 - (t1 /u t2) * t2</tt>, where <tt>/u</tt> represents unsigned division.
           
           If <tt>t2</tt> is zero, then the result is undefined.
           
           The nodes \c t1 and \c t2 must have the same bit-vector type.
        */
        TermPtr MkBvUrem(TermPtr t1, TermPtr t2);

        /**
           \brief Two's complement signed remainder (sign follows dividend).

           It is defined as <tt>t1 - (t1 /s t2) * t2</tt>, where <tt>/s</tt> represents signed division.
           The most significant bit (sign) of the result is equal to the most significant bit of \c t1.
           
           If <tt>t2</tt> is zero, then the result is undefined.
           
           The nodes \c t1 and \c t2 must have the same bit-vector type.
           
           \sa MkBvSmod
        */
        TermPtr MkBvSrem(TermPtr t1, TermPtr t2);

        /**
           \brief Two's complement signed remainder (sign follows divisor).
       
           If <tt>t2</tt> is zero, then the result is undefined.
       
           The nodes \c t1 and \c t2 must have the same bit-vector type.

           \sa MkBvSrem
        */
        TermPtr MkBvSmod(TermPtr t1, TermPtr t2);

        /**
           \brief Unsigned less than.

           The nodes \c t1 and \c t2 must have the same bit-vector type.
        */
        TermPtr MkBvUlt(TermPtr t1, TermPtr t2);
    
        /**
           \brief Two's complement signed less than.
       
           It abbreviates:
           \code
           (or (and (= (extract[|m-1|:|m-1|] s) bit1)
                    (= (extract[|m-1|:|m-1|] t) bit0))
               (and (= (extract[|m-1|:|m-1|] s) (extract[|m-1|:|m-1|] t))
                    (bvult s t)))
           \endcode

           The nodes \c t1 and \c t2 must have the same bit-vector type.
        */
        TermPtr MkBvSlt(TermPtr t1, TermPtr t2);

        /**
           \brief Unsigned less than or equal to.

           The nodes \c t1 and \c t2 must have the same bit-vector type.
        */
        TermPtr MkBvUle(TermPtr t1, TermPtr t2);

        /**
           \brief Two's complement signed less than or equal to.

           The nodes \c t1 and \c t2 must have the same bit-vector type.
        */
        TermPtr MkBvSle(TermPtr t1, TermPtr t2);

        /**
           \brief Unsigned greater than or equal to.

           The nodes \c t1 and \c t2 must have the same bit-vector type.
        */
        TermPtr MkBvUge(TermPtr t1, TermPtr t2);

        /**
           \brief Two's complement signed greater than or equal to.

           The nodes \c t1 and \c t2 must have the same bit-vector type.
        */
        TermPtr MkBvSge(TermPtr t1, TermPtr t2);

        /**
           \brief Unsigned greater than.

           The nodes \c t1 and \c t2 must have the same bit-vector type.
        */
        TermPtr MkBvUgt(TermPtr t1, TermPtr t2);

        /**
           \brief Two's complement signed greater than.

           The nodes \c t1 and \c t2 must have the same bit-vector type.
        */
        TermPtr MkBvSgt(TermPtr t1, TermPtr t2);

        /**
           \brief Concatenate the given bit-vectors.
       
           The nodes \c t1 and \c t2 must have (possibly different) bit-vector types

           The result is a bit-vector of size <tt>n1+n2</tt>, where \c n1 (\c n2) is the size
           of \c t1 (\c t2).
        */
        TermPtr MkBvConcat(TermPtr t1, TermPtr t2);
    
        /**
           \brief Extract the bits \c high down to \c low from a bitvector of
           size \c m to yield a new bitvector of size \c n, where <tt>n =
           high - low + 1</tt>.

           The node \c t must have a bit-vector type.
        */
        TermPtr MkBvExtract(unsigned high, unsigned low, TermPtr t);

        /**
           \brief Sign-extend of the given bit-vector to the (signed) equivalent bitvector of
           size <tt>m+i</tt>, where \c m is the size of the given
           bit-vector.

           The node \c t must have a bit-vector type.
        */
        TermPtr MkBvSignExt(unsigned i, TermPtr t);

        /**
           \brief Extend the given bit-vector with zeros to the (unsigned) equivalent
           bitvector of size <tt>m+i</tt>, where \c m is the size of the
           given bit-vector.
       
           The node \c t1 must have a bit-vector type. 
        */
        TermPtr MkBvZeroExt(unsigned i, TermPtr t);

        /**
           \brief Repeat the bit-vector <tt>i</tt> times.
       
           The node \c t1 must have a bit-vector type. 
        */
        TermPtr MkBvRepeat(unsigned i, TermPtr t);

        /**
           \brief Shift left.

           It is equivalent to multiplication by <tt>2^x</tt> where \c x is the value of the
           third argument.
           
           The nodes \c t1 and \c t2 must have the same bit-vector type.
        */
        TermPtr MkBvShl(TermPtr t1, TermPtr t2);

        /**
           \brief Logical shift right.

           It is equivalent to unsigned division by <tt>2^x</tt> where \c x is the
           value of the third argument.
           
           The nodes \c t1 and \c t2 must have the same bit-vector type.
        */
        TermPtr MkBvLshr(TermPtr t1, TermPtr t2);

        /**
           \brief Arithmetic shift right.
           
           It is like logical shift right except that the most significant
           bits of the result always copy the most significant bit of the
           second argument.
           
           The nodes \c t1 and \c t2 must have the same bit-vector type.
        */
        TermPtr MkBvAshr(TermPtr t1, TermPtr t2);
    
        /**
           \brief Rotate bits of \c t1 to the left \c i times.
       
           The node \c t1 must have a bit-vector type. 
        */
        TermPtr MkBvRotateLeft(unsigned i, TermPtr t1);
    
        /**
           \brief Rotate bits of \c t1 to the right \c i times.
       
           The node \c t1 must have a bit-vector type. 
        */
        TermPtr MkBvRotateRight(unsigned i, TermPtr t1);

        /**
           \brief Rotate bits of \c t1 to the left \c t2 times.
       
           The node \c t1 and \c t2 must have the same bit-vector type. 
        */
        TermPtr MkBvRotateLeft(TermPtr t1, TermPtr t2);
    
        /**
           \brief Rotate bits of \c t1 to the right \c t2 times.
       
           The node \c t1 and \c t2 must have the same bit-vector type. 
        */
        TermPtr MkBvRotateRight(TermPtr t1, TermPtr t2);

        /**
           \brief Convert bit vector to integer.
       
           The node \c t1 must have a bit-vector type. 
        */
        TermPtr MkBv2Int(TermPtr t1, bool is_signed);

        /**
           \brief Convert integer to bit vector.
       
           The node \c t1 must have a integer type. 
        */
        TermPtr MkInt2Bv(unsigned size, TermPtr t1);

        /**
           \brief Check that addition does not overflow.

           The nodes \c t1 and \c t2 must have the same bit-vector type.
        */
        TermPtr MkBvAddNoOverflow(TermPtr t1, TermPtr t2, bool is_signed);

        /**
           \brief Check that addition does not underflow.

           The nodes \c t1 and \c t2 must have the same bit-vector type.
        */
        TermPtr MkBvAddNoUnderflow(TermPtr t1, TermPtr t2);

        /**
           \brief Check that subtraction does not overflow.

           The nodes \c t1 and \c t2 must have the same bit-vector type.
        */
        TermPtr MkBvSubNoOverflow(TermPtr t1, TermPtr t2);

        /**
           \brief Check that subtraction does not underflow.

           The nodes \c t1 and \c t2 must have the same bit-vector type.
        */
        TermPtr MkBvSubNoUnderflow(TermPtr t1, TermPtr t2, bool is_signed);

        /**
           \brief Check that division does not overflow.

           The nodes \c t1 and \c t2 must have the same bit-vector type.
        */
        TermPtr MkBvSDivNoOverflow(TermPtr t1, TermPtr t2);

        /**
           \brief Check that negation does not overflow.
        */
        TermPtr MkBvNegNoOverflow(TermPtr t1);

        /**
           \brief Check that multiplication does not overflow.

           The nodes \c t1 and \c t2 must have the same bit-vector type.
        */
        TermPtr MkBvMulNoOverflow(TermPtr t1, TermPtr t2, bool is_signed);

        /**
           \brief Check that multiplication does not underflow.

           The nodes \c t1 and \c t2 must have the same bit-vector type.
        */
        TermPtr MkBvMulNoUnderflow(TermPtr t1, TermPtr t2);

        /**
           \brief Array read.

           The node \c a must have an array type <tt>[domain -> range]</tt>, and \c i must have the type \c domain.
           The type of the result is \c range.
           
           \sa MkArraySort
           \sa MkArrayStore
        */
        TermPtr MkArraySelect(TermPtr a, TermPtr i);
    
        /**
           \brief Array update.
           
           The node \c a must have an array type <tt>[domain -> range]</tt>, \c i must have type \c domain,
           \c v must have type range. The type of the result is <tt>[domain -> range]</tt>.
       
           \sa MkArraySort
           \sa MkArraySelect
        */
        TermPtr MkArrayStore(TermPtr a, TermPtr i, TermPtr v);

        /**
           \brief Array map.
           
           The \c n nodes \c args must be of array sorts <tt>[domain_i -> range_i]</tt>.
           The function declaration \c f must have type <tt> range_1 .. range_n -> range</tt>.
           \c v must have sort range. The sort of the result is <tt>[domain_i -> range]</tt>.
       
           \sa MkArraySort
           \sa MkArraySelect
           \sa MkArrayStore
        */
        TermPtr MkArrayMap(FuncDeclPtr d, array<TermPtr>^ args);

        /**
           \brief Constant array.
           
           The node \c a must have an array type <tt>[range]</tt>, \c domain indicates the domain
           of the array.
           The type of the result is <tt>[domain -> range]</tt>.
       
           \sa MkArraySort
           \sa MkArraySelect
           \sa MkArrayStore
        */
        TermPtr MkArrayConst(SortPtr domain, TermPtr v);

        /**
           \brief Access the array default.
           
           The node \c a must have an array type <tt>[domain -> range]</tt>.
           The type of the result is <tt>[range]</tt>. The result is a term
           whose value holds the default array value. That is, models should
           ensure that the default for <tt>a</tt> (ElseCase) evaluates to the 
           same value as <tt>MkArrayDefault(a)</tt>.
       
           \sa MkArraySort
           \sa MkArraySelect
           \sa MkArrayStore
           \sa MkArrayconst
        */
        TermPtr MkArrayDefault(TermPtr a);

        /*@}*/


        /**
           @name Sets
        */
        /*@{*/

        /**
           \brief Create Set type.
        */
        SortPtr MkSetSort(SortPtr ty) { return SortPtr(Z3_mk_set_sort(ctx(), get_sort(ty))); }

        /** 
            \brief Create the empty set.
        */
        TermPtr MkEmptySet(SortPtr ty) { return TermPtr(Z3_mk_empty_set(ctx(), get_sort(ty))); }

        /** 
            \brief Create the full set.
        */
        TermPtr MkFullSet(SortPtr ty) { return TermPtr(Z3_mk_full_set(ctx(), get_sort(ty))); }

        /**
           \brief Add an element to a set.
           
           The first argument must be a set, the second an element.
        */
        TermPtr MkSetAdd(TermPtr set, TermPtr elem) {
            return TermPtr(Z3_mk_set_add(ctx(), get_ast(set), get_ast(elem)));
        }

        /**
           \brief Remove an element to a set.
           
           The first argument must be a set, the second an element.
        */
        TermPtr MkSetDel(TermPtr set, TermPtr elem) {
            return TermPtr(Z3_mk_set_del(ctx(), get_ast(set), get_ast(elem)));
        }

        /**
           \brief Take the union of a arrays of sets.
           
           The arguments must all be of the same type and all be of set types.
        */
        TermPtr MkSetUnion(array<TermPtr>^ sets);
        TermPtr MkSetUnion(TermPtr set1, TermPtr set2);

        /**
           \brief Take the intersection of a arrays of sets.
        */
        TermPtr MkSetIntersect(array<TermPtr>^ sets);
        TermPtr MkSetIntersect(TermPtr set1, TermPtr set2);

        /**
           \brief Take the set difference between two sets.
        */
        TermPtr MkSetDifference(TermPtr arg1, TermPtr arg2) {
            return TermPtr(Z3_mk_set_difference(ctx(), get_ast(arg1), get_ast(arg2)));
        }
        /**
           \brief Take the complement of a set.
        */
        TermPtr MkSetComplement(TermPtr arg) {
            return TermPtr(Z3_mk_set_complement(ctx(), get_ast(arg)));
        }

        /**
           \brief Check for set membership.
           
           The first argument should be an element type of the set.
        */
        TermPtr MkSetMember(TermPtr elem, TermPtr set) {
            return TermPtr(Z3_mk_set_member(ctx(), get_ast(elem), get_ast(set)));
        }

        /**
           \brief Check for subsetness of sets.
        */
        TermPtr MkSetSubset(TermPtr arg1, TermPtr arg2) {
            return TermPtr(Z3_mk_set_subset(ctx(), get_ast(arg1), get_ast(arg2)));
        }
        /*@}*/

        
        /**
           @name Injective functions
        */
        /*@{*/

        /**
           \brief Create injective function
        */
        
        FuncDeclPtr MkInjectiveFunction(String^ name, array<SortPtr>^ domain, SortPtr range);

        FuncDeclPtr MkInjectiveFunction(Symbol^ name, array<SortPtr>^ domain, SortPtr range);

        /*@}*/



        /**
           @name Numerals
        */
        /*@{*/
        
        /**
           \brief Create a numeral of a given type. 

           \param numeral An integer, or a string representing the numeral value in decimal notation. 
           If the given type is a real, then the numeral can be a rational, that is, a string of the form <tt>[num]* / [num]*</tt>.
           \param ty The type of the numeral. In the current implementation, the given type can be an int, real, or bit-vectors of arbitrary size. 
       
        */
        TermPtr MkNumeral(String^ numeral, SortPtr ty);
        TermPtr MkNumeral(int n, SortPtr ty);
        TermPtr MkNumeral(unsigned n, SortPtr ty);
        TermPtr MkNumeral(__int64 n, SortPtr ty);
        TermPtr MkNumeral(unsigned __int64 n, SortPtr ty);

        /**
           \brief Create a numeral of type Int.
        */
        TermPtr MkIntNumeral(String^ n) { return MkNumeral(n, MkIntSort()); }
        TermPtr MkIntNumeral(int n) { return MkNumeral(n, MkIntSort()); }
        TermPtr MkIntNumeral(unsigned n) { return MkNumeral(n, MkIntSort()); }
        TermPtr MkIntNumeral(__int64 n) { return MkNumeral(n, MkIntSort()); }
        TermPtr MkIntNumeral(unsigned __int64 n) { return MkNumeral(n, MkIntSort()); }


        /**
           \brief Create a numeral of type Real.
        */
        TermPtr MkRealNumeral(String^ n) { return MkNumeral(n, MkRealSort()); }
        TermPtr MkRealNumeral(int n) { return MkNumeral(n, MkRealSort()); }
        TermPtr MkRealNumeral(unsigned n) { return MkNumeral(n, MkRealSort()); }
        TermPtr MkRealNumeral(__int64 n) { return MkNumeral(n, MkRealSort()); }
        TermPtr MkRealNumeral(unsigned __int64 n) { return MkNumeral(n, MkRealSort()); }

        /*@}*/

        /**
           @name Quantifiers
        */
        /*@{*/
        
        /**
           \brief Create a pattern for quantifier instantiation.

           Z3 uses pattern matching to instantiate quantifiers. If a
           pattern is not provided for a quantifier, then Z3 will
           automatically compute a set of patterns for it. However, for
           optimal performance, the user should provide the patterns.
           
           Patterns comprise an array of terms. The array of terms 
           passed to MkPattern should be
           non-empty.  If the array comprises of more than one term, it is
           a called a multi-pattern.
           
           In general, one can pass in an array of (multi-)patterns in the
           quantifier constructor.

           To summarize, each quantifier takes an array of alternative multi-patterns. 
           The quantifier is instantiated for every multi-pattern that is matched.
           Each multi-pattern is an array of terms. All terms must match for the 
           multi-pattern to trigger instantiation.
           Create a multi-pattern using <tt>MkPattern</tt>.
           Create an array of multi-patterns and pass it to the quantifier constructor.
           If you just want a multi-pattern with a single term, then pass in the singleton array

           
           For example, if you want to create the multi-pattern
           consisting of the two terms: \ccode{(store A I V)} 
           and \ccode{(select A J)} 
           where A, I, J, V are bound variables, create the pattern

           <pre>
           pattern1 = context.MkPattern(new TermPtr[]{ 
                             context.MkArrayStore(A,I,V),
                             context.MkArraySelect(A,J)
                                      })
           </pre>
           Then form the array 
           <pre> 
                 new PatternPtr[]{ pattern1 }

           </pre>
           and pass it to the
           function \ccode{MkForall} or \ccode{MkExists}.
           Suppose you also want to have the quantifier be instantiated if 
           the pattern \ccode{(select (store A I V) J)} is matched, then create the
           pattern:
           <pre>
           pattern2 = context.MkPattern(new TermPtr[] {
                                         context.MkArraySelect(context.MkArrayStore(A,I,V),J) })
           </pre>
           Then form the array:
           <pre>
                 new PatternPtr[] { pattern1, pattern2 }
           </pre>

           \sa MkForall
           \sa MkExists
        */
        PatternPtr MkPattern(array<TermPtr>^ terms);

        /**
           \brief Create a bound variable.

           Bound variables are indexed by de-Bruijn indices. It is perhaps easiest to explain
           the meaning of de-Bruijn indices by indicating the compilation process from
           non-de-Bruijn formulas to de-Bruijn format.

           \verbatim 
           abs(forall (x1) phi) = forall (x1) abs1(phi, x1, 0)
           abs(forall (x1, x2) phi) = abs(forall (x1) abs(forall (x2) phi))
           abs1(x, x, n) = b_n
           abs1(y, x, n) = y
           abs1(f(t1,...,tn), x, n) = f(abs1(t1,x,n), ..., abs1(tn,x,n))
           abs1(forall (x1) phi, x, n) = forall (x1) (abs1(phi, x, n+1))
           \endverbatim

           The last line is significant: the index of a bound variable is different depending
           on the scope in which it appears. The deeper x appears, the higher is its
           index.
       
           \param index de-Bruijn index
           \param ty type of the bound variable

           \sa MkForall
           \sa MkExists
        */
        TermPtr MkBound(unsigned index, SortPtr ty);
    
        /**
           \brief Create a forall formula.
       
           \param weight quantifiers are associated with weights indicating the importance 
                  of using the quantifier during instantiation. By default, pass the weight 0.
           \param patterns array containing the patterns created using #MkPattern.
           \param types array containing the types of the bound variables.
           \param names array containing the names as symbols of the bound variables.
           \param body the body of the quantifier.
       
           \sa MkPattern
           \sa MkBound
           \sa MkExists
        */
        TermPtr MkForall(
            unsigned weight,
            array<PatternPtr>^ patterns,
            array<SortPtr>^ types,
            array<Symbol^>^ names,
            TermPtr body
            );

        /**
           \brief Create a forall formula.
       
           \param weight quantifiers are associated with weights indicating the importance 
                  of using the quantifier during instantiation. By default, pass the weight 0.
           \param patterns array containing the patterns created using #MkPattern.
           \param types array containing the types of the bound variables.
           \param names array containing the names as strings of the bound variables.
           \param body the body of the quantifier.
       
           \sa MkPattern
           \sa MkBound
           \sa MkExists
        */
        TermPtr MkForall(
            unsigned weight,
            array<PatternPtr>^ patterns,
            array<SortPtr>^ types,
            array<String^>^ names,
            TermPtr body
            );

        /**
           \brief Create a forall formula.

           This function allows creating a forall without using de-Bruijn indices in the body or patterns.
           It is sometimes convenient to create the body of a quantifier without de-Bruijn indices, but
           instead use constants. These constants have to be replaced by de-Bruijn indices for the 
           internal representation. This function allows the caller to hand over the task to Z3 of abstracting
           the constants into bound variables, so that each occurrence of the variables in the array 
           <tt>bound</tt> gets replaced by a de-Bruijn index.
       
           \param weight quantifiers are associated with weights indicating the importance 
                  of using the quantifier during instantiation. By default, pass the weight 0.
           \param bound array containing the constants to be abstracted as bound variables.
           \param patterns array containing the patterns created using #MkPattern.
           \param body the body of the quantifier.
       
           \sa MkPattern
           \sa MkExists
        */
        TermPtr MkForall(
            unsigned           weight,
            array<AppPtr>^   bound,
            array<PatternPtr>^ patterns,
            TermPtr body
            );

        /**
           \brief Create an exists formula. Similar to #MkForall.
           
           \sa MkPattern
           \sa MkBound
           \sa MkForall
        */
        TermPtr MkExists(
            unsigned weight,
            array<PatternPtr>^ patterns,
            array<SortPtr>^ types,
            array<Symbol^>^ names,
            TermPtr body
            );

        TermPtr MkExists(
            unsigned weight,
            array<PatternPtr>^ patterns,
            array<SortPtr>^ types,
            array<String^>^ names,
            TermPtr body
            );

        TermPtr MkExists(
            unsigned           weight,
            array<AppPtr>^   bound,
            array<PatternPtr>^ patterns,
            TermPtr            body
            );

        /**
           \brief Create a quantifier with no-pattern directives and symbols.

           Use de-Bruijn indexing.
           
           \sa MkPattern
           \sa MkBound
           \sa MkForall
           \sa MkExists
        */

        TermPtr MkQuantifier(
            bool                  is_forall,
            unsigned              weight,
            array<PatternPtr>^    patterns,
            array<TermPtr>^       no_patterns,
            array<SortPtr>^       types,
            array<Symbol^>^       names,
            TermPtr               body
            )
        {
            return MkQuantifier(is_forall, weight, nullptr, nullptr, patterns, no_patterns, types, names, body);
        }


        TermPtr MkQuantifier(
            bool                  is_forall,
            unsigned              weight,
            Symbol^               quantifier_id,
            Symbol^               skolem_id,
            array<PatternPtr>^    patterns,
            array<TermPtr>^       no_patterns,
            array<SortPtr>^       types,
            array<Symbol^>^       names,
            TermPtr                body
            );



        /**
           \brief Create a quantifier with no-pattern directives and symbols.
           
           Abstract terms as the bound variables.

           \sa MkPattern
           \sa MkBound
           \sa MkForall
           \sa MkExists
        */

        TermPtr MkQuantifier(
            bool                  is_forall,
            unsigned              weight,
            Symbol^               quantifier_id,
            Symbol^               skolem_id,
            array<PatternPtr>^    patterns,
            array<TermPtr>^       no_patterns,
            array<TermPtr>^       bound,
            TermPtr               body
            );


        /*@}*/


        /**
           @name Accessors
        */
        /*@{*/

        /** 
            \brief Return a unique identifier for \c t.
        */

        unsigned GetTermId(TermPtr t);

        /** 
            \brief Return a unique identifier for \c f.
        */
        unsigned GetFuncDeclId(FuncDeclPtr f);

        /** 
            \brief Return a unique identifier for \c s.
        */
        unsigned GetSortId(SortPtr s);
        
        
        /**
           \brief Return \c SymbolKind.Int if the symbol was constructed
           using #MkIntSymbol, and \c SymbolKind.String if the symbol
           was constructed using #MkStringSymbol.
        */
        SymbolKind GetSymbolKind(Symbol^ s);

        /**
           \brief Return the symbol int value. 
       
           \pre GetSymbolKind(s) == SymbolKind.Int

           \sa MkIntSymbol
        */
        int GetSymbolInt(Symbol^ s);
    
        /**
           \brief Return the symbol name. 

           \pre GetSymbolKind(s) = SymbolKind.String

           \sa MkStringSymbol
        */
        String^ GetSymbolString(Symbol^ s);

        /**
           \brief Return \c true if the two given AST nodes are equal.
        */
        bool IsEq(TermPtr t1, TermPtr t2);

        /**
           \brief Return \c true if \c t is well sorted.
        */
        bool IsWellSorted(TermPtr t);

        /**
           \brief Return the kind of the given AST.
        */
        TermKind GetTermKind(TermPtr a);

        /** 
            \brief Return the kind of the built-in operator.

            \pre GetTermKind(a) == TermKind.App
        */
        DeclKind GetDeclKind(FuncDeclPtr d);

        /** 
            \brief Return auxiliary parameters associated with the built-in operator.
            For example, the operator for bit-vector extraction uses
            two parameters, the upper and lower bit-index for extraction.
        */
        array<IRawParameter^>^ GetDeclParameters(FuncDeclPtr d);
    
        /**
           \brief Return the declaration of a constant or function application.

           \pre GetTermKind(a) == TermKind.App
        */
        FuncDeclPtr GetAppDecl(AppPtr a);
        
        /**
           \brief Return the arguments of an application. If \c t
           is an constant, then array is empty.
        */
        array<TermPtr>^ GetAppArgs(AppPtr a);

        /**
           \brief Return the number of a numeric ast.

           \pre GetTermKind(a) == TermKind.Numeral
        */
        String^ GetNumeralString(TermPtr a);

        /**
           \brief Similar to #GetNumeralString, but only succeeds if
           the value can fit in a machine int. Throw InvalidArgument if the call fails.

           \pre GetTermKind(v) == TermKind.Numeral && IsInt32(v)
      
           \sa GetNumeralString
        */
        int GetNumeralInt(TermPtr v);

        bool TryGetNumeralInt(TermPtr v, [Out] int% i);

        /**
           \brief Similar to #GetNumeralString, but only succeeds if
           the value can fit in a machine unsigned int. Throw InvalidArgument if the call fails.

           \pre GetTermKind(v) == TermKind.Numeral
      
           \sa GetNumeralString
        */
        unsigned int GetNumeralUInt(TermPtr v);

        bool TryGetNumeralUInt(TermPtr v, [Out] unsigned int% u);


        /**
           \brief Similar to #GetNumeralString, but only succeeds if
           the value can fit in a machine unsigned long long int. Throw InvalidArgument if the call fails.

           \pre GetTermKind(v) == TermKind.Numeral
           
           \sa GetNumeralString
        */
        unsigned __int64 GetNumeralUInt64(TermPtr v);

        bool TryGetNumeralUInt64(TermPtr v, [Out] unsigned __int64% u);


        /**
           \brief Similar to #GetNumeralString, but only succeeds if
           the value can fit in a machine long long int. Throw InvalidArgument if the call fails.

           \pre GetTermKind(v) == TermKind.Numeral

        */
        __int64 GetNumeralInt64(TermPtr v);

        bool TryGetNumeralInt64(TermPtr v, [Out] __int64% i);

        /**
           \brief Similar to #GetNumeralString, but only succeeds if
           the value can fit in a machine long long int. Throw InvalidArgument if the call fails.

           \pre GetTermKind(v) == TermKind.Numeral

           \sa GetNumeralString
        */
        
        bool TryGetNumeral(TermPtr v, [Out] __int64% num, [Out] __int64% den);

        void GetNumeral(TermPtr v, [Out] System::Numerics::BigInteger% num, [Out] System::Numerics::BigInteger% den);        

        /**
           \brief Return the Boolean value of a truth constant. Return LBool::Undef if a is not a boolean constant (true or false).

           \pre GetTermKind(a) == TermKind.App
        */
        LBool GetBoolValue(TermPtr a);


        /**
           \brief Return the index of a de-Brujin bound variable.

           \pre GetTermKind(a) == TermKind.Var
        */
        unsigned GetVarIndex(TermPtr a) {
            return Z3_get_index_value(ctx(), get_ast(a));
        }

        /** 
            \brief Return components of a quantifier.

            \pre GetTermKind(a) = TermKind.Quantifier
        */
        RawQuantifier^ GetQuantifier(TermPtr a);


        /** 
            \brief Return array of terms in the pattern.

            \pre GetTermKind(a) = TermKind.Pattern
        */
        array<TermPtr>^ GetPatternTerms(PatternPtr p);

        /**
           \brief Return the constant declaration name as a symbol. 
        */
        Symbol^ GetDeclName(FuncDeclPtr d);

        /**
           \brief Return the type name as a symbol. 
        */
        Symbol^ GetSortName(SortPtr ty);

        /**
           \brief Return the type of an AST node.
           
           The AST node must be a constant, application, numeral, bound variable, or quantifier.           
        */
        SortPtr GetSort(TermPtr a);

        /**
           \brief Return the domain of a function declaration.
           
        */
        array<SortPtr>^ GetDomain(FuncDeclPtr d);


        /** 
            \brief Return the range of the given declaration. 

            If \c d is a constant (i.e., has zero arguments), then this
            function returns the type of the constant.
        */
        SortPtr GetRange(FuncDeclPtr d);

        /**
           \brief Return the type kind (e.g., array, tuple, int, bool, etc).
           
           \sa SortKind
        */
        SortKind GetSortKind(SortPtr t);

        /**
           \brief Return the size of the given bit-vector type. 

           \pre GetSortKind(t) = SortKind.Bv

           \sa MkBvSort
           \sa GetSortKind
        */
        unsigned GetBvSortSize(SortPtr t);

        /**
           \brief Return the domain of the given array type.
       
           \pre GetSortKind(t) == SortKind.Array

           \sa MkArraySort
           \sa GetSortKind
        */
        SortPtr GetArraySortDomain(SortPtr t);

        /**
           \brief Return the range of the given array type. 
           
           \pre GetSortKind(t) == SortKind.Array

           \sa MkArraySort
           \sa GetSortKind
        */
        SortPtr GetArraySortRange(SortPtr t);

        /**
           \brief Return the constructor declaration of the given tuple
           type. 

           \pre GetSortKind(t) == SortKind.Tuple

           \sa MkTupleSort
           \sa GetSortKind
        */
        FuncDeclPtr GetTupleConstructor(SortPtr t);
    
        /**
           \brief Return the field declarations of a given tuple type.

           \pre GetSortKind(t) == SortKind.Tuple


           \sa MkTupleSort
           \sa GetSortKind
        */
        array<FuncDeclPtr>^ GetTupleFields(SortPtr t);

        /*@}*/

        /**
           @name Modifiers
        */
        /*@{*/

        /**
           \brief Update the arguments of a term or quantifier.
           \pre The number of arguments passed in new_args should
                be the same as number of arguments to the term t.            
        */
        TermPtr UpdateTerm(TermPtr t, array<TermPtr>^ new_args);

        /*@}*/


        /**
           @name Constraints
        */
        /*@{*/
        
        /** 
            \brief Create a backtracking point.
            
            The logical context can be viewed as a stack of contexts.  The
            scope level is the number of elements on this stack. The stack
            of contexts is simulated using trail (undo) stacks.
            
            \sa Pop
            \sa PersistTerm
        */
        void Push();
    
        /**
           \brief Backtrack.
           
           Restores the context from the top of the stack, and pops it off the
           stack.  Any changes to the logical context (by #AssertCnstr or
           other functions) between the matching #Push and \c Pop
           operators are flushed, and the context is completely restored to
           what it was right before the #Push.
          
           \param num_scopes number of scopes to pop. Default value is 1.

           \sa Push
           \sa PersistTerm
        */
        void Pop(unsigned num_scopes);

        void Pop() { Pop(1); }

        unsigned GetNumScopes();


        /**
           \brief Persist a term during num_scopes of pops.
           
           Normally, references to terms are no longer valid when 
           popping scopes beyond the level where the terms are created.
           If you want to reference a term below the scope where it
           was created, use this method to specify how many pops
           the term should survive.
           The current scope level is given as the current
           total number of calls to push subtracted by the
           total number of calls to pop.
           If num_scopes is larger or equal to the current 
           scope level, then the term pointer persists throughout
           the life-time of the context.

           Example usage:
           
           context.Push(); 
           context.Push(); 
           Term t = context.MkNumeral(1, context.MkIntSort());
           context.PersistTerm(t, 1);
           context.Pop();
           // reference to t is valid.
           context.Pop();
           // reference to t is not valid.
        */
        void PersistTerm(TermPtr t, unsigned num_scopes);


        /**
           \brief Assert a constraing into the logical context.
           
           After one assertion, the logical context may become
           inconsistent.  
           
           The functions #Check or #CheckAndGetModel should be
           used to check whether the logical context is consistent or not.
           
           \sa Check
           \sa CheckAndGetModel
        */
        void AssertCnstr(TermPtr a);
    
        /**
           \brief Check whether the given logical context is consistent or not.
           
           If the logical context is not unsatisfiable (i.e., the return value is different from \c false)
           and model construction is enabled (see #Config), then a model is stored in \c m. Otherwise,
           the value \c null is stored in \c m.
           The caller is responsible for deleting the model using its Dispose method.
           
           \remark Model construction must be enabled using configuration
           parameters (See, #Config).

           \sa Check
        */
        LBool CheckAndGetModel([Out] RawModel^% m);
    
        /**
           \brief Check whether the given logical context is consistent or not.
           
           The function #CheckAndGetModel should be used when models are needed.

        */
        LBool Check();

        /**
           \brief Check whether the given logical context is consistent or 
                  not with respect to auxiliary assumptions.
           
           If the logical context is not unsatisfiable (i.e., the return value is different from \c false)
           and model construction is enabled (see #Config), then a model is stored in \c m. Otherwise,
           the value \c null is stored in \c m.
           The caller is responsible for deleting the model using its Dispose method.
           If the logical context is unsatisfiable, then a proof object is return and stored
           in \c proof.
           An unsatisfiable core (subset) for the set of supplied assumptions is returned.
           
           \remark Model construction must be enabled using configuration
           parameters (See, #Config).

           \param m returned model.
           \param assumptions array of auxiliary assumptions.
           \param proof proof object. Proofs must be enabled for this value to be returned.
           \param core subset of assumptions that is an unsatisfiable core.

           \sa Check
        */
        LBool CheckAssumptions([Out] RawModel^% m, 
                               [In]  array<TermPtr>^ assumptions, 
                               [Out] TermPtr% proof, 
                               [Out] array<TermPtr>^% core);

        /**
           \brief Cancel the current search initiated using #Check, #CheckAndGetModel, or #CheckAssumptions.

           \sa Check
           \sa CheckAndGetModel
           \sa CheckAssumptions
        */
        void SoftCheckCancel();
        


        /**
           \brief Retrieve congruence class representatives for terms.
           
           The function can be used for relying on Z3 to identify equal terms under the current
           set of assumptions. The array of terms and array of class identifiers should have
           the same length. The class identifiers are numerals that are assigned to the same
           value for their corresponding terms if the current context forces the terms to be
           equal. You cannot deduce that terms corresponding to different numerals must be different, 
           (especially when using non-convex theories).
           Also note that not necessarily all implied equalities are returned by this call.
           Only the set of implied equalities that follow from simple constraint and 
           equality propagation is discovered.
           
           A side-effect of the function is a satisfiability check.
           The function return LBool.False if the current assertions are not satisfiable.

           \sa Check
        */

        LBool GetImpliedEqualities(
            [In]  array<TermPtr>^ terms,
            [Out] array<unsigned>^% class_ids
            );


        /**
           \brief Obtain explanation for search failure.
           
           \sa Check()
        */
        SearchFailureExplanation GetSearchFailureExplanation();


        /**
           \brief Return conjunction of literals and formulas assigned to true in the current state.
        */
        TermPtr GetAssignments();

        /**
           \brief Retrieve set of labels set in current satisfying assignment.
        */
        LabeledLiterals^ GetRelevantLabels();

        /**
           \brief Retrieve set of literals satisfying the current assignment.
        */
        LabeledLiterals^ GetRelevantLiterals();

        /**
           \brief Retrieve set of guessed literals satisfying the current assignment.
        */
        LabeledLiterals^ GetGuessedLiterals();

        /**
           \brief Block the combination of remaining non-disabled labels.

           Subsequent calls to Check will not contain satisfying assignments with the same
           combination of labels.
        */
        void BlockLiterals(LabeledLiterals^ labels);

        /**
           \brief Obtain literal corresponding to index in list of literals.
        */
        TermPtr GetLiteral(LabeledLiterals^ labels, unsigned idx) {
            return labels->GetLiteral(idx);
        }

        /**
           \brief Interface to simplifier.

           Provides an interface to the AST simplifier used by Z3.
           It allows clients to piggyback on top of the AST simplifier
           for their own term manipulation.
        */        
        TermPtr Simplify(TermPtr a);
        
    
        /*@}*/
    
        /**
           @name String conversion
        */
        /*@{*/


        /**
           \brief Select mode for the format used for pretty-printing AST nodes.

           The default mode for pretty printing AST nodes is to produce
           SMT-LIB style output where common subexpressions are printed 
           at each occurrence. The mode is called PrintMode.SmtlibFull.
           To print shared common subexpressions only once, use the PrintMode.LowLevel
           mode.        
        */

        void SetPrintMode(PrintMode mode);

        /**
           \brief Convert the given AST node into a string.           
        */
        String^ ToString(AstPtr a);
        
        void Display(System::IO::TextWriter^ w, AstPtr a);
    
        /**
           \brief Convert the given logical context into a string.
       
           This function is mainly used for debugging purposes. It displays
           the internal structure of a logical context.
        */
        virtual String^ ToString() override;

        void Display(System::IO::TextWriter^ w);

        /**
           \brief Convert the given logical context into a string.
       
           This function is mainly used for debugging purposes. It displays
           the internal structure of a logical context.
        */
        String^ StatisticsToString() {
            return gcnew String(Z3_statistics_to_string(ctx()));
        }

        void DisplayStatistics(System::IO::TextWriter^ w) {
            w->Write(StatisticsToString());
        }

        /**
           \brief Convert the given benchmark into SMT-LIB formatted string.
        */
        String^ BenchmarkToSmtlib(String^ name,
                                  String^ logic,
                                  String^ status,
                                  String^ attributes,
                                  array<TermPtr>^ assumptions,
                                  TermPtr formula);

        /*@}*/

        /**
           @name Parser interface
        */
        /*@{*/
        /**
           \brief Parse the given string using the SMT-LIB parser. 
              
           The symbol table of the parser can be initialized using the given types and declarations. 
           The symbols in the arrays \c type_names and \c decl_names don't need to match the names
           of the types and declarations in the arrays \c types and \c decls. This is an useful feature
           since we can use arbitrary names to reference types and declarations defined using the C API.

           The formulas, assumptions and declarations defined in \c str.

           \param  string      The string contianing the SMT-LIB benchmark
           \param  sorts       List of auxiliary sorts used in SMT-LIB benchmark.
           \param  decls       List of declarations to be used for parsing the SMT-LIB string.
           \param  assumptions Returned set of assumptions.
           \param  formulas    Returned set of formulas.
           \param  new_decls   Additional declarations from the SMT-LIB benchmark.
           \param  new_sorts   Additional sorts fromt he SMT-LIB benchmark.
           \param  parser_out  String containing error messages from parsing.
        */
        void ParseSmtlibString(
            String^ string,
            [In]  array<SortPtr>^     sorts,
            [In]  array<FuncDeclPtr>^ decls,
            [Out] array<TermPtr>^%    assumptions,            
            [Out] array<TermPtr>^%    formulas,
            [Out] array<FuncDeclPtr>^% new_decls,
            [Out] array<SortPtr>^%    new_sorts,
            [Out] String^% parser_out
            );
    
        /**
           \brief Similar to #ParseSmtlibString, but reads the benchmark from a file.
        */
        void ParseSmtlibFile(
            String^             file,
            [In]  array<SortPtr>^     sorts,
            [In]  array<FuncDeclPtr>^ decls,
            [Out] array<TermPtr>^%    assumptions,            
            [Out] array<TermPtr>^%    formulas,
            [Out] array<FuncDeclPtr>^% new_decls,
            [Out] array<SortPtr>^%    new_sorts,
            [Out] String^% parser_out
            );


        /**
           \brief Parse a string in the native Z3 format.
           
           Return conjunction of Asserts occurring in the string.
        */
        TermPtr ParseZ3String(String^ s);

        /**
           \brief Parse a file containing formulas in Z3's native format.
           
           Return conjunction of Asserts occurring in the file.
        */
        TermPtr ParseZ3File(String^ filename);

        /**
           \brief Parse a string in the SMT-LIB2 format.
           
           Return conjunction of Asserts occurring in the string.
        */
        TermPtr ParseSmtlib2String(String^ s, array<SortPtr>^ sorts, array<FuncDeclPtr>^ decls);

        /**
           \brief Parse a file containing formulas in SMT-LIB2 format.
           
           Return conjunction of Asserts occurring in the file.
        */
        TermPtr ParseSmtlib2File(String^ filename, array<SortPtr>^ sorts, array<FuncDeclPtr>^ decls);

        /**
           \brief Execute commands from a string in the SMT-LIB2 format.
           
           Return conjunction of Asserts modulo push/pop.
        */
        TermPtr ExecSmtlib2String(String^ s, array<SortPtr>^ sorts, array<FuncDeclPtr>^ decls);

        /**
           \brief Execute commands from a file containing formulas in SMT-LIB2 format.
           
           Return conjunction of Asserts modulo push/pop.
        */
        TermPtr ExecSmtlib2File(String^ filename, array<SortPtr>^ sorts, array<FuncDeclPtr>^ decls);
        /*@}*/

        /**
           @name Errors
        */
        /*{@*/

        /**
           \brief Register a Z3 error handler.
           
           A call to a Z3 function throw Z3Error when
           it is not used correctly.  An error handler can be registered
           and will be called in this case prior to throwing Z3Error.
        */
        static void SetErrorHandler(IErrorHandler^ h);

        /**
           \brief Return a string describing the given error code.
        */
        static String^ GetErrorMessage(ErrorCode err);

        /**
           \brief Free all resources allocated for Z3.
        */
        static void ResetMemory();
        
        /*@}*/


        /**
           @name Miscellaneous
        */
        /*@{*/
    
        /**
           \brief Return Z3 version number information.
        */
        void GetVersion(
            [Out] unsigned % major, 
            [Out] unsigned % minor, 
            [Out] unsigned % build_number, 
            [Out] unsigned % revision_number);
        /*@}*/


        /**
           \brief Create user theory.
        */

		RawTheory^ MkTheory(String^ name);

	internal:
        static Dictionary<GCHandle, RawContext^>^ contexts;

	public:

        /**
           \brief Register fixed-point rules.
        */

        void RegisterRelation(FuncDeclPtr relation);

        void AddRule(TermPtr rule, Symbol^ name);

        /**
           \brief post a query.
           The return value is LBool.True if the query is satisfiabl,e
           it is LBool.False if it is not satisfiabled, and Undef on
           timeouts or approximation.
        */
        LBool Query(TermPtr query);

        /**
           \brief retrieve details on the search satus.
        */
        String^ GetQueryStatus();

        /**
            \brief retrieve formula that satisfies the previous query,
            assuming the return value was LBool.True
        */
        TermPtr GetQueryAnswer();

        String^ FixedpointToString(array<TermPtr>^ queries);

        array<TermPtr>^ SimplifyFixedpointRules(array<TermPtr>^ rules, array<FuncDeclPtr>^ output_predicates);

        // functions for creating custom Fixedpoint relations.
    internal:
        static void fixedpoint_assign_callback(void*, Z3_func_decl, unsigned, Z3_ast const[], unsigned, Z3_ast const[]);
        static void fixedpoint_apply_callback(void*, Z3_func_decl, unsigned, Z3_ast const[], Z3_ast*);
        IntPtr m_fixedpoint_gch;
    private:
        Action3<FuncDeclPtr, array<TermPtr>^, array<TermPtr>^>^ m_fixedpoint_assign;
        Func2<FuncDeclPtr, array<TermPtr>^, TermPtr>^           m_fixedpoint_apply;
        void init_fixedpoint_callbacks();
    public:
        property Action3<FuncDeclPtr, array<TermPtr>^, array<TermPtr>^>^ FixedpointAssign {
            void set(Action3<FuncDeclPtr, array<TermPtr>^, array<TermPtr>^>^ value) {
                m_fixedpoint_assign = value;
                init_fixedpoint_callbacks();
            }
        }
        property Func2<FuncDeclPtr, array<TermPtr>^, TermPtr>^ FixedpointApply {
            void set(Func2<FuncDeclPtr, array<TermPtr>^, TermPtr>^ value) {
                m_fixedpoint_apply = value;
                init_fixedpoint_callbacks();
            }
        }
        
    };

    public ref class RawTheory {
        typedef GCHandle GCHandle;
        typedef GCHandleType GCHandleType;
    private: 
        Z3_theory    m_theory;
        ref_context& m_context;
        String^      m_name;
        static Dictionary<GCHandle,RawTheory^>^ theories;
    protected:
        !RawTheory() {}
    public:        
        property String^ Name { String^ get() { return m_name; } }
    internal:
        RawTheory(ref_context& ctx, String^ name);
        ~RawTheory();
        
        static RawTheory^ GetTheory(Z3_theory th) {
            Z3_theory_data td = Z3_theory_get_ext_data(th);
            return theories[GCHandle::FromIntPtr(IntPtr(td))];
        }


        // Delete Handler
    private:
        Action0^ delete_handler;
    internal:
        static void static_delete_callback(Z3_theory th);

    public:
        property Action0^ DeleteHandler
        {
            void set(Action0^ value)
            {
                delete_handler = value;
            }
        }

        // ReduceEq
    internal:
        static Z3_bool reduce_eq_callback(Z3_theory th, Z3_ast a, Z3_ast b, Z3_ast* r);
    private:
        Func2<TermPtr, TermPtr, TermPtr>^ reduce_eq;
        void set_reduce_eq(Func2<TermPtr, TermPtr, TermPtr>^ value);
    public:
        property Func2<TermPtr, TermPtr, TermPtr>^ ReduceEq {
            void set(Func2<TermPtr, TermPtr, TermPtr>^ value) {
                set_reduce_eq(value);
            }
        }


        // ReduceApp
    private:
        Func2<FuncDeclPtr, array<TermPtr>^, TermPtr>^ reduce_app;
        void set_reduce_app(Func2<FuncDeclPtr, array<TermPtr>^, TermPtr>^ value);
    public:
        property Func2<FuncDeclPtr, array<TermPtr>^, TermPtr>^ ReduceApp {
            void set(Func2<FuncDeclPtr, array<TermPtr>^, TermPtr>^ value) {
                set_reduce_app(value);
            }
        }
    internal:
        static Z3_bool reduce_app_callback(Z3_theory th, Z3_func_decl f, unsigned num_args, Z3_ast const args[], Z3_ast* r);

    // Reduce distinct
    private:
        Func1<array<TermPtr>^, TermPtr>^ reduce_distinct;
        void set_reduce_distinct(Func1<array<TermPtr>^, TermPtr>^ value);
    internal:
        static Z3_bool reduce_distinct_callback(Z3_theory th, unsigned n, Z3_ast const args[], Z3_ast* r);
    public:
        property Func1<array<TermPtr>^, TermPtr>^ ReduceDistinct {
            void set(Func1<array<TermPtr>^, TermPtr>^ value) {
                set_reduce_distinct(value);
            }
        }

        // NewRelevant
    internal: 
        Action<TermPtr>^ new_relevant;
    private: 
        void set_new_relevant(Action<TermPtr>^ value);
    public: 
        property Action<TermPtr>^ NewRelevant {
            void set(Action<TermPtr>^ value) {
                set_new_relevant(value);
            }
        }

        // NewApp
    private: 
        void set_new_app(Action<TermPtr>^ value);
    internal: 
        Action<TermPtr>^ new_app;
    public: 
        property Action<TermPtr>^ NewApp {
            void set(Action<TermPtr>^ value) {
                set_new_app(value);
            }
        }

        // NewElem
    private: 
        void set_new_elem(Action<TermPtr>^ value);
    internal: 
        Action<TermPtr>^ new_elem;
    public: 
        property Action<TermPtr>^ NewElem {
            void set(Action<TermPtr>^ value) {
                set_new_elem(value);
            }
        }
        
        // InitSearch
    private:
        void set_init_search(Action0^ value);
    internal:
        Action0^ init_search;
    public: 
        property Action0^ InitSearch {
            void set(Action0^ value) { set_init_search(value); }
        }

        // Push
    private:
        void set_push(Action0^ value);
    internal:
        Action0^ push;
    public: 
        property Action0^ Push {
            void set(Action0^ value) { set_push(value); }
        }

        // Pop
    private:
        void set_pop(Action0^ value);
    internal:
        Action0^ pop;
    public: 
        property Action0^ Pop {
            void set(Action0^ value) { set_pop(value); }
        }

        // Restart
    private:
        void set_restart(Action0^ value);
    internal:
        Action0^ restart;
    public: 
        property Action0^ Restart {
            void set(Action0^ value) { set_restart(value); }
        }

        // Reset
    private:
        void set_reset(Action0^ value);
    internal:
        Action0^ reset;
    public: 
        property Action0^ Reset {
            void set(Action0^ value) { set_reset(value); }
        }


        // FinalCheck
    private:
        void set_final_check(Func0<bool>^ value);
    internal:
        Func0<bool>^ final_check;
    public: 
        property Func0<bool>^ FinalCheck {
            void set(Func0<bool>^ value) { set_final_check(value); }
        }


        // NewEq
    private:
        void set_new_eq(Action2<TermPtr, TermPtr>^ value);
    internal:
        Action2<TermPtr, TermPtr>^ new_eq;
    public:
        property Action2<TermPtr, TermPtr>^ NewEq
        {
            void set(Action2<TermPtr, TermPtr>^ value) { set_new_eq(value); }
        }


        // NewDiseq
    private:
        void set_new_diseq(Action2<TermPtr, TermPtr>^ value);
    internal:
        Action2<TermPtr, TermPtr>^ new_diseq;
    public:
        property Action2<TermPtr, TermPtr>^ NewDiseq
        {
            void set(Action2<TermPtr, TermPtr>^ value) { set_new_diseq(value); }
        }

        // NewAssignment
    internal:
        Action2<TermPtr, bool>^ new_assignment;
    private:
        void set_new_assignment(Action2<TermPtr, bool>^ value);
    public:
        property Action2<TermPtr, bool>^ NewAssignment {
            void set(Action2<TermPtr, bool>^ value) {
                set_new_assignment(value);
            }
        }

        void AssertTheoryAxiom(TermPtr ax)
        {
            Z3_theory_assert_axiom(m_theory, get_ast(ax));
        }

        void AssumeEq(TermPtr lhs, TermPtr rhs)
        {
            Z3_theory_assume_eq(m_theory, get_ast(lhs), get_ast(rhs));
        }

        void EnableTheoryAxiomSimplification(bool flag)
        {
            Z3_theory_enable_axiom_simplification(m_theory, flag);
        }

        TermPtr GetEqcRoot(TermPtr n)
        {
            return TermPtr(Z3_theory_get_eqc_root(m_theory, get_ast(n)));
        }

        TermPtr GetEqcNext(TermPtr n)
        {
            return TermPtr(Z3_theory_get_eqc_next(m_theory, get_ast(n)));
        }

        
        array<TermPtr>^ GetParents(TermPtr n) {
            unsigned np = Z3_theory_get_num_parents(m_theory, get_ast(n));
            array<TermPtr>^ result = gcnew array<TermPtr>(np);
            for (unsigned i = 0; i < np; ++i)
                {
                result[i] = TermPtr(Z3_theory_get_parent(m_theory, get_ast(n), i));
            }
            return result;
        }

        bool IsTheoryValue(TermPtr a)
        {
            return 0 != Z3_theory_is_value(m_theory, get_ast(a));
        }

        bool IsTheoryDecl(FuncDeclPtr d)
        {
            return 0 != Z3_theory_is_decl(m_theory, get_func_decl(d));
        }

        array<TermPtr>^ GetElems()
        {
            unsigned n = Z3_theory_get_num_elems(m_theory);
            array<TermPtr>^ result = gcnew array<TermPtr>(n);
            for (unsigned i = 0; i < n; ++i)
            {
                result[i] = TermPtr(Z3_theory_get_elem(m_theory, i));
            }
            return result;
        }

        array<TermPtr>^ GetApps()
        {
            unsigned n = Z3_theory_get_num_apps(m_theory);
            array<TermPtr>^ result = gcnew array<TermPtr>(n);
            for (unsigned i = 0; i < n; ++i)
            {
                result[i] = TermPtr(Z3_theory_get_app(m_theory, i));
            }
            return result;
        }

        SortPtr MkSort(Symbol^ s) 
        {
            return SortPtr(Z3_theory_mk_sort(m_context(), m_theory, s->get()));
        }
        
        TermPtr MkValue(Symbol^ s, SortPtr srt) 
        {
            return TermPtr(Z3_theory_mk_value(m_context(), m_theory, s->get(), get_sort(srt)));
        }
        
        TermPtr MkConstant(Symbol^ s, SortPtr srt)
        {
            return TermPtr(Z3_theory_mk_constant(m_context(), m_theory, s->get(), get_sort(srt)));
        }
        
        FuncDeclPtr MkFuncDecl(Symbol^ n, array<SortPtr>^ domain, SortPtr range);

        SortPtr MkSort(String^ s);
        
        TermPtr MkValue(String^ s, SortPtr srt); 
        
        TermPtr MkConstant(String^ s, SortPtr srt);
        
        FuncDeclPtr MkFuncDecl(String^ n, array<SortPtr>^ domain, SortPtr range);
                
    };


    ref class Context;
    ref class Model;
    ref class Theory;

    public ref class Ast : public System::IComparable {
    protected:
        AstPtr      m_ast;
        RawContext^ m_ctx;
        !Ast();
    internal:
        Ast(RawContext^ c, AstPtr a);
        AstPtr GetPtr() { return m_ast; }
        AstPtr operator()() { return m_ast; }
    public:
        ~Ast();

        /**
           \brief Test equality of asts.
        */
        virtual bool Equals(Object^ obj) override;

        /**
           \brief Obtain hash code.
        */
        virtual int GetHashCode() override;

        /**
           \brief Pretty print term, sort or declaration.
        */
        virtual String^ ToString() override;

        /**
           \brief Implement IComparable::CompareTo 
        */
        virtual int CompareTo(Object^ other);

        /**
           \brief overload ==, != 
        */
        // virtual bool operator==(Object^ other);

        // virtual bool operator!=(Object^ other);

        virtual unsigned GetId() { return m_ctx->GetTermId(m_ast); }
    };

    public ref class Sort : public Ast{
    internal:
        Sort(RawContext^ c, SortPtr a) : Ast(c,a) {}
    public:
        String^ GetName();
        virtual unsigned GetId() override { return m_ctx->GetSortId(m_ast); }
    };

    public ref class FuncDecl : public Ast {
    internal:
        FuncDecl(RawContext^ c, FuncDeclPtr a) : Ast(c,a) {}
    public:
        String^ GetDeclName();
        DeclKind GetKind();
        virtual unsigned GetId() override { return m_ctx->GetFuncDeclId(m_ast); }
    };

    public ref class Term : public Ast {
    internal:
        Term(RawContext^ c, TermPtr a) : Ast(c,a) {}
    public:
        /**
           \brief Overloading of Boolean operators.

           \pre Argument type is Boolean.
        */
        static Term^ operator!(Term^ t1);
        static Term^ operator&(Term^ t1, Term^ t2);
        static Term^ operator|(Term^ t1, Term^ t2);
        static Term^ operator^(Term^ t1, Term^ t2);
        /**
           \brief Overloading of common arithmetical operators.
           
           \pre Argument types are integers or reals.
        */
        static Term^ operator+(Term^ t1, Term^ t2);
        static Term^ operator*(Term^ t1, Term^ t2);
        static Term^ operator/(Term^ t1, Term^ t2);
        static Term^ operator-(Term^ t1, Term^ t2);
        static Term^ operator>(Term^ t1, Term^ t2);
        static Term^ operator<(Term^ t1, Term^ t2);
        static Term^ operator>=(Term^ t1, Term^ t2);
        static Term^ operator<=(Term^ t1, Term^ t2);

        /**
           \brief Overloading of array select.

           \pre Argument is an index, the main term is of array type.
        */
        Term^ operator[](Term^ index);

        TermKind GetKind();
        FuncDecl^ GetAppDecl();
        array<Term^>^ GetAppArgs();
        Sort^ GetSort();
        String^ GetNumeralString();
        unsigned GetVarIndex();
        ref class Quantifier^ GetQuantifier();
    };
    
    public ref class Pattern : public Ast {
    internal:
        Pattern(RawContext^ c, PatternPtr a) : Ast(c,a) {}
    };

    public ref class Quantifier {
    public:
        bool                  IsForall;
        unsigned              Weight;
        array<Pattern^>^      Patterns;
        array<Term^>^         NoPatterns;
        array<Sort^>^         Sorts;
        array<Symbol^>^       Names;
        Term^                 Body;
    };

    public ref class ArrayValue {
    public:
        array<Term^>^   Domain; 
        array<Term^>^   Range;
        Term^           ElseCase;
    };

    public ref class TermParameter : public IParameter  { 
        Term^ m_value;
    internal:
        TermParameter(Term^ t) : m_value(t) {}
    public:
        virtual String^ ToString() override { return m_value->ToString(); }
        property  Term^ GetTerm {  Term^ get() { return m_value; } }
    };

    public ref class SortParameter : public IParameter  { 
        Sort^ m_value;
    internal:
        SortParameter(Sort^ s): m_value(s) {}
    public:
        property  Sort^ GetSort {  Sort^ get() { return m_value; } }
        virtual String^ ToString() override { return m_value->ToString(); }
    };

    public ref class FuncDeclParameter : public IParameter  { 
        FuncDecl^ m_value;
    internal:
        FuncDeclParameter(FuncDecl^ d): m_value(d) {}
    public:
        property  FuncDecl^ GetFuncDecl { FuncDecl^ get() { return m_value; } }
        virtual String^ ToString() override { return m_value->ToString(); } 
    };

    /**
       \brief Term and optional proof object returned by user-simplifier
    */
    public ref class TermProof {
        Term^ m_term;
        Term^ m_proof; // proof is optional, use null for absence of proofs.
    public:
        TermProof(Term^ term, Term^ proof): m_term(term), m_proof(proof) {}
        property Term^ GetTerm { Term^ get() { return m_term; } }
        property Term^ Proof { Term^ get() { return m_proof; } }
    };

    /**
       \brief Type safe contexts.
    */
    public ref class Context  {
        
        /// @cond 0
        RawContext^ m_ctx;


    public:
        template<class Tptr, class T>
        array<Tptr>^ CopyArray(array<T^>^ a) {
            if (!a) {
                return gcnew array<Tptr>(0);
            }
            int len = a->Length;
            array<Tptr>^ result = gcnew array<Tptr>(len);
            for (int i = 0; i < len; ++i) {
                if (a[i]) {
                    result[i] = a[i]();
                }
                else {
                    result[i] = IntPtr(0);
                }
            }
            return result;
        }

        array<SortPtr>^ CopyArray(array<Sort^>^ a) {
            return CopyArray<SortPtr, Sort>(a);
        }

        array<FuncDeclPtr>^ CopyArray(array<FuncDecl^>^ a) {
            return CopyArray<FuncDeclPtr, FuncDecl>(a);
        }

        array<TermPtr>^ CopyArray(array<Term^>^ a) {
            return CopyArray<TermPtr,Term>(a);
        }

        array<PatternPtr>^ CopyArray(array<Pattern^>^ a) {
            return CopyArray<PatternPtr,Pattern>(a);
        }
    internal:

        template<class T, class TPtr>
        static array<T^>^ CopyAstArray(RawContext^ ctx, array<TPtr>^ a) {
            if (!a) return nullptr;
            int len = a->Length;
            array<T^>^ result = gcnew array<T^>(len);

            for (int i = 0; i < len; ++i) {
                if (a[i] != IntPtr(0)) {
                    result[i] = gcnew T(ctx,a[i]);
                }
                else {
                    result[i] = nullptr;
                }
            }
            return result;
        }

    public:
        template<class T, class TPtr>
        array<T^>^ CopyAstArray(array<TPtr>^ a) {
            return CopyAstArray<T,TPtr>(m_ctx, a);
        }


        array<Sort^>^ CopySortArray(array<SortPtr>^ a) {
            return CopyAstArray<Sort, SortPtr>(a);
        }

        array<Term^>^ CopyTermArray(array<TermPtr>^ a) {
            return CopyAstArray<Term, TermPtr>(a);
        }

        array<FuncDecl^>^ CopyFuncDeclArray(array<FuncDeclPtr>^ a) {
            return CopyAstArray<FuncDecl, FuncDeclPtr>(a);
        }
    internal:
        static array<Term^>^ CopyTermArray(RawContext^ ctx, array<TermPtr>^ a) {
            return CopyAstArray<Term, TermPtr>(ctx, a);
        }

        static array<Sort^>^ CopySortArray(RawContext^ ctx, array<SortPtr>^ a) {
            return CopyAstArray<Sort, SortPtr>(ctx, a);
        }
        static Quantifier^ GetQuantifier(RawContext^ ctx, Term^ term);

    internal:
        property RawContext^ GetContext { RawContext^ get() { return m_ctx; } }

        /// @endcond


    public:
        /**
           \brief Create a type safe version of a context.
           
           Terms and models created using the type safe context are wrapped within
           objects. The object wrappers prevent confusing the \ccode{IntPtr} type used for 
           terms, sorts and values with arbitrary instances.
           
           Each method in #Context is paired with a corresponding method in Context.
           
           \sa Context.
        */

        Context() { m_ctx = gcnew RawContext(); }

        Context(Config^ config) : m_ctx(gcnew RawContext(config)) {}

        Context(Config^ config, ReferenceCounted^ rc) : m_ctx(gcnew RawContext(config, rc)) {}

        /**
           \brief Set the context from an externally created context.
        */
        void SetContext(Z3_context ctx){ m_ctx->SetContext(ctx); }

        /**
           \brief Dispose method for type safe contexts.
        */
        ~Context() { m_ctx->Reset(); }

        /**
           \brief Enable low-level debug tracing. 

           This method only works with debug builds.
        */

        void EnableDebugTrace(String^ tag) { m_ctx->EnableDebugTrace(tag); }

        /**
           \brief Enable or disable warning messages sent to the console out/error.

           Warnings are printed after passing \c true, warning messages are
           suppressed after calling this method with \c false.
        */

        void ToggleWarningMessages(bool enabled) { m_ctx->ToggleWarningMessages(enabled); }

        void UpdateParamValue(String^ param_id, String^ value) { m_ctx->UpdateParamValue(param_id, value); }

        String^ GetParamValue(String^ param_id) {
            return m_ctx->GetParamValue(param_id);
        }

        /**
           \brief Configure the SMTLIB logic to be used in the given logical context.
        */

        bool SetLogic(String^ logic) { return m_ctx->SetLogic(logic); }

        /**
           @name Symbols
        */
        /*@{*/
        Symbol^ MkSymbol(int i) { return m_ctx->MkSymbol(i); }

        Symbol^ MkSymbol(String^ s) { return m_ctx->MkSymbol(s); }
        /*@}*/

        /**
           @name Modifiers
        */
        /*@{*/

        /**
           \brief Update the arguments of a term or quantifier.
           \pre The number of arguments passed in new_args should
                be the same as number of arguments to the term t.            
        */
        Term^ UpdateTerm(Term^ t, array<Term^>^ new_args) {
            return gcnew Term(m_ctx, m_ctx->UpdateTerm(t(), CopyArray(new_args)));
        }
        
        /*@}*/

        /**
           @name Constraints
        */
        /*@{*/
        void Push() { m_ctx->Push(); }
        void Pop(unsigned num_scopes) { m_ctx->Pop(num_scopes); }
        void Pop() { Pop(1); }
        unsigned GetNumScopes() { return m_ctx->GetNumScopes(); }
        void PersistTerm(Term^ t, unsigned num_scopes) { 
            m_ctx->PersistTerm(t(), num_scopes); 
        }
        LBool Check() { return m_ctx->Check(); }
        LBool CheckAndGetModel([Out] Model^% m);
        LBool CheckAssumptions([Out] Model^% m, 
                               [In]  array<Term^>^ assumptions, 
                               [Out] Term^% proof, 
                               [Out] array<Term^>^% core);
        void SoftCheckCancel();

        LBool GetImpliedEqualities(
            [In]  array<Term^>^ terms,
            [Out] array<unsigned>^% class_ids);

        SearchFailureExplanation GetSearchFailureExplanation() { return m_ctx->GetSearchFailureExplanation(); }
        LabeledLiterals^ GetRelevantLabels() { return m_ctx->GetRelevantLabels(); }
        LabeledLiterals^ GetRelevantLiterals() { return m_ctx->GetRelevantLiterals(); }
        LabeledLiterals^ GetGuessedLiterals() { return m_ctx->GetGuessedLiterals(); }
        void BlockLiterals(LabeledLiterals^ lbls) { m_ctx->BlockLiterals(lbls); }
        Term^ GetLiteral(LabeledLiterals^ lbls, unsigned idx) { return gcnew Term(m_ctx, m_ctx->GetLiteral(lbls, idx)); }
        Term^ Simplify(Term^ a) { return gcnew Term(m_ctx,m_ctx->Simplify(a())); }
        void AssertCnstr(Term^ a) { m_ctx->AssertCnstr(a()); }
        /*@}*/

        virtual String^ ToString() override { return m_ctx->ToString(); }

        void Display(System::IO::TextWriter^ w) { m_ctx->Display(w); }
        Term^ GetAssignments() { return gcnew Term(m_ctx, m_ctx->GetAssignments()); }
        String^ StatisticsToString() { return m_ctx->StatisticsToString(); }
        void DisplayStatistics(System::IO::TextWriter^ w) { m_ctx->DisplayStatistics(w); }

        /**
           \brief Convert the given benchmark into SMT-LIB formatted string.
        */
        String^ BenchmarkToSmtlib(String^ name,
                                  String^ logic,
                                  String^ status,
                                  String^ attributes,
                                  array<Term^>^ assumptions,
                                  Term^ formula);

        void ParseSmtlibString(
            String^            string,
            [In]  array<Sort^>^     sorts,
            [In]  array<FuncDecl^>^ decls,
            [Out] array<Term^>^%    assumptions,            
            [Out] array<Term^>^%    formulas,
            [Out] array<FuncDecl^>^% new_decls,
            [Out] array<Sort^>^%    new_sorts,
            [Out] String^% parser_out
            );
                                         

        void ParseSmtlibFile(
            String^ file,
            [In]  array<Sort^>^     sorts,
            [In]  array<FuncDecl^>^ decls,
            [Out] array<Term^>^%    assumptions,            
            [Out] array<Term^>^%    formulas,
            [Out] array<FuncDecl^>^% new_decls,
            [Out] array<Sort^>^%    new_sorts,
            [Out] String^% parser_out
            );


        Term^ ParseZ3String(String^ s) {
            return gcnew Term(m_ctx,m_ctx->ParseZ3String(s));
        }

        Term^ ParseZ3File(String^ s) {
            return gcnew Term(m_ctx,m_ctx->ParseZ3File(s));
        }

        Term^ ParseSmtlib2String(String^ s, array<Sort^>^ sorts, array<FuncDecl^>^ decls) {
            return gcnew Term(m_ctx,m_ctx->ParseSmtlib2String(s, CopyArray(sorts), CopyArray(decls)));
        }

        Term^ ParseSmtlib2File(String^ s, array<Sort^>^ sorts, array<FuncDecl^>^ decls) {
            return gcnew Term(m_ctx,m_ctx->ParseSmtlib2File(s, CopyArray(sorts), CopyArray(decls)));
        }

        Term^ ExecSmtlib2String(String^ s, array<Sort^>^ sorts, array<FuncDecl^>^ decls) {
            return gcnew Term(m_ctx,m_ctx->ExecSmtlib2String(s, CopyArray(sorts), CopyArray(decls)));
        }

        Term^ ExecSmtlib2File(String^ s, array<Sort^>^ sorts, array<FuncDecl^>^ decls) {
            return gcnew Term(m_ctx,m_ctx->ExecSmtlib2File(s, CopyArray(sorts), CopyArray(decls)));
        }

        static void SetErrorHandler(IErrorHandler^ h) {
            RawContext::SetErrorHandler(h);
        }

        static String^ GetErrorMessage(ErrorCode err) {
            return RawContext::GetErrorMessage(err);
        }

        static void ResetMemory() {
            RawContext::ResetMemory();
        }

        
        void SetPrintMode(PrintMode mode) { m_ctx->SetPrintMode(mode); }

        String^ ToString(Ast^ a) { return m_ctx->ToString(a()); }
        
        void Display(System::IO::TextWriter^ w, Ast^ a) { m_ctx->Display(w, a()); }


        Sort^ MkIntSort() { return gcnew Sort(m_ctx,m_ctx->MkIntSort()); }
        Sort^ MkBoolSort() { return gcnew Sort(m_ctx,m_ctx->MkBoolSort()); }
        Sort^ MkSort(Symbol^ s) { return gcnew Sort(m_ctx,m_ctx->MkSort(s)); }
        Sort^ MkSort(String^ s) { return gcnew Sort(m_ctx,m_ctx->MkSort(s)); }
        Sort^ MkSort(int i) { return gcnew Sort(m_ctx,m_ctx->MkSort(i)); }   
        Sort^ MkFiniteDomainSort(String^ s, unsigned __int64 domain_size) { return gcnew Sort(m_ctx, m_ctx->MkFiniteDomainSort(s, domain_size)); }
        Sort^ MkRealSort() { return gcnew Sort(m_ctx,m_ctx->MkRealSort()); } 
        Sort^ MkBvSort(unsigned sz) { return gcnew Sort(m_ctx,m_ctx->MkBvSort(sz)); }
        Sort^ MkArraySort(Sort^ domain, Sort^ range) { return gcnew Sort(m_ctx,m_ctx->MkArraySort(domain(), range())); }

        Sort^ MkTupleSort(
            Symbol^               mk_tuple_name, 
            array<Symbol^>^       field_names,
            array<Sort^>^       field_types,
            [Out] FuncDecl^%         mk_tuple_decl,
            [In, Out] array<FuncDecl^>^  proj_decl
            );

        Sort^ MkTupleSort(
            String^               mk_tuple_name, 
            array<String^>^       field_names,
            array<Sort^>^       field_types,
            [Out] FuncDecl^%         mk_tuple_decl,
            [In, Out] array<FuncDecl^>^  proj_decl
            );
        
        Sort^ MkEnumerationSort(
            String^             name,
            array<String^>^     enum_names,
            array<FuncDecl^>^ enum_consts,
            array<FuncDecl^>^ enum_testers);

        Sort^ MkListSort(
            String^ name,
            Sort^ elem_sort,
            [Out] FuncDecl^% nil_decl,
            [Out] FuncDecl^% is_nil_decl,
            [Out] FuncDecl^% cons_decl,
            [Out] FuncDecl^% is_cons_decl,
            [Out] FuncDecl^% head_decl,
            [Out] FuncDecl^% tail_decl
            );
        
        Constructor^ MkConstructor(
            String^ name,
            String^ tester,
            array<String^>^ field_names,
            array<Sort^>^ field_sorts,
            array<unsigned>^ field_refs
            );

        
        FuncDecl^ GetConstructor(Constructor^ c);

        FuncDecl^ GetTester(Constructor^ c);

        array<FuncDecl^>^ GetAccessors(Constructor^ c);

        /**
           \brief create datatype sort.
        */

        Sort^ MkDataType(
            String^ name,
            array<Constructor^>^ constructors
            ) {
            return gcnew Sort(m_ctx, m_ctx->MkDataType(name, constructors));
        }

        /**
           \brief create datatype sort.
        */

        array<Sort^>^ MkDataTypes(
            array<String^>^ names,
            array<array<Constructor^>^>^ constructors
            ) {
            return CopySortArray(m_ctx->MkDataTypes(names, constructors));
        }


        FuncDecl^ MkFuncDecl(Symbol^ s, array<Sort^>^ domain, Sort^ range) {
            return gcnew FuncDecl(m_ctx,m_ctx->MkFuncDecl(s, CopyArray(domain), range()));
        }

        FuncDecl^ MkFuncDecl(String^ s, array<Sort^>^ domain, Sort^ range) {
            return gcnew FuncDecl(m_ctx,m_ctx->MkFuncDecl(s, CopyArray(domain), range()));
        }

        FuncDecl^ MkConstDecl(Symbol^ s, Sort^ ty) {
            return MkFuncDecl(s, gcnew array<Sort^>(0), ty);
        }
        FuncDecl^ MkFuncDecl(Symbol^ s, Sort^ domain, Sort^ range) {
            return gcnew FuncDecl(m_ctx,m_ctx->MkFuncDecl(s, domain(), range()));
        }
        FuncDecl^ MkFuncDecl(Symbol^ s, Sort^ d1, Sort^ d2, Sort^ range) {
            return gcnew FuncDecl(m_ctx,m_ctx->MkFuncDecl(s, d1(), d2(), range()));            
        }
        FuncDecl^ MkConstDecl(String^ s, Sort^ ty) {
            return MkFuncDecl(s, gcnew array<Sort^>(0), ty);
        }
        FuncDecl^ MkFuncDecl(String^ s, Sort^ domain, Sort^ range) {
            return gcnew FuncDecl(m_ctx,m_ctx->MkFuncDecl(s, domain(), range()));
        }
        FuncDecl^ MkFuncDecl(String^ s, Sort^ d1, Sort^ d2, Sort^ range) {
            return gcnew FuncDecl(m_ctx,m_ctx->MkFuncDecl(s, d1(), d2(), range()));            
        }
        Term^ MkApp(FuncDecl^ d, array<Term^>^ args) {
            return gcnew Term(m_ctx,m_ctx->MkApp(d(), CopyArray(args)));
        }
        Term^ MkApp(FuncDecl^ d, Term^ arg) {
            return gcnew Term(m_ctx,m_ctx->MkApp(d(), arg()));
        }
        Term^ MkApp(FuncDecl^ d, Term^ arg1, Term^ arg2) {
            return gcnew Term(m_ctx,m_ctx->MkApp(d(), arg1(), arg2()));
        }
        Term^ MkApp(FuncDecl^ d, Term^ arg1, Term^ arg2, Term^ arg3) {
            return gcnew Term(m_ctx,m_ctx->MkApp(d(), arg1(), arg2(), arg3()));
        }
        Term^ MkConst(FuncDecl^ d) {
            return gcnew Term(m_ctx,m_ctx->MkConst(d()));
        }
        Term^ MkConst(String^ s, Sort^ ty) {
            return gcnew  Term(m_ctx,m_ctx->MkConst(s,ty()));
        }
        Term^ MkConst(Symbol^ s, Sort^ ty) {
            return gcnew Term(m_ctx,m_ctx->MkConst(s, ty()));
        }
        FuncDecl^ MkFreshFuncDecl(String^ prefix, array<Sort^>^ domain, Sort^ range) {
            return gcnew FuncDecl(m_ctx,m_ctx->MkFreshFuncDecl(prefix, CopyArray(domain), range()));
        }
        Term^ MkFreshConst(String^ prefix, Sort^ ty) {
            return gcnew Term(m_ctx,m_ctx->MkFreshConst(prefix, ty()));
        }
        Term^ MkTrue() { return gcnew Term(m_ctx,m_ctx->MkTrue()); }
        Term^ MkFalse() { return gcnew Term(m_ctx,m_ctx->MkFalse()); }
        Term^ MkLabel(Symbol^ name, bool pos, Term^ fml) { return gcnew Term(m_ctx,m_ctx->MkLabel(name, pos, fml())); }

        Term^ MkEq(Term^ l, Term^ r) { return gcnew Term(m_ctx,m_ctx->MkEq(l(), r())); }
        Term^ MkDistinct(array<Term^>^ args) {
            return gcnew Term(m_ctx,m_ctx->MkDistinct(CopyArray(args))); 
        }
        Term^ MkNot(Term^ arg) { return gcnew Term(m_ctx,m_ctx->MkNot(arg())); }
        Term^ MkIte(Term^ t1, Term^ t2, Term^ t3) {
            return gcnew Term(m_ctx,m_ctx->MkIte(t1(), t2(), t3()));
        }
        Term^ MkIff(Term^ t1, Term^ t2) { return gcnew Term(m_ctx,m_ctx->MkIff(t1(), t2()));  }
        Term^ MkImplies(Term^ t1, Term^ t2) {return gcnew Term(m_ctx,m_ctx->MkImplies(t1(), t2()));}
        Term^ MkXor(Term^ t1, Term^ t2) { return gcnew Term(m_ctx,m_ctx->MkXor(t1(), t2())); }
        Term^ MkAnd(array<Term^>^ args) { return gcnew Term(m_ctx,m_ctx->MkAnd(CopyArray(args))); }
        Term^ MkAnd(Term^ t1, Term^ t2) { return gcnew Term(m_ctx,m_ctx->MkAnd(t1(), t2())); }
        Term^ MkOr(array<Term^>^ args) { return gcnew Term(m_ctx,m_ctx->MkOr(CopyArray(args))); }
        Term^ MkOr(Term^ t1, Term^ t2) { return gcnew Term(m_ctx,m_ctx->MkOr(t1(), t2())); }
        Term^ MkAdd(array<Term^>^ args) { return gcnew Term(m_ctx,m_ctx->MkAdd(CopyArray(args))); }
        Term^ MkAdd(Term^ t1, Term^ t2) { return gcnew Term(m_ctx,m_ctx->MkAdd(t1(), t2())); }
        Term^ MkMul(array<Term^>^ args) { return gcnew Term(m_ctx,m_ctx->MkMul(CopyArray(args))); }
        Term^ MkMul(Term^ t1, Term^ t2) { return gcnew Term(m_ctx,m_ctx->MkMul(t1(), t2())); }
        Term^ MkSub(array<Term^>^ args) { return gcnew Term(m_ctx,m_ctx->MkSub(CopyArray(args))); }
        Term^ MkSub(Term^ t1, Term^ t2) { return gcnew Term(m_ctx,m_ctx->MkSub(t1(), t2())); }
        Term^ MkUnaryMinus(Term^ arg) { return gcnew Term(m_ctx,m_ctx->MkUnaryMinus(arg())); }
        Term^ MkDiv(Term^ t1, Term^ t2) { return gcnew Term(m_ctx,m_ctx->MkDiv(t1(), t2())); }
        Term^ MkMod(Term^ t1, Term^ t2) { return gcnew Term(m_ctx,m_ctx->MkMod(t1(), t2())); }
        Term^ MkRem(Term^ t1, Term^ t2) { return gcnew Term(m_ctx,m_ctx->MkRem(t1(), t2())); }
        Term^ MkToReal(Term^ t1) { return gcnew Term(m_ctx,m_ctx->MkToReal(t1())); }
        Term^ MkToInt(Term^ t1) { return gcnew Term(m_ctx,m_ctx->MkToInt(t1())); }
        Term^ MkIsInt(Term^ t1) { return gcnew Term(m_ctx,m_ctx->MkIsInt(t1())); }
        Term^ MkLt(Term^ t1, Term^ t2) { return gcnew Term(m_ctx,m_ctx->MkLt(t1(), t2())); }
        Term^ MkLe(Term^ t1, Term^ t2) { return gcnew Term(m_ctx,m_ctx->MkLe(t1(), t2())); }
        Term^ MkGt(Term^ t1, Term^ t2) { return gcnew Term(m_ctx,m_ctx->MkGt(t1(), t2())); }
        Term^ MkGe(Term^ t1, Term^ t2) { return gcnew Term(m_ctx,m_ctx->MkGe(t1(), t2())); }
        Term^ MkBvNot(Term^ t1) { return gcnew Term(m_ctx,m_ctx->MkBvNot(t1())); }
        Term^ MkBvReduceAnd(Term^ t1) { return gcnew Term(m_ctx,m_ctx->MkBvReduceAnd(t1())); }
        Term^ MkBvRedcueOr(Term^ t1) { return gcnew Term(m_ctx,m_ctx->MkBvReduceOr(t1())); }
        Term^ MkBvAnd(Term^ t1, Term^ t2) { return gcnew Term(m_ctx,m_ctx->MkBvAnd(t1(), t2())); }
        Term^ MkBvOr(Term^ t1, Term^ t2) { return gcnew Term(m_ctx,m_ctx->MkBvOr(t1(), t2())); }
        Term^ MkBvXor(Term^ t1, Term^ t2) { return gcnew Term(m_ctx,m_ctx->MkBvXor(t1(), t2())); }
        Term^ MkBvNand(Term^ t1, Term^ t2) { return gcnew Term(m_ctx,m_ctx->MkBvNand(t1(), t2())); }
        Term^ MkBvNor(Term^ t1, Term^ t2) { return gcnew Term(m_ctx,m_ctx->MkBvNor(t1(), t2())); }
        Term^ MkBvXnor(Term^ t1, Term^ t2) { return gcnew Term(m_ctx,m_ctx->MkBvXnor(t1(), t2())); }
        Term^ MkBvNeg(Term^ t1) { return gcnew Term(m_ctx,m_ctx->MkBvNeg(t1())); }
        Term^ MkBvAdd(Term^ t1, Term^ t2) { return gcnew Term(m_ctx,m_ctx->MkBvAdd(t1(), t2())); }
        Term^ MkBvSub(Term^ t1, Term^ t2) { return gcnew Term(m_ctx,m_ctx->MkBvSub(t1(), t2())); }
        Term^ MkBvMul(Term^ t1, Term^ t2) { return gcnew Term(m_ctx,m_ctx->MkBvMul(t1(), t2())); }
        Term^ MkBvUdiv(Term^ t1, Term^ t2) { return gcnew Term(m_ctx,m_ctx->MkBvUdiv(t1(), t2())); }
        Term^ MkBvSdiv(Term^ t1, Term^ t2) { return gcnew Term(m_ctx,m_ctx->MkBvSdiv(t1(), t2())); }
        Term^ MkBvUrem(Term^ t1, Term^ t2) { return gcnew Term(m_ctx,m_ctx->MkBvUrem(t1(), t2())); }
        Term^ MkBvSrem(Term^ t1, Term^ t2) { return gcnew Term(m_ctx,m_ctx->MkBvSrem(t1(), t2())); }
        Term^ MkBvSmod(Term^ t1, Term^ t2) { return gcnew Term(m_ctx,m_ctx->MkBvSmod(t1(), t2())); }
        Term^ MkBvUlt(Term^ t1, Term^ t2) { return gcnew Term(m_ctx,m_ctx->MkBvUlt(t1(), t2())); }
        Term^ MkBvSlt(Term^ t1, Term^ t2) { return gcnew Term(m_ctx,m_ctx->MkBvSlt(t1(), t2())); }
        Term^ MkBvUle(Term^ t1, Term^ t2) { return gcnew Term(m_ctx,m_ctx->MkBvUle(t1(), t2())); }
        Term^ MkBvSle(Term^ t1, Term^ t2) { return gcnew Term(m_ctx,m_ctx->MkBvSle(t1(), t2())); }
        Term^ MkBvUge(Term^ t1, Term^ t2) { return gcnew Term(m_ctx,m_ctx->MkBvUge(t1(), t2())); }
        Term^ MkBvSge(Term^ t1, Term^ t2) { return gcnew Term(m_ctx,m_ctx->MkBvSge(t1(), t2())); }
        Term^ MkBvUgt(Term^ t1, Term^ t2) { return gcnew Term(m_ctx,m_ctx->MkBvUgt(t1(), t2())); }
        Term^ MkBvSgt(Term^ t1, Term^ t2) { return gcnew Term(m_ctx,m_ctx->MkBvSgt(t1(), t2())); }
        Term^ MkBvConcat(Term^ t1, Term^ t2) { return gcnew Term(m_ctx,m_ctx->MkBvConcat(t1(), t2())); }
        Term^ MkBvExtract(unsigned high, unsigned low, Term^ t) {
            return gcnew Term(m_ctx,m_ctx->MkBvExtract(high, low, t()));
        }
        Term^ MkBvSignExt(unsigned i, Term^ t) {
            return gcnew Term(m_ctx,m_ctx->MkBvSignExt(i, t()));
        }
        Term^ MkBvZeroExt(unsigned i, Term^ t) {
            return gcnew Term(m_ctx,m_ctx->MkBvZeroExt(i, t()));
        }
        Term^ MkBvRepeat(unsigned i, Term^ t) {
            return gcnew Term(m_ctx,m_ctx->MkBvRepeat(i, t()));
        }
        Term^ MkBvShl(Term^ t1, Term^ t2) { return gcnew Term(m_ctx,m_ctx->MkBvShl(t1(), t2())); }
        Term^ MkBvLshr(Term^ t1, Term^ t2) { return gcnew Term(m_ctx,m_ctx->MkBvLshr(t1(), t2())); }
        Term^ MkBvAshr(Term^ t1, Term^ t2) { return gcnew Term(m_ctx,m_ctx->MkBvAshr(t1(), t2())); }
        Term^ MkBvRotateLeft(unsigned i, Term^ t1) { return gcnew Term(m_ctx,m_ctx->MkBvRotateLeft(i,t1())); }
        Term^ MkBvRotateRight(unsigned i, Term^ t1) { return gcnew Term(m_ctx,m_ctx->MkBvRotateRight(i,t1()));  }
        Term^ MkBvRotateLeft(Term^ t1, Term^ t2) { return gcnew Term(m_ctx,m_ctx->MkBvRotateLeft(t1(), t2())); }
        Term^ MkBvRotateRight(Term^ t1, Term^ t2) { return gcnew Term(m_ctx,m_ctx->MkBvRotateRight(t1(), t2()));  }
        Term^ MkBv2Int(Term^ t1, bool is_signed) { return gcnew Term(m_ctx, m_ctx->MkBv2Int(t1(), is_signed)); }
        Term^ MkInt2Bv(unsigned n, Term^ t1) { return gcnew Term(m_ctx, m_ctx->MkInt2Bv(n, t1())); }
        Term^ MkBvAddNoOverflow(Term^ t1, Term^ t2, bool is_signed) { 
            return gcnew Term(m_ctx,m_ctx->MkBvAddNoOverflow(t1(), t2(), is_signed)); 
        }
        Term^ MkBvAddNoUnderflow(Term^ t1, Term^ t2) { 
            return gcnew Term(m_ctx,m_ctx->MkBvAddNoUnderflow(t1(), t2())); 
        }
        Term^ MkBvSubNoOverflow(Term^ t1, Term^ t2) { 
            return gcnew Term(m_ctx,m_ctx->MkBvSubNoOverflow(t1(), t2())); 
        }
        Term^ MkBvSubNoUnderflow(Term^ t1, Term^ t2, bool is_signed) { 
            return gcnew Term(m_ctx,m_ctx->MkBvSubNoUnderflow(t1(), t2(), is_signed)); 
        }
        Term^ MkBvSDivNoOverflow(Term^ t1, Term^ t2) { 
            return gcnew Term(m_ctx,m_ctx->MkBvSDivNoOverflow(t1(), t2())); 
        }
        Term^ MkBvNegNoOverflow(Term^ t1) { 
            return gcnew Term(m_ctx,m_ctx->MkBvNegNoOverflow(t1())); 
        }
        Term^ MkBvMulNoOverflow(Term^ t1, Term^ t2, bool is_signed) { 
            return gcnew Term(m_ctx,m_ctx->MkBvMulNoOverflow(t1(), t2(), is_signed)); 
        }
        Term^ MkBvMulNoUnderflow(Term^ t1, Term^ t2) { 
            return gcnew Term(m_ctx,m_ctx->MkBvMulNoUnderflow(t1(), t2())); 
        }
        Term^ MkArraySelect(Term^ a, Term^ i) { return gcnew Term(m_ctx,m_ctx->MkArraySelect(a(), i()));  }
        Term^ MkArrayStore(Term^ a, Term^ i, Term^ v) {
            return gcnew Term(m_ctx,m_ctx->MkArrayStore(a(), i(), v()));
        }
        Term^ MkArrayMap(FuncDecl^ f, array<Term^>^ args) {
            return gcnew Term(m_ctx, m_ctx->MkArrayMap(f(), CopyArray(args)));
        }
        Term^ MkArrayConst(Sort^ domain, Term^ v) { return gcnew Term(m_ctx,m_ctx->MkArrayConst(domain(), v())); }
        Term^ MkArrayDefault(Term^ a) { return gcnew Term(m_ctx,m_ctx->MkArrayDefault(a())); }
        Sort^ MkSetSort(Sort^ ty) { return gcnew Sort(m_ctx,m_ctx->MkSetSort(ty())); }
        Term^ MkEmptySet(Sort^ ty) { return gcnew Term(m_ctx,m_ctx->MkEmptySet(ty())); }
        Term^ MkFullSet(Sort^ ty) { return gcnew Term(m_ctx,m_ctx->MkFullSet(ty())); }
        Term^ MkSetAdd(Term^ set, Term^ elem) { return gcnew Term(m_ctx,m_ctx->MkSetAdd(set(), elem())); }
        Term^ MkSetDel(Term^ set, Term^ elem) { return gcnew Term(m_ctx,m_ctx->MkSetDel(set(), elem())); }
        Term^ MkSetUnion(array<Term^>^ sets) {
            return gcnew Term(m_ctx,m_ctx->MkSetUnion(CopyArray(sets)));
        }
        Term^ MkSetUnion(Term^ set1, Term^ set2) {
            return gcnew Term(m_ctx,m_ctx->MkSetUnion(set1(), set2()));
        }
        Term^ MkSetIntersect(array<Term^>^ sets) {
            return gcnew Term(m_ctx,m_ctx->MkSetIntersect(CopyArray(sets)));
        }
        Term^ MkSetIntersect(Term^ set1, Term^ set2) {
            return gcnew Term(m_ctx,m_ctx->MkSetIntersect(set1(), set2()));
        }
        Term^ MkSetDifference(Term^ t1, Term^ t2) {
            return gcnew Term(m_ctx,m_ctx->MkSetDifference(t1(), t2()));
        }
        Term^ MkSetComplement(Term^ arg) {
            return gcnew Term(m_ctx,m_ctx->MkSetComplement(arg()));
        }
        Term^ MkSetMember(Term^ elem, Term^ set) {
            return gcnew Term(m_ctx,m_ctx->MkSetMember(elem(), set()));
        }
        Term^ MkSetSubset(Term^ t1, Term^ t2) {
            return gcnew Term(m_ctx,m_ctx->MkSetSubset(t1(), t2()));
        }
        
        FuncDecl^ MkInjectiveFunction(String^ name, array<Sort^>^ domain, Sort^ range) {
            return gcnew FuncDecl(m_ctx,m_ctx->MkInjectiveFunction(name, CopyArray(domain), range()));
        }
        FuncDecl^ MkInjectiveFunction(Symbol^ name, array<Sort^>^ domain, Sort^ range) {
            return gcnew FuncDecl(m_ctx,m_ctx->MkInjectiveFunction(name, CopyArray(domain), range()));
        }

        Term^ MkNumeral(String^ numeral, Sort^ ty) {
            return gcnew Term(m_ctx,m_ctx->MkNumeral(numeral, ty()));
        }
        Term^ MkNumeral(int n, Sort^ ty) { return gcnew Term(m_ctx,m_ctx->MkNumeral(n, ty()));  }
        Term^ MkNumeral(unsigned n, Sort^ ty) { return gcnew Term(m_ctx,m_ctx->MkNumeral(n, ty())); }
        Term^ MkNumeral(__int64 n, Sort^ ty) { return gcnew Term(m_ctx,m_ctx->MkNumeral(n, ty())); }
        Term^ MkNumeral(unsigned __int64 n, Sort^ ty) { return gcnew Term(m_ctx,m_ctx->MkNumeral(n, ty())); }

        Term^ MkIntNumeral(String^ n) { return MkNumeral(n, MkIntSort()); }
        Term^ MkIntNumeral(int n) { return MkNumeral(n, MkIntSort()); }
        Term^ MkIntNumeral(unsigned n) { return MkNumeral(n, MkIntSort()); }
        Term^ MkIntNumeral(__int64 n) { return MkNumeral(n, MkIntSort()); }
        Term^ MkIntNumeral(unsigned __int64 n) { return MkNumeral(n, MkIntSort()); }
        
        Term^ MkRealNumeral(String^ n) { return MkNumeral(n, MkRealSort()); }
        Term^ MkRealNumeral(int n) { return MkNumeral(n, MkRealSort()); }
        Term^ MkRealNumeral(unsigned n) { return MkNumeral(n, MkRealSort()); }
        Term^ MkRealNumeral(__int64 n) { return MkNumeral(n, MkRealSort()); }
        Term^ MkRealNumeral(unsigned __int64 n) { return MkNumeral(n, MkRealSort()); }

        Pattern^ MkPattern(array<Term^>^ terms) { return gcnew Pattern(m_ctx,m_ctx->MkPattern(CopyArray(terms))); }
        Term^ MkBound(unsigned index, Sort^ ty) { return gcnew Term(m_ctx,m_ctx->MkBound(index, ty())); }

        Term^ MkForall(
            unsigned weight,
            array<Pattern^>^ patterns,
            array<Sort^>^ types,
            array<Symbol^>^ names,
            Term^ body
            ) {
            return gcnew Term(m_ctx,m_ctx->MkForall(weight, CopyArray(patterns), CopyArray(types), names, body()));
        }

        Term^ MkForall(
            unsigned weight,
            array<Pattern^>^ patterns,
            array<Sort^>^ types,
            array<String^>^ names,
            Term^ body
            ) {
            return gcnew Term(m_ctx,m_ctx->MkForall(weight, CopyArray(patterns), CopyArray(types), names, body()));
        }

        Term^ MkForall(
            unsigned           weight,
            array<Term^>^   bound,
            array<Pattern^>^ patterns,
            Term^ body
            ) {
            return gcnew Term(m_ctx,m_ctx->MkForall(weight, CopyArray(bound), CopyArray(patterns), body()));
        }


        Term^ MkExists(
            unsigned weight,
            array<Pattern^>^ patterns,
            array<Sort^>^ types,
            array<Symbol^>^ names,
            Term^ body
            ) {
            return gcnew Term(m_ctx,m_ctx->MkExists(weight, CopyArray(patterns), CopyArray(types), names, body()));
        }

        Term^ MkExists(
            unsigned weight,
            array<Pattern^>^ patterns,
            array<Sort^>^ types,
            array<String^>^ names,
            Term^ body
            ) {
            return gcnew Term(m_ctx,m_ctx->MkExists(weight, CopyArray(patterns), CopyArray(types), names, body()));
        }

        Term^ MkExists(
            unsigned           weight,
            array<Term^>^   bound,
            array<Pattern^>^ patterns,
            Term^            body
            ) {
            return gcnew Term(m_ctx,m_ctx->MkExists(weight, CopyArray(bound), CopyArray(patterns), body()));
        }



        Term^ MkQuantifier(
            bool             is_forall,
            unsigned         weight,
            array<Pattern^>^ patterns,
            array<Term^>^    no_patterns,
            array<Sort^>^    types,
            array<Symbol^>^  names,
            Term^            body
            ) {
            return MkQuantifier(is_forall, weight, nullptr, nullptr, patterns, no_patterns, types, names, body);
        }

        Term^ MkQuantifier(
            bool             is_forall,
            unsigned         weight,
            Symbol^          quantifier_id,
            Symbol^          skolem_id,
            array<Pattern^>^ patterns,
            array<Term^>^    no_patterns,
            array<Sort^>^    types,
            array<Symbol^>^  names,
            Term^            body
            ) {
            return gcnew Term(m_ctx,m_ctx->MkQuantifier(
                                     is_forall, weight, 
                                     quantifier_id, skolem_id,
                                     CopyArray(patterns),
                                     CopyArray(no_patterns),
                                     CopyArray(types),
                                     names,
                                     body()));
        }

        Term^ MkQuantifier(
            bool             is_forall,
            unsigned         weight,
            Symbol^          quantifier_id,
            Symbol^          skolem_id,
            array<Pattern^>^ patterns,
            array<Term^>^    no_patterns,
            array<Term^>^    bound,
            Term^            body
            ) {
            return gcnew Term(m_ctx,m_ctx->MkQuantifier(
                                     is_forall, weight, 
                                     quantifier_id, skolem_id,
                                     CopyArray(patterns),
                                     CopyArray(no_patterns),
                                     CopyArray(bound),
                                     body()));
        }

        SymbolKind GetSymbolKind(Symbol^ s) { return m_ctx->GetSymbolKind(s); }
        int GetSymbolInt(Symbol^ s) { return m_ctx->GetSymbolInt(s); }
        String^ GetSymbolString(Symbol^ s) { return m_ctx->GetSymbolString(s); }
        bool IsEq(Term^ t1, Term^ t2) { return m_ctx->IsEq(t1(), t2()); }
        bool IsWellSorted(Term^ t) { return m_ctx->IsWellSorted(t()); }
        TermKind GetTermKind(Term^ a) { return m_ctx->GetTermKind(a()); }
        DeclKind GetDeclKind(FuncDecl^ d) { return m_ctx->GetDeclKind(d()); }
        array<IParameter^>^ GetDeclParameters(FuncDecl^ d);
        FuncDecl^ GetAppDecl(Term^ a) { return gcnew FuncDecl(m_ctx,m_ctx->GetAppDecl(a())); }
        array<Term^>^ GetAppArgs(Term^ a) { return CopyTermArray(m_ctx->GetAppArgs(a())); }
        String^ GetNumeralString(Term^ a) { return m_ctx->GetNumeralString(a()); }
        int GetNumeralInt(Term^ v) { return m_ctx->GetNumeralInt(v()); }
        bool TryGetNumeralInt(Term^ v, [Out] int% i) { return m_ctx->TryGetNumeralInt(v(), i); }
        unsigned int GetNumeralUInt(Term^ v) { return m_ctx->GetNumeralUInt(v()); }
        bool TryGetNumeralUInt(Term^ v, [Out] unsigned int% u) { return m_ctx->TryGetNumeralUInt(v(), u); }
        __int64 GetNumeralInt64(Term^ v) { return m_ctx->GetNumeralInt64(v()); }
        bool TryGetNumeralInt64(Term^ v, [Out] __int64% i) { return m_ctx->TryGetNumeralInt64(v(), i); }
        unsigned __int64 GetNumeralUInt64(Term^ v) { return m_ctx->GetNumeralUInt64(v()); }
        bool TryGetNumeralUInt64(Term^ v, [Out] unsigned __int64% u) { return m_ctx->TryGetNumeralUInt64(v(), u); }
        bool TryGetNumeral(Term^ v, [Out] __int64% num, [Out] __int64% den) { return m_ctx->TryGetNumeral(v(), num, den); }
        void GetNumeral(Term^ v, [Out] System::Numerics::BigInteger% num, [Out] System::Numerics::BigInteger% den) {
            m_ctx->GetNumeral(v(), num, den);
        }

        LBool GetBoolValue(Term^ v) { return m_ctx->GetBoolValue(v()); }

        unsigned GetVarIndex(Term^ a) { return m_ctx->GetVarIndex(a()); }
        Quantifier^ GetQuantifier(Term^ a) { return GetQuantifier(m_ctx, a); }

        array<Term^>^ GetPatternTerms(Pattern^ p) { return CopyTermArray(m_ctx->GetPatternTerms(p())); }
        Symbol^ GetDeclName(FuncDecl^ d) { return m_ctx->GetDeclName(d()); }
        Symbol^ GetSortName(Sort^ ty) { return m_ctx->GetSortName(ty()); }
        Sort^ GetSort(Term^ a) { return gcnew Sort(m_ctx,m_ctx->GetSort(a())); }
        array<Sort^>^ GetDomain(FuncDecl^ d) { return CopySortArray(m_ctx->GetDomain(d())); }
        Sort^ GetRange(FuncDecl^ d) { return gcnew Sort(m_ctx,m_ctx->GetRange(d())); }
        SortKind GetSortKind(Sort^ t) { return m_ctx->GetSortKind(t()); }
        unsigned GetBvSortSize(Sort^ t) { return m_ctx->GetBvSortSize(t()); }
        Sort^ GetArraySortDomain(Sort^ t) { return gcnew Sort(m_ctx,m_ctx->GetArraySortDomain(t())); }
        Sort^ GetArraySortRange(Sort^ t) { return gcnew Sort(m_ctx,m_ctx->GetArraySortRange(t())); }
        FuncDecl^ GetTupleConstructor(Sort^ t) { return gcnew FuncDecl(m_ctx,m_ctx->GetTupleConstructor(t())); }
        array<FuncDecl^>^ GetTupleFields(Sort^ t) { return CopyFuncDeclArray(m_ctx->GetTupleFields(t())); }

        Theory^ MkTheory(String^ name);
		
        void RegisterRelation(FuncDecl^ r) { m_ctx->RegisterRelation(r()); }

        void AddRule(Term^ rule, Symbol^ name) { m_ctx->AddRule(rule(), name); }

        LBool Query(Term^ query) { return m_ctx->Query(query()); }

        String^ GetQueryStatus() { return m_ctx->GetQueryStatus(); }

        Term^ GetQueryAnswer() { return gcnew Term(m_ctx, m_ctx->GetQueryAnswer()); }

        String^ FixedpointkToString(array<Term^>^ queries) {
            return m_ctx->FixedpointToString(CopyArray(queries)); 
        }
        array<Term^>^ SimplifyFixedpointRules(array<Term^>^ rules, array<FuncDecl^>^ output_predicates) {
            return CopyTermArray(m_ctx->SimplifyFixedpointRules(CopyArray(rules), CopyArray(output_predicates)));
        }
        // functions for creating custom Fixedpoint relations.

    private:
        Action3<FuncDecl^, array<Term^>^, array<Term^>^>^ m_assign_callback;
        void AssignCallbackAux(FuncDeclPtr f, array<TermPtr>^ args, array<TermPtr>^ outs) {
            m_assign_callback(gcnew FuncDecl(m_ctx, f), CopyAstArray<Term, TermPtr>(args), CopyAstArray<Term, TermPtr>(outs));
        }
        Func2<FuncDecl^, array<Term^>^, Term^>^ m_apply_callback;
        TermPtr ApplyCallbackAux(FuncDeclPtr f, array<TermPtr>^ args) {
            return m_apply_callback(gcnew FuncDecl(m_ctx, f), CopyAstArray<Term, TermPtr>(args))();
        }
    public:
        property Action3<FuncDecl^, array<Term^>^, array<Term^>^>^ FixedpointAssign {
            void set(Action3<FuncDecl^, array<Term^>^, array<Term^>^>^ value) {
                m_assign_callback = value;
                m_ctx->FixedpointAssign = gcnew Action3<FuncDeclPtr, array<TermPtr>^, array<TermPtr>^>(this,&Context::AssignCallbackAux);
            }
        }
        property Func2<FuncDecl^, array<Term^>^, Term^>^ FixedpointApply {
            void set(Func2<FuncDecl^, array<Term^>^, Term^>^ value) {
                m_apply_callback = value;
                m_ctx->FixedpointApply = gcnew Func2<FuncDeclPtr, array<TermPtr>^, TermPtr>(this,&Context::ApplyCallbackAux);
            }
        }
    };

    public ref class FunctionEntry {
    public:
        array<Term^>^ Arguments;
        Term^         Result;
    };

    public ref class FunctionGraph {
    public:
        FuncDecl^        Declaration;
        array<FunctionEntry^>^ Entries;
        Term^               Else;
    };


    public ref class Model {
        RawModel^ m_model;
        Context^ m_ctx;

        ArrayValue^ Mk(RawArrayValue^ av);
        FunctionEntry^ Mk(RawFunctionEntry^ fe);
        FunctionGraph^ Mk(RawFunctionGraph^ fg);
        Dictionary<FuncDecl^, FunctionGraph^>^ Mk(Dictionary<FuncDeclPtr, RawFunctionGraph^>^ fgs);

    internal:
        property Context^ GetContext { Context^ get() { return m_ctx; }}
        property RawModel^ GetModel { RawModel^ get() { return m_model; }}

        Model(RawModel^ m, Context^ c) : m_model(m), m_ctx(c) {}

    public:
        ~Model() { m_model->Reset(); }

        array<FuncDecl^>^ GetModelConstants() {
            return m_ctx->CopyFuncDeclArray(m_model->GetModelConstants());
        }

        bool TryGetArrayValue(Term^ a, [Out] ArrayValue^% av);

        Dictionary<FuncDecl^, FunctionGraph^>^ GetFunctionGraphs() { return Mk(m_model->GetFunctionGraphs()); }

        Term^ Eval(Term^ t) { return gcnew Term(m_ctx->GetContext, m_model->Eval(t())); }

        Term^ Eval(FuncDecl^ d, array<Term^>^ args) {
            return gcnew Term(m_ctx->GetContext, m_model->Eval(d(), m_ctx->CopyArray(args)));
        }

        void Display(System::IO::TextWriter^ w) { m_model->Display(w); }

    };

    public ref class Theory
    {
        Context^ m_context;
        RawTheory^ m_theory;

    public:
        property String^ Name { String^ get() { return m_theory->Name; } }

    internal: 
        Theory(Context^ ctx, String^ name)
        {
            m_context = ctx;
            m_theory = gcnew RawTheory(ctx->GetContext->ref_context(), name);
        }

    private:
        array<Term^>^ MkTerms(array<TermPtr>^ ts)
        {
            return m_context->CopyAstArray<Term, TermPtr>(ts);
        }
        Term^ MkTerm(TermPtr t) { return gcnew Term(m_context->GetContext, t); }
        FuncDecl^ MkFuncDecl(FuncDeclPtr f) { return gcnew FuncDecl(m_context->GetContext, f); }

        TermPtr GetTermPtr(Term^ t)
        {
            if (t) return t();
            return IntPtr::Zero;
        }

    public:
        property Action0^ DeleteHandler
        {
            void set(Action0^ value) 
            {
                m_theory->DeleteHandler = value;
            }
        }
    private:
        Func2<Term^, Term^, Term^>^ reduce_eq;
        TermPtr ReduceEqAux(TermPtr a, TermPtr b) {
            return GetTermPtr(reduce_eq(MkTerm(a), MkTerm(b)));
        }
    public:
        property Func2<Term^, Term^, Term^>^ ReduceEq
            {
                void set(Func2<Term^, Term^, Term^>^ value)
                {
                    reduce_eq = value;
                    m_theory->ReduceEq = gcnew Func2<TermPtr,TermPtr,TermPtr>(this,&Theory::ReduceEqAux);
                }
            }
    private:
        Func2<FuncDecl^, array<Term^>^, Term^>^ reduce_app;
        TermPtr ReduceAppAux(FuncDeclPtr a, array<TermPtr>^ b) {
            return GetTermPtr(reduce_app(MkFuncDecl(a), MkTerms(b)));
        }
    public:
        property Func2<FuncDecl^, array<Term^>^, Term^>^ ReduceApp
            {
                void set(Func2<FuncDecl^, array<Term^>^, Term^>^ value)
                {
                    reduce_app = value;
                    m_theory->ReduceApp = gcnew Func2<FuncDeclPtr,array<TermPtr>^,TermPtr>(this,&Theory::ReduceAppAux);
                }
            }
    private:
        Func1<array<Term^>^, Term^>^ reduce_distinct;
        TermPtr ReduceDistinctAux(array<TermPtr>^ args) {
            return GetTermPtr(reduce_distinct(MkTerms(args)));
        }
        
    public:
        property Func1<array<Term^>^, Term^>^ ReduceDistinct
            {
                void set(Func1<array<Term^>^, Term^>^ value)
                {
                    reduce_distinct = value;
                    m_theory->ReduceDistinct = gcnew Func1<array<TermPtr>^,TermPtr>(this, &Theory::ReduceDistinctAux);
                }
            }
    private:
        Action<Term^>^ new_app;
        void NewAppAux(TermPtr a) { return new_app(MkTerm(a)); }
    public:
        property Action<Term^>^ NewApp
        {
            void set(Action<Term^>^ value)
            {
                new_app = value;
                m_theory->NewApp = gcnew Action<TermPtr>(this, &Theory::NewAppAux);
            }
        }
    private:
        Action<Term^>^ new_elem;
        void NewElemAux(TermPtr a) { return new_elem(MkTerm(a)); }
    public:
        property Action<Term^>^ NewElem
        {
            void set(Action<Term^>^ value)
            {
                new_elem = value;
                m_theory->NewElem = gcnew Action<TermPtr>(this, &Theory::NewElemAux);
            }
        }
        property Action0^ InitSearch
        {
            void set(Action0^ value)
            {
                m_theory->InitSearch = value;
            }
        }
        property Action0^ Push
        {
            void set(Action0^ value)
            {
                m_theory->Push = value;
            }
        }
        property Action0^ Pop
        {
            void set(Action0^ value)
            {
                m_theory->Pop = value;
            }
        }
        property Action0^ Reset
        {
            void set(Action0^ value)
            {
                m_theory->Reset = value;
            }
        }
        property Action0^ Restart
        {
            void set(Action0^ value)
            {
                m_theory->Restart = value;
            }
        }

        property Func0<bool>^ FinalCheck
        {
            void set(Func0<bool>^ value)
            {
                m_theory->FinalCheck = value;
            }
        }
    private:
        Action2<Term^,Term^>^ new_eq;
        void NewEqAux(TermPtr a, TermPtr b) {
            new_eq(MkTerm(a), MkTerm(b));
        }
    public:
        property Action2<Term^, Term^>^ NewEq
            {
                void set(Action2<Term^, Term^>^  value) 
                {
                    new_eq = value;
                    m_theory->NewEq = gcnew Action2<TermPtr,TermPtr>(this, &Theory::NewEqAux);
                }
            }
    private:
        Action2<Term^,Term^>^ new_diseq;
        void NewDiseqAux(TermPtr a, TermPtr b) {
            new_diseq(MkTerm(a), MkTerm(b));
        }
    public:
        property Action2<Term^, Term^>^ NewDiseq
            {
                void set(Action2<Term^, Term^>^  value) 
                {
                    new_diseq = value;
                    m_theory->NewDiseq = gcnew Action2<TermPtr,TermPtr>(this, &Theory::NewDiseqAux);
                }
            }
    private:
        Action2<Term^,bool>^ new_assignment;
        void NewAssignmentAux(TermPtr a, bool b) {
            new_assignment(MkTerm(a), b);
        }
    public:
        property Action2<Term^, bool>^ NewAssignment
            {
                void set(Action2<Term^, bool>^  value) 
                {
                    new_assignment = value;
                    m_theory->NewAssignment = gcnew Action2<TermPtr,bool>(this, &Theory::NewAssignmentAux);
                }
            }
    private:
        Action<Term^>^ new_relevant;
        void NewRelevantAux(TermPtr a) { new_relevant(MkTerm(a)); }
    public:
        property Action<Term^>^ NewRelevant
        {
            void set(Action<Term^>^ value) {
                new_relevant = value;
                m_theory->NewRelevant = gcnew Action<TermPtr>(this, &Theory::NewRelevantAux);
            }
        }
        
        void AssertTheoryAxiom(Term^ ax)
        {
            m_theory->AssertTheoryAxiom(ax());
        }

        void AssumeEq(Term^ lhs, Term^ rhs)
        {
            m_theory->AssumeEq(lhs(), rhs());
        }


        void EnableTheoryAxiomSimplification(bool flag)
        {
            m_theory->EnableTheoryAxiomSimplification(flag);
        }

        Term^ GetEqcRoot(Term^ n)
        {
            return MkTerm(m_theory->GetEqcRoot(n()));
        }

        Term^ GetEqcNext(Term^ n)
        {
            return MkTerm(m_theory->GetEqcNext(n()));
        }

        array<Term^>^ GetParents(Term^ n)
        {
            return MkTerms(m_theory->GetParents(n()));
        }

        bool IsTheoryValue(Term^ a)
        {
            return m_theory->IsTheoryValue(a());
        }

        bool IsTheoryDecl(FuncDecl^ d)
        {
            return m_theory->IsTheoryDecl(d());
        }

        array<Term^>^ GetElems()
        {
            return MkTerms(m_theory->GetElems());
        }

        array<Term^>^ GetApps()
        {
            return MkTerms(m_theory->GetApps());
        }


        Sort^ MkSort(Symbol^ s) 
            {
                return gcnew Sort(m_context->GetContext,m_theory->MkSort(s));
            }
        
        Term^ MkValue(Symbol^ s, Sort^ srt) 
            {
                return MkTerm(m_theory->MkValue(s, srt()));
            }
        
        Term^ MkConstant(Symbol^ s, Sort^ srt)
            {
                return MkTerm(m_theory->MkConstant(s, srt()));
            }
        
        FuncDecl^ MkFuncDecl(Symbol^ n, array<Sort^>^ domain, Sort^ range)
            {
                array<SortPtr>^ dom = gcnew array<SortPtr>(domain->Length);
                for (int i = 0; i < domain->Length; ++i) dom[i] = domain[i]();
                return gcnew FuncDecl(m_context->GetContext, m_theory->MkFuncDecl(n, dom, range()));
            }

        Sort^ MkSort(String^ s) 
            {
                return gcnew Sort(m_context->GetContext,m_theory->MkSort(s));
            }
        
        Term^ MkValue(String^ s, Sort^ srt) 
            {
                return MkTerm(m_theory->MkValue(s, srt()));
            }
        
        Term^ MkConstant(String^ s, Sort^ srt)
            {
                return MkTerm(m_theory->MkConstant(s, srt()));
            }
        
        FuncDecl^ MkFuncDecl(String^ n, array<Sort^>^ domain, Sort^ range)
            {
                return this->MkFuncDecl(m_context->MkSymbol(n), domain, range);
            }
        

    };


/*@}*/

};
};

#endif
