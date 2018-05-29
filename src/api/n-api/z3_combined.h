# 1 "../../api/z3.h"
# 1 "<built-in>" 1
# 1 "<built-in>" 3
# 341 "<built-in>" 3
# 1 "<command line>" 1
# 1 "<built-in>" 2
# 1 "../../api/z3.h" 2
# 24 "../../api/z3.h"
# 1 "/Applications/Xcode_9.3.0_fb.app/Contents/Developer/Toolchains/XcodeDefault.xctoolchain/usr/lib/clang/9.1.0/include/stdbool.h" 1 3 4
# 25 "../../api/z3.h" 2
# 1 "/Applications/Xcode_9.3.0_fb.app/Contents/Developer/Toolchains/XcodeDefault.xctoolchain/usr/lib/clang/9.1.0/include/stdint.h" 1 3 4
# 63 "/Applications/Xcode_9.3.0_fb.app/Contents/Developer/Toolchains/XcodeDefault.xctoolchain/usr/lib/clang/9.1.0/include/stdint.h" 3 4
# 1 "/usr/include/stdint.h" 1 3 4
# 18 "/usr/include/stdint.h" 3 4
# 1 "/usr/include/sys/_types/_int8_t.h" 1 3 4
# 30 "/usr/include/sys/_types/_int8_t.h" 3 4
typedef __signed char int8_t;
# 19 "/usr/include/stdint.h" 2 3 4
# 1 "/usr/include/sys/_types/_int16_t.h" 1 3 4
# 30 "/usr/include/sys/_types/_int16_t.h" 3 4
typedef short int16_t;
# 20 "/usr/include/stdint.h" 2 3 4
# 1 "/usr/include/sys/_types/_int32_t.h" 1 3 4
# 30 "/usr/include/sys/_types/_int32_t.h" 3 4
typedef int int32_t;
# 21 "/usr/include/stdint.h" 2 3 4
# 1 "/usr/include/sys/_types/_int64_t.h" 1 3 4
# 30 "/usr/include/sys/_types/_int64_t.h" 3 4
typedef long long int64_t;
# 22 "/usr/include/stdint.h" 2 3 4

# 1 "/usr/include/_types/_uint8_t.h" 1 3 4
# 31 "/usr/include/_types/_uint8_t.h" 3 4
typedef unsigned char uint8_t;
# 24 "/usr/include/stdint.h" 2 3 4
# 1 "/usr/include/_types/_uint16_t.h" 1 3 4
# 31 "/usr/include/_types/_uint16_t.h" 3 4
typedef unsigned short uint16_t;
# 25 "/usr/include/stdint.h" 2 3 4
# 1 "/usr/include/_types/_uint32_t.h" 1 3 4
# 31 "/usr/include/_types/_uint32_t.h" 3 4
typedef unsigned int uint32_t;
# 26 "/usr/include/stdint.h" 2 3 4
# 1 "/usr/include/_types/_uint64_t.h" 1 3 4
# 31 "/usr/include/_types/_uint64_t.h" 3 4
typedef unsigned long long uint64_t;
# 27 "/usr/include/stdint.h" 2 3 4


typedef int8_t int_least8_t;
typedef int16_t int_least16_t;
typedef int32_t int_least32_t;
typedef int64_t int_least64_t;
typedef uint8_t uint_least8_t;
typedef uint16_t uint_least16_t;
typedef uint32_t uint_least32_t;
typedef uint64_t uint_least64_t;



typedef int8_t int_fast8_t;
typedef int16_t int_fast16_t;
typedef int32_t int_fast32_t;
typedef int64_t int_fast64_t;
typedef uint8_t uint_fast8_t;
typedef uint16_t uint_fast16_t;
typedef uint32_t uint_fast32_t;
typedef uint64_t uint_fast64_t;





# 1 "/usr/include/sys/_types.h" 1 3 4
# 32 "/usr/include/sys/_types.h" 3 4
# 1 "/usr/include/sys/cdefs.h" 1 3 4
# 587 "/usr/include/sys/cdefs.h" 3 4
# 1 "/usr/include/sys/_symbol_aliasing.h" 1 3 4
# 588 "/usr/include/sys/cdefs.h" 2 3 4
# 653 "/usr/include/sys/cdefs.h" 3 4
# 1 "/usr/include/sys/_posix_availability.h" 1 3 4
# 654 "/usr/include/sys/cdefs.h" 2 3 4
# 33 "/usr/include/sys/_types.h" 2 3 4
# 1 "/usr/include/machine/_types.h" 1 3 4
# 32 "/usr/include/machine/_types.h" 3 4
# 1 "/usr/include/i386/_types.h" 1 3 4
# 37 "/usr/include/i386/_types.h" 3 4
typedef signed char __int8_t;



typedef unsigned char __uint8_t;
typedef short __int16_t;
typedef unsigned short __uint16_t;
typedef int __int32_t;
typedef unsigned int __uint32_t;
typedef long long __int64_t;
typedef unsigned long long __uint64_t;

typedef long __darwin_intptr_t;
typedef unsigned int __darwin_natural_t;
# 70 "/usr/include/i386/_types.h" 3 4
typedef int __darwin_ct_rune_t;





typedef union {
 char __mbstate8[128];
 long long _mbstateL;
} __mbstate_t;

typedef __mbstate_t __darwin_mbstate_t;


typedef long int __darwin_ptrdiff_t;







typedef long unsigned int __darwin_size_t;





typedef __builtin_va_list __darwin_va_list;





typedef int __darwin_wchar_t;




typedef __darwin_wchar_t __darwin_rune_t;


typedef int __darwin_wint_t;




typedef unsigned long __darwin_clock_t;
typedef __uint32_t __darwin_socklen_t;
typedef long __darwin_ssize_t;
typedef long __darwin_time_t;
# 33 "/usr/include/machine/_types.h" 2 3 4
# 34 "/usr/include/sys/_types.h" 2 3 4
# 55 "/usr/include/sys/_types.h" 3 4
typedef __int64_t __darwin_blkcnt_t;
typedef __int32_t __darwin_blksize_t;
typedef __int32_t __darwin_dev_t;
typedef unsigned int __darwin_fsblkcnt_t;
typedef unsigned int __darwin_fsfilcnt_t;
typedef __uint32_t __darwin_gid_t;
typedef __uint32_t __darwin_id_t;
typedef __uint64_t __darwin_ino64_t;

typedef __darwin_ino64_t __darwin_ino_t;



typedef __darwin_natural_t __darwin_mach_port_name_t;
typedef __darwin_mach_port_name_t __darwin_mach_port_t;
typedef __uint16_t __darwin_mode_t;
typedef __int64_t __darwin_off_t;
typedef __int32_t __darwin_pid_t;
typedef __uint32_t __darwin_sigset_t;
typedef __int32_t __darwin_suseconds_t;
typedef __uint32_t __darwin_uid_t;
typedef __uint32_t __darwin_useconds_t;
typedef unsigned char __darwin_uuid_t[16];
typedef char __darwin_uuid_string_t[37];


# 1 "/usr/include/sys/_pthread/_pthread_types.h" 1 3 4
# 57 "/usr/include/sys/_pthread/_pthread_types.h" 3 4
struct __darwin_pthread_handler_rec {
 void (*__routine)(void *);
 void *__arg;
 struct __darwin_pthread_handler_rec *__next;
};

struct _opaque_pthread_attr_t {
 long __sig;
 char __opaque[56];
};

struct _opaque_pthread_cond_t {
 long __sig;
 char __opaque[40];
};

struct _opaque_pthread_condattr_t {
 long __sig;
 char __opaque[8];
};

struct _opaque_pthread_mutex_t {
 long __sig;
 char __opaque[56];
};

struct _opaque_pthread_mutexattr_t {
 long __sig;
 char __opaque[8];
};

struct _opaque_pthread_once_t {
 long __sig;
 char __opaque[8];
};

struct _opaque_pthread_rwlock_t {
 long __sig;
 char __opaque[192];
};

struct _opaque_pthread_rwlockattr_t {
 long __sig;
 char __opaque[16];
};

struct _opaque_pthread_t {
 long __sig;
 struct __darwin_pthread_handler_rec *__cleanup_stack;
 char __opaque[8176];
};

typedef struct _opaque_pthread_attr_t __darwin_pthread_attr_t;
typedef struct _opaque_pthread_cond_t __darwin_pthread_cond_t;
typedef struct _opaque_pthread_condattr_t __darwin_pthread_condattr_t;
typedef unsigned long __darwin_pthread_key_t;
typedef struct _opaque_pthread_mutex_t __darwin_pthread_mutex_t;
typedef struct _opaque_pthread_mutexattr_t __darwin_pthread_mutexattr_t;
typedef struct _opaque_pthread_once_t __darwin_pthread_once_t;
typedef struct _opaque_pthread_rwlock_t __darwin_pthread_rwlock_t;
typedef struct _opaque_pthread_rwlockattr_t __darwin_pthread_rwlockattr_t;
typedef struct _opaque_pthread_t *__darwin_pthread_t;
# 81 "/usr/include/sys/_types.h" 2 3 4
# 53 "/usr/include/stdint.h" 2 3 4
# 1 "/usr/include/sys/_types/_intptr_t.h" 1 3 4
# 30 "/usr/include/sys/_types/_intptr_t.h" 3 4
# 1 "/usr/include/machine/types.h" 1 3 4
# 35 "/usr/include/machine/types.h" 3 4
# 1 "/usr/include/i386/types.h" 1 3 4
# 81 "/usr/include/i386/types.h" 3 4
# 1 "/usr/include/sys/_types/_u_int8_t.h" 1 3 4
# 30 "/usr/include/sys/_types/_u_int8_t.h" 3 4
typedef unsigned char u_int8_t;
# 82 "/usr/include/i386/types.h" 2 3 4
# 1 "/usr/include/sys/_types/_u_int16_t.h" 1 3 4
# 30 "/usr/include/sys/_types/_u_int16_t.h" 3 4
typedef unsigned short u_int16_t;
# 83 "/usr/include/i386/types.h" 2 3 4
# 1 "/usr/include/sys/_types/_u_int32_t.h" 1 3 4
# 30 "/usr/include/sys/_types/_u_int32_t.h" 3 4
typedef unsigned int u_int32_t;
# 84 "/usr/include/i386/types.h" 2 3 4
# 1 "/usr/include/sys/_types/_u_int64_t.h" 1 3 4
# 30 "/usr/include/sys/_types/_u_int64_t.h" 3 4
typedef unsigned long long u_int64_t;
# 85 "/usr/include/i386/types.h" 2 3 4


typedef int64_t register_t;





# 1 "/usr/include/sys/_types/_intptr_t.h" 1 3 4
# 93 "/usr/include/i386/types.h" 2 3 4
# 1 "/usr/include/sys/_types/_uintptr_t.h" 1 3 4
# 30 "/usr/include/sys/_types/_uintptr_t.h" 3 4
typedef unsigned long uintptr_t;
# 94 "/usr/include/i386/types.h" 2 3 4



typedef u_int64_t user_addr_t;
typedef u_int64_t user_size_t;
typedef int64_t user_ssize_t;
typedef int64_t user_long_t;
typedef u_int64_t user_ulong_t;
typedef int64_t user_time_t;
typedef int64_t user_off_t;







typedef u_int64_t syscall_arg_t;
# 36 "/usr/include/machine/types.h" 2 3 4
# 31 "/usr/include/sys/_types/_intptr_t.h" 2 3 4

typedef __darwin_intptr_t intptr_t;
# 54 "/usr/include/stdint.h" 2 3 4




# 1 "/usr/include/_types/_intmax_t.h" 1 3 4
# 32 "/usr/include/_types/_intmax_t.h" 3 4
typedef long int intmax_t;
# 59 "/usr/include/stdint.h" 2 3 4
# 1 "/usr/include/_types/_uintmax_t.h" 1 3 4
# 32 "/usr/include/_types/_uintmax_t.h" 3 4
typedef long unsigned int uintmax_t;
# 60 "/usr/include/stdint.h" 2 3 4
# 64 "/Applications/Xcode_9.3.0_fb.app/Contents/Developer/Toolchains/XcodeDefault.xctoolchain/usr/lib/clang/9.1.0/include/stdint.h" 2 3 4
# 26 "../../api/z3.h" 2
# 1 "../../api/z3_macros.h" 1
# 27 "../../api/z3.h" 2
# 1 "../../api/z3_api.h" 1







typedef struct _Z3_symbol *Z3_symbol;
typedef struct _Z3_literals *Z3_literals;
typedef struct _Z3_config *Z3_config;
typedef struct _Z3_context *Z3_context;
typedef struct _Z3_sort *Z3_sort;

typedef struct _Z3_func_decl *Z3_func_decl;
typedef struct _Z3_ast *Z3_ast;

typedef struct _Z3_app *Z3_app;
typedef struct _Z3_pattern *Z3_pattern;
typedef struct _Z3_model *Z3_model;
typedef struct _Z3_constructor *Z3_constructor;
typedef struct _Z3_constructor_list *Z3_constructor_list;
typedef struct _Z3_params *Z3_params;
typedef struct _Z3_param_descrs *Z3_param_descrs;
typedef struct _Z3_goal *Z3_goal;
typedef struct _Z3_tactic *Z3_tactic;
typedef struct _Z3_probe *Z3_probe;
typedef struct _Z3_stats *Z3_stats;
typedef struct _Z3_solver *Z3_solver;
typedef struct _Z3_ast_vector *Z3_ast_vector;
typedef struct _Z3_ast_map *Z3_ast_map;
typedef struct _Z3_apply_result *Z3_apply_result;
typedef struct _Z3_func_interp *Z3_func_interp;

typedef struct _Z3_func_entry *Z3_func_entry;
typedef struct _Z3_fixedpoint *Z3_fixedpoint;
typedef struct _Z3_optimize *Z3_optimize;
typedef struct _Z3_rcf_num *Z3_rcf_num;
# 77 "../../api/z3_api.h"
typedef _Bool Z3_bool;




typedef const char * Z3_string;
typedef Z3_string * Z3_string_ptr;
# 98 "../../api/z3_api.h"
typedef enum
{
    Z3_L_FALSE = -1,
    Z3_L_UNDEF,
    Z3_L_TRUE
} Z3_lbool;
# 112 "../../api/z3_api.h"
typedef enum
{
    Z3_INT_SYMBOL,
    Z3_STRING_SYMBOL
} Z3_symbol_kind;
# 132 "../../api/z3_api.h"
typedef enum
{
    Z3_PARAMETER_INT,
    Z3_PARAMETER_DOUBLE,
    Z3_PARAMETER_RATIONAL,
    Z3_PARAMETER_SYMBOL,
    Z3_PARAMETER_SORT,
    Z3_PARAMETER_AST,
    Z3_PARAMETER_FUNC_DECL
} Z3_parameter_kind;




typedef enum
{
    Z3_UNINTERPRETED_SORT,
    Z3_BOOL_SORT,
    Z3_INT_SORT,
    Z3_REAL_SORT,
    Z3_BV_SORT,
    Z3_ARRAY_SORT,
    Z3_DATATYPE_SORT,
    Z3_RELATION_SORT,
    Z3_FINITE_DOMAIN_SORT,
    Z3_FLOATING_POINT_SORT,
    Z3_ROUNDING_MODE_SORT,
    Z3_SEQ_SORT,
    Z3_RE_SORT,
    Z3_UNKNOWN_SORT = 1000
} Z3_sort_kind;
# 176 "../../api/z3_api.h"
typedef enum
{
    Z3_NUMERAL_AST,
    Z3_APP_AST,
    Z3_VAR_AST,
    Z3_QUANTIFIER_AST,
    Z3_SORT_AST,
    Z3_FUNC_DECL_AST,
    Z3_UNKNOWN_AST = 1000
} Z3_ast_kind;
# 978 "../../api/z3_api.h"
typedef enum {

    Z3_OP_TRUE = 0x100,
    Z3_OP_FALSE,
    Z3_OP_EQ,
    Z3_OP_DISTINCT,
    Z3_OP_ITE,
    Z3_OP_AND,
    Z3_OP_OR,
    Z3_OP_IFF,
    Z3_OP_XOR,
    Z3_OP_NOT,
    Z3_OP_IMPLIES,
    Z3_OP_OEQ,


    Z3_OP_ANUM = 0x200,
    Z3_OP_AGNUM,
    Z3_OP_LE,
    Z3_OP_GE,
    Z3_OP_LT,
    Z3_OP_GT,
    Z3_OP_ADD,
    Z3_OP_SUB,
    Z3_OP_UMINUS,
    Z3_OP_MUL,
    Z3_OP_DIV,
    Z3_OP_IDIV,
    Z3_OP_REM,
    Z3_OP_MOD,
    Z3_OP_TO_REAL,
    Z3_OP_TO_INT,
    Z3_OP_IS_INT,
    Z3_OP_POWER,


    Z3_OP_STORE = 0x300,
    Z3_OP_SELECT,
    Z3_OP_CONST_ARRAY,
    Z3_OP_ARRAY_MAP,
    Z3_OP_ARRAY_DEFAULT,
    Z3_OP_SET_UNION,
    Z3_OP_SET_INTERSECT,
    Z3_OP_SET_DIFFERENCE,
    Z3_OP_SET_COMPLEMENT,
    Z3_OP_SET_SUBSET,
    Z3_OP_AS_ARRAY,
    Z3_OP_ARRAY_EXT,


    Z3_OP_BNUM = 0x400,
    Z3_OP_BIT1,
    Z3_OP_BIT0,
    Z3_OP_BNEG,
    Z3_OP_BADD,
    Z3_OP_BSUB,
    Z3_OP_BMUL,

    Z3_OP_BSDIV,
    Z3_OP_BUDIV,
    Z3_OP_BSREM,
    Z3_OP_BUREM,
    Z3_OP_BSMOD,



    Z3_OP_BSDIV0,
    Z3_OP_BUDIV0,
    Z3_OP_BSREM0,
    Z3_OP_BUREM0,
    Z3_OP_BSMOD0,

    Z3_OP_ULEQ,
    Z3_OP_SLEQ,
    Z3_OP_UGEQ,
    Z3_OP_SGEQ,
    Z3_OP_ULT,
    Z3_OP_SLT,
    Z3_OP_UGT,
    Z3_OP_SGT,

    Z3_OP_BAND,
    Z3_OP_BOR,
    Z3_OP_BNOT,
    Z3_OP_BXOR,
    Z3_OP_BNAND,
    Z3_OP_BNOR,
    Z3_OP_BXNOR,

    Z3_OP_CONCAT,
    Z3_OP_SIGN_EXT,
    Z3_OP_ZERO_EXT,
    Z3_OP_EXTRACT,
    Z3_OP_REPEAT,

    Z3_OP_BREDOR,
    Z3_OP_BREDAND,
    Z3_OP_BCOMP,

    Z3_OP_BSHL,
    Z3_OP_BLSHR,
    Z3_OP_BASHR,
    Z3_OP_ROTATE_LEFT,
    Z3_OP_ROTATE_RIGHT,
    Z3_OP_EXT_ROTATE_LEFT,
    Z3_OP_EXT_ROTATE_RIGHT,

    Z3_OP_BIT2BOOL,
    Z3_OP_INT2BV,
    Z3_OP_BV2INT,
    Z3_OP_CARRY,
    Z3_OP_XOR3,

    Z3_OP_BSMUL_NO_OVFL,
    Z3_OP_BUMUL_NO_OVFL,
    Z3_OP_BSMUL_NO_UDFL,
    Z3_OP_BSDIV_I,
    Z3_OP_BUDIV_I,
    Z3_OP_BSREM_I,
    Z3_OP_BUREM_I,
    Z3_OP_BSMOD_I,


    Z3_OP_PR_UNDEF = 0x500,
    Z3_OP_PR_TRUE,
    Z3_OP_PR_ASSERTED,
    Z3_OP_PR_GOAL,
    Z3_OP_PR_MODUS_PONENS,
    Z3_OP_PR_REFLEXIVITY,
    Z3_OP_PR_SYMMETRY,
    Z3_OP_PR_TRANSITIVITY,
    Z3_OP_PR_TRANSITIVITY_STAR,
    Z3_OP_PR_MONOTONICITY,
    Z3_OP_PR_QUANT_INTRO,
    Z3_OP_PR_DISTRIBUTIVITY,
    Z3_OP_PR_AND_ELIM,
    Z3_OP_PR_NOT_OR_ELIM,
    Z3_OP_PR_REWRITE,
    Z3_OP_PR_REWRITE_STAR,
    Z3_OP_PR_PULL_QUANT,
    Z3_OP_PR_PUSH_QUANT,
    Z3_OP_PR_ELIM_UNUSED_VARS,
    Z3_OP_PR_DER,
    Z3_OP_PR_QUANT_INST,
    Z3_OP_PR_HYPOTHESIS,
    Z3_OP_PR_LEMMA,
    Z3_OP_PR_UNIT_RESOLUTION,
    Z3_OP_PR_IFF_TRUE,
    Z3_OP_PR_IFF_FALSE,
    Z3_OP_PR_COMMUTATIVITY,
    Z3_OP_PR_DEF_AXIOM,
    Z3_OP_PR_DEF_INTRO,
    Z3_OP_PR_APPLY_DEF,
    Z3_OP_PR_IFF_OEQ,
    Z3_OP_PR_NNF_POS,
    Z3_OP_PR_NNF_NEG,
    Z3_OP_PR_SKOLEMIZE,
    Z3_OP_PR_MODUS_PONENS_OEQ,
    Z3_OP_PR_TH_LEMMA,
    Z3_OP_PR_HYPER_RESOLVE,


    Z3_OP_RA_STORE = 0x600,
    Z3_OP_RA_EMPTY,
    Z3_OP_RA_IS_EMPTY,
    Z3_OP_RA_JOIN,
    Z3_OP_RA_UNION,
    Z3_OP_RA_WIDEN,
    Z3_OP_RA_PROJECT,
    Z3_OP_RA_FILTER,
    Z3_OP_RA_NEGATION_FILTER,
    Z3_OP_RA_RENAME,
    Z3_OP_RA_COMPLEMENT,
    Z3_OP_RA_SELECT,
    Z3_OP_RA_CLONE,
    Z3_OP_FD_CONSTANT,
    Z3_OP_FD_LT,


    Z3_OP_SEQ_UNIT,
    Z3_OP_SEQ_EMPTY,
    Z3_OP_SEQ_CONCAT,
    Z3_OP_SEQ_PREFIX,
    Z3_OP_SEQ_SUFFIX,
    Z3_OP_SEQ_CONTAINS,
    Z3_OP_SEQ_EXTRACT,
    Z3_OP_SEQ_REPLACE,
    Z3_OP_SEQ_AT,
    Z3_OP_SEQ_LENGTH,
    Z3_OP_SEQ_INDEX,
    Z3_OP_SEQ_TO_RE,
    Z3_OP_SEQ_IN_RE,


    Z3_OP_STR_TO_INT,
    Z3_OP_INT_TO_STR,


    Z3_OP_RE_PLUS,
    Z3_OP_RE_STAR,
    Z3_OP_RE_OPTION,
    Z3_OP_RE_CONCAT,
    Z3_OP_RE_UNION,
    Z3_OP_RE_RANGE,
    Z3_OP_RE_LOOP,
    Z3_OP_RE_INTERSECT,
    Z3_OP_RE_EMPTY_SET,
    Z3_OP_RE_FULL_SET,
    Z3_OP_RE_COMPLEMENT,


    Z3_OP_LABEL = 0x700,
    Z3_OP_LABEL_LIT,


    Z3_OP_DT_CONSTRUCTOR=0x800,
    Z3_OP_DT_RECOGNISER,
    Z3_OP_DT_IS,
    Z3_OP_DT_ACCESSOR,
    Z3_OP_DT_UPDATE_FIELD,


    Z3_OP_PB_AT_MOST=0x900,
    Z3_OP_PB_AT_LEAST,
    Z3_OP_PB_LE,
    Z3_OP_PB_GE,
    Z3_OP_PB_EQ,


    Z3_OP_FPA_RM_NEAREST_TIES_TO_EVEN,
    Z3_OP_FPA_RM_NEAREST_TIES_TO_AWAY,
    Z3_OP_FPA_RM_TOWARD_POSITIVE,
    Z3_OP_FPA_RM_TOWARD_NEGATIVE,
    Z3_OP_FPA_RM_TOWARD_ZERO,

    Z3_OP_FPA_NUM,
    Z3_OP_FPA_PLUS_INF,
    Z3_OP_FPA_MINUS_INF,
    Z3_OP_FPA_NAN,
    Z3_OP_FPA_PLUS_ZERO,
    Z3_OP_FPA_MINUS_ZERO,

    Z3_OP_FPA_ADD,
    Z3_OP_FPA_SUB,
    Z3_OP_FPA_NEG,
    Z3_OP_FPA_MUL,
    Z3_OP_FPA_DIV,
    Z3_OP_FPA_REM,
    Z3_OP_FPA_ABS,
    Z3_OP_FPA_MIN,
    Z3_OP_FPA_MAX,
    Z3_OP_FPA_FMA,
    Z3_OP_FPA_SQRT,
    Z3_OP_FPA_ROUND_TO_INTEGRAL,

    Z3_OP_FPA_EQ,
    Z3_OP_FPA_LT,
    Z3_OP_FPA_GT,
    Z3_OP_FPA_LE,
    Z3_OP_FPA_GE,
    Z3_OP_FPA_IS_NAN,
    Z3_OP_FPA_IS_INF,
    Z3_OP_FPA_IS_ZERO,
    Z3_OP_FPA_IS_NORMAL,
    Z3_OP_FPA_IS_SUBNORMAL,
    Z3_OP_FPA_IS_NEGATIVE,
    Z3_OP_FPA_IS_POSITIVE,

    Z3_OP_FPA_FP,
    Z3_OP_FPA_TO_FP,
    Z3_OP_FPA_TO_FP_UNSIGNED,
    Z3_OP_FPA_TO_UBV,
    Z3_OP_FPA_TO_SBV,
    Z3_OP_FPA_TO_REAL,

    Z3_OP_FPA_TO_IEEE_BV,

    Z3_OP_FPA_BVWRAP,
    Z3_OP_FPA_BV2RM,

    Z3_OP_INTERNAL,

    Z3_OP_UNINTERPRETED
} Z3_decl_kind;
# 1275 "../../api/z3_api.h"
typedef enum {
    Z3_PK_UINT,
    Z3_PK_BOOL,
    Z3_PK_DOUBLE,
    Z3_PK_SYMBOL,
    Z3_PK_STRING,
    Z3_PK_OTHER,
    Z3_PK_INVALID
} Z3_param_kind;
# 1292 "../../api/z3_api.h"
typedef enum {
    Z3_PRINT_SMTLIB_FULL,
    Z3_PRINT_LOW_LEVEL,
    Z3_PRINT_SMTLIB2_COMPLIANT
} Z3_ast_print_mode;
# 1316 "../../api/z3_api.h"
typedef enum
{
    Z3_OK,
    Z3_SORT_ERROR,
    Z3_IOB,
    Z3_INVALID_ARG,
    Z3_PARSER_ERROR,
    Z3_NO_PARSER,
    Z3_INVALID_PATTERN,
    Z3_MEMOUT_FAIL,
    Z3_FILE_ACCESS_ERROR,
    Z3_INTERNAL_FATAL,
    Z3_INVALID_USAGE,
    Z3_DEC_REF_ERROR,
    Z3_EXCEPTION
} Z3_error_code;
# 1367 "../../api/z3_api.h"
typedef void Z3_error_handler(Z3_context c, Z3_error_code e);
# 1379 "../../api/z3_api.h"
typedef enum
{
    Z3_GOAL_PRECISE,
    Z3_GOAL_UNDER,
    Z3_GOAL_OVER,
    Z3_GOAL_UNDER_OVER
} Z3_goal_prec;
# 1417 "../../api/z3_api.h"
    void __attribute__ ((visibility ("default"))) Z3_global_param_set(Z3_string param_id, Z3_string param_value);
# 1428 "../../api/z3_api.h"
    void __attribute__ ((visibility ("default"))) Z3_global_param_reset_all(void);
# 1442 "../../api/z3_api.h"
    Z3_bool __attribute__ ((visibility ("default"))) Z3_global_param_get(Z3_string param_id, Z3_string_ptr param_value);
# 1479 "../../api/z3_api.h"
    Z3_config __attribute__ ((visibility ("default"))) Z3_mk_config(void);
# 1488 "../../api/z3_api.h"
    void __attribute__ ((visibility ("default"))) Z3_del_config(Z3_config c);
# 1499 "../../api/z3_api.h"
    void __attribute__ ((visibility ("default"))) Z3_set_param_value(Z3_config c, Z3_string param_id, Z3_string param_value);
# 1532 "../../api/z3_api.h"
    Z3_context __attribute__ ((visibility ("default"))) Z3_mk_context(Z3_config c);
# 1556 "../../api/z3_api.h"
    Z3_context __attribute__ ((visibility ("default"))) Z3_mk_context_rc(Z3_config c);
# 1565 "../../api/z3_api.h"
    void __attribute__ ((visibility ("default"))) Z3_del_context(Z3_context c);
# 1574 "../../api/z3_api.h"
    void __attribute__ ((visibility ("default"))) Z3_inc_ref(Z3_context c, Z3_ast a);
# 1583 "../../api/z3_api.h"
    void __attribute__ ((visibility ("default"))) Z3_dec_ref(Z3_context c, Z3_ast a);
# 1592 "../../api/z3_api.h"
    void __attribute__ ((visibility ("default"))) Z3_update_param_value(Z3_context c, Z3_string param_id, Z3_string param_value);







    void __attribute__ ((visibility ("default"))) Z3_interrupt(Z3_context c);
# 1618 "../../api/z3_api.h"
    Z3_params __attribute__ ((visibility ("default"))) Z3_mk_params(Z3_context c);






    void __attribute__ ((visibility ("default"))) Z3_params_inc_ref(Z3_context c, Z3_params p);






    void __attribute__ ((visibility ("default"))) Z3_params_dec_ref(Z3_context c, Z3_params p);






    void __attribute__ ((visibility ("default"))) Z3_params_set_bool(Z3_context c, Z3_params p, Z3_symbol k, Z3_bool v);






    void __attribute__ ((visibility ("default"))) Z3_params_set_uint(Z3_context c, Z3_params p, Z3_symbol k, unsigned v);






    void __attribute__ ((visibility ("default"))) Z3_params_set_double(Z3_context c, Z3_params p, Z3_symbol k, double v);






    void __attribute__ ((visibility ("default"))) Z3_params_set_symbol(Z3_context c, Z3_params p, Z3_symbol k, Z3_symbol v);







    Z3_string __attribute__ ((visibility ("default"))) Z3_params_to_string(Z3_context c, Z3_params p);
# 1677 "../../api/z3_api.h"
    void __attribute__ ((visibility ("default"))) Z3_params_validate(Z3_context c, Z3_params p, Z3_param_descrs d);
# 1689 "../../api/z3_api.h"
    void __attribute__ ((visibility ("default"))) Z3_param_descrs_inc_ref(Z3_context c, Z3_param_descrs p);






    void __attribute__ ((visibility ("default"))) Z3_param_descrs_dec_ref(Z3_context c, Z3_param_descrs p);






    Z3_param_kind __attribute__ ((visibility ("default"))) Z3_param_descrs_get_kind(Z3_context c, Z3_param_descrs p, Z3_symbol n);






    unsigned __attribute__ ((visibility ("default"))) Z3_param_descrs_size(Z3_context c, Z3_param_descrs p);
# 1719 "../../api/z3_api.h"
    Z3_symbol __attribute__ ((visibility ("default"))) Z3_param_descrs_get_name(Z3_context c, Z3_param_descrs p, unsigned i);






    Z3_string __attribute__ ((visibility ("default"))) Z3_param_descrs_get_documentation(Z3_context c, Z3_param_descrs p, Z3_symbol s);







    Z3_string __attribute__ ((visibility ("default"))) Z3_param_descrs_to_string(Z3_context c, Z3_param_descrs p);
# 1753 "../../api/z3_api.h"
    Z3_symbol __attribute__ ((visibility ("default"))) Z3_mk_int_symbol(Z3_context c, int i);
# 1764 "../../api/z3_api.h"
    Z3_symbol __attribute__ ((visibility ("default"))) Z3_mk_string_symbol(Z3_context c, Z3_string s);
# 1778 "../../api/z3_api.h"
    Z3_sort __attribute__ ((visibility ("default"))) Z3_mk_uninterpreted_sort(Z3_context c, Z3_symbol s);
# 1787 "../../api/z3_api.h"
    Z3_sort __attribute__ ((visibility ("default"))) Z3_mk_bool_sort(Z3_context c);
# 1800 "../../api/z3_api.h"
    Z3_sort __attribute__ ((visibility ("default"))) Z3_mk_int_sort(Z3_context c);
# 1809 "../../api/z3_api.h"
    Z3_sort __attribute__ ((visibility ("default"))) Z3_mk_real_sort(Z3_context c);
# 1820 "../../api/z3_api.h"
    Z3_sort __attribute__ ((visibility ("default"))) Z3_mk_bv_sort(Z3_context c, unsigned sz);
# 1835 "../../api/z3_api.h"
    Z3_sort __attribute__ ((visibility ("default"))) Z3_mk_finite_domain_sort(Z3_context c, Z3_symbol name, uint64_t size);
# 1848 "../../api/z3_api.h"
    Z3_sort __attribute__ ((visibility ("default"))) Z3_mk_array_sort(Z3_context c, Z3_sort domain, Z3_sort range);
# 1858 "../../api/z3_api.h"
    Z3_sort __attribute__ ((visibility ("default"))) Z3_mk_array_sort_n(Z3_context c, unsigned n, Z3_sort const * domain, Z3_sort range);
# 1877 "../../api/z3_api.h"
    Z3_sort __attribute__ ((visibility ("default"))) Z3_mk_tuple_sort(Z3_context c,
                                        Z3_symbol mk_tuple_name,
                                        unsigned num_fields,
                                        Z3_symbol const field_names[],
                                        Z3_sort const field_sorts[],
                                        Z3_func_decl * mk_tuple_decl,
                                        Z3_func_decl proj_decl[]);
# 1906 "../../api/z3_api.h"
    Z3_sort __attribute__ ((visibility ("default"))) Z3_mk_enumeration_sort(Z3_context c,
                                          Z3_symbol name,
                                          unsigned n,
                                          Z3_symbol const enum_names[],
                                          Z3_func_decl enum_consts[],
                                          Z3_func_decl enum_testers[]);
# 1931 "../../api/z3_api.h"
    Z3_sort __attribute__ ((visibility ("default"))) Z3_mk_list_sort(Z3_context c,
                                   Z3_symbol name,
                                   Z3_sort elem_sort,
                                   Z3_func_decl* nil_decl,
                                   Z3_func_decl* is_nil_decl,
                                   Z3_func_decl* cons_decl,
                                   Z3_func_decl* is_cons_decl,
                                   Z3_func_decl* head_decl,
                                   Z3_func_decl* tail_decl
                                   );
# 1957 "../../api/z3_api.h"
    Z3_constructor __attribute__ ((visibility ("default"))) Z3_mk_constructor(Z3_context c,
                                            Z3_symbol name,
                                            Z3_symbol recognizer,
                                            unsigned num_fields,
                                            Z3_symbol const field_names[],
                                            Z3_sort const sorts[],
                                            unsigned sort_refs[]
                                            );
# 1974 "../../api/z3_api.h"
    void __attribute__ ((visibility ("default"))) Z3_del_constructor(Z3_context c, Z3_constructor constr);
# 1987 "../../api/z3_api.h"
    Z3_sort __attribute__ ((visibility ("default"))) Z3_mk_datatype(Z3_context c,
                                  Z3_symbol name,
                                  unsigned num_constructors,
                                  Z3_constructor constructors[]);
# 2001 "../../api/z3_api.h"
    Z3_constructor_list __attribute__ ((visibility ("default"))) Z3_mk_constructor_list(Z3_context c,
                                                      unsigned num_constructors,
                                                      Z3_constructor const constructors[]);
# 2015 "../../api/z3_api.h"
    void __attribute__ ((visibility ("default"))) Z3_del_constructor_list(Z3_context c, Z3_constructor_list clist);
# 2028 "../../api/z3_api.h"
    void __attribute__ ((visibility ("default"))) Z3_mk_datatypes(Z3_context c,
                                unsigned num_sorts,
                                Z3_symbol const sort_names[],
                                Z3_sort sorts[],
                                Z3_constructor_list constructor_lists[]);
# 2046 "../../api/z3_api.h"
    void __attribute__ ((visibility ("default"))) Z3_query_constructor(Z3_context c,
                                     Z3_constructor constr,
                                     unsigned num_fields,
                                     Z3_func_decl* constructor,
                                     Z3_func_decl* tester,
                                     Z3_func_decl accessors[]);
# 2075 "../../api/z3_api.h"
    Z3_func_decl __attribute__ ((visibility ("default"))) Z3_mk_func_decl(Z3_context c, Z3_symbol s,
                                        unsigned domain_size, Z3_sort const domain[],
                                        Z3_sort range);
# 2087 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_app(
        Z3_context c,
        Z3_func_decl d,
        unsigned num_args,
        Z3_ast const args[]);
# 2107 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_const(Z3_context c, Z3_symbol s, Z3_sort ty);
# 2121 "../../api/z3_api.h"
    Z3_func_decl __attribute__ ((visibility ("default"))) Z3_mk_fresh_func_decl(Z3_context c, Z3_string prefix,
                                                   unsigned domain_size, Z3_sort const domain[],
                                                   Z3_sort range);
# 2138 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fresh_const(Z3_context c, Z3_string prefix, Z3_sort ty);
# 2148 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_true(Z3_context c);






    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_false(Z3_context c);
# 2164 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_eq(Z3_context c, Z3_ast l, Z3_ast r);
# 2178 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_distinct(Z3_context c, unsigned num_args, Z3_ast const args[]);
# 2187 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_not(Z3_context c, Z3_ast a);
# 2197 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_ite(Z3_context c, Z3_ast t1, Z3_ast t2, Z3_ast t3);
# 2206 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_iff(Z3_context c, Z3_ast t1, Z3_ast t2);
# 2215 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_implies(Z3_context c, Z3_ast t1, Z3_ast t2);
# 2224 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_xor(Z3_context c, Z3_ast t1, Z3_ast t2);
# 2236 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_and(Z3_context c, unsigned num_args, Z3_ast const args[]);
# 2248 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_or(Z3_context c, unsigned num_args, Z3_ast const args[]);
# 2263 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_add(Z3_context c, unsigned num_args, Z3_ast const args[]);
# 2276 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_mul(Z3_context c, unsigned num_args, Z3_ast const args[]);
# 2288 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_sub(Z3_context c, unsigned num_args, Z3_ast const args[]);
# 2297 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_unary_minus(Z3_context c, Z3_ast arg);
# 2308 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_div(Z3_context c, Z3_ast arg1, Z3_ast arg2);
# 2317 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_mod(Z3_context c, Z3_ast arg1, Z3_ast arg2);
# 2326 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_rem(Z3_context c, Z3_ast arg1, Z3_ast arg2);
# 2335 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_power(Z3_context c, Z3_ast arg1, Z3_ast arg2);
# 2344 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_lt(Z3_context c, Z3_ast t1, Z3_ast t2);
# 2353 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_le(Z3_context c, Z3_ast t1, Z3_ast t2);
# 2362 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_gt(Z3_context c, Z3_ast t1, Z3_ast t2);
# 2371 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_ge(Z3_context c, Z3_ast t1, Z3_ast t2);
# 2390 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_int2real(Z3_context c, Z3_ast t1);
# 2403 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_real2int(Z3_context c, Z3_ast t1);
# 2413 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_is_int(Z3_context c, Z3_ast t1);
# 2425 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_bvnot(Z3_context c, Z3_ast t1);
# 2434 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_bvredand(Z3_context c, Z3_ast t1);
# 2443 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_bvredor(Z3_context c, Z3_ast t1);
# 2452 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_bvand(Z3_context c, Z3_ast t1, Z3_ast t2);
# 2461 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_bvor(Z3_context c, Z3_ast t1, Z3_ast t2);
# 2470 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_bvxor(Z3_context c, Z3_ast t1, Z3_ast t2);
# 2479 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_bvnand(Z3_context c, Z3_ast t1, Z3_ast t2);
# 2488 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_bvnor(Z3_context c, Z3_ast t1, Z3_ast t2);
# 2497 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_bvxnor(Z3_context c, Z3_ast t1, Z3_ast t2);
# 2506 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_bvneg(Z3_context c, Z3_ast t1);
# 2515 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_bvadd(Z3_context c, Z3_ast t1, Z3_ast t2);
# 2524 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_bvsub(Z3_context c, Z3_ast t1, Z3_ast t2);
# 2533 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_bvmul(Z3_context c, Z3_ast t1, Z3_ast t2);
# 2546 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_bvudiv(Z3_context c, Z3_ast t1, Z3_ast t2);
# 2563 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_bvsdiv(Z3_context c, Z3_ast t1, Z3_ast t2);
# 2576 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_bvurem(Z3_context c, Z3_ast t1, Z3_ast t2);
# 2592 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_bvsrem(Z3_context c, Z3_ast t1, Z3_ast t2);
# 2605 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_bvsmod(Z3_context c, Z3_ast t1, Z3_ast t2);
# 2614 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_bvult(Z3_context c, Z3_ast t1, Z3_ast t2);
# 2631 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_bvslt(Z3_context c, Z3_ast t1, Z3_ast t2);
# 2640 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_bvule(Z3_context c, Z3_ast t1, Z3_ast t2);
# 2649 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_bvsle(Z3_context c, Z3_ast t1, Z3_ast t2);
# 2658 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_bvuge(Z3_context c, Z3_ast t1, Z3_ast t2);
# 2667 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_bvsge(Z3_context c, Z3_ast t1, Z3_ast t2);
# 2676 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_bvugt(Z3_context c, Z3_ast t1, Z3_ast t2);
# 2685 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_bvsgt(Z3_context c, Z3_ast t1, Z3_ast t2);
# 2697 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_concat(Z3_context c, Z3_ast t1, Z3_ast t2);
# 2707 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_extract(Z3_context c, unsigned high, unsigned low, Z3_ast t1);
# 2718 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_sign_ext(Z3_context c, unsigned i, Z3_ast t1);
# 2729 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_zero_ext(Z3_context c, unsigned i, Z3_ast t1);
# 2738 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_repeat(Z3_context c, unsigned i, Z3_ast t1);
# 2754 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_bvshl(Z3_context c, Z3_ast t1, Z3_ast t2);
# 2770 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_bvlshr(Z3_context c, Z3_ast t1, Z3_ast t2);
# 2787 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_bvashr(Z3_context c, Z3_ast t1, Z3_ast t2);
# 2796 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_rotate_left(Z3_context c, unsigned i, Z3_ast t1);
# 2805 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_rotate_right(Z3_context c, unsigned i, Z3_ast t1);
# 2814 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_ext_rotate_left(Z3_context c, Z3_ast t1, Z3_ast t2);
# 2823 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_ext_rotate_right(Z3_context c, Z3_ast t1, Z3_ast t2);
# 2835 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_int2bv(Z3_context c, unsigned n, Z3_ast t1);
# 2849 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_bv2int(Z3_context c,Z3_ast t1, Z3_bool is_signed);
# 2859 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_bvadd_no_overflow(Z3_context c, Z3_ast t1, Z3_ast t2, Z3_bool is_signed);
# 2869 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_bvadd_no_underflow(Z3_context c, Z3_ast t1, Z3_ast t2);
# 2879 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_bvsub_no_overflow(Z3_context c, Z3_ast t1, Z3_ast t2);
# 2889 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_bvsub_no_underflow(Z3_context c, Z3_ast t1, Z3_ast t2, Z3_bool is_signed);
# 2899 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_bvsdiv_no_overflow(Z3_context c, Z3_ast t1, Z3_ast t2);
# 2909 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_bvneg_no_overflow(Z3_context c, Z3_ast t1);
# 2919 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_bvmul_no_overflow(Z3_context c, Z3_ast t1, Z3_ast t2, Z3_bool is_signed);
# 2929 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_bvmul_no_underflow(Z3_context c, Z3_ast t1, Z3_ast t2);
# 2947 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_select(Z3_context c, Z3_ast a, Z3_ast i);
# 2956 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_select_n(Z3_context c, Z3_ast a, unsigned n, Z3_ast const* idxs);
# 2974 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_store(Z3_context c, Z3_ast a, Z3_ast i, Z3_ast v);







    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_store_n(Z3_context c, Z3_ast a, unsigned n, Z3_ast const* idxs, Z3_ast v);
# 2996 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_const_array(Z3_context c, Z3_sort domain, Z3_ast v);
# 3011 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_map(Z3_context c, Z3_func_decl f, unsigned n, Z3_ast const* args);
# 3023 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_array_default(Z3_context c, Z3_ast array);
# 3032 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_as_array(Z3_context c, Z3_func_decl f);
# 3042 "../../api/z3_api.h"
    Z3_sort __attribute__ ((visibility ("default"))) Z3_mk_set_sort(Z3_context c, Z3_sort ty);






    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_empty_set(Z3_context c, Z3_sort domain);






    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_full_set(Z3_context c, Z3_sort domain);
# 3065 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_set_add(Z3_context c, Z3_ast set, Z3_ast elem);
# 3074 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_set_del(Z3_context c, Z3_ast set, Z3_ast elem);






    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_set_union(Z3_context c, unsigned num_args, Z3_ast const args[]);






    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_set_intersect(Z3_context c, unsigned num_args, Z3_ast const args[]);






    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_set_difference(Z3_context c, Z3_ast arg1, Z3_ast arg2);






    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_set_complement(Z3_context c, Z3_ast arg);
# 3111 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_set_member(Z3_context c, Z3_ast elem, Z3_ast set);






    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_set_subset(Z3_context c, Z3_ast arg1, Z3_ast arg2);
# 3128 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_array_ext(Z3_context c, Z3_ast arg1, Z3_ast arg2);
# 3146 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_numeral(Z3_context c, Z3_string numeral, Z3_sort ty);
# 3163 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_real(Z3_context c, int num, int den);
# 3175 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_int(Z3_context c, int v, Z3_sort ty);
# 3187 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_unsigned_int(Z3_context c, unsigned v, Z3_sort ty);
# 3199 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_int64(Z3_context c, int64_t v, Z3_sort ty);
# 3211 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_unsigned_int64(Z3_context c, uint64_t v, Z3_sort ty);







    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_bv_numeral(Z3_context c, unsigned sz, Z3_bool const* bits);
# 3231 "../../api/z3_api.h"
    Z3_sort __attribute__ ((visibility ("default"))) Z3_mk_seq_sort(Z3_context c, Z3_sort s);






    Z3_bool __attribute__ ((visibility ("default"))) Z3_is_seq_sort(Z3_context c, Z3_sort s);






    Z3_sort __attribute__ ((visibility ("default"))) Z3_mk_re_sort(Z3_context c, Z3_sort seq);






    Z3_bool __attribute__ ((visibility ("default"))) Z3_is_re_sort(Z3_context c, Z3_sort s);
# 3262 "../../api/z3_api.h"
    Z3_sort __attribute__ ((visibility ("default"))) Z3_mk_string_sort(Z3_context c);






    Z3_bool __attribute__ ((visibility ("default"))) Z3_is_string_sort(Z3_context c, Z3_sort s);





    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_string(Z3_context c, Z3_string s);






    Z3_bool __attribute__ ((visibility ("default"))) Z3_is_string(Z3_context c, Z3_ast s);
# 3291 "../../api/z3_api.h"
    Z3_string __attribute__ ((visibility ("default"))) Z3_get_string(Z3_context c, Z3_ast s);
# 3300 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_seq_empty(Z3_context c, Z3_sort seq);






    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_seq_unit(Z3_context c, Z3_ast a);
# 3316 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_seq_concat(Z3_context c, unsigned n, Z3_ast const args[]);
# 3325 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_seq_prefix(Z3_context c, Z3_ast prefix, Z3_ast s);
# 3334 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_seq_suffix(Z3_context c, Z3_ast suffix, Z3_ast s);
# 3343 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_seq_contains(Z3_context c, Z3_ast container, Z3_ast containee);






    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_seq_extract(Z3_context c, Z3_ast s, Z3_ast offset, Z3_ast length);






    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_seq_replace(Z3_context c, Z3_ast s, Z3_ast src, Z3_ast dst);






    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_seq_at(Z3_context c, Z3_ast s, Z3_ast index);






    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_seq_length(Z3_context c, Z3_ast s);
# 3381 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_seq_index(Z3_context c, Z3_ast s, Z3_ast substr, Z3_ast offset);






    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_str_to_int(Z3_context c, Z3_ast s);







    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_int_to_str(Z3_context c, Z3_ast s);






    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_seq_to_re(Z3_context c, Z3_ast seq);






    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_seq_in_re(Z3_context c, Z3_ast seq, Z3_ast re);






    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_re_plus(Z3_context c, Z3_ast re);






    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_re_star(Z3_context c, Z3_ast re);






    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_re_option(Z3_context c, Z3_ast re);
# 3440 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_re_union(Z3_context c, unsigned n, Z3_ast const args[]);
# 3449 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_re_concat(Z3_context c, unsigned n, Z3_ast const args[]);







    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_re_range(Z3_context c, Z3_ast lo, Z3_ast hi);
# 3467 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_re_loop(Z3_context c, Z3_ast r, unsigned lo, unsigned hi);
# 3476 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_re_intersect(Z3_context c, unsigned n, Z3_ast const args[]);






    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_re_complement(Z3_context c, Z3_ast re);
# 3492 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_re_empty(Z3_context c, Z3_sort re);
# 3502 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_re_full(Z3_context c, Z3_sort re);
# 3530 "../../api/z3_api.h"
    Z3_pattern __attribute__ ((visibility ("default"))) Z3_mk_pattern(Z3_context c, unsigned num_patterns, Z3_ast const terms[]);
# 3561 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_bound(Z3_context c, unsigned index, Z3_sort ty);
# 3586 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_forall(Z3_context c, unsigned weight,
                               unsigned num_patterns, Z3_pattern const patterns[],
                               unsigned num_decls, Z3_sort const sorts[],
                               Z3_symbol const decl_names[],
                               Z3_ast body);
# 3602 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_exists(Z3_context c, unsigned weight,
                               unsigned num_patterns, Z3_pattern const patterns[],
                               unsigned num_decls, Z3_sort const sorts[],
                               Z3_symbol const decl_names[],
                               Z3_ast body);
# 3629 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_quantifier(
        Z3_context c,
        Z3_bool is_forall,
        unsigned weight,
        unsigned num_patterns, Z3_pattern const patterns[],
        unsigned num_decls, Z3_sort const sorts[],
        Z3_symbol const decl_names[],
        Z3_ast body);
# 3663 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_quantifier_ex(
        Z3_context c,
        Z3_bool is_forall,
        unsigned weight,
        Z3_symbol quantifier_id,
        Z3_symbol skolem_id,
        unsigned num_patterns, Z3_pattern const patterns[],
        unsigned num_no_patterns, Z3_ast const no_patterns[],
        unsigned num_decls, Z3_sort const sorts[],
        Z3_symbol const decl_names[],
        Z3_ast body);
# 3693 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_forall_const(
        Z3_context c,
        unsigned weight,
        unsigned num_bound,
        Z3_app const bound[],
        unsigned num_patterns,
        Z3_pattern const patterns[],
        Z3_ast body
        );
# 3723 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_exists_const(
        Z3_context c,
        unsigned weight,
        unsigned num_bound,
        Z3_app const bound[],
        unsigned num_patterns,
        Z3_pattern const patterns[],
        Z3_ast body
        );







    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_quantifier_const(
        Z3_context c,
        Z3_bool is_forall,
        unsigned weight,
        unsigned num_bound, Z3_app const bound[],
        unsigned num_patterns, Z3_pattern const patterns[],
        Z3_ast body
        );







    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_quantifier_const_ex(
        Z3_context c,
        Z3_bool is_forall,
        unsigned weight,
        Z3_symbol quantifier_id,
        Z3_symbol skolem_id,
        unsigned num_bound, Z3_app const bound[],
        unsigned num_patterns, Z3_pattern const patterns[],
        unsigned num_no_patterns, Z3_ast const no_patterns[],
        Z3_ast body
        );
# 3777 "../../api/z3_api.h"
    Z3_symbol_kind __attribute__ ((visibility ("default"))) Z3_get_symbol_kind(Z3_context c, Z3_symbol s);
# 3788 "../../api/z3_api.h"
    int __attribute__ ((visibility ("default"))) Z3_get_symbol_int(Z3_context c, Z3_symbol s);
# 3803 "../../api/z3_api.h"
    Z3_string __attribute__ ((visibility ("default"))) Z3_get_symbol_string(Z3_context c, Z3_symbol s);






    Z3_symbol __attribute__ ((visibility ("default"))) Z3_get_sort_name(Z3_context c, Z3_sort d);






    unsigned __attribute__ ((visibility ("default"))) Z3_get_sort_id(Z3_context c, Z3_sort s);






    Z3_ast __attribute__ ((visibility ("default"))) Z3_sort_to_ast(Z3_context c, Z3_sort s);






    Z3_bool __attribute__ ((visibility ("default"))) Z3_is_eq_sort(Z3_context c, Z3_sort s1, Z3_sort s2);
# 3840 "../../api/z3_api.h"
    Z3_sort_kind __attribute__ ((visibility ("default"))) Z3_get_sort_kind(Z3_context c, Z3_sort t);
# 3852 "../../api/z3_api.h"
    unsigned __attribute__ ((visibility ("default"))) Z3_get_bv_sort_size(Z3_context c, Z3_sort t);







    Z3_bool __attribute__ ((visibility ("default"))) Z3_get_finite_domain_sort_size(Z3_context c, Z3_sort s, uint64_t* r);
# 3873 "../../api/z3_api.h"
    Z3_sort __attribute__ ((visibility ("default"))) Z3_get_array_sort_domain(Z3_context c, Z3_sort t);
# 3885 "../../api/z3_api.h"
    Z3_sort __attribute__ ((visibility ("default"))) Z3_get_array_sort_range(Z3_context c, Z3_sort t);
# 3898 "../../api/z3_api.h"
    Z3_func_decl __attribute__ ((visibility ("default"))) Z3_get_tuple_sort_mk_decl(Z3_context c, Z3_sort t);
# 3910 "../../api/z3_api.h"
    unsigned __attribute__ ((visibility ("default"))) Z3_get_tuple_sort_num_fields(Z3_context c, Z3_sort t);
# 3924 "../../api/z3_api.h"
    Z3_func_decl __attribute__ ((visibility ("default"))) Z3_get_tuple_sort_field_decl(Z3_context c, Z3_sort t, unsigned i);
# 3937 "../../api/z3_api.h"
    unsigned __attribute__ ((visibility ("default"))) Z3_get_datatype_sort_num_constructors(
        Z3_context c, Z3_sort t);
# 3952 "../../api/z3_api.h"
    Z3_func_decl __attribute__ ((visibility ("default"))) Z3_get_datatype_sort_constructor(
        Z3_context c, Z3_sort t, unsigned idx);
# 3967 "../../api/z3_api.h"
    Z3_func_decl __attribute__ ((visibility ("default"))) Z3_get_datatype_sort_recognizer(
        Z3_context c, Z3_sort t, unsigned idx);
# 3983 "../../api/z3_api.h"
    Z3_func_decl __attribute__ ((visibility ("default"))) Z3_get_datatype_sort_constructor_accessor(Z3_context c,
                                                                  Z3_sort t,
                                                                  unsigned idx_c,
                                                                  unsigned idx_a);
# 4007 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_datatype_update_field(Z3_context c, Z3_func_decl field_access,
                                           Z3_ast t, Z3_ast value);
# 4019 "../../api/z3_api.h"
    unsigned __attribute__ ((visibility ("default"))) Z3_get_relation_arity(Z3_context c, Z3_sort s);
# 4031 "../../api/z3_api.h"
    Z3_sort __attribute__ ((visibility ("default"))) Z3_get_relation_column(Z3_context c, Z3_sort s, unsigned col);
# 4040 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_atmost(Z3_context c, unsigned num_args,
                               Z3_ast const args[], unsigned k);
# 4050 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_atleast(Z3_context c, unsigned num_args,
                                Z3_ast const args[], unsigned k);
# 4060 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_pble(Z3_context c, unsigned num_args,
                             Z3_ast const args[], int const coeffs[],
                             int k);
# 4071 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_pbge(Z3_context c, unsigned num_args,
                             Z3_ast const args[], int const coeffs[],
                             int k);
# 4082 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_pbeq(Z3_context c, unsigned num_args,
                             Z3_ast const args[], int const coeffs[],
                             int k);






    Z3_ast __attribute__ ((visibility ("default"))) Z3_func_decl_to_ast(Z3_context c, Z3_func_decl f);






    Z3_bool __attribute__ ((visibility ("default"))) Z3_is_eq_func_decl(Z3_context c, Z3_func_decl f1, Z3_func_decl f2);






    unsigned __attribute__ ((visibility ("default"))) Z3_get_func_decl_id(Z3_context c, Z3_func_decl f);






    Z3_symbol __attribute__ ((visibility ("default"))) Z3_get_decl_name(Z3_context c, Z3_func_decl d);






    Z3_decl_kind __attribute__ ((visibility ("default"))) Z3_get_decl_kind(Z3_context c, Z3_func_decl d);
# 4128 "../../api/z3_api.h"
    unsigned __attribute__ ((visibility ("default"))) Z3_get_domain_size(Z3_context c, Z3_func_decl d);
# 4137 "../../api/z3_api.h"
    unsigned __attribute__ ((visibility ("default"))) Z3_get_arity(Z3_context c, Z3_func_decl d);
# 4148 "../../api/z3_api.h"
    Z3_sort __attribute__ ((visibility ("default"))) Z3_get_domain(Z3_context c, Z3_func_decl d, unsigned i);
# 4158 "../../api/z3_api.h"
    Z3_sort __attribute__ ((visibility ("default"))) Z3_get_range(Z3_context c, Z3_func_decl d);






    unsigned __attribute__ ((visibility ("default"))) Z3_get_decl_num_parameters(Z3_context c, Z3_func_decl d);
# 4176 "../../api/z3_api.h"
    Z3_parameter_kind __attribute__ ((visibility ("default"))) Z3_get_decl_parameter_kind(Z3_context c, Z3_func_decl d, unsigned idx);
# 4185 "../../api/z3_api.h"
    int __attribute__ ((visibility ("default"))) Z3_get_decl_int_parameter(Z3_context c, Z3_func_decl d, unsigned idx);
# 4194 "../../api/z3_api.h"
    double __attribute__ ((visibility ("default"))) Z3_get_decl_double_parameter(Z3_context c, Z3_func_decl d, unsigned idx);
# 4203 "../../api/z3_api.h"
    Z3_symbol __attribute__ ((visibility ("default"))) Z3_get_decl_symbol_parameter(Z3_context c, Z3_func_decl d, unsigned idx);
# 4212 "../../api/z3_api.h"
    Z3_sort __attribute__ ((visibility ("default"))) Z3_get_decl_sort_parameter(Z3_context c, Z3_func_decl d, unsigned idx);
# 4221 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_get_decl_ast_parameter(Z3_context c, Z3_func_decl d, unsigned idx);
# 4230 "../../api/z3_api.h"
    Z3_func_decl __attribute__ ((visibility ("default"))) Z3_get_decl_func_decl_parameter(Z3_context c, Z3_func_decl d, unsigned idx);
# 4239 "../../api/z3_api.h"
    Z3_string __attribute__ ((visibility ("default"))) Z3_get_decl_rational_parameter(Z3_context c, Z3_func_decl d, unsigned idx);






    Z3_ast __attribute__ ((visibility ("default"))) Z3_app_to_ast(Z3_context c, Z3_app a);






    Z3_func_decl __attribute__ ((visibility ("default"))) Z3_get_app_decl(Z3_context c, Z3_app a);







    unsigned __attribute__ ((visibility ("default"))) Z3_get_app_num_args(Z3_context c, Z3_app a);
# 4270 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_get_app_arg(Z3_context c, Z3_app a, unsigned i);






    Z3_bool __attribute__ ((visibility ("default"))) Z3_is_eq_ast(Z3_context c, Z3_ast t1, Z3_ast t2);
# 4290 "../../api/z3_api.h"
    unsigned __attribute__ ((visibility ("default"))) Z3_get_ast_id(Z3_context c, Z3_ast t);
# 4299 "../../api/z3_api.h"
    unsigned __attribute__ ((visibility ("default"))) Z3_get_ast_hash(Z3_context c, Z3_ast a);
# 4308 "../../api/z3_api.h"
    Z3_sort __attribute__ ((visibility ("default"))) Z3_get_sort(Z3_context c, Z3_ast a);






    Z3_bool __attribute__ ((visibility ("default"))) Z3_is_well_sorted(Z3_context c, Z3_ast t);






    Z3_lbool __attribute__ ((visibility ("default"))) Z3_get_bool_value(Z3_context c, Z3_ast a);






    Z3_ast_kind __attribute__ ((visibility ("default"))) Z3_get_ast_kind(Z3_context c, Z3_ast a);




    Z3_bool __attribute__ ((visibility ("default"))) Z3_is_app(Z3_context c, Z3_ast a);




    Z3_bool __attribute__ ((visibility ("default"))) Z3_is_numeral_ast(Z3_context c, Z3_ast a);






    Z3_bool __attribute__ ((visibility ("default"))) Z3_is_algebraic_number(Z3_context c, Z3_ast a);
# 4355 "../../api/z3_api.h"
    Z3_app __attribute__ ((visibility ("default"))) Z3_to_app(Z3_context c, Z3_ast a);
# 4364 "../../api/z3_api.h"
    Z3_func_decl __attribute__ ((visibility ("default"))) Z3_to_func_decl(Z3_context c, Z3_ast a);
# 4373 "../../api/z3_api.h"
    Z3_string __attribute__ ((visibility ("default"))) Z3_get_numeral_string(Z3_context c, Z3_ast a);
# 4383 "../../api/z3_api.h"
    Z3_string __attribute__ ((visibility ("default"))) Z3_get_numeral_decimal_string(Z3_context c, Z3_ast a, unsigned precision);
# 4392 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_get_numerator(Z3_context c, Z3_ast a);
# 4401 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_get_denominator(Z3_context c, Z3_ast a);
# 4417 "../../api/z3_api.h"
    Z3_bool __attribute__ ((visibility ("default"))) Z3_get_numeral_small(Z3_context c, Z3_ast a, int64_t* num, int64_t* den);
# 4429 "../../api/z3_api.h"
    Z3_bool __attribute__ ((visibility ("default"))) Z3_get_numeral_int(Z3_context c, Z3_ast v, int* i);
# 4441 "../../api/z3_api.h"
    Z3_bool __attribute__ ((visibility ("default"))) Z3_get_numeral_uint(Z3_context c, Z3_ast v, unsigned* u);
# 4453 "../../api/z3_api.h"
    Z3_bool __attribute__ ((visibility ("default"))) Z3_get_numeral_uint64(Z3_context c, Z3_ast v, uint64_t* u);
# 4465 "../../api/z3_api.h"
    Z3_bool __attribute__ ((visibility ("default"))) Z3_get_numeral_int64(Z3_context c, Z3_ast v, int64_t* i);
# 4477 "../../api/z3_api.h"
    Z3_bool __attribute__ ((visibility ("default"))) Z3_get_numeral_rational_int64(Z3_context c, Z3_ast v, int64_t* num, int64_t* den);
# 4488 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_get_algebraic_number_lower(Z3_context c, Z3_ast a, unsigned precision);
# 4499 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_get_algebraic_number_upper(Z3_context c, Z3_ast a, unsigned precision);






    Z3_ast __attribute__ ((visibility ("default"))) Z3_pattern_to_ast(Z3_context c, Z3_pattern p);






    unsigned __attribute__ ((visibility ("default"))) Z3_get_pattern_num_terms(Z3_context c, Z3_pattern p);






    Z3_ast __attribute__ ((visibility ("default"))) Z3_get_pattern(Z3_context c, Z3_pattern p, unsigned idx);
# 4529 "../../api/z3_api.h"
    unsigned __attribute__ ((visibility ("default"))) Z3_get_index_value(Z3_context c, Z3_ast a);
# 4538 "../../api/z3_api.h"
    Z3_bool __attribute__ ((visibility ("default"))) Z3_is_quantifier_forall(Z3_context c, Z3_ast a);
# 4547 "../../api/z3_api.h"
    unsigned __attribute__ ((visibility ("default"))) Z3_get_quantifier_weight(Z3_context c, Z3_ast a);
# 4556 "../../api/z3_api.h"
    unsigned __attribute__ ((visibility ("default"))) Z3_get_quantifier_num_patterns(Z3_context c, Z3_ast a);
# 4565 "../../api/z3_api.h"
    Z3_pattern __attribute__ ((visibility ("default"))) Z3_get_quantifier_pattern_ast(Z3_context c, Z3_ast a, unsigned i);
# 4574 "../../api/z3_api.h"
    unsigned __attribute__ ((visibility ("default"))) Z3_get_quantifier_num_no_patterns(Z3_context c, Z3_ast a);
# 4583 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_get_quantifier_no_pattern_ast(Z3_context c, Z3_ast a, unsigned i);
# 4592 "../../api/z3_api.h"
    unsigned __attribute__ ((visibility ("default"))) Z3_get_quantifier_num_bound(Z3_context c, Z3_ast a);
# 4601 "../../api/z3_api.h"
    Z3_symbol __attribute__ ((visibility ("default"))) Z3_get_quantifier_bound_name(Z3_context c, Z3_ast a, unsigned i);
# 4610 "../../api/z3_api.h"
    Z3_sort __attribute__ ((visibility ("default"))) Z3_get_quantifier_bound_sort(Z3_context c, Z3_ast a, unsigned i);
# 4619 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_get_quantifier_body(Z3_context c, Z3_ast a);
# 4631 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_simplify(Z3_context c, Z3_ast a);
# 4642 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_simplify_ex(Z3_context c, Z3_ast a, Z3_params p);






    Z3_string __attribute__ ((visibility ("default"))) Z3_simplify_get_help(Z3_context c);






    Z3_param_descrs __attribute__ ((visibility ("default"))) Z3_simplify_get_param_descrs(Z3_context c);
# 4669 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_update_term(Z3_context c, Z3_ast a, unsigned num_args, Z3_ast const args[]);
# 4678 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_substitute(Z3_context c,
                                Z3_ast a,
                                unsigned num_exprs,
                                Z3_ast const from[],
                                Z3_ast const to[]);







    Z3_ast __attribute__ ((visibility ("default"))) Z3_substitute_vars(Z3_context c,
                                     Z3_ast a,
                                     unsigned num_exprs,
                                     Z3_ast const to[]);
# 4702 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_translate(Z3_context source, Z3_ast a, Z3_context target);
# 4713 "../../api/z3_api.h"
    Z3_model __attribute__ ((visibility ("default"))) Z3_mk_model(Z3_context c);






    void __attribute__ ((visibility ("default"))) Z3_model_inc_ref(Z3_context c, Z3_model m);






    void __attribute__ ((visibility ("default"))) Z3_model_dec_ref(Z3_context c, Z3_model m);
# 4752 "../../api/z3_api.h"
    Z3_bool __attribute__ ((visibility ("default"))) Z3_model_eval(Z3_context c, Z3_model m, Z3_ast t, Z3_bool model_completion, Z3_ast * v);
# 4763 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_model_get_const_interp(Z3_context c, Z3_model m, Z3_func_decl a);






    Z3_bool __attribute__ ((visibility ("default"))) Z3_model_has_interp(Z3_context c, Z3_model m, Z3_func_decl a);
# 4784 "../../api/z3_api.h"
    Z3_func_interp __attribute__ ((visibility ("default"))) Z3_model_get_func_interp(Z3_context c, Z3_model m, Z3_func_decl f);
# 4793 "../../api/z3_api.h"
    unsigned __attribute__ ((visibility ("default"))) Z3_model_get_num_consts(Z3_context c, Z3_model m);
# 4804 "../../api/z3_api.h"
    Z3_func_decl __attribute__ ((visibility ("default"))) Z3_model_get_const_decl(Z3_context c, Z3_model m, unsigned i);
# 4814 "../../api/z3_api.h"
    unsigned __attribute__ ((visibility ("default"))) Z3_model_get_num_funcs(Z3_context c, Z3_model m);
# 4825 "../../api/z3_api.h"
    Z3_func_decl __attribute__ ((visibility ("default"))) Z3_model_get_func_decl(Z3_context c, Z3_model m, unsigned i);
# 4839 "../../api/z3_api.h"
    unsigned __attribute__ ((visibility ("default"))) Z3_model_get_num_sorts(Z3_context c, Z3_model m);
# 4851 "../../api/z3_api.h"
    Z3_sort __attribute__ ((visibility ("default"))) Z3_model_get_sort(Z3_context c, Z3_model m, unsigned i);
# 4861 "../../api/z3_api.h"
    Z3_ast_vector __attribute__ ((visibility ("default"))) Z3_model_get_sort_universe(Z3_context c, Z3_model m, Z3_sort s);






    Z3_model __attribute__ ((visibility ("default"))) Z3_model_translate(Z3_context c, Z3_model m, Z3_context dst);
# 4881 "../../api/z3_api.h"
    Z3_bool __attribute__ ((visibility ("default"))) Z3_is_as_array(Z3_context c, Z3_ast a);
# 4890 "../../api/z3_api.h"
    Z3_func_decl __attribute__ ((visibility ("default"))) Z3_get_as_array_func_decl(Z3_context c, Z3_ast a);
# 4903 "../../api/z3_api.h"
    Z3_func_interp __attribute__ ((visibility ("default"))) Z3_add_func_interp(Z3_context c, Z3_model m, Z3_func_decl f, Z3_ast default_value);






    void __attribute__ ((visibility ("default"))) Z3_add_const_interp(Z3_context c, Z3_model m, Z3_func_decl f, Z3_ast a);






    void __attribute__ ((visibility ("default"))) Z3_func_interp_inc_ref(Z3_context c, Z3_func_interp f);






    void __attribute__ ((visibility ("default"))) Z3_func_interp_dec_ref(Z3_context c, Z3_func_interp f);
# 4935 "../../api/z3_api.h"
    unsigned __attribute__ ((visibility ("default"))) Z3_func_interp_get_num_entries(Z3_context c, Z3_func_interp f);
# 4947 "../../api/z3_api.h"
    Z3_func_entry __attribute__ ((visibility ("default"))) Z3_func_interp_get_entry(Z3_context c, Z3_func_interp f, unsigned i);
# 4957 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_func_interp_get_else(Z3_context c, Z3_func_interp f);
# 4967 "../../api/z3_api.h"
    void __attribute__ ((visibility ("default"))) Z3_func_interp_set_else(Z3_context c, Z3_func_interp f, Z3_ast else_value);






    unsigned __attribute__ ((visibility ("default"))) Z3_func_interp_get_arity(Z3_context c, Z3_func_interp f);
# 4990 "../../api/z3_api.h"
    void __attribute__ ((visibility ("default"))) Z3_func_interp_add_entry(Z3_context c, Z3_func_interp fi, Z3_ast_vector args, Z3_ast value);






    void __attribute__ ((visibility ("default"))) Z3_func_entry_inc_ref(Z3_context c, Z3_func_entry e);






    void __attribute__ ((visibility ("default"))) Z3_func_entry_dec_ref(Z3_context c, Z3_func_entry e);
# 5016 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_func_entry_get_value(Z3_context c, Z3_func_entry e);
# 5025 "../../api/z3_api.h"
    unsigned __attribute__ ((visibility ("default"))) Z3_func_entry_get_num_args(Z3_context c, Z3_func_entry e);
# 5036 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_func_entry_get_arg(Z3_context c, Z3_func_entry e, unsigned i);
# 5046 "../../api/z3_api.h"
    Z3_bool __attribute__ ((visibility ("default"))) Z3_open_log(Z3_string filename);
# 5057 "../../api/z3_api.h"
    void __attribute__ ((visibility ("default"))) Z3_append_log(Z3_string string);






    void __attribute__ ((visibility ("default"))) Z3_close_log(void);
# 5074 "../../api/z3_api.h"
    void __attribute__ ((visibility ("default"))) Z3_toggle_warning_messages(Z3_bool enabled);
# 5096 "../../api/z3_api.h"
    void __attribute__ ((visibility ("default"))) Z3_set_ast_print_mode(Z3_context c, Z3_ast_print_mode mode);
# 5110 "../../api/z3_api.h"
    Z3_string __attribute__ ((visibility ("default"))) Z3_ast_to_string(Z3_context c, Z3_ast a);




    Z3_string __attribute__ ((visibility ("default"))) Z3_pattern_to_string(Z3_context c, Z3_pattern p);




    Z3_string __attribute__ ((visibility ("default"))) Z3_sort_to_string(Z3_context c, Z3_sort s);




    Z3_string __attribute__ ((visibility ("default"))) Z3_func_decl_to_string(Z3_context c, Z3_func_decl d);
# 5136 "../../api/z3_api.h"
    Z3_string __attribute__ ((visibility ("default"))) Z3_model_to_string(Z3_context c, Z3_model m);
# 5156 "../../api/z3_api.h"
    Z3_string __attribute__ ((visibility ("default"))) Z3_benchmark_to_smtlib_string(Z3_context c,
                                                   Z3_string name,
                                                   Z3_string logic,
                                                   Z3_string status,
                                                   Z3_string attributes,
                                                   unsigned num_assumptions,
                                                   Z3_ast const assumptions[],
                                                   Z3_ast formula);
# 5177 "../../api/z3_api.h"
    Z3_ast_vector __attribute__ ((visibility ("default"))) Z3_parse_smtlib2_string(Z3_context c,
                                          Z3_string str,
                                          unsigned num_sorts,
                                          Z3_symbol const sort_names[],
                                          Z3_sort const sorts[],
                                          unsigned num_decls,
                                          Z3_symbol const decl_names[],
                                          Z3_func_decl const decls[]);






    Z3_ast_vector __attribute__ ((visibility ("default"))) Z3_parse_smtlib2_file(Z3_context c,
                                        Z3_string file_name,
                                        unsigned num_sorts,
                                        Z3_symbol const sort_names[],
                                        Z3_sort const sorts[],
                                        unsigned num_decls,
                                        Z3_symbol const decl_names[],
                                        Z3_func_decl const decls[]);
# 5210 "../../api/z3_api.h"
    Z3_string __attribute__ ((visibility ("default"))) Z3_eval_smtlib2_string(Z3_context, Z3_string str);






    Z3_string __attribute__ ((visibility ("default"))) Z3_get_parser_error(Z3_context c);
# 5233 "../../api/z3_api.h"
    Z3_error_code __attribute__ ((visibility ("default"))) Z3_get_error_code(Z3_context c);
# 5247 "../../api/z3_api.h"
    void __attribute__ ((visibility ("default"))) Z3_set_error_handler(Z3_context c, Z3_error_handler h);







    void __attribute__ ((visibility ("default"))) Z3_set_error(Z3_context c, Z3_error_code e);






    Z3_string __attribute__ ((visibility ("default"))) Z3_get_error_msg(Z3_context c, Z3_error_code err);





    Z3_string __attribute__ ((visibility ("default"))) Z3_get_error_msg_ex(Z3_context c, Z3_error_code err);
# 5279 "../../api/z3_api.h"
    void __attribute__ ((visibility ("default"))) Z3_get_version(unsigned * major, unsigned * minor, unsigned * build_number, unsigned * revision_number);






    Z3_string __attribute__ ((visibility ("default"))) Z3_get_full_version(void);







    void __attribute__ ((visibility ("default"))) Z3_enable_trace(Z3_string tag);







    void __attribute__ ((visibility ("default"))) Z3_disable_trace(Z3_string tag);
# 5314 "../../api/z3_api.h"
    void __attribute__ ((visibility ("default"))) Z3_reset_memory(void);
# 5324 "../../api/z3_api.h"
    void __attribute__ ((visibility ("default"))) Z3_finalize_memory(void);
# 5346 "../../api/z3_api.h"
    Z3_goal __attribute__ ((visibility ("default"))) Z3_mk_goal(Z3_context c, Z3_bool models, Z3_bool unsat_cores, Z3_bool proofs);






    void __attribute__ ((visibility ("default"))) Z3_goal_inc_ref(Z3_context c, Z3_goal g);






    void __attribute__ ((visibility ("default"))) Z3_goal_dec_ref(Z3_context c, Z3_goal g);
# 5369 "../../api/z3_api.h"
    Z3_goal_prec __attribute__ ((visibility ("default"))) Z3_goal_precision(Z3_context c, Z3_goal g);
# 5383 "../../api/z3_api.h"
    void __attribute__ ((visibility ("default"))) Z3_goal_assert(Z3_context c, Z3_goal g, Z3_ast a);






    Z3_bool __attribute__ ((visibility ("default"))) Z3_goal_inconsistent(Z3_context c, Z3_goal g);






    unsigned __attribute__ ((visibility ("default"))) Z3_goal_depth(Z3_context c, Z3_goal g);






    void __attribute__ ((visibility ("default"))) Z3_goal_reset(Z3_context c, Z3_goal g);






    unsigned __attribute__ ((visibility ("default"))) Z3_goal_size(Z3_context c, Z3_goal g);
# 5420 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_goal_formula(Z3_context c, Z3_goal g, unsigned idx);






    unsigned __attribute__ ((visibility ("default"))) Z3_goal_num_exprs(Z3_context c, Z3_goal g);






    Z3_bool __attribute__ ((visibility ("default"))) Z3_goal_is_decided_sat(Z3_context c, Z3_goal g);






    Z3_bool __attribute__ ((visibility ("default"))) Z3_goal_is_decided_unsat(Z3_context c, Z3_goal g);






    Z3_goal __attribute__ ((visibility ("default"))) Z3_goal_translate(Z3_context source, Z3_goal g, Z3_context target);
# 5457 "../../api/z3_api.h"
    Z3_model __attribute__ ((visibility ("default"))) Z3_goal_convert_model(Z3_context c, Z3_goal g, Z3_model m);






    Z3_string __attribute__ ((visibility ("default"))) Z3_goal_to_string(Z3_context c, Z3_goal g);






    Z3_string __attribute__ ((visibility ("default"))) Z3_goal_to_dimacs_string(Z3_context c, Z3_goal g);
# 5486 "../../api/z3_api.h"
    Z3_tactic __attribute__ ((visibility ("default"))) Z3_mk_tactic(Z3_context c, Z3_string name);






    void __attribute__ ((visibility ("default"))) Z3_tactic_inc_ref(Z3_context c, Z3_tactic t);






    void __attribute__ ((visibility ("default"))) Z3_tactic_dec_ref(Z3_context c, Z3_tactic g);
# 5512 "../../api/z3_api.h"
    Z3_probe __attribute__ ((visibility ("default"))) Z3_mk_probe(Z3_context c, Z3_string name);






    void __attribute__ ((visibility ("default"))) Z3_probe_inc_ref(Z3_context c, Z3_probe p);






    void __attribute__ ((visibility ("default"))) Z3_probe_dec_ref(Z3_context c, Z3_probe p);







    Z3_tactic __attribute__ ((visibility ("default"))) Z3_tactic_and_then(Z3_context c, Z3_tactic t1, Z3_tactic t2);







    Z3_tactic __attribute__ ((visibility ("default"))) Z3_tactic_or_else(Z3_context c, Z3_tactic t1, Z3_tactic t2);






    Z3_tactic __attribute__ ((visibility ("default"))) Z3_tactic_par_or(Z3_context c, unsigned num, Z3_tactic const ts[]);







    Z3_tactic __attribute__ ((visibility ("default"))) Z3_tactic_par_and_then(Z3_context c, Z3_tactic t1, Z3_tactic t2);







    Z3_tactic __attribute__ ((visibility ("default"))) Z3_tactic_try_for(Z3_context c, Z3_tactic t, unsigned ms);







    Z3_tactic __attribute__ ((visibility ("default"))) Z3_tactic_when(Z3_context c, Z3_probe p, Z3_tactic t);







    Z3_tactic __attribute__ ((visibility ("default"))) Z3_tactic_cond(Z3_context c, Z3_probe p, Z3_tactic t1, Z3_tactic t2);







    Z3_tactic __attribute__ ((visibility ("default"))) Z3_tactic_repeat(Z3_context c, Z3_tactic t, unsigned max);






    Z3_tactic __attribute__ ((visibility ("default"))) Z3_tactic_skip(Z3_context c);






    Z3_tactic __attribute__ ((visibility ("default"))) Z3_tactic_fail(Z3_context c);






    Z3_tactic __attribute__ ((visibility ("default"))) Z3_tactic_fail_if(Z3_context c, Z3_probe p);







    Z3_tactic __attribute__ ((visibility ("default"))) Z3_tactic_fail_if_not_decided(Z3_context c);






    Z3_tactic __attribute__ ((visibility ("default"))) Z3_tactic_using_params(Z3_context c, Z3_tactic t, Z3_params p);






    Z3_probe __attribute__ ((visibility ("default"))) Z3_probe_const(Z3_context x, double val);
# 5641 "../../api/z3_api.h"
    Z3_probe __attribute__ ((visibility ("default"))) Z3_probe_lt(Z3_context x, Z3_probe p1, Z3_probe p2);
# 5650 "../../api/z3_api.h"
    Z3_probe __attribute__ ((visibility ("default"))) Z3_probe_gt(Z3_context x, Z3_probe p1, Z3_probe p2);
# 5659 "../../api/z3_api.h"
    Z3_probe __attribute__ ((visibility ("default"))) Z3_probe_le(Z3_context x, Z3_probe p1, Z3_probe p2);
# 5668 "../../api/z3_api.h"
    Z3_probe __attribute__ ((visibility ("default"))) Z3_probe_ge(Z3_context x, Z3_probe p1, Z3_probe p2);
# 5677 "../../api/z3_api.h"
    Z3_probe __attribute__ ((visibility ("default"))) Z3_probe_eq(Z3_context x, Z3_probe p1, Z3_probe p2);
# 5686 "../../api/z3_api.h"
    Z3_probe __attribute__ ((visibility ("default"))) Z3_probe_and(Z3_context x, Z3_probe p1, Z3_probe p2);
# 5695 "../../api/z3_api.h"
    Z3_probe __attribute__ ((visibility ("default"))) Z3_probe_or(Z3_context x, Z3_probe p1, Z3_probe p2);
# 5704 "../../api/z3_api.h"
    Z3_probe __attribute__ ((visibility ("default"))) Z3_probe_not(Z3_context x, Z3_probe p);






    unsigned __attribute__ ((visibility ("default"))) Z3_get_num_tactics(Z3_context c);
# 5720 "../../api/z3_api.h"
    Z3_string __attribute__ ((visibility ("default"))) Z3_get_tactic_name(Z3_context c, unsigned i);






    unsigned __attribute__ ((visibility ("default"))) Z3_get_num_probes(Z3_context c);
# 5736 "../../api/z3_api.h"
    Z3_string __attribute__ ((visibility ("default"))) Z3_get_probe_name(Z3_context c, unsigned i);






    Z3_string __attribute__ ((visibility ("default"))) Z3_tactic_get_help(Z3_context c, Z3_tactic t);






    Z3_param_descrs __attribute__ ((visibility ("default"))) Z3_tactic_get_param_descrs(Z3_context c, Z3_tactic t);






    Z3_string __attribute__ ((visibility ("default"))) Z3_tactic_get_descr(Z3_context c, Z3_string name);






    Z3_string __attribute__ ((visibility ("default"))) Z3_probe_get_descr(Z3_context c, Z3_string name);







    double __attribute__ ((visibility ("default"))) Z3_probe_apply(Z3_context c, Z3_probe p, Z3_goal g);






    Z3_apply_result __attribute__ ((visibility ("default"))) Z3_tactic_apply(Z3_context c, Z3_tactic t, Z3_goal g);






    Z3_apply_result __attribute__ ((visibility ("default"))) Z3_tactic_apply_ex(Z3_context c, Z3_tactic t, Z3_goal g, Z3_params p);






    void __attribute__ ((visibility ("default"))) Z3_apply_result_inc_ref(Z3_context c, Z3_apply_result r);






    void __attribute__ ((visibility ("default"))) Z3_apply_result_dec_ref(Z3_context c, Z3_apply_result r);






    Z3_string __attribute__ ((visibility ("default"))) Z3_apply_result_to_string(Z3_context c, Z3_apply_result r);






    unsigned __attribute__ ((visibility ("default"))) Z3_apply_result_get_num_subgoals(Z3_context c, Z3_apply_result r);
# 5823 "../../api/z3_api.h"
    Z3_goal __attribute__ ((visibility ("default"))) Z3_apply_result_get_subgoal(Z3_context c, Z3_apply_result r, unsigned i);
# 5865 "../../api/z3_api.h"
    Z3_solver __attribute__ ((visibility ("default"))) Z3_mk_solver(Z3_context c);
# 5892 "../../api/z3_api.h"
    Z3_solver __attribute__ ((visibility ("default"))) Z3_mk_simple_solver(Z3_context c);
# 5903 "../../api/z3_api.h"
    Z3_solver __attribute__ ((visibility ("default"))) Z3_mk_solver_for_logic(Z3_context c, Z3_symbol logic);
# 5915 "../../api/z3_api.h"
    Z3_solver __attribute__ ((visibility ("default"))) Z3_mk_solver_from_tactic(Z3_context c, Z3_tactic t);






    Z3_solver __attribute__ ((visibility ("default"))) Z3_solver_translate(Z3_context source, Z3_solver s, Z3_context target);






    void __attribute__ ((visibility ("default"))) Z3_solver_import_model_converter(Z3_context ctx, Z3_solver src, Z3_solver dst);






    Z3_string __attribute__ ((visibility ("default"))) Z3_solver_get_help(Z3_context c, Z3_solver s);






    Z3_param_descrs __attribute__ ((visibility ("default"))) Z3_solver_get_param_descrs(Z3_context c, Z3_solver s);






    void __attribute__ ((visibility ("default"))) Z3_solver_set_params(Z3_context c, Z3_solver s, Z3_params p);






    void __attribute__ ((visibility ("default"))) Z3_solver_inc_ref(Z3_context c, Z3_solver s);






    void __attribute__ ((visibility ("default"))) Z3_solver_dec_ref(Z3_context c, Z3_solver s);
# 5975 "../../api/z3_api.h"
    void __attribute__ ((visibility ("default"))) Z3_solver_push(Z3_context c, Z3_solver s);
# 5986 "../../api/z3_api.h"
    void __attribute__ ((visibility ("default"))) Z3_solver_pop(Z3_context c, Z3_solver s, unsigned n);






    void __attribute__ ((visibility ("default"))) Z3_solver_reset(Z3_context c, Z3_solver s);
# 6003 "../../api/z3_api.h"
    unsigned __attribute__ ((visibility ("default"))) Z3_solver_get_num_scopes(Z3_context c, Z3_solver s);
# 6013 "../../api/z3_api.h"
    void __attribute__ ((visibility ("default"))) Z3_solver_assert(Z3_context c, Z3_solver s, Z3_ast a);
# 6029 "../../api/z3_api.h"
    void __attribute__ ((visibility ("default"))) Z3_solver_assert_and_track(Z3_context c, Z3_solver s, Z3_ast a, Z3_ast p);






    void __attribute__ ((visibility ("default"))) Z3_solver_from_file(Z3_context c, Z3_solver s, Z3_string file_name);






    void __attribute__ ((visibility ("default"))) Z3_solver_from_string(Z3_context c, Z3_solver s, Z3_string file_name);






    Z3_ast_vector __attribute__ ((visibility ("default"))) Z3_solver_get_assertions(Z3_context c, Z3_solver s);






    Z3_ast_vector __attribute__ ((visibility ("default"))) Z3_solver_get_units(Z3_context c, Z3_solver s);
# 6075 "../../api/z3_api.h"
    Z3_lbool __attribute__ ((visibility ("default"))) Z3_solver_check(Z3_context c, Z3_solver s);
# 6088 "../../api/z3_api.h"
    Z3_lbool __attribute__ ((visibility ("default"))) Z3_solver_check_assumptions(Z3_context c, Z3_solver s,
                                                unsigned num_assumptions, Z3_ast const assumptions[]);
# 6109 "../../api/z3_api.h"
    Z3_lbool __attribute__ ((visibility ("default"))) Z3_get_implied_equalities(Z3_context c,
                                              Z3_solver s,
                                              unsigned num_terms,
                                              Z3_ast const terms[],
                                              unsigned class_ids[]);







    Z3_lbool __attribute__ ((visibility ("default"))) Z3_solver_get_consequences(Z3_context c,
                                               Z3_solver s,
                                               Z3_ast_vector assumptions,
                                               Z3_ast_vector variables,
                                               Z3_ast_vector consequences);
# 6146 "../../api/z3_api.h"
    Z3_ast_vector __attribute__ ((visibility ("default"))) Z3_solver_cube(Z3_context c, Z3_solver s, Z3_ast_vector vars, unsigned backtrack_level);
# 6156 "../../api/z3_api.h"
    Z3_model __attribute__ ((visibility ("default"))) Z3_solver_get_model(Z3_context c, Z3_solver s);
# 6167 "../../api/z3_api.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_solver_get_proof(Z3_context c, Z3_solver s);







    Z3_ast_vector __attribute__ ((visibility ("default"))) Z3_solver_get_unsat_core(Z3_context c, Z3_solver s);







    Z3_string __attribute__ ((visibility ("default"))) Z3_solver_get_reason_unknown(Z3_context c, Z3_solver s);
# 6192 "../../api/z3_api.h"
    Z3_stats __attribute__ ((visibility ("default"))) Z3_solver_get_statistics(Z3_context c, Z3_solver s);






    Z3_string __attribute__ ((visibility ("default"))) Z3_solver_to_string(Z3_context c, Z3_solver s);
# 6211 "../../api/z3_api.h"
    Z3_string __attribute__ ((visibility ("default"))) Z3_stats_to_string(Z3_context c, Z3_stats s);






    void __attribute__ ((visibility ("default"))) Z3_stats_inc_ref(Z3_context c, Z3_stats s);






    void __attribute__ ((visibility ("default"))) Z3_stats_dec_ref(Z3_context c, Z3_stats s);






    unsigned __attribute__ ((visibility ("default"))) Z3_stats_size(Z3_context c, Z3_stats s);
# 6241 "../../api/z3_api.h"
    Z3_string __attribute__ ((visibility ("default"))) Z3_stats_get_key(Z3_context c, Z3_stats s, unsigned idx);
# 6250 "../../api/z3_api.h"
    Z3_bool __attribute__ ((visibility ("default"))) Z3_stats_is_uint(Z3_context c, Z3_stats s, unsigned idx);
# 6259 "../../api/z3_api.h"
    Z3_bool __attribute__ ((visibility ("default"))) Z3_stats_is_double(Z3_context c, Z3_stats s, unsigned idx);
# 6268 "../../api/z3_api.h"
    unsigned __attribute__ ((visibility ("default"))) Z3_stats_get_uint_value(Z3_context c, Z3_stats s, unsigned idx);
# 6277 "../../api/z3_api.h"
    double __attribute__ ((visibility ("default"))) Z3_stats_get_double_value(Z3_context c, Z3_stats s, unsigned idx);






    uint64_t __attribute__ ((visibility ("default"))) Z3_get_estimated_alloc_size(void);
# 28 "../../api/z3.h" 2
# 1 "../../api/z3_ast_containers.h" 1
# 39 "../../api/z3_ast_containers.h"
    Z3_ast_vector __attribute__ ((visibility ("default"))) Z3_mk_ast_vector(Z3_context c);






    void __attribute__ ((visibility ("default"))) Z3_ast_vector_inc_ref(Z3_context c, Z3_ast_vector v);






    void __attribute__ ((visibility ("default"))) Z3_ast_vector_dec_ref(Z3_context c, Z3_ast_vector v);






    unsigned __attribute__ ((visibility ("default"))) Z3_ast_vector_size(Z3_context c, Z3_ast_vector v);
# 69 "../../api/z3_ast_containers.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_ast_vector_get(Z3_context c, Z3_ast_vector v, unsigned i);
# 78 "../../api/z3_ast_containers.h"
    void __attribute__ ((visibility ("default"))) Z3_ast_vector_set(Z3_context c, Z3_ast_vector v, unsigned i, Z3_ast a);






    void __attribute__ ((visibility ("default"))) Z3_ast_vector_resize(Z3_context c, Z3_ast_vector v, unsigned n);






    void __attribute__ ((visibility ("default"))) Z3_ast_vector_push(Z3_context c, Z3_ast_vector v, Z3_ast a);






    Z3_ast_vector __attribute__ ((visibility ("default"))) Z3_ast_vector_translate(Z3_context s, Z3_ast_vector v, Z3_context t);






    Z3_string __attribute__ ((visibility ("default"))) Z3_ast_vector_to_string(Z3_context c, Z3_ast_vector v);
# 120 "../../api/z3_ast_containers.h"
    Z3_ast_map __attribute__ ((visibility ("default"))) Z3_mk_ast_map(Z3_context c);






    void __attribute__ ((visibility ("default"))) Z3_ast_map_inc_ref(Z3_context c, Z3_ast_map m);






    void __attribute__ ((visibility ("default"))) Z3_ast_map_dec_ref(Z3_context c, Z3_ast_map m);






    Z3_bool __attribute__ ((visibility ("default"))) Z3_ast_map_contains(Z3_context c, Z3_ast_map m, Z3_ast k);
# 150 "../../api/z3_ast_containers.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_ast_map_find(Z3_context c, Z3_ast_map m, Z3_ast k);






    void __attribute__ ((visibility ("default"))) Z3_ast_map_insert(Z3_context c, Z3_ast_map m, Z3_ast k, Z3_ast v);






    void __attribute__ ((visibility ("default"))) Z3_ast_map_erase(Z3_context c, Z3_ast_map m, Z3_ast k);






    void __attribute__ ((visibility ("default"))) Z3_ast_map_reset(Z3_context c, Z3_ast_map m);






    unsigned __attribute__ ((visibility ("default"))) Z3_ast_map_size(Z3_context c, Z3_ast_map m);






    Z3_ast_vector __attribute__ ((visibility ("default"))) Z3_ast_map_keys(Z3_context c, Z3_ast_map m);






    Z3_string __attribute__ ((visibility ("default"))) Z3_ast_map_to_string(Z3_context c, Z3_ast_map m);
# 29 "../../api/z3.h" 2
# 1 "../../api/z3_algebraic.h" 1
# 39 "../../api/z3_algebraic.h"
    Z3_bool __attribute__ ((visibility ("default"))) Z3_algebraic_is_value(Z3_context c, Z3_ast a);
# 48 "../../api/z3_algebraic.h"
    Z3_bool __attribute__ ((visibility ("default"))) Z3_algebraic_is_pos(Z3_context c, Z3_ast a);
# 57 "../../api/z3_algebraic.h"
    Z3_bool __attribute__ ((visibility ("default"))) Z3_algebraic_is_neg(Z3_context c, Z3_ast a);
# 66 "../../api/z3_algebraic.h"
    Z3_bool __attribute__ ((visibility ("default"))) Z3_algebraic_is_zero(Z3_context c, Z3_ast a);
# 75 "../../api/z3_algebraic.h"
    int __attribute__ ((visibility ("default"))) Z3_algebraic_sign(Z3_context c, Z3_ast a);
# 86 "../../api/z3_algebraic.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_algebraic_add(Z3_context c, Z3_ast a, Z3_ast b);
# 97 "../../api/z3_algebraic.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_algebraic_sub(Z3_context c, Z3_ast a, Z3_ast b);
# 108 "../../api/z3_algebraic.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_algebraic_mul(Z3_context c, Z3_ast a, Z3_ast b);
# 120 "../../api/z3_algebraic.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_algebraic_div(Z3_context c, Z3_ast a, Z3_ast b);
# 131 "../../api/z3_algebraic.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_algebraic_root(Z3_context c, Z3_ast a, unsigned k);
# 141 "../../api/z3_algebraic.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_algebraic_power(Z3_context c, Z3_ast a, unsigned k);
# 151 "../../api/z3_algebraic.h"
    Z3_bool __attribute__ ((visibility ("default"))) Z3_algebraic_lt(Z3_context c, Z3_ast a, Z3_ast b);
# 161 "../../api/z3_algebraic.h"
    Z3_bool __attribute__ ((visibility ("default"))) Z3_algebraic_gt(Z3_context c, Z3_ast a, Z3_ast b);
# 171 "../../api/z3_algebraic.h"
    Z3_bool __attribute__ ((visibility ("default"))) Z3_algebraic_le(Z3_context c, Z3_ast a, Z3_ast b);
# 181 "../../api/z3_algebraic.h"
    Z3_bool __attribute__ ((visibility ("default"))) Z3_algebraic_ge(Z3_context c, Z3_ast a, Z3_ast b);
# 191 "../../api/z3_algebraic.h"
    Z3_bool __attribute__ ((visibility ("default"))) Z3_algebraic_eq(Z3_context c, Z3_ast a, Z3_ast b);
# 201 "../../api/z3_algebraic.h"
    Z3_bool __attribute__ ((visibility ("default"))) Z3_algebraic_neq(Z3_context c, Z3_ast a, Z3_ast b);
# 213 "../../api/z3_algebraic.h"
    Z3_ast_vector __attribute__ ((visibility ("default"))) Z3_algebraic_roots(Z3_context c, Z3_ast p, unsigned n, Z3_ast a[]);
# 224 "../../api/z3_algebraic.h"
    int __attribute__ ((visibility ("default"))) Z3_algebraic_eval(Z3_context c, Z3_ast p, unsigned n, Z3_ast a[]);
# 30 "../../api/z3.h" 2
# 1 "../../api/z3_polynomial.h" 1
# 45 "../../api/z3_polynomial.h"
    Z3_ast_vector __attribute__ ((visibility ("default"))) Z3_polynomial_subresultants(Z3_context c, Z3_ast p, Z3_ast q, Z3_ast x);
# 31 "../../api/z3.h" 2
# 1 "../../api/z3_rcf.h" 1
# 39 "../../api/z3_rcf.h"
    void __attribute__ ((visibility ("default"))) Z3_rcf_del(Z3_context c, Z3_rcf_num a);






    Z3_rcf_num __attribute__ ((visibility ("default"))) Z3_rcf_mk_rational(Z3_context c, Z3_string val);






    Z3_rcf_num __attribute__ ((visibility ("default"))) Z3_rcf_mk_small_int(Z3_context c, int val);






    Z3_rcf_num __attribute__ ((visibility ("default"))) Z3_rcf_mk_pi(Z3_context c);






    Z3_rcf_num __attribute__ ((visibility ("default"))) Z3_rcf_mk_e(Z3_context c);






    Z3_rcf_num __attribute__ ((visibility ("default"))) Z3_rcf_mk_infinitesimal(Z3_context c);
# 85 "../../api/z3_rcf.h"
    unsigned __attribute__ ((visibility ("default"))) Z3_rcf_mk_roots(Z3_context c, unsigned n, Z3_rcf_num const a[], Z3_rcf_num roots[]);






    Z3_rcf_num __attribute__ ((visibility ("default"))) Z3_rcf_add(Z3_context c, Z3_rcf_num a, Z3_rcf_num b);






    Z3_rcf_num __attribute__ ((visibility ("default"))) Z3_rcf_sub(Z3_context c, Z3_rcf_num a, Z3_rcf_num b);






    Z3_rcf_num __attribute__ ((visibility ("default"))) Z3_rcf_mul(Z3_context c, Z3_rcf_num a, Z3_rcf_num b);






    Z3_rcf_num __attribute__ ((visibility ("default"))) Z3_rcf_div(Z3_context c, Z3_rcf_num a, Z3_rcf_num b);






    Z3_rcf_num __attribute__ ((visibility ("default"))) Z3_rcf_neg(Z3_context c, Z3_rcf_num a);






    Z3_rcf_num __attribute__ ((visibility ("default"))) Z3_rcf_inv(Z3_context c, Z3_rcf_num a);






    Z3_rcf_num __attribute__ ((visibility ("default"))) Z3_rcf_power(Z3_context c, Z3_rcf_num a, unsigned k);






    Z3_bool __attribute__ ((visibility ("default"))) Z3_rcf_lt(Z3_context c, Z3_rcf_num a, Z3_rcf_num b);






    Z3_bool __attribute__ ((visibility ("default"))) Z3_rcf_gt(Z3_context c, Z3_rcf_num a, Z3_rcf_num b);






    Z3_bool __attribute__ ((visibility ("default"))) Z3_rcf_le(Z3_context c, Z3_rcf_num a, Z3_rcf_num b);






    Z3_bool __attribute__ ((visibility ("default"))) Z3_rcf_ge(Z3_context c, Z3_rcf_num a, Z3_rcf_num b);






    Z3_bool __attribute__ ((visibility ("default"))) Z3_rcf_eq(Z3_context c, Z3_rcf_num a, Z3_rcf_num b);






    Z3_bool __attribute__ ((visibility ("default"))) Z3_rcf_neq(Z3_context c, Z3_rcf_num a, Z3_rcf_num b);






    Z3_string __attribute__ ((visibility ("default"))) Z3_rcf_num_to_string(Z3_context c, Z3_rcf_num a, Z3_bool compact, Z3_bool html);






    Z3_string __attribute__ ((visibility ("default"))) Z3_rcf_num_to_decimal_string(Z3_context c, Z3_rcf_num a, unsigned prec);







    void __attribute__ ((visibility ("default"))) Z3_rcf_get_numerator_denominator(Z3_context c, Z3_rcf_num a, Z3_rcf_num * n, Z3_rcf_num * d);
# 32 "../../api/z3.h" 2
# 1 "../../api/z3_fixedpoint.h" 1
# 39 "../../api/z3_fixedpoint.h"
    Z3_fixedpoint __attribute__ ((visibility ("default"))) Z3_mk_fixedpoint(Z3_context c);






    void __attribute__ ((visibility ("default"))) Z3_fixedpoint_inc_ref(Z3_context c, Z3_fixedpoint d);






    void __attribute__ ((visibility ("default"))) Z3_fixedpoint_dec_ref(Z3_context c, Z3_fixedpoint d);
# 67 "../../api/z3_fixedpoint.h"
    void __attribute__ ((visibility ("default"))) Z3_fixedpoint_add_rule(Z3_context c, Z3_fixedpoint d, Z3_ast rule, Z3_symbol name);
# 86 "../../api/z3_fixedpoint.h"
    void __attribute__ ((visibility ("default"))) Z3_fixedpoint_add_fact(Z3_context c, Z3_fixedpoint d,
                                       Z3_func_decl r,
                                       unsigned num_args, unsigned args[]);
# 98 "../../api/z3_fixedpoint.h"
    void __attribute__ ((visibility ("default"))) Z3_fixedpoint_assert(Z3_context c, Z3_fixedpoint d, Z3_ast axiom);
# 115 "../../api/z3_fixedpoint.h"
    Z3_lbool __attribute__ ((visibility ("default"))) Z3_fixedpoint_query(Z3_context c, Z3_fixedpoint d, Z3_ast query);
# 129 "../../api/z3_fixedpoint.h"
    Z3_lbool __attribute__ ((visibility ("default"))) Z3_fixedpoint_query_relations(
        Z3_context c, Z3_fixedpoint d,
        unsigned num_relations, Z3_func_decl const relations[]);
# 146 "../../api/z3_fixedpoint.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_fixedpoint_get_answer(Z3_context c, Z3_fixedpoint d);
# 155 "../../api/z3_fixedpoint.h"
    Z3_string __attribute__ ((visibility ("default"))) Z3_fixedpoint_get_reason_unknown(Z3_context c, Z3_fixedpoint d);







    void __attribute__ ((visibility ("default"))) Z3_fixedpoint_update_rule(Z3_context c, Z3_fixedpoint d, Z3_ast a, Z3_symbol name);
# 174 "../../api/z3_fixedpoint.h"
    unsigned __attribute__ ((visibility ("default"))) Z3_fixedpoint_get_num_levels(Z3_context c, Z3_fixedpoint d, Z3_func_decl pred);
# 186 "../../api/z3_fixedpoint.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_fixedpoint_get_cover_delta(Z3_context c, Z3_fixedpoint d, int level, Z3_func_decl pred);
# 200 "../../api/z3_fixedpoint.h"
    void __attribute__ ((visibility ("default"))) Z3_fixedpoint_add_cover(Z3_context c, Z3_fixedpoint d, int level, Z3_func_decl pred, Z3_ast property);






    Z3_stats __attribute__ ((visibility ("default"))) Z3_fixedpoint_get_statistics(Z3_context c, Z3_fixedpoint d);
# 217 "../../api/z3_fixedpoint.h"
    void __attribute__ ((visibility ("default"))) Z3_fixedpoint_register_relation(Z3_context c, Z3_fixedpoint d, Z3_func_decl f);
# 228 "../../api/z3_fixedpoint.h"
    void __attribute__ ((visibility ("default"))) Z3_fixedpoint_set_predicate_representation(
        Z3_context c,
        Z3_fixedpoint d,
        Z3_func_decl f,
        unsigned num_relations,
        Z3_symbol const relation_kinds[]);






    Z3_ast_vector __attribute__ ((visibility ("default"))) Z3_fixedpoint_get_rules(
        Z3_context c,
        Z3_fixedpoint f);






    Z3_ast_vector __attribute__ ((visibility ("default"))) Z3_fixedpoint_get_assertions(
        Z3_context c,
        Z3_fixedpoint f);






    void __attribute__ ((visibility ("default"))) Z3_fixedpoint_set_params(Z3_context c, Z3_fixedpoint f, Z3_params p);






    Z3_string __attribute__ ((visibility ("default"))) Z3_fixedpoint_get_help(Z3_context c, Z3_fixedpoint f);






    Z3_param_descrs __attribute__ ((visibility ("default"))) Z3_fixedpoint_get_param_descrs(Z3_context c, Z3_fixedpoint f);
# 283 "../../api/z3_fixedpoint.h"
    Z3_string __attribute__ ((visibility ("default"))) Z3_fixedpoint_to_string(
        Z3_context c,
        Z3_fixedpoint f,
        unsigned num_queries,
        Z3_ast queries[]);
# 300 "../../api/z3_fixedpoint.h"
    Z3_ast_vector __attribute__ ((visibility ("default"))) Z3_fixedpoint_from_string(Z3_context c,
                                                   Z3_fixedpoint f,
                                                   Z3_string s);
# 315 "../../api/z3_fixedpoint.h"
    Z3_ast_vector __attribute__ ((visibility ("default"))) Z3_fixedpoint_from_file(Z3_context c,
                                                 Z3_fixedpoint f,
                                                 Z3_string s);
# 329 "../../api/z3_fixedpoint.h"
    void __attribute__ ((visibility ("default"))) Z3_fixedpoint_push(Z3_context c, Z3_fixedpoint d);
# 340 "../../api/z3_fixedpoint.h"
    void __attribute__ ((visibility ("default"))) Z3_fixedpoint_pop(Z3_context c, Z3_fixedpoint d);



    typedef void Z3_fixedpoint_reduce_assign_callback_fptr(
        void*, Z3_func_decl,
        unsigned, Z3_ast const [],
        unsigned, Z3_ast const []);

    typedef void Z3_fixedpoint_reduce_app_callback_fptr(
        void*, Z3_func_decl,
        unsigned, Z3_ast const [],
        Z3_ast*);



    void __attribute__ ((visibility ("default"))) Z3_fixedpoint_init(Z3_context c, Z3_fixedpoint d, void* state);






    void __attribute__ ((visibility ("default"))) Z3_fixedpoint_set_reduce_assign_callback(
        Z3_context c ,Z3_fixedpoint d, Z3_fixedpoint_reduce_assign_callback_fptr cb);


    void __attribute__ ((visibility ("default"))) Z3_fixedpoint_set_reduce_app_callback(
        Z3_context c, Z3_fixedpoint d, Z3_fixedpoint_reduce_app_callback_fptr cb);
# 33 "../../api/z3.h" 2
# 1 "../../api/z3_optimization.h" 1
# 39 "../../api/z3_optimization.h"
    Z3_optimize __attribute__ ((visibility ("default"))) Z3_mk_optimize(Z3_context c);






    void __attribute__ ((visibility ("default"))) Z3_optimize_inc_ref(Z3_context c, Z3_optimize d);






    void __attribute__ ((visibility ("default"))) Z3_optimize_dec_ref(Z3_context c, Z3_optimize d);






    void __attribute__ ((visibility ("default"))) Z3_optimize_assert(Z3_context c, Z3_optimize o, Z3_ast a);
# 72 "../../api/z3_optimization.h"
    unsigned __attribute__ ((visibility ("default"))) Z3_optimize_assert_soft(Z3_context c, Z3_optimize o, Z3_ast a, Z3_string weight, Z3_symbol id);
# 81 "../../api/z3_optimization.h"
    unsigned __attribute__ ((visibility ("default"))) Z3_optimize_maximize(Z3_context c, Z3_optimize o, Z3_ast t);
# 91 "../../api/z3_optimization.h"
    unsigned __attribute__ ((visibility ("default"))) Z3_optimize_minimize(Z3_context c, Z3_optimize o, Z3_ast t);
# 103 "../../api/z3_optimization.h"
    void __attribute__ ((visibility ("default"))) Z3_optimize_push(Z3_context c, Z3_optimize d);
# 114 "../../api/z3_optimization.h"
    void __attribute__ ((visibility ("default"))) Z3_optimize_pop(Z3_context c, Z3_optimize d);
# 123 "../../api/z3_optimization.h"
    Z3_lbool __attribute__ ((visibility ("default"))) Z3_optimize_check(Z3_context c, Z3_optimize o);
# 133 "../../api/z3_optimization.h"
    Z3_string __attribute__ ((visibility ("default"))) Z3_optimize_get_reason_unknown(Z3_context c, Z3_optimize d);
# 144 "../../api/z3_optimization.h"
    Z3_model __attribute__ ((visibility ("default"))) Z3_optimize_get_model(Z3_context c, Z3_optimize o);
# 155 "../../api/z3_optimization.h"
    void __attribute__ ((visibility ("default"))) Z3_optimize_set_params(Z3_context c, Z3_optimize o, Z3_params p);
# 165 "../../api/z3_optimization.h"
    Z3_param_descrs __attribute__ ((visibility ("default"))) Z3_optimize_get_param_descrs(Z3_context c, Z3_optimize o);
# 176 "../../api/z3_optimization.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_optimize_get_lower(Z3_context c, Z3_optimize o, unsigned idx);
# 187 "../../api/z3_optimization.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_optimize_get_upper(Z3_context c, Z3_optimize o, unsigned idx);
# 202 "../../api/z3_optimization.h"
    Z3_ast_vector __attribute__ ((visibility ("default"))) Z3_optimize_get_lower_as_vector(Z3_context c, Z3_optimize o, unsigned idx);
# 213 "../../api/z3_optimization.h"
    Z3_ast_vector __attribute__ ((visibility ("default"))) Z3_optimize_get_upper_as_vector(Z3_context c, Z3_optimize o, unsigned idx);
# 223 "../../api/z3_optimization.h"
    Z3_string __attribute__ ((visibility ("default"))) Z3_optimize_to_string(Z3_context c, Z3_optimize o);
# 236 "../../api/z3_optimization.h"
    void __attribute__ ((visibility ("default"))) Z3_optimize_from_string(Z3_context c, Z3_optimize o, Z3_string s);
# 249 "../../api/z3_optimization.h"
    void __attribute__ ((visibility ("default"))) Z3_optimize_from_file(Z3_context c, Z3_optimize o, Z3_string s);






    Z3_string __attribute__ ((visibility ("default"))) Z3_optimize_get_help(Z3_context c, Z3_optimize t);






    Z3_stats __attribute__ ((visibility ("default"))) Z3_optimize_get_statistics(Z3_context c, Z3_optimize d);






    Z3_ast_vector __attribute__ ((visibility ("default"))) Z3_optimize_get_assertions(Z3_context c, Z3_optimize o);
# 282 "../../api/z3_optimization.h"
    Z3_ast_vector __attribute__ ((visibility ("default"))) Z3_optimize_get_objectives(Z3_context c, Z3_optimize o);
# 34 "../../api/z3.h" 2
# 1 "../../api/z3_fpa.h" 1
# 38 "../../api/z3_fpa.h"
    Z3_sort __attribute__ ((visibility ("default"))) Z3_mk_fpa_rounding_mode_sort(Z3_context c);
# 47 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_round_nearest_ties_to_even(Z3_context c);
# 56 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_rne(Z3_context c);
# 65 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_round_nearest_ties_to_away(Z3_context c);
# 74 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_rna(Z3_context c);
# 83 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_round_toward_positive(Z3_context c);
# 92 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_rtp(Z3_context c);
# 101 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_round_toward_negative(Z3_context c);
# 110 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_rtn(Z3_context c);
# 119 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_round_toward_zero(Z3_context c);
# 128 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_rtz(Z3_context c);
# 141 "../../api/z3_fpa.h"
    Z3_sort __attribute__ ((visibility ("default"))) Z3_mk_fpa_sort(Z3_context c, unsigned ebits, unsigned sbits);
# 150 "../../api/z3_fpa.h"
    Z3_sort __attribute__ ((visibility ("default"))) Z3_mk_fpa_sort_half(Z3_context c);
# 159 "../../api/z3_fpa.h"
    Z3_sort __attribute__ ((visibility ("default"))) Z3_mk_fpa_sort_16(Z3_context c);
# 168 "../../api/z3_fpa.h"
    Z3_sort __attribute__ ((visibility ("default"))) Z3_mk_fpa_sort_single(Z3_context c);
# 177 "../../api/z3_fpa.h"
    Z3_sort __attribute__ ((visibility ("default"))) Z3_mk_fpa_sort_32(Z3_context c);
# 186 "../../api/z3_fpa.h"
    Z3_sort __attribute__ ((visibility ("default"))) Z3_mk_fpa_sort_double(Z3_context c);
# 195 "../../api/z3_fpa.h"
    Z3_sort __attribute__ ((visibility ("default"))) Z3_mk_fpa_sort_64(Z3_context c);
# 204 "../../api/z3_fpa.h"
    Z3_sort __attribute__ ((visibility ("default"))) Z3_mk_fpa_sort_quadruple(Z3_context c);
# 213 "../../api/z3_fpa.h"
    Z3_sort __attribute__ ((visibility ("default"))) Z3_mk_fpa_sort_128(Z3_context c);
# 223 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_nan(Z3_context c, Z3_sort s);
# 236 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_inf(Z3_context c, Z3_sort s, Z3_bool negative);
# 249 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_zero(Z3_context c, Z3_sort s, Z3_bool negative);
# 267 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_fp(Z3_context c, Z3_ast sgn, Z3_ast exp, Z3_ast sig);
# 285 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_numeral_float(Z3_context c, float v, Z3_sort ty);
# 303 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_numeral_double(Z3_context c, double v, Z3_sort ty);
# 318 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_numeral_int(Z3_context c, signed v, Z3_sort ty);
# 335 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_numeral_int_uint(Z3_context c, Z3_bool sgn, signed exp, unsigned sig, Z3_sort ty);
# 352 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_numeral_int64_uint64(Z3_context c, Z3_bool sgn, int64_t exp, uint64_t sig, Z3_sort ty);
# 362 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_abs(Z3_context c, Z3_ast t);
# 372 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_neg(Z3_context c, Z3_ast t);
# 386 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_add(Z3_context c, Z3_ast rm, Z3_ast t1, Z3_ast t2);
# 400 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_sub(Z3_context c, Z3_ast rm, Z3_ast t1, Z3_ast t2);
# 414 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_mul(Z3_context c, Z3_ast rm, Z3_ast t1, Z3_ast t2);
# 428 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_div(Z3_context c, Z3_ast rm, Z3_ast t1, Z3_ast t2);
# 445 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_fma(Z3_context c, Z3_ast rm, Z3_ast t1, Z3_ast t2, Z3_ast t3);
# 458 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_sqrt(Z3_context c, Z3_ast rm, Z3_ast t);
# 471 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_rem(Z3_context c, Z3_ast t1, Z3_ast t2);
# 485 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_round_to_integral(Z3_context c, Z3_ast rm, Z3_ast t);
# 498 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_min(Z3_context c, Z3_ast t1, Z3_ast t2);
# 511 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_max(Z3_context c, Z3_ast t1, Z3_ast t2);
# 524 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_leq(Z3_context c, Z3_ast t1, Z3_ast t2);
# 537 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_lt(Z3_context c, Z3_ast t1, Z3_ast t2);
# 550 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_geq(Z3_context c, Z3_ast t1, Z3_ast t2);
# 563 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_gt(Z3_context c, Z3_ast t1, Z3_ast t2);
# 578 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_eq(Z3_context c, Z3_ast t1, Z3_ast t2);
# 590 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_is_normal(Z3_context c, Z3_ast t);
# 602 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_is_subnormal(Z3_context c, Z3_ast t);
# 614 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_is_zero(Z3_context c, Z3_ast t);
# 626 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_is_infinite(Z3_context c, Z3_ast t);
# 638 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_is_nan(Z3_context c, Z3_ast t);
# 650 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_is_negative(Z3_context c, Z3_ast t);
# 662 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_is_positive(Z3_context c, Z3_ast t);
# 680 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_to_fp_bv(Z3_context c, Z3_ast bv, Z3_sort s);
# 698 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_to_fp_float(Z3_context c, Z3_ast rm, Z3_ast t, Z3_sort s);
# 716 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_to_fp_real(Z3_context c, Z3_ast rm, Z3_ast t, Z3_sort s);
# 735 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_to_fp_signed(Z3_context c, Z3_ast rm, Z3_ast t, Z3_sort s);
# 754 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_to_fp_unsigned(Z3_context c, Z3_ast rm, Z3_ast t, Z3_sort s);
# 770 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_to_ubv(Z3_context c, Z3_ast rm, Z3_ast t, unsigned sz);
# 786 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_to_sbv(Z3_context c, Z3_ast rm, Z3_ast t, unsigned sz);
# 800 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_to_real(Z3_context c, Z3_ast t);
# 813 "../../api/z3_fpa.h"
    unsigned __attribute__ ((visibility ("default"))) Z3_fpa_get_ebits(Z3_context c, Z3_sort s);
# 823 "../../api/z3_fpa.h"
    unsigned __attribute__ ((visibility ("default"))) Z3_fpa_get_sbits(Z3_context c, Z3_sort s);
# 833 "../../api/z3_fpa.h"
    Z3_bool __attribute__ ((visibility ("default"))) Z3_fpa_is_numeral_nan(Z3_context c, Z3_ast t);
# 843 "../../api/z3_fpa.h"
    Z3_bool __attribute__ ((visibility ("default"))) Z3_fpa_is_numeral_inf(Z3_context c, Z3_ast t);
# 853 "../../api/z3_fpa.h"
    Z3_bool __attribute__ ((visibility ("default"))) Z3_fpa_is_numeral_zero(Z3_context c, Z3_ast t);
# 863 "../../api/z3_fpa.h"
    Z3_bool __attribute__ ((visibility ("default"))) Z3_fpa_is_numeral_normal(Z3_context c, Z3_ast t);
# 873 "../../api/z3_fpa.h"
    Z3_bool __attribute__ ((visibility ("default"))) Z3_fpa_is_numeral_subnormal(Z3_context c, Z3_ast t);
# 883 "../../api/z3_fpa.h"
    Z3_bool __attribute__ ((visibility ("default"))) Z3_fpa_is_numeral_positive(Z3_context c, Z3_ast t);
# 893 "../../api/z3_fpa.h"
    Z3_bool __attribute__ ((visibility ("default"))) Z3_fpa_is_numeral_negative(Z3_context c, Z3_ast t);
# 905 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_fpa_get_numeral_sign_bv(Z3_context c, Z3_ast t);
# 917 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_fpa_get_numeral_significand_bv(Z3_context c, Z3_ast t);
# 931 "../../api/z3_fpa.h"
    Z3_bool __attribute__ ((visibility ("default"))) Z3_fpa_get_numeral_sign(Z3_context c, Z3_ast t, int * sgn);
# 944 "../../api/z3_fpa.h"
    Z3_string __attribute__ ((visibility ("default"))) Z3_fpa_get_numeral_significand_string(Z3_context c, Z3_ast t);
# 959 "../../api/z3_fpa.h"
    Z3_bool __attribute__ ((visibility ("default"))) Z3_fpa_get_numeral_significand_uint64(Z3_context c, Z3_ast t, uint64_t * n);
# 973 "../../api/z3_fpa.h"
    Z3_string __attribute__ ((visibility ("default"))) Z3_fpa_get_numeral_exponent_string(Z3_context c, Z3_ast t, Z3_bool biased);
# 988 "../../api/z3_fpa.h"
    Z3_bool __attribute__ ((visibility ("default"))) Z3_fpa_get_numeral_exponent_int64(Z3_context c, Z3_ast t, int64_t * n, Z3_bool biased);
# 1002 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_fpa_get_numeral_exponent_bv(Z3_context c, Z3_ast t, Z3_bool biased);
# 1019 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_to_ieee_bv(Z3_context c, Z3_ast t);
# 1038 "../../api/z3_fpa.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_mk_fpa_to_fp_int_real(Z3_context c, Z3_ast rm, Z3_ast exp, Z3_ast sig, Z3_sort s);
# 35 "../../api/z3.h" 2
# 1 "../../api/z3_spacer.h" 1
# 46 "../../api/z3_spacer.h"
    Z3_lbool __attribute__ ((visibility ("default"))) Z3_fixedpoint_query_from_lvl (Z3_context c,Z3_fixedpoint d, Z3_ast query, unsigned lvl);
# 55 "../../api/z3_spacer.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_fixedpoint_get_ground_sat_answer(Z3_context c,Z3_fixedpoint d);






    Z3_ast_vector __attribute__ ((visibility ("default"))) Z3_fixedpoint_get_rules_along_trace(Z3_context c,Z3_fixedpoint d);






    Z3_symbol __attribute__ ((visibility ("default"))) Z3_fixedpoint_get_rule_names_along_trace(Z3_context c,Z3_fixedpoint d);
# 79 "../../api/z3_spacer.h"
    void __attribute__ ((visibility ("default"))) Z3_fixedpoint_add_invariant(Z3_context c, Z3_fixedpoint d, Z3_func_decl pred, Z3_ast property);
# 88 "../../api/z3_spacer.h"
    Z3_ast __attribute__ ((visibility ("default"))) Z3_fixedpoint_get_reachable(Z3_context c, Z3_fixedpoint d, Z3_func_decl pred);






    Z3_ast __attribute__ ((visibility ("default"))) Z3_qe_model_project
      (Z3_context c,
       Z3_model m,
       unsigned num_bounds,
       Z3_app const bound[],
       Z3_ast body);







    Z3_ast __attribute__ ((visibility ("default"))) Z3_qe_model_project_skolem
      (Z3_context c,
       Z3_model m,
       unsigned num_bounds,
       Z3_app const bound[],
       Z3_ast body,
       Z3_ast_map map);






    Z3_ast __attribute__ ((visibility ("default"))) Z3_model_extrapolate
      (Z3_context c,
       Z3_model m,
       Z3_ast fml);






    Z3_ast __attribute__ ((visibility ("default"))) Z3_qe_lite
      (Z3_context c,
       Z3_ast_vector vars,
       Z3_ast body);
# 36 "../../api/z3.h" 2

