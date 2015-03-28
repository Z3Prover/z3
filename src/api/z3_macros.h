#ifdef __in
#define Z3_in __in
#else
#define Z3_in
#endif

#ifdef __out
#define Z3_out __out
#else
#define Z3_out
#endif

#ifdef __out_opt
#define Z3_out_opt __out_opt
#else
#define Z3_out_opt Z3_out
#endif

#ifdef __ecount
#define Z3_ecount(num_args) __ecount(num_args)
#else
#define Z3_ecount(num_args)
#endif 

#ifdef __in_ecount
#define Z3_in_ecount(num_args) __in_ecount(num_args)
#else
#define Z3_in_ecount(num_args) Z3_in Z3_ecount(num_args)
#endif 

#ifdef __out_ecount
#define Z3_out_ecount(num_args) __out_ecount(num_args)
#else
#define Z3_out_ecount(num_args) Z3_out Z3_ecount(num_args)
#endif 

#ifdef __inout_ecount
#define Z3_inout_ecount(num_args) __inout_ecount(num_args)
#else
#define Z3_inout_ecount(num_args) Z3_inout Z3_ecount(num_args)
#endif 

#ifdef __inout
#define Z3_inout __inout
#else
#define Z3_inout Z3_in Z3_out
#endif

#ifndef Z3_bool_opt
#define Z3_bool_opt Z3_bool
#endif

#ifndef Z3_API
# ifdef __GNUC__
#  define Z3_API __attribute__ ((visibility ("default")))
# else
#  define Z3_API
# endif
#endif 

#ifndef DEFINE_TYPE
#define DEFINE_TYPE(T) typedef struct _ ## T *T
#endif

#ifndef DEFINE_VOID
#define DEFINE_VOID(T) typedef void* T
#endif

#ifndef BEGIN_MLAPI_EXCLUDE
#define BEGIN_MLAPI_EXCLUDE
#endif
#ifndef END_MLAPI_EXCLUDE
#define END_MLAPI_EXCLUDE
#endif
