
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

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
