
/*++
Copyright (c) 2015 Microsoft Corporation

--*/
#pragma once

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

#ifndef Z3_DECLARE_CLOSURE
#define Z3_DECLARE_CLOSURE(_NAME_,_RETURN_,_ARGS_) typedef _RETURN_ _NAME_ _ARGS_
#endif
