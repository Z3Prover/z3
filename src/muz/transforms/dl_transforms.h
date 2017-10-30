/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    dl_transforms.h

Abstract:

    Default transformations.

Author:

    Nikolaj Bjorner (nbjorner) 2013-08-28.

Revision History:

    Extracted from dl_context

--*/
#ifndef DL_TRANSFORMS_H_
#define DL_TRANSFORMS_H_

#include "muz/base/dl_context.h"

namespace datalog {
    void apply_default_transformation(context& ctx);
}

#endif
