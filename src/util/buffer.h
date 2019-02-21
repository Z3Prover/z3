/*++
Copyright (c) 2019 Microsoft Corporation

Module Name:

    buffer.h

Author:

    Daniel Schemmel 2019-2-23

--*/

#pragma once

#include "buffvec.h"

template<typename T, unsigned INITIAL_SIZE=16>
using buffer = buffvec<T, unsigned, INITIAL_SIZE>;
