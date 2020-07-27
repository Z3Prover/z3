/*++
Copyright (c) 2008 Microsoft Corporation

Module Name:

    progress_callback.h

Abstract:

    Virtual callback for reporting progress.

Author:

    Michal Moskal (micmo) 2009-02-17.

Revision History:

--*/
#pragma once

class progress_callback {
public:
    virtual ~progress_callback() {}
    
    // Called on every check for resource limit exceeded (much more frequent).
    virtual void fast_progress_sample() {}

    // Less frequent invoked.
    virtual void slow_progress_sample() {}
};

