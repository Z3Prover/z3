/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    foreach_file.h

Abstract:

    Traverse files in a directory that match a given suffix.
    Apply a method to each of the files.

Author:

    Nikolaj Bjorner (nbjorner) 2006-11-3.

Revision History:

--*/
#pragma once

#ifndef FOR_EACH_FILE_H_
#define FOR_EACH_FILE_H_

struct for_each_file_proc {
    virtual bool operator()(const char* file_path) = 0;
};

bool for_each_file(for_each_file_proc& proc, const char* base, const char* suffix);
    

#endif /* FOR_EACH_FILE_H_ */

