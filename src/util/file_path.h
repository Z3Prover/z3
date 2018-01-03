/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    file_path.h

Abstract:

    File path functions.

Author:

    Nikolaj Bjorner (nbjorner) 2017-11-19

Revision History:

--*/
#ifndef FILE_PATH_H_
#define FILE_PATH_H_
#include <cstring>

inline char const * get_extension(char const * file_name) {
    if (file_name == 0)
        return 0;
    char const * last_dot = 0;
    for (;;) {
        char const * tmp = strchr(file_name, '.');
        if (tmp == 0) {
            return last_dot;
        }
        last_dot  = tmp + 1;
        file_name = last_dot;
    }
}

#endif /* FILE_PATH_H_ */


