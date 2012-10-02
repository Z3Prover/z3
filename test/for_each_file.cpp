/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    foreach_file.cpp

Abstract:

    Traverse files in a directory that match a given suffix.
    Apply a method to each of the files.

Author:

    Nikolaj Bjorner (nbjorner) 2006-11-3.

Revision History:

--*/
#ifdef _WINDOWS
#include <string>
#include <windows.h>
#include <strsafe.h>
#include "for_each_file.h"

bool for_each_file(for_each_file_proc& proc, const char* base, const char* suffix)
{
    std::string pattern(base);
    pattern += "\\";
    pattern += suffix;

    char buffer[MAX_PATH];
    
    WIN32_FIND_DATAA data;
    HANDLE h = FindFirstFileA(pattern.c_str(),&data);

    while (h != INVALID_HANDLE_VALUE) {

        StringCchPrintfA(buffer, ARRAYSIZE(buffer), "%s\\%s", base, data.cFileName);       

        if (!proc(buffer)) {
            return false;
        }
        
        if (!FindNextFileA(h,&data)) {
            break;
        }
    }

    // 
    // Now recurse through sub-directories.
    //

    pattern = base;
    pattern += "\\*";
    h = FindFirstFileA(pattern.c_str(),&data);

    while (h != INVALID_HANDLE_VALUE) {

        if ((data.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY) &&
            data.cFileName[0] != '.'
            ){
            std::string subdir(base);
            subdir += "\\";
            subdir += data.cFileName;
            if (!for_each_file(proc, subdir.c_str(), suffix)) {
                return false;
            }
        }
        
        if (!FindNextFileA(h,&data)) {
            break;
        }
    }

    return true;
};
#endif

