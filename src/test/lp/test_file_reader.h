/*++
Copyright (c) 2017 Microsoft Corporation

Module Name:

    <name>

Abstract:

    <abstract>

Author:

    Lev Nachmanson (levnach)

Revision History:


--*/

#pragma once

// reads a text file
#include <string>
#include <vector>
#include <unordered_map>
#include <iostream>
#include <fstream>
#include "math/lp/lp_utils.h"
#include "math/lp/lp_solver.h"

namespace lp {

template <typename T>
struct test_result {
    lp_status m_status;
    T m_cost;
    std::unordered_map<std::string, T> column_values;
};

template <typename T>
class test_file_reader {
    struct raw_blob {
        std::vector<std::string> m_unparsed_strings;
        std::vector<raw_blob> m_blobs;
    };

    struct test_file_blob {
        std::string m_name;
        std::string m_content;
        std::unordered_map<std::string, std::string> m_table;
        std::unordered_map<std::string, test_file_blob> m_blobs;

        test_result<T> * get_test_result() {
            test_result<T> * tr = new test_result<T>();
            throw "not impl";
            return tr;
        }
    };
    std::ifstream m_file_stream;
public:
    // constructor
    test_file_reader(std::string file_name) :  m_file_stream(file_name) {
        if (!m_file_stream.is_open()) {
            std::cout << "cannot open file " << "\'" << file_name << "\'" << std::endl;
        }
    }

    raw_blob scan_to_row_blob() {
    }

    test_file_blob scan_row_blob_to_test_file_blob(raw_blob /* rblob */) {
    }

    test_result<T> * get_test_result() {
        if (!m_file_stream.is_open()) {
            return nullptr;
        }

        raw_blob rblob = scan_to_row_blob();

        test_file_blob tblob = scan_row_blob_to_test_file_blob(rblob);

        return tblob.get_test_result();
    }
};
}
