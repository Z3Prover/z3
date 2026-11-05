#pragma once

#include "Z3Cherry.h"
#include <z3++.h>

#include <stdexcept>
#include <string>
#include <unordered_set>
#include <vector>

namespace checker {
using Rational = FStar_Pervasives_Native_tuple2__int_int;
using Result = FStar_Pervasives_Native_option__int;
using ClauseTrail = FStar_Pervasives_Native_option__tuple2_list_clause_view_ast;

class NativeError : public std::runtime_error {
public:
    using std::runtime_error::runtime_error;
};

class NativeSession {
    NativeSession* previous;
    std::unordered_set<Z3_ast> retained;
public:
    z3::context& context;
    explicit NativeSession(z3::context& context);
    ~NativeSession();
    NativeSession(NativeSession const&) = delete;
    NativeSession& operator=(NativeSession const&) = delete;
    Z3_ast keep(Z3_ast ast);
};

// The flattened `ff-pac` certificate of a finite-field theory lemma, or None.
FStar_Pervasives_Native_option__ff_pac_view view_ff_pac(Z3_ast certificate);

std::string text(cherry_string value);
std::string integer(cherry_int value);
[[noreturn]] void fail(cherry_string message);

template<class Cell, class Function>
void each(cherry_obj* values, Function function) {
    while (!cherry_is_scalar(values)) {
        auto* cell = reinterpret_cast<Cell*>(values);
        function(cell->hd);
        values = cell->tl;
    }
}

template<class Cell>
size_t length(cherry_obj* values) {
    size_t result = 0;
    each<Cell>(values, [&](auto const&) { ++result; });
    return result;
}

template<class Cell>
cherry_obj* list(std::vector<decltype(Cell{}.hd)> const& values) {
    cherry_obj* result = CHERRY_SCALAR(0);
    for (auto it = values.rbegin(); it != values.rend(); ++it) {
        auto* cell = reinterpret_cast<Cell*>(cherry_alloc(sizeof(Cell), 1));
        cell->hd = *it;
        cell->tl = result;
        result = &cell->hdr;
    }
    return result;
}

template<class Option>
Option some(decltype(Option{}.val.Some) value) {
    Option result{};
    result.tag = static_cast<decltype(result.tag)>(1);
    result.val.Some = value;
    return result;
}
}

extern "C" {
void checker_drop_marshaled(Z3Cherry_marshaled value);
void checker_drop_diagnostic(Z3ProofDocument_document_diagnostic value);
void checker_drop_sort(Z3AstTheory_sort value);
void checker_drop_native_sorts(Prims_list__native_sort value);
void checker_drop_asts(Prims_list__ast value);
void checker_drop_result(checker::Result value);
void checker_drop_ff_pac(FStar_Pervasives_Native_option__ff_pac_view value);
}
