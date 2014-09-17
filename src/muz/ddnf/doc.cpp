/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    doc.cpp

Abstract:

    difference of cubes.

Author:

    Nuno Lopes (a-nlopes) 2013-03-01
    Nikolaj Bjorner (nbjorner) 2014-09-15

Revision History:

    Based on ternary_diff_bitvector by Nuno Lopes.

--*/

#include "doc.h"
void doc_manager::reset() {
}
doc* doc_manager::allocate() {
    return 0;
}
doc* doc_manager::allocate1() {
    return 0;
}
doc* doc_manager::allocate0() {
    return 0;                                                
}
doc* doc_manager::allocateX() {
    return 0;
}
doc* doc_manager::allocate(doc const& src) {
    return 0;
}
doc* doc_manager::allocate(uint64 n) {
    return 0;
}
doc* doc_manager::allocate(rational const& r) {
    return 0;
}
doc* doc_manager::allocate(uint64 n, unsigned hi, unsigned lo) {
    return 0;
}
doc* doc_manager::allocate(doc, unsigned const* permutation) {
    return 0;
}
void doc_manager::deallocate(doc* src) {
}
void doc_manager::copy(doc& dst, doc const& src) const {
}
doc& doc_manager::fill0(doc& src) const {
    return src;
}
doc& doc_manager::fill1(doc& src) const {
    return src;
}
doc& doc_manager::fillX(doc& src) const {
    return src;
}
bool doc_manager::set_and(doc& dst, doc const& src) const {
    return false;
}
void doc_manager::complement(doc const& src, ptr_vector<doc>& result) {
}
void doc_manager::subtract(doc const& A, doc const& B, ptr_vector<doc>& result) {
}
bool doc_manager::equals(doc const& a, doc const& b) const {
    return false;
}
bool doc_manager::is_full(doc const& src) const {
    return false;
}
unsigned doc_manager::hash(doc const& src) const {
    return 0;
}
bool doc_manager::contains(doc const& a, doc const& b) const {
    return false;
}
std::ostream& doc_manager::display(std::ostream& out, doc const& b) const {
    return out;
}

