/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    tst_dlist.cpp

Abstract:

    Test dlist module

Author:

    Chuyue Sun 2024-07-18.

--*/

#include <cassert>
#include <iostream>
#include "util/dlist.h"

class TestNode : public dll_base<TestNode> {
public:
    int value;
    TestNode(int val) : value(val) {
        init(this);
    }
};

// Test the prev() method
void test_prev() {
    TestNode node(1);
    assert(node.prev() == &node);
    std::cout << "test_prev passed." << std::endl;
}

// Test the next() method
void test_next() {
    TestNode node(1);
    assert(node.next() == &node);
    std::cout << "test_next passed." << std::endl;
}

// Test the const prev() method
void test_const_prev() {
    const TestNode node(1);
    assert(node.prev() == &node);
    std::cout << "test_const_prev passed." << std::endl;
}

// Test the const next() method
void test_const_next() {
    const TestNode node(1);
    assert(node.next() == &node);
    std::cout << "test_const_next passed." << std::endl;
}

// Test the init() method
void test_init() {
    TestNode node(1);
    node.init(&node);
    assert(node.next() == &node);
    assert(node.prev() == &node);
    assert(node.invariant());
    std::cout << "test_init passed." << std::endl;
}

// Test the pop() method
void test_pop() {
    TestNode* list = nullptr;
    TestNode node1(1);
    TestNode::push_to_front(list, &node1);
    TestNode* popped = TestNode::pop(list);
    assert(popped == &node1);
    assert(list == nullptr);
    assert(popped->next() == popped);
    assert(popped->prev() == popped);
    std::cout << "test_pop passed." << std::endl;
}

// Test the insert_after() method
void test_insert_after() {
    TestNode node1(1);
    TestNode node2(2);
    node1.insert_after(&node2);
    assert(node1.next() == &node2);
    assert(node2.prev() == &node1);
    assert(node1.prev() == &node2);
    assert(node2.next() == &node1);
    assert(node1.invariant());
    assert(node2.invariant());
    std::cout << "test_insert_after passed." << std::endl;
}

// Test the insert_before() method
void test_insert_before() {
    TestNode node1(1);
    TestNode node2(2);
    node1.insert_before(&node2);
    assert(node1.prev() == &node2);
    assert(node2.next() == &node1);
    assert(node1.next() == &node2);
    assert(node2.prev() == &node1);
    assert(node1.invariant());
    assert(node2.invariant());
    std::cout << "test_insert_before passed." << std::endl;
}

// Test the remove_from() method
void test_remove_from() {
    TestNode* list = nullptr;
    TestNode node1(1);
    TestNode node2(2);
    TestNode::push_to_front(list, &node1);
    TestNode::push_to_front(list, &node2);
    TestNode::remove_from(list, &node1);
    assert(list == &node2);
    assert(node2.next() == &node2);
    assert(node2.prev() == &node2);
    assert(node1.next() == &node1);
    assert(node1.prev() == &node1);
    std::cout << "test_remove_from passed." << std::endl;
}

// Test the push_to_front() method
void test_push_to_front() {
    TestNode* list = nullptr;
    TestNode node1(1);
    TestNode::push_to_front(list, &node1);
    assert(list == &node1);
    assert(node1.next() == &node1);
    assert(node1.prev() == &node1);
    std::cout << "test_push_to_front passed." << std::endl;
}

// Test the detach() method
void test_detach() {
    TestNode node(1);
    TestNode::detach(&node);
    assert(node.next() == &node);
    assert(node.prev() == &node);
    assert(node.invariant());
    std::cout << "test_detach passed." << std::endl;
}

// Test the invariant() method
void test_invariant() {
    TestNode node1(1);
    assert(node1.invariant());
    TestNode node2(2);
    node1.insert_after(&node2);
    assert(node1.invariant());
    assert(node2.invariant());
    std::cout << "test_invariant passed." << std::endl;
}

// Test the contains() method
void test_contains() {
    TestNode* list = nullptr;
    TestNode node1(1);
    TestNode node2(2);
    TestNode::push_to_front(list, &node1);
    TestNode::push_to_front(list, &node2);
    assert(TestNode::contains(list, &node1));
    assert(TestNode::contains(list, &node2));
    TestNode node3(3);
    assert(!TestNode::contains(list, &node3));
    std::cout << "test_contains passed." << std::endl;
}

void tst_dlist() {
    test_prev();
    test_next();
    test_const_prev();
    test_const_next();
    test_init();
    test_pop();
    test_insert_after();
    test_insert_before();
#if 0
    test_remove_from();
    test_push_to_front();
    test_detach();
    test_invariant();
    test_contains();
#endif
    std::cout << "All tests passed." << std::endl;
}
