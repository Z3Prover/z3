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
    SASSERT(node.prev() == &node);
    std::cout << "test_prev passed." << std::endl;
}

// Test the next() method
static void test_next() {
    TestNode node(1);
    SASSERT(node.next() == &node);
    std::cout << "test_next passed." << std::endl;
}

// Test the const prev() method
static void test_const_prev() {
    const TestNode node(1);
    SASSERT(node.prev() == &node);
    std::cout << "test_const_prev passed." << std::endl;
}

// Test the const next() method
static void test_const_next() {
    const TestNode node(1);
    SASSERT(node.next() == &node);
    std::cout << "test_const_next passed." << std::endl;
}

// Test the init() method
static void test_init() {
    TestNode node(1);
    node.init(&node);
    SASSERT(node.next() == &node);
    SASSERT(node.prev() == &node);
    SASSERT(node.invariant());
    std::cout << "test_init passed." << std::endl;
}

// Test the pop() method
static void test_pop() {
    TestNode* list = nullptr;
    TestNode node1(1);
    TestNode::push_to_front(list, &node1);
    TestNode* popped = TestNode::pop(list);
    SASSERT(popped == &node1);
    SASSERT(list == nullptr);
    SASSERT(popped->next() == popped);
    SASSERT(popped->prev() == popped);
    std::cout << "test_pop passed." << std::endl;
}

// Test the insert_after() method
static void test_insert_after() {
    TestNode node1(1);
    TestNode node2(2);
    node1.insert_after(&node2);
    SASSERT(node1.next() == &node2);
    SASSERT(node2.prev() == &node1);
    SASSERT(node1.prev() == &node2);
    SASSERT(node2.next() == &node1);
    SASSERT(node1.invariant());
    SASSERT(node2.invariant());
    std::cout << "test_insert_after passed." << std::endl;
}

// Test the insert_before() method
static void test_insert_before() {
    TestNode node1(1);
    TestNode node2(2);
    node1.insert_before(&node2);
    SASSERT(node1.prev() == &node2);
    SASSERT(node2.next() == &node1);
    SASSERT(node1.next() == &node2);
    SASSERT(node2.prev() == &node1);
    SASSERT(node1.invariant());
    SASSERT(node2.invariant());
    std::cout << "test_insert_before passed." << std::endl;
}

#if 0
// Test the remove_from() method
static void test_remove_from() {
    TestNode* list = nullptr;
    TestNode node1(1);
    TestNode node2(2);
    TestNode::push_to_front(list, &node1);
    TestNode::push_to_front(list, &node2);
    TestNode::remove_from(list, &node1);
    SASSERT(list == &node2);
    SASSERT(node2.next() == &node2);
    SASSERT(node2.prev() == &node2);
    std::cout << "test_remove_from passed." << std::endl;
}
#endif

// Test the push_to_front() method
static void test_push_to_front() {
    TestNode* list = nullptr;
    TestNode node1(1);
    TestNode::push_to_front(list, &node1);
    SASSERT(list == &node1);
    SASSERT(node1.next() == &node1);
    SASSERT(node1.prev() == &node1);
    std::cout << "test_push_to_front passed." << std::endl;
}

// Test the detach() method
static void test_detach() {
    TestNode node(1);
    TestNode::detach(&node);
    SASSERT(node.next() == &node);
    SASSERT(node.prev() == &node);
    SASSERT(node.invariant());
    std::cout << "test_detach passed." << std::endl;
}

// Test the invariant() method
static void test_invariant() {
    TestNode node1(1);
    SASSERT(node1.invariant());
    TestNode node2(2);
    node1.insert_after(&node2);
    SASSERT(node1.invariant());
    SASSERT(node2.invariant());
    std::cout << "test_invariant passed." << std::endl;
}

// Test the contains() method
static void test_contains() {
    TestNode* list = nullptr;
    TestNode node1(1);
    TestNode node2(2);
    TestNode::push_to_front(list, &node1);
    TestNode::push_to_front(list, &node2);
    SASSERT(TestNode::contains(list, &node1));
    SASSERT(TestNode::contains(list, &node2));
    TestNode node3(3);
    SASSERT(!TestNode::contains(list, &node3));
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
    test_push_to_front();
    test_detach();
    test_invariant();
    test_contains();
    //test_remove_from;
    std::cout << "All tests passed." << std::endl;
}
