/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    act_cache.cpp

Abstract:

    expr -> expr activity cache
    It maintains at most N unused entries

Author:

    Leonardo (leonardo) 2011-04-12

Notes:

--*/
#include"act_cache.h"

#define MIN_MAX_UNUSED   1024
#define INITIAL_CAPACITY 128

/*
  This cache is a mapping from expr -> tagged expressions
  A tagged expression is essentially a pair (expr, flag)
  Thus, an entry
       t -> (s, 0)
  maps the key t to value s, and says that key t was never accessed.
  That is, client code never executed find(t)
  Similarly, an entry
       t -> (s, 1)
  also maps the key t to value s, but signs that key t was already accessed 
  by client code.

  When a new key/value pair is inserted the flag is 0.
  The flag is set to 1 after the key is accessed.

  The number of unused entries (m_unused) is equal to the number of entries
  of the form
       t -> (s, 0)
  That is, it is the number of keys that were never accessed by client code.
  
  The cache maintains at most m_max_unused entries.
  When the maximum number of unused entries exceeds m_max_unused, then
  the cache will delete the oldest unused entry.
*/

/**
   m_queue stores the recently added keys.
   The queue is implemented as pair: m_queue (vector), m_qhead (unsigned).
   The "active" part of m_queue is the range [m_qhead, m_queue.size())
   The "inactive" part [0, m_qhead) contains keys that were already used by client code.
   This procedure, deletes the inactive part, and makes m_qhead == 0.
*/
void act_cache::compress_queue() {
    SASSERT(m_qhead > 0);
    unsigned sz = m_queue.size();
    unsigned j = 0;
    for (unsigned i = m_qhead; i < sz; i++, j++) { 
        m_queue[j] = m_queue[i];
    }
    m_queue.shrink(j);
    m_qhead = 0;
}

void act_cache::init() {
    if (m_max_unused < MIN_MAX_UNUSED)
        m_max_unused = MIN_MAX_UNUSED;
    m_unused = 0;
    m_qhead = 0;
}

void act_cache::dec_refs() {
    map::iterator it  = m_table.begin();
    map::iterator end = m_table.end();
    for (; it != end; ++it) {
        m_manager.dec_ref((*it).m_key);
        m_manager.dec_ref(UNTAG(expr*, (*it).m_value));
    }
}

act_cache::act_cache(ast_manager & m):
    m_manager(m),
    m_max_unused(m.get_num_asts()) {
    init();
}

act_cache::act_cache(ast_manager & m, unsigned max_unused):
    m_manager(m),
    m_max_unused(max_unused) {
    init();
}
 
act_cache::~act_cache() {
    dec_refs();
}

/**
   \brief Search m_queue from [m_qhead, m_queue.size()) until it finds
   an unused key. That is a key associated with an entry
       key -> (value, 0)
*/
void act_cache::del_unused() {
    unsigned sz = m_queue.size();
    while (m_qhead < sz) {
        expr * k = m_queue[m_qhead];
        m_qhead++;
        SASSERT(m_table.contains(k));
        map::key_value * entry = m_table.find_core(k);
        SASSERT(entry);
        if (GET_TAG(entry->m_value) == 0) {
            // Key k was never accessed by client code.
            // That is, find(k) was never executed by client code.
            m_unused--;
            expr * v = entry->m_value;
            m_table.erase(k);
            m_manager.dec_ref(k);
            m_manager.dec_ref(v);
            break;
        }
    }
    if (m_qhead == sz) {
        // The "active" part of the queue is empty.
        // So, we perform a "cheap" compress.
        m_queue.reset();
        m_qhead = 0;
    }
    else if (m_qhead > m_max_unused) {
        compress_queue();
    }
}

/**
   \brief Insert a new entry k -> v into the cache.
*/
void act_cache::insert(expr * k, expr * v) {
    SASSERT(k);
    if (m_unused >= m_max_unused)
        del_unused();
    expr * dummy = reinterpret_cast<expr*>(1);
    map::key_value & entry = m_table.insert_if_not_there(k, dummy);
#if 0
    unsigned static counter = 0;
    counter++;
    if (counter % 100000 == 0)
        verbose_stream() << "[act-cache] counter: " << counter << " used_slots: " << m_table.used_slots() << " capacity: " << m_table.capacity() << " size: " << m_table.size() << " collisions: " << m_table.collisions() << "\n";
#endif

#ifdef Z3DEBUG
    unsigned expected_tag;
#endif
    if (entry.m_value == dummy) {
        // new entry;
        m_manager.inc_ref(k);
        m_manager.inc_ref(v);
        entry.m_value = v;
        m_queue.push_back(k);
        m_unused++;
        DEBUG_CODE(expected_tag = 0;); // new entry
    }
    else if (UNTAG(expr*, entry.m_value) == v) {
        // already there
        DEBUG_CODE(expected_tag = GET_TAG(entry.m_value);); 
    }
    else {
        // replacing old entry
        m_manager.inc_ref(v);
        m_manager.dec_ref(UNTAG(expr*, entry.m_value));
        entry.m_value = v;
        SASSERT(GET_TAG(entry.m_value) == 0);
        // replaced old entry, and reset the tag.
        DEBUG_CODE(expected_tag = 0;); 
    }
    DEBUG_CODE({
        expr * v2;
        SASSERT(m_table.find(k, v2));
        SASSERT(v == UNTAG(expr*, v2));
        SASSERT(expected_tag == GET_TAG(v2));
    });
}

/**
   \brief Search for key k in the cache.
   If entry k -> (v, tag) is found, we set tag to 1.
*/
expr * act_cache::find(expr * k) {
    map::key_value * entry = m_table.find_core(k);
    if (entry == 0)
        return 0;
    if (GET_TAG(entry->m_value) == 0) {
        entry->m_value = TAG(expr*, entry->m_value, 1);
        SASSERT(GET_TAG(entry->m_value) == 1);
        SASSERT(m_unused > 0);
        m_unused--;
        DEBUG_CODE({
            expr * v;
            SASSERT(m_table.find(k, v));
            SASSERT(GET_TAG(v) == 1);
        });
    }
    return UNTAG(expr*, entry->m_value);
}

void act_cache::reset() {
    dec_refs();
    m_table.reset();
    m_queue.reset();
    m_unused = 0;
    m_qhead = 0;
}

void act_cache::cleanup() {
    dec_refs();
    m_table.finalize();
    m_queue.finalize();
    m_unused = 0;
    m_qhead = 0;
}

bool act_cache::check_invariant() const {
    return true;
}
