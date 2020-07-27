/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    ref_util.h

Abstract:

    Some goodies for managing reference counters.

Author:

    Leonardo (leonardo) 2011-06-07

Notes:

--*/
#pragma once

/**
   \brief Decrement the reference counter of the keys and values stored in the map,
   then reset the map.
*/
template<typename Mng1, typename Mng2, typename Map>
void dec_ref_map_key_values(Mng1 & m1, Mng2 & m2, Map & map) {
    typename Map::iterator it  = map.begin();
    typename Map::iterator end = map.end();
    for (; it != end; ++it) {
        m1.dec_ref(it->m_key);
        m2.dec_ref(it->m_value);
    }
    map.reset();
}

/**
   \brief Decrement the reference counter of the keys and values stored in the map,
   then reset the map.
*/
template<typename Mng, typename Map>
void dec_ref_map_key_values(Mng & m, Map & map) {
    dec_ref_map_key_values(m, m, map);
}

/**
   \brief Decrement the reference counter of the keys stored in the map,
   then reset the map.
*/
template<typename Mng, typename Map>
void dec_ref_map_keys(Mng & m, Map & map) {
    typename Map::iterator it  = map.begin();
    typename Map::iterator end = map.end();
    for (; it != end; ++it) {
        m.dec_ref(it->m_key);
    }
    map.reset();
}


/**
   \brief Decrement the reference counter of the values stored in the map,
   then reset the map.
*/
template<typename Mng, typename Map>
void dec_ref_map_values(Mng & m, Map & map) {
    typename Map::iterator it  = map.begin();
    typename Map::iterator end = map.end();
    for (; it != end; ++it) {
        m.dec_ref(it->m_value);
    }
    map.reset();
}


/**
   \brief Decrement the reference counter of the values stored in the map,
   then reset the map.
*/
template<typename Mng, typename C>
void dec_ref_collection_values(Mng & m, C & c) {
    typename C::iterator it  = c.begin();
    typename C::iterator end = c.end();
    for (; it != end; ++it) {
        m.dec_ref(*it);
    }
    c.reset();
}


