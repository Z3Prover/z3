/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    map_util.h

Abstract:

    Some goodies for managing reference counters
    stored in maps.

Author:

    Leonardo (leonardo) 2011-06-07

Notes:

--*/
#pragma once

/**
   \brief Decrement the reference counter of the keys and values stored in the map,
   then reset the map.
*/
template<typename Mng, typename Map>
void dec_ref_key_values(Mng & m, Map & map) {
    typename Map::iterator it  = map.begin();
    typename Map::iterator end = map.end();
    for (; it != end; ++it) {
        m.dec_ref(it->m_key);
        m.dec_ref(it->m_value);
    }
    map.reset();
}

/**
   \brief Decrement the reference counter of the keys stored in the map,
   then reset the map.
*/
template<typename Mng, typename Map>
void dec_ref_keys(Mng & m, Map & map) {
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
void dec_ref_values(Mng & m, Map & map) {
    typename Map::iterator it  = map.begin();
    typename Map::iterator end = map.end();
    for (; it != end; ++it) {
        m.dec_ref(it->m_value);
    }
    map.reset();
}


