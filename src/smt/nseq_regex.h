/*++
Copyright (c) 2026 Microsoft Corporation

Module Name:

    nseq_regex.h

Abstract:

    Regex membership handling using Brzozowski derivatives.
    Processes str_mem constraints after character consumption.

Author:

    Nikolaj Bjorner (nbjorner) 2026-03-01

--*/
#pragma once

#include "ast/euf/euf_sgraph.h"
#include "smt/seq/seq_nielsen.h"

namespace smt {

    class nseq_regex {
        euf::sgraph& m_sg;

    public:
        nseq_regex(euf::sgraph& sg) : m_sg(sg) {}

        // check if a regex snode represents the empty language
        bool is_empty_regex(euf::snode* re) const {
            return re && re->is_fail();
        }

        // compute derivative of regex re with respect to char elem and
        // return a new str_mem for the resulting constraint
        seq::str_mem derive(seq::str_mem const& mem, euf::snode* elem) {
            euf::snode* deriv = m_sg.brzozowski_deriv(mem.m_regex, elem);
            euf::snode* new_str = m_sg.drop_first(mem.m_str);
            return seq::str_mem(new_str, deriv, mem.m_history, mem.m_id, mem.m_dep);
        }

        // process a regex membership constraint after one character has been consumed
        // returns false if the resulting regex is empty (conflict)
        bool process_str_mem(seq::str_mem const& mem,
                              vector<seq::str_mem>& out_mems) {
            if (!mem.m_str || !mem.m_regex)
                return true;
            // if regex does not accept the empty string and the string side is empty, conflict
            if (mem.m_str->is_empty()) {
                return mem.m_regex->is_nullable();
            }
            // compute minterms for the regex
            euf::snode_vector minterms;
            m_sg.compute_minterms(mem.m_regex, minterms);
            for (euf::snode* ch : minterms) {
                seq::str_mem new_mem = derive(mem, ch);
                if (!is_empty_regex(new_mem.m_regex))
                    out_mems.push_back(new_mem);
            }
            return true;
        }
    };

}
