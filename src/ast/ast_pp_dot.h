/*++

Abstract: Pretty-printer for proofs in Graphviz format

--*/

#pragma once

#include <iostream>
#include "ast_pp.h"

class ast_pp_dot {
    ast_manager &       m_manager;
    proof * const       m_pr;

  public:
    ast_pp_dot(proof *pr, ast_manager &m) : m_manager(m), m_pr(pr) {}
    ast_pp_dot(proof_ref &e) : m_manager(e.m()), m_pr(e.get()) {}
    
    std::ostream & pp(std::ostream & out) const;
    ast_manager & get_manager() const { return m_manager; }
};

std::ostream &operator<<(std::ostream &out, const ast_pp_dot & p);