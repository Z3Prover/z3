/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    tactic_manager.h

Abstract:
    Collection of tactics & probes

Author:

    Leonardo (leonardo) 2012-03-06

Notes:

--*/
#pragma once

#include "cmd_context/tactic_cmds.h"
#include "cmd_context/simplifier_cmds.h"
#include "util/dictionary.h"

class tactic_manager {
protected:
    dictionary<tactic_cmd*>  m_name2tactic;
    dictionary<probe_info*>  m_name2probe;
    dictionary<simplifier_cmd*> m_name2simplifier;
    ptr_vector<tactic_cmd>   m_tactics;
    ptr_vector<simplifier_cmd> m_simplifiers;
    ptr_vector<probe_info>   m_probes;
    void finalize_tactic_manager();
public:
    ~tactic_manager();

    void insert(tactic_cmd * c);
    void insert(simplifier_cmd* c);
    void insert(probe_info * p);
    tactic_cmd * find_tactic_cmd(symbol const & s) const; 
    probe_info * find_probe(symbol const & s) const;     
    simplifier_cmd* find_simplifier_cmd(symbol const& s) const;

    unsigned num_tactics() const { return m_tactics.size(); }
    unsigned num_probes() const { return m_probes.size(); }
    unsigned num_simplifiers() const { return m_simplifiers.size(); }
    tactic_cmd * get_tactic(unsigned i) const { return m_tactics[i]; }
    probe_info * get_probe(unsigned i) const { return m_probes[i]; }
    simplifier_cmd *get_simplifier(unsigned i) const { return m_simplifiers[i]; }

    ptr_vector<simplifier_cmd> const& simplifiers() const { return m_simplifiers; }
    ptr_vector<tactic_cmd> const& tactics() const { return m_tactics; }
    ptr_vector<probe_info> const& probes() const { return m_probes; }
};

// Populates ctx with every built-in tactic, probe, and simplifier that got linked into this
// binary, by walking tactic_registration::g_head / probe_registration::g_head /
// simplifier_registration::g_head (see tactic/tactic.h, tactic/probe.h,
// ast/simplifiers/dependent_expr_state.h). Called once per tactic_manager, i.e. once per Z3
// context -- replaces the old per-final-target generated install_tactic.cpp.
void install_tactics(tactic_manager & ctx);




