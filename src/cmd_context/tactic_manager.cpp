/*++
Copyright (c) 2012 Microsoft Corporation

Module Name:

    tactic_manager.cpp

Abstract:

    Collection of tactics, simplifiers & probes

Author:

    Leonardo (leonardo) 2012-03-06

Notes:

--*/
#include "cmd_context/tactic_manager.h"
#include "tactic/tactic.h"

// Self-registration (Z3_ADD_TACTIC/Z3_ADD_PROBE/Z3_ADD_SIMPLIFIER) happens in an inline
// global in each header. In static builds an object file is only linked in if something
// references it, so every registering header must be included from this always-linked
// translation unit (the registered factory then also retains the implementation).
// This header is generated at build time from the REGISTRATION_HEADERS of every
// z3_add_component() (see cmake/z3_generate_registrations.cmake).
#include "z3_registrations.h"

tactic_manager::~tactic_manager() {
    finalize_tactic_manager();
}

void tactic_manager::finalize_tactic_manager() {
    std::for_each(m_tactics.begin(), m_tactics.end(), delete_proc<tactic_cmd>());
    m_tactics.reset();
    m_name2tactic.reset();

    std::for_each(m_simplifiers.begin(), m_simplifiers.end(), delete_proc<simplifier_cmd>());
    m_simplifiers.reset();
    m_name2simplifier.reset();

    std::for_each(m_probes.begin(), m_probes.end(), delete_proc<probe_info>());
    m_probes.reset();
    m_name2probe.reset();
}

void tactic_manager::insert(tactic_cmd * c) {
    symbol const & s = c->get_name();
    SASSERT(!m_name2tactic.contains(s));
    m_name2tactic.insert(s, c);
    m_tactics.push_back(c);
}

void tactic_manager::insert(simplifier_cmd * c) {
    symbol const & s = c->get_name();
    SASSERT(!m_name2simplifier.contains(s));
    m_name2simplifier.insert(s, c);
    m_simplifiers.push_back(c);
}

void tactic_manager::insert(probe_info * p) {
    symbol const & s = p->get_name();
    SASSERT(!m_name2probe.contains(s));
    m_name2probe.insert(s, p);
    m_probes.push_back(p);
}

tactic_cmd * tactic_manager::find_tactic_cmd(symbol const & s) const {
    tactic_cmd * c = nullptr;
    m_name2tactic.find(s, c);
    return c;
}

simplifier_cmd * tactic_manager::find_simplifier_cmd(symbol const & s) const {
    simplifier_cmd * c = nullptr;
    m_name2simplifier.find(s, c);
    return c;
}

probe_info * tactic_manager::find_probe(symbol const & s) const {
    probe_info * p = nullptr;
    m_name2probe.find(s, p);
    return p;
}

void install_tactics(tactic_manager & ctx) {
    for (auto * r = tactic_registration::g_head; r; r = r->next)
        ctx.insert(alloc(tactic_cmd, symbol(r->name), r->descr, r->factory));
    for (auto * r = probe_registration::g_head; r; r = r->next)
        ctx.insert(alloc(probe_info, symbol(r->name), r->descr, r->factory()));
    for (auto * r = simplifier_registration::g_head; r; r = r->next)
        ctx.insert(alloc(simplifier_cmd, symbol(r->name), r->descr, r->factory));
}

