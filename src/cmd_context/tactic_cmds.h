/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    tactic_cmds.h

Abstract:
    Support for tactics in SMT 2.0 frontend.

Author:

    Leonardo (leonardo) 2011-11-20

Notes:

--*/
#ifndef TACTIC_CMDS_H_
#define TACTIC_CMDS_H_

#include"ast.h"
#include"cmd_context_types.h"
#include"ref.h"

class tactic;
class probe;
class tactic_factory;

class tactic_cmd {
    symbol           m_name;
    char const *     m_descr;
    tactic_factory * m_factory;
public:
    tactic_cmd(symbol const & n, char const * d, tactic_factory * f):
        m_name(n), m_descr(d), m_factory(f) {
        SASSERT(m_factory);
    }

    ~tactic_cmd();

    symbol get_name() const { return m_name; }
    
    char const * get_descr() const { return m_descr; }
    
    tactic * mk(ast_manager & m);
};

void install_core_tactic_cmds(cmd_context & ctx);
tactic * sexpr2tactic(cmd_context & ctx, sexpr * n);

class probe_info {
    symbol           m_name;
    char const *     m_descr;
    ref<probe>       m_probe;
public:
    probe_info(symbol const & n, char const * d, probe * p);
    ~probe_info();

    symbol get_name() const { return m_name; }
    char const * get_descr() const { return m_descr; }
    
    probe * get() const { return m_probe.get(); }
};

probe * sexpr2probe(cmd_context & ctx, sexpr * n);

#endif
