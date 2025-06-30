/*++
Copyright (c) 2006 Microsoft Corporation

Module Name:

    smtlib_frontend.h

Abstract:

    Smtlib frontend.

Author:

    Leonardo de Moura (leonardo) 2006-11-2.

Revision History:

--*/
#pragma once

namespace smt { class context; }

unsigned read_smtlib_file(char const * benchmark_file);
unsigned read_smtlib2_commands(char const * command_file);
void help_tactics();
void help_simplifiers();
void help_probes();
void help_tactic(char const* name, bool markdown);
void help_simplifier(char const* name, bool markdown);

// Functions to register/unregister the active SMT context for timeout handling
void register_smt_context(smt::context* ctx);
void unregister_smt_context();


