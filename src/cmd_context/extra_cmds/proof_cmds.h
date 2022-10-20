/*++
Copyright (c) 2022 Microsoft Corporation

Module Name:

    proof_cmds.h

Abstract:
    Commands for reading proofs.

Author:

    Nikolaj Bjorner (nbjorner) 2022-8-26

Notes:

--*/
#pragma once

/**
   proof_cmds is a structure that tracks an evidence trail.

   The main interface is to:
     add literals one by one,
     add proof hints
     until receiving end-command: assumption, learned, deleted.
   Evidence can be checked:
     - By DRUP
     - Theory lemmas

*/


class cmd_context;
void install_proof_cmds(cmd_context & ctx);
void init_proof_cmds(cmd_context& ctx);
