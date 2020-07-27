/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    scoped_proof.h

Abstract:

    Scoped proof environments. Toggles enabling proofs.

Author:

    Nikolaj Bjorner (nbjorner) 2013-08-28

Revision History:

--*/
#pragma once

#include "ast/ast.h"

class scoped_proof_mode {
    ast_manager&   m;
    proof_gen_mode m_mode;
public:
    scoped_proof_mode(ast_manager& m, proof_gen_mode mode): m(m) {
        m_mode = m.proof_mode();
        m.toggle_proof_mode(mode);
    }
    ~scoped_proof_mode() {
            m.toggle_proof_mode(m_mode);            
        }
    
};

class scoped_proof : public scoped_proof_mode {
public:
    scoped_proof(ast_manager& m): scoped_proof_mode(m, PGM_ENABLED) {}
};

class scoped_no_proof : public scoped_proof_mode {
public:
    scoped_no_proof(ast_manager& m): scoped_proof_mode(m, PGM_DISABLED) {}
};

class scoped_restore_proof : public scoped_proof_mode {
public:
    scoped_restore_proof(ast_manager& m): scoped_proof_mode(m, m.proof_mode()) {}
};



