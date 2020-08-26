/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    euf_justification.h

Abstract:

    justification structure for euf

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-23

--*/

#pragma once

namespace euf {

    class justification {
        enum kind_t {
            axiom_t, 
            congruence_t, 
            external_t
        };
        kind_t m_kind;
        bool   m_comm;
        void*  m_external;
        justification(bool comm):
            m_kind(congruence_t),
            m_comm(comm),
            m_external(nullptr)
        {}

        justification(void* ext):
            m_kind(external_t),
            m_comm(false),
            m_external(ext)
        {}

    public:
        justification():
            m_kind(axiom_t),
            m_comm(false),
            m_external(nullptr)
        {}

        static justification axiom() { return justification(); }
        static justification congruence(bool c) { return justification(c); }
        static justification external(void* ext) { return justification(ext); }
        
        bool   is_external() const { return m_kind == external_t; }
        bool   is_congruence() const { return m_kind == congruence_t; }
        bool   is_commutative() const { return m_comm; }
        template <typename T>
        T*  ext() const { SASSERT(is_external()); return static_cast<T*>(m_external); }            

        justification copy(std::function<void*(void*)>& copy_justification) const {
            switch (m_kind) {
            case external_t:
                return external(copy_justification(m_external));
            case axiom_t:
                return axiom();
            case congruence_t:
                return congruence(m_comm);
            default:
                UNREACHABLE();
                return axiom();
            }
        }
    };
}
