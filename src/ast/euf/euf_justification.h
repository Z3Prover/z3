/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    euf_justification.h

Abstract:

    justification structure for euf

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-23

Notes:

- congruence closure justifications are given a timestamp so it is easy to sort them.
  See the longer descriptoin in euf_proof_checker.cpp

--*/

#pragma once

namespace euf {

    class justification {
        enum class kind_t {
            axiom_t, 
            congruence_t, 
            external_t
        };
        kind_t m_kind;
        bool   m_comm;
        union {
            void*    m_external;
            uint64_t m_timestamp;
        };

        justification(bool comm, uint64_t ts):
            m_kind(kind_t::congruence_t),
            m_comm(comm),
            m_timestamp(ts)
        {}

        justification(void* ext):
            m_kind(kind_t::external_t),
            m_comm(false),
            m_external(ext)
        {}

    public:
        justification():
            m_kind(kind_t::axiom_t),
            m_comm(false),
            m_external(nullptr)
        {}

        static justification axiom() { return justification(); }
        static justification congruence(bool c, uint64_t ts) { return justification(c, ts); }
        static justification external(void* ext) { return justification(ext); }
        
        bool   is_external() const { return m_kind == kind_t::external_t; }
        bool   is_congruence() const { return m_kind == kind_t::congruence_t; }
        bool   is_commutative() const { return m_comm; }
        uint64_t timestamp() const { SASSERT(is_congruence()); return m_timestamp; }
        template <typename T>
        T*  ext() const { SASSERT(is_external()); return static_cast<T*>(m_external); }            

        justification copy(std::function<void*(void*)>& copy_justification) const {
            switch (m_kind) {
            case kind_t::external_t:
                return external(copy_justification(m_external));
            case kind_t::axiom_t:
                return axiom();
            case kind_t::congruence_t:
                return congruence(m_comm, m_timestamp);
            default:
                UNREACHABLE();
                return axiom();
            }
        }

        std::ostream& display(std::ostream& out, std::function<void (std::ostream&, void*)> const& ext) const {
            switch (m_kind) {
            case kind_t::external_t:
                if (ext)
                    ext(out, m_external);
                else
                    out << "external";
                return out;
            case kind_t::axiom_t:
                return out << "axiom";
            case kind_t::congruence_t:
                return out << "congruence";
            default:
                UNREACHABLE();
                return out;
            }
            return out;
        }
    };

    inline std::ostream& operator<<(std::ostream& out, justification const& j) {
        return j.display(out, nullptr);
    }
}
