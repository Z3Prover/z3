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
  See the longer description in euf_proof_checker.cpp

--*/

#pragma once

#include "util/dependency.h"

namespace euf {

    class enode;

    typedef int theory_var;
    typedef int theory_id;
    const theory_var null_theory_var = -1;
    const theory_id null_theory_id = -1;

    class justification {
    public:
        typedef stacked_dependency_manager<justification>             dependency_manager;
        typedef stacked_dependency_manager<justification>::dependency dependency;
    private:
        enum class kind_t {
            axiom_t, 
            congruence_t, 
            external_t,
            dependent_t,
            equality_t
        };
        kind_t m_kind;
        union {
            int    m_theory_id;
            bool   m_comm;
            enode* m_n1;
        };
        union {
            void*    m_external;
            uint64_t m_timestamp;
            dependency* m_dependency;
            enode* m_n2;
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

        justification(dependency* dep, int):
            m_kind(kind_t::dependent_t),
            m_comm(false),
            m_dependency(dep)
        {}

        justification(enode* n1, enode* n2):
            m_kind(kind_t::equality_t),
            m_n1(n1),
            m_n2(n2)
        {}

        justification(int theory_id):
            m_kind(kind_t::axiom_t),
            m_theory_id(theory_id),
            m_external(nullptr)
        {}

    public:

        justification():
            m_kind(kind_t::axiom_t),
            m_theory_id(null_theory_id),
            m_external(nullptr)
        {}

        static justification axiom(int theory_id) { return justification(theory_id); }
        static justification congruence(bool c, uint64_t ts) { return justification(c, ts); }
        static justification external(void* ext) { return justification(ext); }
        static justification dependent(dependency* d) { return justification(d, 1); }
        static justification equality(enode* a, enode* b) { return justification(a, b); }
        
        bool   is_axiom() const { return m_kind == kind_t::axiom_t; }
        bool   is_external() const { return m_kind == kind_t::external_t; }
        bool   is_congruence() const { return m_kind == kind_t::congruence_t; }
        bool   is_commutative() const { return m_comm; }
        bool   is_dependent() const { return m_kind == kind_t::dependent_t; }
        bool   is_equality() const { return m_kind == kind_t::equality_t; }
        dependency* get_dependency() const { SASSERT(is_dependent());  return m_dependency; }
        enode* lhs() const { SASSERT(is_equality()); return m_n1; }
        enode* rhs() const { SASSERT(is_equality()); return m_n2; }
        uint64_t timestamp() const { SASSERT(is_congruence()); return m_timestamp; }
        theory_id get_theory_id() const { SASSERT(is_axiom()); return m_theory_id; }
        template <typename T>
        T*  ext() const { SASSERT(is_external()); return static_cast<T*>(m_external); }            

        justification copy(std::function<void*(void*)>& copy_justification) const {
            switch (m_kind) {
            case kind_t::external_t:
                return external(copy_justification(m_external));
            case kind_t::axiom_t:
                return axiom(m_theory_id);
            case kind_t::congruence_t:
                return congruence(m_comm, m_timestamp);
            case kind_t::dependent_t:
                NOT_IMPLEMENTED_YET();
                return dependent(m_dependency);
            default:
                UNREACHABLE();
                return axiom(-1);
            }
        }

        std::ostream& display(std::ostream& out, std::function<void(std::ostream&, void*)> const& ext) const;

    };

    inline std::ostream& operator<<(std::ostream& out, justification const& j) {
        return j.display(out, nullptr);
    }
}
