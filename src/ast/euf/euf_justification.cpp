/*++
Copyright (c) 2020 Microsoft Corporation

Module Name:

    euf_justification.cpp

Abstract:

    justification structure for euf

Author:

    Nikolaj Bjorner (nbjorner) 2020-08-23

--*/


#include "ast/euf/euf_justification.h"
#include "ast/euf/euf_enode.h"

namespace euf {


    std::ostream& justification::display(std::ostream& out, std::function<void (std::ostream&, void*)> const& ext) const {
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
        case kind_t::dependent_t: {
            vector<justification, false> js;                
            out << "dependent";
            for (auto const& j : dependency_manager::s_linearize(m_dependency, js))
                j.display(out << " ", ext);
            return out;
        }
        case kind_t::equality_t: 
            return out << "equality #" << m_n1->get_id() << " == #" << m_n2->get_id();
            
        default:
            UNREACHABLE();
            return out;
        }
        return out;
    }

}
