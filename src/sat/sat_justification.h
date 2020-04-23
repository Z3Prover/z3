/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    sat_justification.h

Abstract:

    Justifications for SAT assignments

Author:

    Leonardo de Moura (leonardo) 2011-05-21.

Revision History:

--*/
#ifndef SAT_JUSTIFICATIONS_H_
#define SAT_JUSTIFICATIONS_H_

namespace sat {
    
    class justification {
    public:
        enum kind { NONE, BINARY, TERNARY, CLAUSE, EXT_JUSTIFICATION };
    private:
        unsigned m_level;
        size_t m_val1;
        unsigned m_val2; 
        justification(unsigned lvl, ext_justification_idx idx, kind k):m_level(lvl), m_val1(idx), m_val2(k) {}
        unsigned val1() const { return static_cast<unsigned>(m_val1); }
    public:
        justification(unsigned lvl):m_level(lvl), m_val1(0), m_val2(NONE) {}
        explicit justification(unsigned lvl, literal l):m_level(lvl), m_val1(l.to_uint()), m_val2(BINARY) {}
        justification(unsigned lvl, literal l1, literal l2):m_level(lvl), m_val1(l1.to_uint()), m_val2(TERNARY + (l2.to_uint() << 3)) {}
        explicit justification(unsigned lvl, clause_offset cls_off):m_level(lvl), m_val1(cls_off), m_val2(CLAUSE) {}
        static justification mk_ext_justification(unsigned lvl, ext_justification_idx idx) { return justification(lvl, idx, EXT_JUSTIFICATION); }
        
        unsigned level() const { return m_level; }

        kind get_kind() const { return static_cast<kind>(m_val2 & 7); }
        
        bool is_none() const { return m_val2 == NONE; }
        
        bool is_binary_clause() const { return m_val2 == BINARY; }
        literal get_literal() const { SASSERT(is_binary_clause()); return to_literal(val1()); }

        bool is_ternary_clause() const { return get_kind() == TERNARY; }
        literal get_literal1() const { SASSERT(is_ternary_clause()); return to_literal(val1()); }
        literal get_literal2() const { SASSERT(is_ternary_clause()); return to_literal(m_val2 >> 3); }

        bool is_clause() const { return m_val2 == CLAUSE; }
        clause_offset get_clause_offset() const { return m_val1; }
        
        bool is_ext_justification() const { return m_val2 == EXT_JUSTIFICATION; }
        ext_justification_idx get_ext_justification_idx() const { return m_val1; }
    };

    inline std::ostream & operator<<(std::ostream & out, justification const & j) {
        switch (j.get_kind()) {
        case justification::NONE:
            out << "none";
            break;
        case justification::BINARY:
            out << "binary " << j.get_literal();
            break;
        case justification::TERNARY:
            out << "ternary " << j.get_literal1() << " " << j.get_literal2();
            break;
        case justification::CLAUSE:
            out << "clause";
            break;
        case justification::EXT_JUSTIFICATION:
            out << "external";
            break;
        }
        out << " @" << j.level();
        return out;
    }
};

#endif
