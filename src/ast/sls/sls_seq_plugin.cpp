/*++
Copyright (c) 2024 Microsoft Corporation

Module Name:

    sls_seq_plugin.cpp

Abstract:

    Sequence/String SLS
    
Author:

    Nikolaj Bjorner (nbjorner) 2024-11-22
    
--*/

#include "ast/sls/sls_seq_plugin.h"
#include "ast/sls/sls_context.h"


namespace sls {
    
    seq_plugin::seq_plugin(context& c):
        plugin(c),
        seq(c.get_manager())
    {}
    
    void seq_plugin::propagate_literal(sat::literal lit) {
    }
    
    expr_ref seq_plugin::get_value(expr* e) {
        return expr_ref(m);
    }
    
    bool seq_plugin::propagate() {
        return false;
    }
    
    bool seq_plugin::is_sat() {
        return true;
    }
    
    void seq_plugin::register_term(expr* e) {
    }
    
    std::ostream& seq_plugin::display(std::ostream& out) const {
        return out;
    }
    
    bool seq_plugin::set_value(expr* e, expr* v) {
        return false;
    }

    zstring& seq_plugin::strval0(expr* e) {
        SASSERT(seq.is_string(e->get_sort()));
        unsigned id = e->get_id();
        m_values.reserve(id + 1);
        if (!m_values[id]) 
            m_values.set(id, alloc(eval, m));
        return m_values[id]->val0.svalue;
    }

    bool seq_plugin::bval1(expr* e) {
        SASSERT(is_app(e));
        if (to_app(e)->get_family_id() == seq.get_family_id())
            return bval1_seq(to_app(e));

        NOT_IMPLEMENTED_YET();
        return false;
    }

    bool seq_plugin::bval1_seq(app* e) {
        expr* a, *b;
        switch (e->get_decl_kind()) {
        case OP_SEQ_CONTAINS: {
            VERIFY(seq.str.is_contains(e, a, b));
            if (seq.is_string(a->get_sort())) 
                return strval0(a).contains(strval0(b));
            else {
                NOT_IMPLEMENTED_YET();
            }
            break;
        }
        case OP_SEQ_PREFIX:
        case OP_SEQ_SUFFIX:
        case OP_SEQ_NTH:
        case OP_SEQ_NTH_I:
        case OP_SEQ_NTH_U:
        case OP_SEQ_IN_RE:
        case OP_SEQ_FOLDL:
        case OP_SEQ_FOLDLI:
        case OP_STRING_LT:
        case OP_STRING_LE:
        case OP_STRING_IS_DIGIT:
            NOT_IMPLEMENTED_YET();
            break;
        default:
            break;
        }
        return false;
    }

    zstring const& seq_plugin::strval1(expr* e) {
        SASSERT(is_app(e));
        SASSERT(seq.is_string(e->get_sort()));
        if (to_app(e)->get_family_id() == seq.get_family_id()) {
            switch (to_app(e)->get_decl_kind()) {
            case OP_SEQ_UNIT:
            case OP_SEQ_EMPTY:
            case OP_SEQ_CONCAT:
            case OP_SEQ_EXTRACT:
            case OP_SEQ_REPLACE:
            case OP_SEQ_AT:
            case OP_SEQ_NTH:
            case OP_SEQ_NTH_I:
            case OP_SEQ_NTH_U:
            case OP_SEQ_LENGTH:
            case OP_SEQ_INDEX:
            case OP_SEQ_LAST_INDEX:
            case OP_SEQ_TO_RE:
            case OP_SEQ_IN_RE:
            case OP_SEQ_REPLACE_RE_ALL:
            case OP_SEQ_REPLACE_RE:
            case OP_SEQ_REPLACE_ALL:
            case OP_SEQ_MAP:
            case OP_SEQ_MAPI:
            case OP_SEQ_FOLDL:
            case OP_SEQ_FOLDLI:           
            case OP_RE_PLUS:            
            case OP_RE_STAR:
            case OP_RE_OPTION:
            case OP_RE_RANGE:
            case OP_RE_CONCAT:
            case OP_RE_UNION:
            case OP_RE_DIFF:
            case OP_RE_INTERSECT:
            case OP_RE_LOOP:
            case OP_RE_POWER:
            case OP_RE_COMPLEMENT:
            case OP_RE_EMPTY_SET:
            case OP_RE_FULL_SEQ_SET:
            case OP_RE_FULL_CHAR_SET:
            case OP_RE_OF_PRED:
            case OP_RE_REVERSE:
            case OP_RE_DERIVATIVE:
            case OP_STRING_CONST:
            case OP_STRING_ITOS:
            case OP_STRING_STOI:
            case OP_STRING_UBVTOS:
            case OP_STRING_SBVTOS:
            case OP_STRING_LT:
            case OP_STRING_LE:
            case OP_STRING_IS_DIGIT:
            case OP_STRING_TO_CODE:
            case OP_STRING_FROM_CODE:
                NOT_IMPLEMENTED_YET();
                break;
            default:
                UNREACHABLE();
                break;
            }
        }
        auto const& v = strval0(e);
        m_values[e->get_id()]->val1.svalue = v;
        return m_values[e->get_id()]->val1.svalue;
    }
    
    void seq_plugin::repair_up(app* e) {
    }
    
    bool seq_plugin::repair_down(app* e) {
        switch (e->get_decl_kind()) {
        case OP_SEQ_UNIT:
        case OP_SEQ_EMPTY:
        case OP_SEQ_CONCAT:
        case OP_SEQ_PREFIX:
        case OP_SEQ_SUFFIX:
        case OP_SEQ_CONTAINS:
            return repair_contains(e);
        case OP_SEQ_EXTRACT:
        case OP_SEQ_REPLACE:
        case OP_SEQ_AT:
        case OP_SEQ_NTH:
        case OP_SEQ_NTH_I:
        case OP_SEQ_NTH_U:
        case OP_SEQ_LENGTH:
        case OP_SEQ_INDEX:
        case OP_SEQ_LAST_INDEX:
        case OP_SEQ_TO_RE:
        case OP_SEQ_IN_RE:
        case OP_SEQ_REPLACE_RE_ALL:
        case OP_SEQ_REPLACE_RE:
        case OP_SEQ_REPLACE_ALL:
        case OP_SEQ_MAP:
        case OP_SEQ_MAPI:
        case OP_SEQ_FOLDL:
        case OP_SEQ_FOLDLI:           
        case OP_RE_PLUS:            
        case OP_RE_STAR:
        case OP_RE_OPTION:
        case OP_RE_RANGE:
        case OP_RE_CONCAT:
        case OP_RE_UNION:
        case OP_RE_DIFF:
        case OP_RE_INTERSECT:
        case OP_RE_LOOP:
        case OP_RE_POWER:
        case OP_RE_COMPLEMENT:
        case OP_RE_EMPTY_SET:
        case OP_RE_FULL_SEQ_SET:
        case OP_RE_FULL_CHAR_SET:
        case OP_RE_OF_PRED:
        case OP_RE_REVERSE:
        case OP_RE_DERIVATIVE:
        case OP_STRING_CONST:
        case OP_STRING_ITOS:
        case OP_STRING_STOI:
        case OP_STRING_UBVTOS:
        case OP_STRING_SBVTOS:
        case OP_STRING_LT:
        case OP_STRING_LE:
        case OP_STRING_IS_DIGIT:
        case OP_STRING_TO_CODE:
        case OP_STRING_FROM_CODE:
        default:
            break;                      
        }
        return false;
    }

    bool seq_plugin::repair_contains(expr* e) {
        expr* a, *b;
        VERIFY(seq.str.is_contains(e, a, b));
        zstring sa = strval0(a);
        zstring sb = strval0(b);
        unsigned lena = sa.length();
        unsigned lenb = sb.length();

        m_str_updates.reset();
        if (ctx.is_true(e)) {            
            // add b to a in front
            // add b to a in back
            // add part of b to a front/back
            // take random subsequence of a and set it to b
            // reduce size of b

            m_str_updates.push_back({ a, sb + sa, 1 });
            m_str_updates.push_back({ a, sa + sb, 1 });
            if (lena > 1) {
                unsigned mid = ctx.rand(lena-2) + 1;
                zstring sa1 = sa.extract(0, mid);
                zstring sa2 = sa.extract(mid, lena - mid); 
                m_str_updates.push_back({ a, sa1 + sb + sa2, 1});
            }
            if (lenb > 0) {
                m_str_updates.push_back({ b, sb.extract(0, lenb-1), 1});
                m_str_updates.push_back({ b, sb.extract(1, lenb-1), 1});
            }
        }
        else {
            // remove occurrences of b in a, if b is non-empty
            // append character to b
            // set b to be a + character
            // 
        }
        return apply_str_update();
    }

    bool seq_plugin::apply_str_update() {
        double sum_scores = 0;
        for (auto const& [e, val, score] : m_str_updates)
            sum_scores += score;
        
        while (!m_str_updates.empty()) {
            unsigned i = m_str_updates.size();
            double lim = sum_scores * ((double)ctx.rand() / random_gen().max_value());
            do {
                lim -= m_str_updates[--i].m_score;
            }
            while (lim >= 0 && i > 0);
            
            auto [e, value, score] = m_str_updates[i];

            if (update(e, value))
                return true;

            sum_scores -= score;
            m_str_updates[i] = m_str_updates.back();
            m_str_updates.pop_back();
        }

        return false;
    }

    bool seq_plugin::update(expr* e, zstring const& value) {
        strval0(e) = value;
        ctx.new_value_eh(e);
        return true;
    }

    
    void seq_plugin::repair_literal(sat::literal lit) {
    }
    
}
