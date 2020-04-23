/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    theory_seq_empty.h

Abstract:

    <abstract>

Author:

    Nikolaj Bjorner (nbjorner) 2011-14-11

Revision History:

--*/
#ifndef SEQ_FACTORY_H_
#define SEQ_FACTORY_H_

#include "ast/seq_decl_plugin.h"
#include "model/model_core.h"

class seq_factory : public value_factory {
    typedef hashtable<symbol, symbol_hash_proc, symbol_eq_proc> symbol_set;
    model_core& m_model;
    ast_manager& m;
    seq_util     u;
    symbol_set   m_strings;
    unsigned     m_next;
    std::string  m_unique_delim;
    obj_map<sort, expr*> m_unique_sequences;
    expr_ref_vector m_trail;
public:
    
    seq_factory(ast_manager & m, family_id fid, model_core& md):
        value_factory(m, fid),
        m_model(md),
        m(m),
        u(m),
        m_next(0),
        m_unique_delim("!"),
        m_trail(m)
    {
        m_strings.insert(symbol(""));
        m_strings.insert(symbol("a"));
        m_strings.insert(symbol("b"));
    }
    
    void add_trail(expr* e) {
        m_trail.push_back(e);
    }
    
    void set_prefix(char const* p) {
        m_unique_delim = p;
    }
    
    // generic method for setting unique sequences
    void set_prefix(expr* uniq) {
        m_trail.push_back(uniq);
        m_unique_sequences.insert(m.get_sort(uniq), uniq);
    }
    
    expr* get_some_value(sort* s) override {
        if (u.is_seq(s)) {
            return u.str.mk_empty(s);
        }
        sort* seq = nullptr;
        if (u.is_re(s, seq)) {
            return u.re.mk_to_re(u.str.mk_empty(seq));
        }
        UNREACHABLE();
        return nullptr;
    }
    bool get_some_values(sort* s, expr_ref& v1, expr_ref& v2) override {
        if (u.is_string(s)) {
            v1 = u.str.mk_string(symbol("a"));
            v2 = u.str.mk_string(symbol("b"));
            return true;
        }
        sort* ch;
        if (u.is_seq(s, ch)) {
            if (m_model.get_some_values(ch, v1, v2)) {
                v1 = u.str.mk_unit(v1);
                v2 = u.str.mk_unit(v2);
                return true;
            }
            else {
                    return false;
            }
        }
        NOT_IMPLEMENTED_YET();
        return false; 
    }
    expr* get_fresh_value(sort* s) override {
        if (u.is_string(s)) {
            while (true) {
                std::ostringstream strm;
                strm << m_unique_delim << std::hex << m_next++ << std::dec << m_unique_delim;
                symbol sym(strm.str().c_str());
                if (m_strings.contains(sym)) continue;
                m_strings.insert(sym);
                return u.str.mk_string(sym);
            }
        }
        sort* seq = nullptr, *ch = nullptr;
        if (u.is_re(s, seq)) {
            expr* v0 = get_fresh_value(seq);
                return u.re.mk_to_re(v0);
        }
        if (u.is_char(s)) {
            //char s[2] = { ++m_char, 0 };
            //return u.str.mk_char(zstring(s), 0);
            return u.str.mk_char(zstring("a"), 0);
        }
        if (u.is_seq(s, ch)) {
            expr* v = m_model.get_fresh_value(ch);
            if (!v) return nullptr;
            return u.str.mk_unit(v);
            }
        UNREACHABLE();
        return nullptr;
    }
    void register_value(expr* n) override {
        symbol sym;
        if (u.str.is_string(n, sym)) {
            m_strings.insert(sym);
            if (sym.str().find(m_unique_delim) != std::string::npos) {
                add_new_delim();
            }
        }
    }
private:
    
    void add_new_delim() {
        bool found = true;
        while (found) {
            found = false;
            m_unique_delim += "!";
            symbol_set::iterator it = m_strings.begin(), end = m_strings.end();
            for (; it != end && !found; ++it) {
                found = it->str().find(m_unique_delim) != std::string::npos;                    
            }
        }
    }
};

#endif 
