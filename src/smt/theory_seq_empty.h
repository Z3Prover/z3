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
#ifndef THEORY_SEQ_EMPTY_H_
#define THEORY_SEQ_EMPTY_H_

#include "smt_theory.h"
#include "seq_decl_plugin.h"

namespace smt {
    class seq_factory : public value_factory {
        typedef hashtable<symbol, symbol_hash_proc, symbol_eq_proc> symbol_set;
        proto_model& m_model;
        ast_manager& m;
        seq_util     u;
        symbol_set   m_strings;
        unsigned     m_next;
        std::string  m_unique_delim;
        obj_map<sort, expr*> m_unique_sequences;
        expr_ref_vector m_trail;
    public:

        seq_factory(ast_manager & m, family_id fid, proto_model& md):
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

        virtual expr* get_some_value(sort* s) { 
            if (u.is_seq(s)) {
                return u.str.mk_empty(s);
            }
            sort* seq = 0;
            if (u.is_re(s, seq)) {
                return u.re.mk_to_re(u.str.mk_empty(seq));
            }
            UNREACHABLE();
            return 0;
        }
        virtual bool get_some_values(sort* s, expr_ref& v1, expr_ref& v2) { 
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
        virtual expr* get_fresh_value(sort* s) { 
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
            sort* seq = 0, *ch = 0;
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
                return u.str.mk_unit(v);
            }
            UNREACHABLE();
            return 0;
        }
        virtual void register_value(expr* n) {
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

    class theory_seq_empty : public theory {
        bool m_used;
        virtual final_check_status final_check_eh() { return m_used?FC_GIVEUP:FC_DONE; }
        virtual bool internalize_atom(app*, bool) { if (!m_used) { get_context().push_trail(value_trail<context,bool>(m_used)); m_used = true; } return false; }
        virtual bool internalize_term(app*) { return internalize_atom(0,false);  }
        virtual void new_eq_eh(theory_var, theory_var) { }
        virtual void new_diseq_eh(theory_var, theory_var) {}
        virtual theory* mk_fresh(context* new_ctx) { return alloc(theory_seq_empty, new_ctx->get_manager()); }
        virtual char const * get_name() const { return "seq-empty"; }
        virtual void display(std::ostream& out) const {}
    public:
        theory_seq_empty(ast_manager& m):theory(m.mk_family_id("seq")), m_used(false) {}
        virtual void init_model(model_generator & mg) {
            mg.register_factory(alloc(seq_factory, get_manager(), get_family_id(), mg.get_model()));
        }

    };

};

#endif /* THEORY_SEQ_EMPTY_H_ */

