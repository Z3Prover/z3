/*++
Copyright (c) 2015 Microsoft Corporation

Module Name:

ackr_info.h

Abstract:

Author:

Mikolas Janota

Revision History:
--*/
#ifndef ACKR_INFO_H_
#define ACKR_INFO_H_

#include"obj_hashtable.h"
#include"ast.h"
#include"ref.h"
#include"expr_replacer.h"
#include"ast_translation.h"

/** \brief
   Information about how a formula is being converted into
   a formula without  uninterpreted function symbols via ackermannization.

 The intended use is that new terms are added via set_abstr.
 Once all terms are abstracted, call seal.
 The function abstract may only be called when sealed.

   The class enables reference counting.
**/
class ackr_info {
    public:
        ackr_info(ast_manager& m)
        : m_m(m)
        , m_er(mk_default_expr_replacer(m))
        , m_subst(m_m)
        , m_ref_count(0)
        , m_sealed(false)
        {}

        virtual ~ackr_info() {
            for (t2ct::iterator i = m_t2c.begin(); i != m_t2c.end(); ++i) {
                m_m.dec_ref(i->m_key);
                m_m.dec_ref(i->m_value);
            }
        }

        inline void set_abstr(app* term, app* c) {
            SASSERT(!m_sealed);
            SASSERT(c && term);
            m_t2c.insert(term,c);
            m_c2t.insert(c->get_decl(),term);
            m_subst.insert(term, c);
            m_m.inc_ref(term);
            m_m.inc_ref(c);
        }

        inline void abstract(expr * e, expr_ref& res) {
            SASSERT(m_sealed);
            (*m_er)(e, res);
        }

        inline app* find_term(func_decl* c)  const {
            app * rv = 0;
            m_c2t.find(c,rv);
            return rv;
        }

        inline app* get_abstr(app* term)  const {
            app * const rv = m_t2c.find(term);
            SASSERT(rv);
            return rv;
        }

        inline void seal() {
            m_sealed=true;
            m_er->set_substitution(&m_subst);
        }

        virtual ackr_info * translate(ast_translation & translator) {
            ackr_info * const retv = alloc(ackr_info, translator.to());
            for (t2ct::iterator i = m_t2c.begin(); i != m_t2c.end(); ++i) {
                app * const k = translator(i->m_key);
                app * const v = translator(i->m_value);
                retv->set_abstr(k, v);
            }
            if (m_sealed) retv->seal();
            return retv;
        }

        //
        // Reference counting
        //
        void inc_ref() { ++m_ref_count; }
        void dec_ref() {
            --m_ref_count;
            if (m_ref_count == 0) {
                dealloc(this);
            }
        }
    private:
        typedef obj_map<app, app*> t2ct;
        typedef obj_map<func_decl, app*> c2tt;
        ast_manager& m_m;

        t2ct m_t2c; // terms to constants
        c2tt m_c2t; // constants to terms (inversion of m_t2c)

        // replacer and substitution used to compute abstractions
        scoped_ptr<expr_replacer> m_er;
        expr_substitution m_subst;

        unsigned m_ref_count; // reference counting
        bool m_sealed; // debugging
};

typedef ref<ackr_info> ackr_info_ref;

#endif /* ACKR_INFO_H_ */
