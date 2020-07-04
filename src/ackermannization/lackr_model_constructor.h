 /*++
 Copyright (c) 2015 Microsoft Corporation

 Module Name:

  model_constructor.h

 Abstract:
   Given a propositional abstraction, attempt to construct a model.


 Author:

 Mikolas Janota

 Revision History:
 --*/
#pragma once

#include "ast/ast.h"
#include "ackermannization/ackr_info.h"
#include "ackermannization/ackr_helper.h"
#include "model/model.h"

class lackr_model_constructor {
    public:
        typedef std::pair<app *, app *>           app_pair;
        typedef vector<app_pair>                  conflict_list;
        lackr_model_constructor(ast_manager& m, ackr_info_ref info);
        ~lackr_model_constructor();
        bool check(model_ref& abstr_model);
        const conflict_list& get_conflicts() {
            SASSERT(m_state == CONFLICT);
            return m_conflicts;
        }
        void make_model(model_ref& model);

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
        struct imp;
        imp * m_imp;
        ast_manager &                      m;
        enum {CHECKED, CONFLICT, UNKNOWN}  m_state;
        conflict_list                      m_conflicts;
        const ackr_info_ref                m_info;

        unsigned m_ref_count; // reference counting
};

typedef ref<lackr_model_constructor> lackr_model_constructor_ref;
