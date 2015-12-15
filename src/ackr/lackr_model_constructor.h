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
#ifndef LACKR_MODEL_CONSTRUCTOR_H_626
#define LACKR_MODEL_CONSTRUCTOR_H_626
#include"ast.h"
#include"ackr_info.h"
#include"model.h"
class lackr_model_constructor {
    public:
        typedef std::pair<app *, app *>           app_pair;
        typedef vector<app_pair>                  conflict_list;
        lackr_model_constructor(ast_manager& m, ackr_info_ref info);
        bool check(model_ref& abstr_model);
        const conflict_list& get_conflicts() {
            SASSERT(state == CONFLICT);
            return conflicts;
        }
    private:
        struct imp;
        enum {CHECKED, CONFLICT, UNKNOWN}  state;
        conflict_list                      conflicts;
        ast_manager&                       m;
        const ackr_info_ref                info;
};
#endif /* MODEL_CONSTRUCTOR_H_626 */
