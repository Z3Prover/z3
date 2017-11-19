/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    model_converter.h

Abstract:

    Abstract interface for converting models.

Author:

    Leonardo (leonardo) 2011-04-21

Notes:

--*/
#ifndef MODEL_CONVERTER_H_
#define MODEL_CONVERTER_H_

#include "util/ref.h"
#include "ast/ast_pp_util.h"
#include "model/model.h"
#include "tactic/converter.h"

class labels_vec : public svector<symbol> {};
class smt2_pp_environment; 

class model_converter : public converter {
protected:
    smt2_pp_environment* m_env;
    void display_add(std::ostream& out, ast_manager& m, func_decl* f, expr* e) const;
    void display_del(std::ostream& out, func_decl* f) const;
    void display_add(std::ostream& out, ast_manager& m);
    
public:

    model_converter(): m_env(nullptr) {}

    virtual void operator()(model_ref & m) = 0;

    virtual void operator()(labels_vec & r) {}
    
    virtual model_converter * translate(ast_translation & translator) = 0;
    
    virtual void collect(ast_pp_util& visitor) { m_env = &visitor.env(); }

    /**
       \brief we are adding a formula to the context of the model converter.
       The operator has as side effect of adding definitions as assertions to the
       formula and removing these definitions from the model converter.
     */
    virtual void operator()(expr_ref& formula) { UNREACHABLE(); }
};

typedef ref<model_converter> model_converter_ref;
typedef sref_vector<model_converter> model_converter_ref_vector;
typedef sref_buffer<model_converter> model_converter_ref_buffer;

model_converter * concat(model_converter * mc1, model_converter * mc2);

model_converter * model2model_converter(model * m);

model_converter * model_and_labels2model_converter(model * m, buffer<symbol> &r);

void model_converter2model(ast_manager & mng, model_converter * mc, model_ref & m);

void apply(model_converter_ref & mc, model_ref & m);


#endif
