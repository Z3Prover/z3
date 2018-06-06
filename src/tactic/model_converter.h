/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    model_converter.h

Abstract:

    Abstract interface for converting models.

Author:

    Leonardo (leonardo) 2011-04-21

Notes:

    A model converter, mc, can be used to convert a model for one 
    of a generated subgoal into a model for an initial goal or solver state.
    For a goal or solver state that is decided, a model converter can be
    a simple wrapper around a model.

    Logically, given a formula F and subgoal formula F_s a model converter mc
    for F_s relative to F has the property:

        m |= F_s  iff mc(m) |= F     for every model m

    For the evaluator associated with models, m, we expect

        eval(m)(F_s) <=> eval(mc(m))(F)

    This property holds for both eval, that decides on a fixed value
    for constants that have no interpretation in m and for 'peval' 
    (partial eval) that retuns just the constants that are unfixed.
    (in the model evaluator one can control this behavior using a 
    configuration flag)

    and more generally over the eval method have:

        G => F_s   iff peval(mc(e))(G) => F   for every formula G

    
    where e is the empty model (a model that does not evaluate any

    When a model converter supports application to a formula it satisfies
    the following property:

       mc(G) & F_s is SAT  iff G & F is SAT

    For a model converter that is a sequence of definitions and removals
    of functions we can obtain mc(G) by adding back or expanding definitinos
    that are required to interpret G fully in the context of F_s.

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

    virtual void get_units(obj_map<expr, bool>& fmls) { UNREACHABLE(); }
};

typedef ref<model_converter> model_converter_ref;
typedef sref_vector<model_converter> model_converter_ref_vector;
typedef sref_buffer<model_converter> model_converter_ref_buffer;

model_converter * concat(model_converter * mc1, model_converter * mc2);

model_converter * model2model_converter(model * m);

model_converter * model_and_labels2model_converter(model * m, labels_vec const &r);

void model_converter2model(ast_manager & mng, model_converter * mc, model_ref & m);

void apply(model_converter_ref & mc, model_ref & m);


#endif
