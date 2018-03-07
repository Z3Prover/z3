/*++
Copyright (c) 2011 Microsoft Corporation

Module Name:

    spacer_util.h

Abstract:

    Utility functions for SPACER.

Author:

    Krystof Hoder (t-khoder) 2011-8-19.
    Arie Gurfinkel
    Anvesh Komuravelli

Revision History:

--*/

#ifndef _SPACER_UTIL_H_
#define _SPACER_UTIL_H_

#include "ast/ast.h"
#include "ast/ast_pp.h"
#include "util/obj_hashtable.h"
#include "util/ref_vector.h"
#include "util/trace.h"
#include "util/vector.h"
#include "ast/arith_decl_plugin.h"
#include "ast/array_decl_plugin.h"
#include "ast/bv_decl_plugin.h"
#include "ast/ast_util.h"
#include "ast/expr_map.h"
#include "model/model.h"

#include "util/stopwatch.h"
#include "muz/spacer/spacer_antiunify.h"

class model;
class model_core;
class model_evaluator;

namespace spacer {

inline unsigned infty_level () {return UINT_MAX;}

inline bool is_infty_level(unsigned lvl)
{ return lvl == infty_level (); }

inline unsigned next_level(unsigned lvl)
{ return is_infty_level(lvl)?lvl:(lvl+1); }

inline unsigned prev_level (unsigned lvl)
{
    if(is_infty_level(lvl)) { return infty_level(); }
    if(lvl == 0) { return 0; }
    return lvl -1;
}

struct pp_level {
    unsigned m_level;
    pp_level(unsigned l): m_level(l) {}
};

inline std::ostream& operator<<(std::ostream& out, pp_level const& p)
{
    if (is_infty_level(p.m_level)) {
        return out << "oo";
    } else {
        return out << p.m_level;
    }
}




typedef ptr_vector<app> app_vector;
typedef ptr_vector<func_decl> decl_vector;
typedef obj_hashtable<func_decl> func_decl_set;


class model_evaluator_util {
    ast_manager&           m;
    model_ref              m_model;
    model_evaluator*       m_mev;

    /// initialize with a given model. All previous state is lost. model can be NULL
    void reset (model *model);
public:
    model_evaluator_util(ast_manager& m);
    ~model_evaluator_util();

    void set_model(model &model) {reset (&model);}
    model_ref &get_model() {return m_model;}
    ast_manager& get_ast_manager() const {return m;}

public:
    bool is_true (const expr_ref_vector &v);
    bool is_false(expr* x);
    bool is_true(expr* x);

    bool eval (const expr_ref_vector &v, expr_ref &result, bool model_completion);
    /// evaluates an expression
    bool eval (expr *e, expr_ref &result, bool model_completion);
    // expr_ref eval(expr* e, bool complete=true);
};


/**
   \brief replace variables that are used in many disequalities by
   an equality using the model.

   Assumption: the model satisfies the conjunctions.
*/
void reduce_disequalities(model& model, unsigned threshold, expr_ref& fml);

/**
   \brief hoist non-boolean if expressions.
*/
void hoist_non_bool_if(expr_ref& fml);

bool is_difference_logic(ast_manager& m, unsigned num_fmls, expr* const* fmls);

bool is_utvpi_logic(ast_manager& m, unsigned num_fmls, expr* const* fmls);

/**
 * do the following in sequence
 * 1. use qe_lite to cheaply eliminate vars
 * 2. for remaining boolean vars, substitute using M
 * 3. use MBP for remaining array and arith variables
 * 4. for any remaining arith variables, substitute using M
 */
void qe_project (ast_manager& m, app_ref_vector& vars, expr_ref& fml,
                 const model_ref& M, bool reduce_all_selects=false, bool native_mbp=false,
                 bool dont_sub=false);

void qe_project (ast_manager& m, app_ref_vector& vars, expr_ref& fml, model_ref& M, expr_map& map);

void expand_literals(ast_manager &m, expr_ref_vector& conjs);
void compute_implicant_literals (model_evaluator_util &mev,
                                 expr_ref_vector &formula, expr_ref_vector &res);
void simplify_bounds (expr_ref_vector &lemmas);
void normalize(expr *e, expr_ref &out, bool use_simplify_bounds = true, bool factor_eqs = false);

/** ground expression by replacing all free variables by skolem constants */
void ground_expr (expr *e, expr_ref &out, app_ref_vector &vars);


void mbqi_project (model &M, app_ref_vector &vars, expr_ref &fml);

bool contains_selects (expr* fml, ast_manager& m);
void get_select_indices (expr* fml, app_ref_vector& indices, ast_manager& m);

void find_decls (expr* fml, app_ref_vector& decls, std::string& prefix);

/** extended pretty-printer
 * used for debugging
 * disables aliasing of common sub-expressions
*/
struct mk_epp : public mk_pp {
    params_ref m_epp_params;
    expr_ref m_epp_expr;
    mk_epp(ast *t, ast_manager &m, unsigned indent = 0, unsigned num_vars = 0, char const * var_prefix = nullptr);
    void rw(expr *e, expr_ref &out);

};

}

#endif
