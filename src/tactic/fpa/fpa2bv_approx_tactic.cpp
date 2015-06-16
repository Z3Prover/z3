/*++
 Copyright (c) 2012 Microsoft Corporation

 Module Name:

 fpa2bv_approx_tactic.cpp

 Abstract:

 Tactic that converts floating points to bit-vectors lazily

 Author:

 Aleksander Zeljic 2012-11-15

 Notes:

 --*/
#include"tactical.h"
#include"cooperate.h"
#include"ref_util.h"

#include"th_rewriter.h"
#include"bit_blaster_rewriter.h"
#include"bit_blaster_model_converter.h"
#include"model_v2_pp.h"
#include"goal2sat.h"
#include"sat_solver.h"
#include"fpa_decl_plugin.h"
#include"fpa2bv_converter_prec.h"
#include"fpa2bv_model_converter.h"
#include"fpa2bv_converter.h"
#include"propagate_values_tactic.h"
#include"fpa2bv_rewriter_prec.h"
#include"fpa2bv_approx_tactic.h"
#include"const_intro_rewriter.h"
#include"ctx_simplify_tactic.h"
#include"filter_model_converter.h"
#include <list>
#include <queue>
#include <math.h>

#include<iostream>

#define K_MIN 10
#define K_PERCENTAGE 0.3
#define PREC_INCREMENT 20
#define ERR_OP 0 //

struct pair
{
    expr * exp;
    double quotient;// mpf *
};

bool isinfinite(double x) {
#ifdef _WIN32
    int c = _fpclass(x);
    return c == _FPCLASS_PINF || c == _FPCLASS_NINF;
#else
    return fpclassify(x) == FP_INFINITE;
#endif
}

class fpa2bv_approx_tactic: public tactic {
    struct imp {
        ast_manager & m;
        goal2sat m_goal2sat;
        sat2goal m_sat2goal;
        params_ref m_params;
        unsigned m_num_steps;
        bool m_proofs_enabled;
        bool m_produce_models;
        bool m_produce_unsat_cores;
        bool m_cancel;

        fpa_approximation_mode m_mode;
        ast_manager * m_temp_manager;
        model_ref m_fpa_model;
        fpa_util m_float_util;

        imp(ast_manager & _m, params_ref const & p, fpa_approximation_mode mode) :
            m(_m),
            m_params(p),
            m_proofs_enabled(false),
            m_produce_models(false),
            m_produce_unsat_cores(false),
            m_cancel(false),
            m_mode(mode),
            m_temp_manager(0),
            m_float_util(_m) {
        }

        void updt_params(params_ref const & p) {
            m_params = p;         
        }

        void set_cancel(bool f) {
            //If f is true stop everything
            m_cancel = f;
        }

        void init_precision_mapping(func_decl_ref_vector const & cnsts, 
                obj_map<func_decl, unsigned> & map,
                obj_map<func_decl, app*> & const2term_map) {
            for (unsigned i = 0; i < cnsts.size(); i++)
            {
                if (const2term_map.contains(cnsts.get(i)) || m_mode == FPAA_SMALL_FLOATS)
                    map.insert_if_not_there(cnsts.get(i), 0);
                else
                    map.insert_if_not_there(cnsts.get(i), MAX_PRECISION);
            }
        }

        bool proof_guided_refinement(
                goal_ref const & g,
                func_decl_ref_vector const & cnsts,
                obj_map<func_decl, unsigned> & cnst2prec_map,
                obj_map<func_decl, unsigned> & new_map)
        {
            // We have no model. Let's just increase precision of everything.
            bool res = false;
            for (unsigned i = 0; i < cnsts.size(); i++)
            {
                unsigned old = cnst2prec_map.find(cnsts.get(i));
                unsigned n = old + PREC_INCREMENT;
                if (old >= MAX_PRECISION) n = MAX_PRECISION;
                else { if (n > MAX_PRECISION) n = MAX_PRECISION; res = true; }
                new_map.insert(cnsts.get(i), n);
            }
            return res;
        }

        void boolean_comparison_of_models(goal_ref g, model_ref const & mdl, model_ref const & full_mdl, obj_map<func_decl, app*> & cnst2term_map, obj_map<expr,int>& count)
        {
            std::queue<expr*> to_traverse;
            app * cur;
            int cur_cnt;

            expr_ref mdl_eval(m), full_eval(m);

            for (unsigned i=0; i < g->size(); i++){
                mdl->eval(g->form(i),mdl_eval,true);
                full_mdl->eval(g->form(i),full_eval,true);

                //Push only if the full model evaluates to false, or if the models differ?
                if (!m.is_true(full_eval)) // m.is_true(full_eval) != m.is_true(mdl_eval)
                    to_traverse.push(g->form(i));
            }

            while (to_traverse.size() > 0) {
                cur = to_app(to_traverse.front());
#ifdef Z3DEBUG
                std::cout<<"Analyze - traversing: "<<mk_ismt2_pp(cur,m)<<std::endl;
                std::cout.flush();
#endif
                if (m_float_util.is_rm(cur) || m_float_util.is_numeral(cur)) {
                    to_traverse.pop();
                    continue;
                }
                else if(!m.is_bool(cur)){
                    //Push and add potential counter to the map for the descendants
                    //Inserting children in the count map

                    //Count will contain only introduced constants not other expressions
                    if (count.contains(cur) ){
                        cur_cnt = count.find(cur);
                        count.remove(cur);
                        count.insert(cur,1+cur_cnt);
                    }
                    else if(cnst2term_map.contains(cur->get_decl()))
                        count.insert(cur,1);

                    if(cnst2term_map.contains(cur->get_decl()))
                        to_traverse.push(cnst2term_map.find(cur->get_decl()));

                    for(unsigned i=0;i<cur->get_num_args();i++) {
                        if(m_float_util.is_rm(cur->get_arg(i)) || m_float_util.is_numeral(cur->get_arg(i)))
                            continue;
                        to_traverse.push(cur->get_arg(i));
                    }
                }
                else { //Comparing boolean values from the model and the expanded model
                    mdl->eval(cur,mdl_eval,true);
                    full_mdl->eval(cur,full_eval,true);


                    if (m.is_true(full_eval) != m.is_true(mdl_eval)) {
                        //queue arguments
                        for(unsigned i=0; i < cur->get_num_args(); i++)
                            to_traverse.push(cur->get_arg(i));
                    }
                }
                to_traverse.pop();
            }
#ifdef Z3DEBUG
            std::cout<<"Expression count"<<std::endl;
            for(obj_map<expr,int>::iterator it = count.begin();
                    it!= count.end();
                    it++) {
                std::cout<<mk_ismt2_pp(it->m_key,m)<<":"<<it->m_value<<std::endl;
            }
            std::cout<<"-------------------------"<<std::endl;
            std::cout.flush();
#endif
        }
        //Equality as assignment?
        void fix_cnst2cnst_equalities(goal_ref const & g,model_ref & full_mdl) {
            app * eq;
#ifdef Z3DEBUG
            std::cout<<"Fixing trivial equalities"<<std::endl;
#endif
            for (unsigned i=0; i<g->size();i++) {
                eq = to_app(g->form(i));

                if (eq->get_family_id() == m.get_basic_family_id() &&
                        eq->get_decl_kind() == OP_EQ){
                    //eq is in fact an equality
                    app * lhs = to_app(eq->get_arg(0));
                    app * rhs = to_app(eq->get_arg(1));
                    expr * lhs_e,*rhs_e,*exp, *exp_e;
                    app *other = NULL;


                    if(lhs->get_num_args()==0 &&
                            rhs ->get_num_args()==0){
                        //over constants
                        lhs_e = full_mdl->get_const_interp(lhs->get_decl());
                        rhs_e = full_mdl->get_const_interp(rhs->get_decl());

                        // != would work as well, to make sure they are not both NULL,
                        //and could simplify later checks
                        if(lhs_e != rhs_e) { //SASSERT(lhs_e || rhs_e);
                            //and one is registered in the full model while the other is not
                            if(!lhs_e){// && rhs_e){
                                other = lhs;
                                exp_e = rhs_e;
                                exp = rhs;
                            }
                            else { // if(!rhs_e && lhs_e){
                                other = rhs;
                                exp_e = lhs_e;
                                exp = lhs;
                            }
                            full_mdl->register_decl(other->get_decl(),exp_e);

#ifdef Z3DEBUG
                            std::cout<<mk_ismt2_pp(eq,m)<<" : "<<"assigning "<<mk_ismt2_pp(other,m)<<
                                    " value of "<<mk_ismt2_pp(exp,m)<<":"<<mk_ismt2_pp(exp_e,m)<<std::endl;
#endif
                        }
                    }
                }
            }
        }

        void obtain_values(
                app * rhs,
                model_ref const & mdl,
                model_ref & full_mdl,
                mpf_manager & mpf_mngr,
                obj_map<func_decl,app*> & cnst2term_map,
                obj_map<expr, bool> & precise_op,
                obj_map<expr, mpf*> & actual_value,
                obj_map<expr, double> & err_est,
                mpf_rounding_mode & rm,
                bool & precise_children,
                bool & seen_all_children,
                bool & children_have_finite_err,
                mpf * arg_val,
                mpf * est_arg_val
                //expr_ref * arg_e
        ){

            expr_ref arg_e[] = { expr_ref(m), expr_ref(m), expr_ref(m), expr_ref(m) };
            unsigned i=0;
            //Set rounding mode
            if (rhs->get_num_args() > 0 && m_float_util.is_rm(rhs->get_arg(0))) {
                expr_ref rm_val(m);
                mdl->eval(rhs->get_arg(0), rm_val, true);
                m_float_util.is_rm_numeral(rm_val, rm);
                i = 1;
            }
            //Collect argument values
            for (; i < rhs->get_num_args(); i++) {
                expr * arg = rhs->get_arg(i);

                if (is_app(arg) && to_app(arg)->get_num_args() == 0) {
                    if (precise_op.contains(arg)) {
                        precise_children &= precise_op.find(arg);
                    }
                    else if (!cnst2term_map.contains(to_app(arg)->get_decl())) {
                        /* that's okay */
                    }
                    else {
#ifdef Z3DEBUG
                        std::cout << "Not seen all children of " << mk_ismt2_pp(rhs, m) <<
                                " (spec. " << mk_ismt2_pp(arg, m) << ")" << std::endl;
#endif
                        precise_children = false;
                        seen_all_children = false;
                        break;
                    }
                }

                // Value from small model
                mdl->eval(arg, arg_e[i],true);
                m_float_util.is_numeral(arg_e[i], arg_val[i]);

                if( children_have_finite_err &&
                        err_est.contains(arg) &&
                        isinfinite(err_est.find(arg)))
                    children_have_finite_err=false;

                if (actual_value.contains(arg))
                    mpf_mngr.set(est_arg_val[i], *actual_value.find(arg));
                else if (seen_all_children && is_app(arg) && to_app(arg)->get_num_args()==0) {
                    //We have seen all children so if it is a constant and not in actual_value then
                    //it is an input variable and its est_val is the same as actual value
                    mpf * tmp = alloc(mpf);
                    mpf_mngr.set(*tmp, arg_val[i]);
                    actual_value.insert(arg, tmp);
                    mpf_mngr.set(est_arg_val[i], *tmp);
                }
                else
                    std::cout << "Estimated value missing: " << mk_ismt2_pp(arg,m) << std::endl;
            }

        }


        void full_semantics_eval(
                app * rhs,
                mpf_manager & mpf_mngr,
                mpf_rounding_mode & rm,
                mpf * arg_val,
                mpf * est_arg_val,
                mpf & rhs_value,
                mpf & est_rhs_value){

            switch (rhs->get_decl()->get_decl_kind()) {
            case OP_FPA_ADD:
                mpf_mngr.add(rm, arg_val[1], arg_val[2], rhs_value);
                mpf_mngr.add(rm, est_arg_val[1], est_arg_val[2], est_rhs_value);
                break;
            case OP_FPA_SUB:
                mpf_mngr.sub(rm, arg_val[1], arg_val[2], rhs_value);
                mpf_mngr.sub(rm, est_arg_val[1], est_arg_val[2], est_rhs_value);
                break;
            case OP_FPA_NEG:
                mpf_mngr.neg(arg_val[0], rhs_value);
                mpf_mngr.neg(est_arg_val[0], est_rhs_value);//Does it even make sense to look at this?
                break;
            case OP_FPA_MUL:
                mpf_mngr.mul(rm, arg_val[1], arg_val[2], rhs_value);
                mpf_mngr.mul(rm, est_arg_val[1], est_arg_val[2], est_rhs_value);
                break;
            case OP_FPA_DIV:
                mpf_mngr.div(rm, arg_val[1], arg_val[2], rhs_value);
                mpf_mngr.div(rm, est_arg_val[1], est_arg_val[2], est_rhs_value);
                break;
            case OP_FPA_REM:
                mpf_mngr.rem(arg_val[0], arg_val[1], rhs_value);
                mpf_mngr.rem(est_arg_val[0], est_arg_val[1], est_rhs_value);
                break;
            case OP_FPA_FMA:
                mpf_mngr.fused_mul_add(rm, arg_val[1], arg_val[2], arg_val[3], rhs_value);
                mpf_mngr.fused_mul_add(rm, est_arg_val[1], est_arg_val[2], est_arg_val[3], est_rhs_value);
                break;
            case OP_FPA_SQRT:
                mpf_mngr.sqrt(rm, arg_val[1], rhs_value);
                mpf_mngr.sqrt(rm, est_arg_val[1], est_rhs_value);
                break;
            case OP_FPA_TO_FP:
            {
                unsigned ebits = rhs->get_decl()->get_parameter(0).get_int();
                unsigned sbits = rhs->get_decl()->get_parameter(1).get_int();
                mpf_mngr.set(rhs_value, ebits, sbits, rm, arg_val[1]);
                mpf_mngr.set(est_rhs_value, ebits, sbits, rm, est_arg_val[1]);
                break;
            }
            case OP_FPA_ABS:
            {
                mpf_mngr.abs(arg_val[0], rhs_value);
                mpf_mngr.abs(est_arg_val[0], est_rhs_value);
                break;
            }
            case OP_FPA_MIN:
            {
                mpf_mngr.minimum( arg_val[1], arg_val[2], rhs_value);
                mpf_mngr.minimum( est_arg_val[1], est_arg_val[2], est_rhs_value);
                break;
            }
            case OP_FPA_MAX:
            {
                mpf_mngr.maximum( arg_val[1], arg_val[2], rhs_value);
                mpf_mngr.maximum( est_arg_val[1], est_arg_val[2], est_rhs_value);
                break;
            }
            case OP_FPA_ROUND_TO_INTEGRAL:
            {
                mpf_mngr.round_to_integral(rm,arg_val[1],rhs_value);
                mpf_mngr.round_to_integral(rm,est_arg_val[1],est_rhs_value);
                break;
            }

            default:
                NOT_IMPLEMENTED_YET();
                break;
            }

        }

        void evaluate_constant(
                app * rhs,
                model_ref const & mdl,
                mpf_manager & mpf_mngr,
                obj_map<expr, mpf*> & actual_value,
                mpf & rhs_value,
                mpf & est_rhs_value){

            expr_ref exp(m);
            mdl->eval(rhs, exp, true);
            m_float_util.is_numeral(exp, rhs_value); //OLD:is_value

            if (actual_value.contains(rhs))
                mpf_mngr.set(est_rhs_value, *actual_value.find(rhs));
            else {
                mpf * tmp = alloc(mpf);
                mpf_mngr.set(*tmp, rhs_value);
                actual_value.insert(rhs, tmp);
                mpf_mngr.set(est_rhs_value, rhs_value);
            }
        }

        void calculate_error(
                expr_ref & lhs,
                mpf_manager & mpf_mngr,
                obj_map<expr, bool> & precise_op,
                obj_map<expr, double> & err_est,
                mpf & lhs_value,
                mpf & est_rhs_value,
                bool children_have_finite_err){
            mpf err, rel_err;
            if (!mpf_mngr.eq(lhs_value, est_rhs_value) &&
                    !(mpf_mngr.is_nan(lhs_value) && mpf_mngr.is_nan(est_rhs_value))) {
#ifdef Z3DEBUG
                std::cout << "Increasing precision of " << mk_ismt2_pp(lhs, m) <<
                        " because " << mk_ismt2_pp(lhs, m) << " != " <<
                        mpf_mngr.to_string(est_rhs_value) << std::endl;
#endif
                //TODO: smarter adjustment to be implemented
                precise_op.insert(lhs, false);
                if (mpf_mngr.is_regular(lhs_value) && mpf_mngr.is_regular(est_rhs_value)) {
                    mpf_mngr.sub(MPF_ROUND_TOWARD_ZERO, est_rhs_value, lhs_value, err);
                    mpf_mngr.div(MPF_ROUND_TOWARD_ZERO, err, lhs_value, rel_err);
                    mpf_mngr.abs(rel_err);
                }
                else// One of the two is a special value; in this case the relative error is +INF
                    mpf_mngr.mk_pinf(11, 53, rel_err);

                if(children_have_finite_err)
                    err_est.insert(lhs, mpf_mngr.to_double(rel_err));

#ifdef Z3DEBUG
                std::cout << "Error estimate: "<<mpf_mngr.to_string(rel_err) << std::endl;
#endif
            }
            else {
#ifdef Z3DEBUG
                std::cout << mk_ismt2_pp(lhs, m) << " is precise." << std::endl;
#endif
                precise_op.insert(lhs, true);
            }
#ifdef Z3DEBUG
            std::cout << "****************************" << std::endl;
#endif
        }

        bool evaluate_model(goal_ref const & g, model_ref & mdl){
            bool is_model = true;
            expr_ref res(m);
            for (unsigned j = 0; j < g->size(); j++) {
                mdl->eval(g->form(j), res, true);
                if (!m.is_true(res)) {
                    std::cout << "Failed: " << mk_ismt2_pp(g->form(j), m) << std::endl;
                    std::cout << "Evaluates to: " << mk_ismt2_pp(res, m) << std::endl;
                    is_model=false;
                }
            }
            return is_model;
        }
        void evaluate_and_patch(
                func_decl_ref_vector const & cnsts,
                model_ref const & mdl,
                model_ref & full_mdl,
                goal_ref const & g,
                obj_map<func_decl,app*> & cnst2term_map,
                obj_map<expr, double> & err_est) {

            mpf_manager & mpf_mngr = m_float_util.fm();
            expr_ref lhs(m), lhs_eval(m);
            app * rhs;
            mpf arg_val[4]; //First argument can be rounding mode
            mpf est_arg_val[4];
            mpf lhs_value, rhs_value, est_rhs_value;
            mpf_rounding_mode rm;

            mpf err, rel_err;



            obj_map<expr, bool> precise_op;
            obj_map<expr, mpf*> actual_value;
            while (precise_op.size() != cnst2term_map.size())
                for(unsigned i=0;i<cnsts.size();i++)
                    if(cnst2term_map.contains(cnsts.get(i)))
                    {
                        lhs = m.mk_const(cnsts.get(i));
                        rhs = cnst2term_map.find(cnsts.get(i));
                        if (precise_op.contains(lhs))//already visited, skip
                                return;

                        mdl->eval(lhs, lhs_eval, true);

                        if (m_float_util.is_numeral(lhs_eval, lhs_value)) {//OLD:is_value
                            bool precise_children = true;
                            bool seen_all_children = true;
                            bool children_have_finite_err = true;

                            obtain_values(rhs, mdl, full_mdl,mpf_mngr,cnst2term_map,precise_op,actual_value,
                                    err_est, rm, precise_children, seen_all_children, children_have_finite_err, arg_val, est_arg_val );


                            if (seen_all_children) {//If some arguments are not evaluated yet, skip
                                if (rhs->get_num_args() == 0)
                                    evaluate_constant(rhs,mdl,mpf_mngr,actual_value, rhs_value, est_rhs_value);
                                else
                                    full_semantics_eval(rhs,mpf_mngr,rm,arg_val,est_arg_val, rhs_value, est_rhs_value);

                                if (mpf_mngr.eq(rhs_value, est_rhs_value)) {
                                    full_mdl->register_decl((to_app(lhs))->get_decl(), m_float_util.mk_value(est_rhs_value));
                                    precise_op.insert(lhs, true);
                                }
                                else {
                                    full_mdl->register_decl((to_app(lhs))->get_decl(), m_float_util.mk_value(est_rhs_value));
#ifdef Z3DEBUG
                                    std::cout << "Assigning " << mk_ismt2_pp(lhs, m) <<
                                            " value " << mpf_mngr.to_string(est_rhs_value) << std::endl
                                            << "Values of " << mk_ismt2_pp(lhs, m) << std::endl
                                            << "Precise children: " << ((precise_children) ? "True" : "False") << std::endl
                                            << "Lhs:   " << mk_ismt2_pp(lhs_eval, m) << std::endl
                                            << "Model:    " << mpf_mngr.to_string(rhs_value) << std::endl
                                            << "Estimate: " << mpf_mngr.to_string(est_rhs_value) << std::endl;
#endif

                                    calculate_error(lhs,mpf_mngr,precise_op,err_est,lhs_value,est_rhs_value,children_have_finite_err);

                                }
                                if (!actual_value.contains(lhs)) {
                                    mpf * tmp = alloc(mpf);
                                    mpf_mngr.set(*tmp, est_rhs_value);
                                    actual_value.insert(lhs, tmp);
                                }

                                if (!precise_children && !precise_op.contains(lhs)) {
                                    std::cout << mk_ismt2_pp(lhs, m) << " is imprecise because some children are imprecise." << std::endl;
                                    precise_op.insert(lhs, false);
                                }
                            }
                        }
                    }

            for (obj_map<expr, mpf *>::iterator it = actual_value.begin();
                    it != actual_value.end();
                    it++)
                mpf_mngr.del(*it->m_value);

            mpf_mngr.del(err);
            mpf_mngr.del(rel_err);
            mpf_mngr.del(lhs_value);
            mpf_mngr.del(rhs_value);
            mpf_mngr.del(est_rhs_value);

            for (unsigned i = 0; i < 4; i++) {
                mpf_mngr.del(arg_val[i]);
                mpf_mngr.del(est_arg_val[i]);
            }
        }

        bool precise_model_reconstruction(
                model_ref const & mdl,
                model_ref & full_mdl,
                goal_ref const & g,
                obj_map<expr, double> & err_est,//mpf*
                func_decl_ref_vector const & cnsts,
                obj_map<func_decl, app*> & cnst2term_map) {
#ifdef Z3DEBUG
            std::cout << "Attempting to patch small-float model" << std::endl;
#endif
            expr_ref res(m);
            bool is_model=true;

            //Evaluation of the model using full fpa semantics and construction of the full model
           evaluate_and_patch(cnsts, mdl, full_mdl, g, cnst2term_map, err_est);

#ifdef Z3DEBUG
            std::cout<<std::endl<<"Printing err_est map"<<std::endl;
            for(obj_map<expr,double>::iterator it = err_est.begin();
                    it!= err_est.end(); it++) {
                std::cout<<mk_ismt2_pp(it->m_key,m)<<":"<<it->m_value<<std::endl;
            }
            std::cout<<"-------------------------"<<std::endl;
            std::cout.flush();
#endif
            //Assigning values when input_cnst = intro_cnst;
            fix_cnst2cnst_equalities(g,full_mdl);

            //Completing the model with values for input variables
            for (unsigned j=0; j < mdl->get_num_constants(); j++) {
                if (!cnst2term_map.contains(mdl->get_constant(j))
                        && !full_mdl->get_const_interp(mdl->get_constant(j))) {
                    mdl->eval(mdl->get_constant(j), res);
                    full_mdl->register_decl(mdl->get_constant(j), res);
                }
            }

            //Evaluate the full model
            is_model = evaluate_model(g,full_mdl);

            return is_model;
        }

        void calculate_relative_error(
                obj_map<expr, double> & err_est,
                obj_map<expr, int> & expr_count,
                obj_map<expr, double> & err_ratio_map) {
            unsigned num_args=0;
            expr_ref exp(m);
            double out_err,cur,err_ratio, avg_err;

            //AZ: Currently ignoring the expr_count, since it was blocking consideration of some expressions
            for (obj_map<expr, double>::iterator it = err_est.begin();
                    it != err_est.end();
                    it++) {
                // if any ancestor node has an error current node will be in expr_count.
                /*if (!expr_count.contains(it->m_key))
                                continue;*/

                exp = it->m_key;
                out_err = it->m_value;
                num_args = to_app(exp)->get_num_args();

                // Calculate average error of input params
                avg_err = 0.0;
                if (num_args > 0) {
                    for (unsigned i=0; i<num_args; i++) {
                        expr * arg = to_app(exp)->get_arg(i);
                        if (err_est.contains(arg)) {
                            cur = err_est.find(arg);
                            avg_err = avg_err + cur;
                        }
                    }
                    avg_err = avg_err/num_args;
                }
                // Relative error when input error exists, otherwise just output error
                err_ratio = fabs((avg_err != (double) 0)? out_err / avg_err : out_err);

                if(expr_count.contains(exp)) {
                    if(ERR_OP)
                        err_ratio *= 1 + expr_count.find(exp);
                    else
                        err_ratio += expr_count.find(exp);
                }
                err_ratio_map.insert(exp, err_ratio);                
            }

            TRACE("fpa2bv_approx", 
                    tout << "ERROR RATIO MAP: " << std::endl;
            for (obj_map<expr, double>::iterator it = err_ratio_map.begin();// mpf*
                    it != err_ratio_map.end();
                    it++)
                tout << mk_ismt2_pp(it->m_key, m) << ": " <<it->m_value<< std::endl; );


#ifdef Z3DEBUG
            std::cout<<"Error ratio:"<<std::endl;
            for (obj_map<expr, double>::iterator it = err_ratio_map.begin();//mpf*
                    it != err_ratio_map.end();
                    it++)
                std::cout<< mk_ismt2_pp(it->m_key, m) << ": " << it->m_value<< std::endl;
            std::cout.flush();
#endif

        }


        void rank_terms(obj_map<expr, double> & err_ratio_map, std::list <struct pair *> & ranked_terms)
        {
            unsigned kth = (unsigned)(err_ratio_map.size()*K_PERCENTAGE);
            if (kth<10) kth=K_MIN;
            SASSERT(!err_ratio_map.empty());

            //Insertion sort the error ratios, keeping only the k highest elements
            obj_map<expr, double>::iterator it = err_ratio_map.begin();
            struct pair * p = new struct pair();
            p->exp=it->m_key;
            p->quotient=it->m_value;
            ranked_terms.push_front(p);

            for (it++; it != err_ratio_map.end(); it++) {
                if (ranked_terms.size()<kth || it->m_value >= ranked_terms.back()->quotient) {
                    std::list<struct pair *>::iterator pos = ranked_terms.begin();
                    while (pos!=ranked_terms.end() && it->m_value <= ranked_terms.back()->quotient)
                        pos++;
                    struct pair * p = new struct pair();
                    p->exp=it->m_key;
                    p->quotient=it->m_value;
                    ranked_terms.insert(pos, p);
                    if (ranked_terms.size() > kth) {
                        delete ranked_terms.back();
                        ranked_terms.pop_back();
                    }
                }
            }

        }

        void increase_precision(
                std::list <struct pair *> & ranked_terms,
                func_decl_ref_vector const & cnsts,
                obj_map<func_decl, unsigned> & cnst2prec_map,
                obj_map<func_decl, app*> & cnst2term_map,
                obj_map<func_decl, unsigned> & new_map){

            //Refine chosen terms and find the any input 'variables' which are
            //its immediate arguments and refine them as well
#ifdef Z3DEBUG
            std::cout<<"Increasing precision:"<<std::endl;
#endif
            for(std::list<struct pair *>::iterator itp = ranked_terms.begin();
                    itp != ranked_terms.end();
                    itp++) {
                app * cur = to_app((*itp)->exp);
                func_decl * f = cur->get_decl();
                unsigned new_prec = PREC_INCREMENT, old_prec;
                bool in_new_map;

                if (cnst2prec_map.contains(f))
                    new_prec += cnst2prec_map.find(f);

                new_prec= (new_prec > MAX_PRECISION) ? MAX_PRECISION : new_prec;
                new_map.insert(f, new_prec);

#ifdef Z3DEBUG
                std::cout << f->get_name() << ":" << new_prec << std::endl;
                std::cout << mk_ismt2_pp(cur, m) << ":" << new_prec << std::endl;
#endif

                if(cnst2term_map.contains(f))
                    cur = cnst2term_map.find(f);
                // Refine constants that are direct arguments of this term
                for(unsigned i=0; i<cur->get_num_args();i++){
                    func_decl * arg_decl = to_app(cur->get_arg(i))->get_decl();
                    if (!cnst2term_map.contains(arg_decl) && //Not a constant introduced by flattening
                            !m_float_util.is_rm(cur->get_arg(i)) && //OLD:is_rm(...,rm)
                            !m_float_util.is_numeral(cur->get_arg(i))) { //OLD:is_value
                        //It is an input 'variable'
                        if ( (in_new_map = new_map.contains(arg_decl)))
                            old_prec=new_map.find(arg_decl);
                        else if (cnst2prec_map.contains(arg_decl))
                            old_prec = cnst2prec_map.find(arg_decl);
                        else
                            old_prec=0;

                        if (old_prec < new_prec) {
                            if (in_new_map)
                                new_map.remove(arg_decl);
                            SASSERT(new_prec <= MAX_PRECISION);
                            new_map.insert(arg_decl, new_prec);
                            std::cout << "    " << arg_decl->get_name() << ":" << new_prec << std::endl;
#ifdef Z3DEBUG
                            std::cout<<"    "<<mk_ismt2_pp(cur->get_arg(i),m)<<":"<<new_prec<<std::endl;
#endif
                        }
                    }
                }
                std::cout.flush();
                delete *itp;
            }

            //Complete precision map
            func_decl * f;
            for(unsigned j=0; j<cnsts.size();j++)
                if(!new_map.contains((f=cnsts.get(j))))
                    new_map.insert(f, cnst2prec_map.find(f));

        }

        void model_guided_approximation_refinement(
                model_ref const & mdl,
                model_ref & full_mdl,
                goal_ref const & g,
                func_decl_ref_vector const & cnsts,
                obj_map<func_decl, unsigned> & cnst2prec_map,
                obj_map<func_decl, app*> & cnst2term_map,
                obj_map<expr, double> & err_est,
                obj_map<func_decl, unsigned> & new_map) {

            obj_map<expr, double> err_ratio_map;
            obj_map<expr, int> expr_count;
            std::list <struct pair *> ranked_terms;

            boolean_comparison_of_models(g, mdl, full_mdl, cnst2term_map, expr_count);
            calculate_relative_error(err_est, expr_count, err_ratio_map);
            if (err_ratio_map.empty()) {
                proof_guided_refinement(g,cnsts,cnst2prec_map,new_map);
            }
            else {
                rank_terms (err_ratio_map,ranked_terms);
                increase_precision(ranked_terms,cnsts,cnst2prec_map,cnst2term_map,new_map);
            }
        }

        void simplify(goal_ref mg) {
            ast_manager &m = mg->m(); // CMW: <--- We use the manager of the goal, so this works for any manager.
            expr_ref new_curr(m);
            proof_ref new_pr(m);

            th_rewriter simplifier(m, m_params);

            // CMW: we need to eliminate AND expressions.
            params_ref elim_and(m_params);
            elim_and.set_bool("elim_and", true);
            // elim_and.set_uint("max_depth", 1); // CMW: This number can have a big impact on performance, either way.
            simplifier.updt_params(elim_and);

            SASSERT(mg->is_well_sorted());
            TRACE("before_simplifier", mg->display(tout););
            m_num_steps = 0;
            if (mg->inconsistent())
                return;
            for (unsigned idx = 0; idx < mg->size(); idx++) {
                if (mg->inconsistent())
                    break;
                expr * curr = mg->form(idx);
                simplifier(curr, new_curr, new_pr);
                m_num_steps += simplifier.get_num_steps();
                if (mg->proofs_enabled()) {
                    proof * pr = mg->pr(idx);
                    new_pr = m.mk_modus_ponens(pr, new_pr);
                }
                mg->update(idx, new_curr, new_pr, mg->dep(idx));
            }
            TRACE("after_simplifier_bug", mg->display(tout););
            mg->elim_redundancies();
            TRACE("after_simplifier", mg->display(tout););
            TRACE("after_simplifier_detail", mg->display_with_dependencies(tout););
            SASSERT(mg->is_well_sorted());
        }

        bool fully_encoded(obj_map<func_decl, unsigned> const & precision_map)
        {
            for (obj_map<func_decl, unsigned>::iterator it = precision_map.begin();
                    it != precision_map.end();
                    it++)
                if (it->m_value < MAX_PRECISION) return false;
            return true;
        }

        void bitblast(goal_ref const & g,
                fpa2bv_converter_prec & fpa2bv,
                bit_blaster_rewriter & bv2bool,
                obj_map<func_decl,unsigned> & const2prec_map,
                sat::solver & solver,
                atom2bool_var & map)
        {
            // CMW: This is all done using the temporary manager!
            expr_ref new_curr(*m_temp_manager);
            proof_ref new_pr(*m_temp_manager);
            std::cout.flush();

            SASSERT(g->is_well_sorted());

            simplify(g);

            //fpa2bv
            fpa2bv_rewriter_prec fpa2bv_rw(*m_temp_manager, fpa2bv, m_params);
            fpa2bv_rw.m_cfg.set_mappings(&const2prec_map);
            m_num_steps = 0;
            unsigned size = g->size();
            for (unsigned idx = 0; idx < size; idx++) {
                if (g->inconsistent())
                    break;
                expr * curr = g->form(idx);
#ifdef Z3DEBUG
                std::cout<<mk_ismt2_pp(curr,m)<<std::endl;
                std::cout.flush();
#endif
                fpa2bv_rw(curr, new_curr, new_pr);
                m_num_steps += fpa2bv_rw.get_num_steps();
                if (m_proofs_enabled) {
                    proof * pr = g->pr(idx);
                    new_pr = m_temp_manager->mk_modus_ponens(pr, new_pr);
                }
                g->update(idx, new_curr, new_pr, g->dep(idx));

                SASSERT(g->is_well_sorted());
            }

            //Adding the equalities that fix bits
            for(unsigned i=0;i<fpa2bv.m_extra_assertions.size();i++)
                g->assert_expr(fpa2bv.m_extra_assertions.get(i));

            SASSERT(g->is_well_sorted());

            simplify(g);

            //Bitblasting
            TRACE("before_bit_blaster", g->display(tout););
            m_num_steps = 0;
            size = g->size();
            for (unsigned idx = 0; idx < size; idx++) {
                if (g->inconsistent())
                    break;
                expr * curr = g->form(idx);
                bv2bool(curr, new_curr, new_pr);
                m_num_steps += bv2bool.get_num_steps();
                if (m_proofs_enabled) {
                    proof * pr = g->pr(idx);
                    new_pr = m_temp_manager->mk_modus_ponens(pr, new_pr);
                }
                g->update(idx, new_curr, new_pr, g->dep(idx));
            }

            g->inc_depth();

            simplify(g);

            TRACE("before_sat_solver", g->display(tout););
            g->elim_redundancies();

            goal2sat::dep2asm_map d2am ;
            m_goal2sat(*g, m_params, solver, map,  d2am , false);


            TRACE("sat_solver_unknown", tout << "interpreted_atoms: " << map.interpreted_atoms() << "\n";
            atom2bool_var::iterator it = map.begin();
            atom2bool_var::iterator end = map.end();
            for (; it != end; ++it) {
                if (!is_uninterp_const(it->m_key))
                    tout << mk_ismt2_pp(it->m_key, *m_temp_manager) << "\n";
            });

            CASSERT("sat_solver", solver.check_invariant());
            IF_VERBOSE(TACTIC_VERBOSITY_LVL, solver.display_status(verbose_stream()););
            TRACE("sat_dimacs", solver.display_dimacs(tout););
        }

        model_ref get_fpa_model(goal_ref const & g,
                fpa2bv_converter_prec & fpa2bv,
                bit_blaster_rewriter & bv2bool,
                sat::solver & solver,
                atom2bool_var & map) {
            // CMW: This is all done using the temporary manager, until at the very end we translate the model back to this->m.
            model_ref md = alloc(model, *m_temp_manager);
            sat::model const & ll_m = solver.get_model();
            TRACE("sat_tactic", for (unsigned i = 0; i < ll_m.size(); i++)
                tout << i << ":" << ll_m[i] << " "; tout << "\n";);
            atom2bool_var::iterator it = map.begin();
            atom2bool_var::iterator end = map.end();
            for (; it != end; ++it) {
                expr * n = it->m_key;
                sat::bool_var v = it->m_value;
                if (is_app(n) && to_app(n)->get_decl()->get_arity() != 0)
                    continue;
                TRACE("sat_tactic", tout << "extracting value of " << mk_ismt2_pp(n, *m_temp_manager) << "\nvar: " << v << "\n";);
                switch (sat::value_at(v, ll_m)) {
                case l_true: md->register_decl(to_app(n)->get_decl(), m_temp_manager->mk_true()); break;
                case l_false: md->register_decl(to_app(n)->get_decl(), m_temp_manager->mk_false()); break;
                default:
                    break;
                }
            }

            TRACE("sat_tactic", model_v2_pp(tout, *md););
            model_converter_ref bb_mc = mk_bit_blaster_model_converter(*m_temp_manager, bv2bool.const2bits());

            model_converter_ref bv_mc = mk_fpa2bv_model_converter(*m_temp_manager, fpa2bv.const2bv(), fpa2bv.rm_const2bv(), fpa2bv.uf2bvuf(), fpa2bv.uf23bvuf());
            bb_mc->operator()(md, 0);
            bv_mc->operator()(md, 0);

#ifdef Z3DEBUG
            std::cout << "Model: " << std::endl;
            for (unsigned i = 0 ; i < md->get_num_constants(); i++) {
                func_decl * d = md->get_constant(i);
                std::cout << d->get_name() << " = " << mk_ismt2_pp(md->get_const_interp(d), *m_temp_manager) << std::endl;
            }
#endif
            // md is in terms of the temporary manager.
            ast_translation translator(*m_temp_manager, this->m);
            return md->translate(translator);
        }

        void encode_fpa_terms(  goal_ref const & g,
                obj_map<func_decl,app*> & const2term_map)
        {
            for (obj_map<func_decl, app*>::iterator it = const2term_map.begin();
                    it!=const2term_map.end();
                    it++) {
                expr_ref q(m);
#ifdef Z3DEBUG
                std::cout << "Adding " << it->m_key->get_name() << " = " << mk_ismt2_pp(it->m_value, m) << std::endl;
#endif
                q = m.mk_eq(m.mk_const(it->m_key), it->m_value);
                g->assert_expr(q);
            }
        }

        lbool approximate_model_construction(goal_ref & g, obj_map<func_decl, unsigned> & const2prec_map) {
            lbool r = l_undef;
            // CMW: The following will introduce lots of stuff that we don't need (e.g., symbols)
            // To save memory, we use a separate, new manager that we can throw away afterwards.
            m_temp_manager = alloc(ast_manager, PGM_DISABLED);
            {
                ast_translation translator(m, *m_temp_manager);
                goal_ref ng = g->translate(translator);
                obj_map<func_decl, unsigned> const2prec_map_tm;

                for (obj_map<func_decl, unsigned>::iterator it = const2prec_map.begin();
                        it!=const2prec_map.end();
                        it++)
                    const2prec_map_tm.insert(translator(it->m_key), it->m_value);

                sat::solver sat_solver(m_params, 0);
                atom2bool_var atom_map(*m_temp_manager);
                { tactic_report report_i("fpa2bv_approx_before_bitblaster", *ng); }
                fpa2bv_converter_prec fpa2bv(*m_temp_manager, m_mode);
                bit_blaster_rewriter bv2bool(*m_temp_manager, m_params);
                bitblast(ng, fpa2bv, bv2bool, const2prec_map_tm, sat_solver, atom_map);
                { tactic_report report_i("fpa2bv_approx_after_bitblaster", *ng); }

                std::cout << "Iteration variables: " << sat_solver.num_vars() << std::endl;
                std::cout << "Iteration clauses: " << sat_solver.num_clauses() << std::endl;
                r = sat_solver.check();

                if (r == l_true)
                {
                    // we need to get the model and translate it back to m.
                    m_fpa_model = get_fpa_model(ng, fpa2bv, bv2bool, sat_solver, atom_map).get();
                }
                else
                    m_fpa_model = 0;

                // CMW: translator, etc, gets destroyed here, so all references
                // to temporary expressions are gone.
            }

            dealloc(m_temp_manager);
            m_temp_manager = 0;

            return r;
        }

        void lift( goal_ref const & g, func_decl_ref_vector & constants, obj_map<func_decl, app*> * const2term_map )
        {
            expr_ref new_new_curr(m);
            expr_ref new_curr(m);
            proof_ref new_pr(m);

            simplify(g);

            //Renaming subexpressions using new constants
            const_intro_rewriter const_rewriter(m, m_params);
            for (unsigned idx = 0; idx < g->size(); idx++) {
                if (g->inconsistent())
                    break;
                expr * curr = g->form(idx);
                const_rewriter(curr, new_curr, new_pr); //Introduces constants that replace subexpressions
                m_num_steps += const_rewriter.get_num_steps();
                if (m_proofs_enabled) {
                    proof * pr = g->pr(idx);
                    new_pr = m.mk_modus_ponens(pr, new_pr);
                }
                g->update(idx, new_curr, new_pr, g->dep(idx));
            }


            constants.set(const_rewriter.m_cfg.m_introduced_consts);
            const2term_map->swap(const_rewriter.m_cfg.m_const2term_map);

            // Note: Ideally, we would directly encode them. For now we're lazy and just add equalities
            // and we rely on fpa2bv_converter_prec to `magically' recognize the equalities we added.
            { tactic_report report_i("fpa2bv_approx_before_fpa_terms", *(g.get())); }
            encode_fpa_terms(g, *const2term_map);
            SASSERT(g.get()->is_well_sorted());


        }

        void verify_precise_model(  goal_ref const & g,
                model_ref & full_mdl,
                func_decl_ref_vector & constants,
                obj_map<func_decl, app*> & const2term_map,
                model_converter_ref & mc,
                goal_ref_buffer & result ){
            expr_ref res(m);

            for (unsigned j = 0; j < g->size(); j++) {
                full_mdl->eval(g->form(j), res, true);
                if (!m.is_true(res)) {
                    std::cout << "Failed: " << mk_ismt2_pp(g->form(j), m) << std::endl;
                    std::cout << "Evaluates to: " << mk_ismt2_pp(res, m) << std::endl;
                }
                SASSERT(m.is_true(res));
            }

            std::cout << "Full model: " << std::endl;
            for (unsigned i = 0 ; i < full_mdl->get_num_decls(); i++)
            {
                func_decl * d = full_mdl->get_decl(i);
                if(constants.contains(d))
                    std::cout << d->get_name() << " = " << mk_ismt2_pp(full_mdl->get_const_interp(d), m) << std::endl;
            }
            std::cout.flush();

            result.back()->reset();

            // Filter all the constants we introduced earlier from the model.
            filter_model_converter * fmc = alloc(filter_model_converter, m);
            for (obj_map<func_decl, app*>::iterator it = const2term_map.begin();
                    it != const2term_map.end();
                    it++)
                fmc->insert(it->m_key);
            mc = concat(fmc, model2model_converter(m_fpa_model.get()));
        }

        void setup_options(goal_ref const & g){
            SASSERT(g->is_well_sorted());
            fail_if_proof_generation("fpa2bv_approx", g);
            fail_if_unsat_core_generation("fpa2bv_approx", g);
            m_proofs_enabled = g->proofs_enabled();
            m_produce_models = g->models_enabled();
            m_produce_unsat_cores = g->unsat_core_enabled();
            m_num_steps = 0;
        }



        void print_constants(func_decl_ref_vector & constants, obj_map<func_decl, unsigned> & const2prec_map){
#ifdef Z3DEBUG
            for(unsigned i=0;i<constants.size();i++)
            {
                func_decl * q = constants.get(i);
                std::cout<<q->get_name()<<":"<<const2prec_map.find(q)<<std::endl;
            }
#endif
        }

        virtual void operator()(goal_ref const & g, goal_ref_buffer & result,
                model_converter_ref & mc, proof_converter_ref & pc,
                expr_dependency_ref & core) {
            bool solved=false;
            mc = 0;
            pc = 0;
            core = 0;
            obj_map<func_decl, unsigned> const2prec_map;
            obj_map<func_decl, unsigned> next_const2prec_map;
            func_decl_ref_vector constants(m);
            obj_map<func_decl, app*> const2term_map;
            lbool r = l_true;
            unsigned iteration_cnt = 0;
            stopwatch sw;

            tactic_report report("fpa2bv_approx", *g);
            TRACE("fpa2bv_approx", tout << "BEFORE: " << std::endl; g->display(tout););
            result.reset();
            result.push_back(g.get());

            SASSERT(g->is_well_sorted());
            if (g->inconsistent())
                return;

            lift(g, constants, &const2term_map);

            init_precision_mapping(constants, const2prec_map, const2term_map);

            std::cout << "Simplified goal:" << std::endl;
            g->display(std::cout);

            while (!solved && !m_cancel)
            {
                std::cout << "=============== Starting iteration " << ++iteration_cnt << std::endl;

                sw.reset();
                sw.start();

                // Copy the goal
                goal_ref  mg(alloc(goal, g->m(),g->proofs_enabled(),g->models_enabled(),g->unsat_core_enabled()));
                mg->copy_from(*g.get());
                tactic_report report_i("fpa2bv_approx_i", *mg);

                print_constants(constants, const2prec_map);

                TRACE("fpa2bv_approx_goal_i", mg->display(tout); );

                r = approximate_model_construction(mg, const2prec_map);

                std::cout << "Approximation is " << (r==l_true?"SAT":r==l_false?"UNSAT":"UNKNOWN") << std::endl;

                if (r == l_true) {
                    model_ref full_mdl = alloc(model, m);
                    obj_map<expr, double> err_est;

                    if (fully_encoded(const2prec_map)) {
                        full_mdl = m_fpa_model;
                        solved = true;
                        std::cout<<"Model is at full precision, no patching needed!"<<std::endl;
                        std::cout.flush();
                    }
                    else {
                        solved = precise_model_reconstruction(m_fpa_model, full_mdl, mg, err_est, constants, const2term_map);

                        std::cout<<"Patching of the model "<<((solved)?"succeeded":"failed")<<std::endl;
                        std::cout.flush();
                    }
                    if (!solved)
                        model_guided_approximation_refinement(m_fpa_model, full_mdl, mg, constants, const2prec_map, const2term_map, err_est, next_const2prec_map);
                    else
                        verify_precise_model(g,full_mdl,constants,const2term_map,mc,result);

                } else if (r == l_false) {
                    if(!proof_guided_refinement(g, constants, const2prec_map, next_const2prec_map))
                    {// Refinement failed -> This is unsat.
                        solved = true;
                        result.back()->reset();
                        result.back()->assert_expr(m.mk_false());
                    }
                } else {
                    // CMW: When the sat solver comes back with `unknown', what shall we do?
                    // AZ: Blindly refine?
                    m_cancel = true;
                }

                const2prec_map.swap(next_const2prec_map);
                next_const2prec_map.reset();
                std::cout << "Iteration time: " << sw.get_current_seconds() << std::endl;
            }

            std::cout << "=============== Terminating " << std::endl;
            dec_ref_map_key_values(m, const2term_map);
            std::cout << "Iteration count: " << iteration_cnt << std::endl;
        }
    };

    imp * m_imp;
    params_ref m_params;

public:
    fpa2bv_approx_tactic(ast_manager & m, params_ref const & p) :
        m_params(p){
        m_imp = alloc(imp, m, p, FPAA_DEFAULT_MODE);
    }

    virtual tactic * translate(ast_manager & m) {
        return alloc(fpa2bv_approx_tactic, m, m_params);
    }

    virtual ~fpa2bv_approx_tactic() {
        dealloc(m_imp);
    }

    virtual void updt_params(params_ref const & p) {
        m_params = p;
        m_imp->updt_params(p);
    }

    virtual void collect_param_descrs(param_descrs & r) {
    }

    virtual void operator()(goal_ref const & in, goal_ref_buffer & result,
            model_converter_ref & mc, proof_converter_ref & pc,
            expr_dependency_ref & core) {
        (*m_imp)(in, result, mc, pc, core);
    }

    virtual void cleanup() {
        ast_manager & m = m_imp->m;
        imp * d = m_imp;
#pragma omp critical (tactic_cancel)
        {
            d = m_imp;
        }
        dealloc(d);
        d = alloc(imp, m, m_params, FPAA_DEFAULT_MODE);
#pragma omp critical (tactic_cancel)
        {
            m_imp = d;
        }
    }

protected:
    virtual void set_cancel(bool f) {
    if (m_imp)
        m_imp->set_cancel(f);
}
};

tactic * mk_fpa2bv_approx_tactic(ast_manager & m, params_ref const & p) {
    return and_then(clean(alloc(fpa2bv_approx_tactic, m, p)), mk_fail_if_undecided_tactic());
}


