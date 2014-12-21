/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    theory_fpa.h

Abstract:

    Floating-Point Theory Plugin

Author:

    Christoph (cwinter) 2014-04-23

Revision History:

--*/
#ifndef _THEORY_FPA_H_
#define _THEORY_FPA_H_

#include"smt_theory.h"
#include"trail.h"
#include"fpa2bv_converter.h"
#include"fpa2bv_rewriter.h"
#include"th_rewriter.h"
#include"value_factory.h"
#include"smt_model_generator.h"

namespace smt {

    class fpa_factory : public value_factory {
        float_util          m_util;

        virtual app * mk_value_core(mpf const & val, sort * s) {
            SASSERT(m_util.get_ebits(s) == val.get_ebits());
            SASSERT(m_util.get_sbits(s) == val.get_sbits());
            return m_util.mk_value(val);
        }

    public:
        fpa_factory(ast_manager & m, family_id fid) :
            value_factory(m, fid),
            m_util(m) {
        }

        virtual ~fpa_factory() {}

        virtual expr * get_some_value(sort * s) { NOT_IMPLEMENTED_YET(); }
        virtual bool get_some_values(sort * s, expr_ref & v1, expr_ref & v2) { NOT_IMPLEMENTED_YET(); }
        virtual expr * get_fresh_value(sort * s) { NOT_IMPLEMENTED_YET(); }
        virtual void register_value(expr * n) { /* Ignore */ }

        app * mk_value(mpf const & x) { 
            return m_util.mk_value(x);
        }
    };    

    class theory_fpa : public theory {
        class th_trail_stack : public trail_stack<theory_fpa> {
        public: 
            th_trail_stack(theory_fpa & th) : trail_stack<theory_fpa>(th) {}
            virtual ~th_trail_stack() {}
        };

        class fpa2bv_converter_wrapped : public fpa2bv_converter {
        public:
            theory_fpa & m_th;
            fpa2bv_converter_wrapped(ast_manager & m, theory_fpa * th) :
                fpa2bv_converter(m),
                m_th(*th) {}
            virtual ~fpa2bv_converter_wrapped() {}
            virtual void mk_const(func_decl * f, expr_ref & result);
            virtual void mk_rm_const(func_decl * f, expr_ref & result);
        };
        
        class fpa_value_proc : public model_value_proc {
        protected:
            theory_fpa                    & m_th;
            app_ref                         m_a;
            svector<model_value_dependency> m_dependencies;
        public:
            fpa_value_proc(theory_fpa * th, app_ref & a) : m_th(*th), m_a(a) {}
            void add_dependency(enode * n) { m_dependencies.push_back(model_value_dependency(n)); }
            virtual ~fpa_value_proc() {}
            virtual void get_dependencies(buffer<model_value_dependency> & result) {
                result.append(m_dependencies.size(), m_dependencies.c_ptr());
            }
            virtual app * mk_value(model_generator & mg, ptr_vector<expr> & values);
        };

        class fpa_rm_value_proc : public fpa_value_proc {
            float_util & m_fu;
            bv_util    & m_bu;
        public:
            fpa_rm_value_proc(theory_fpa * th, app_ref & a) : 
                fpa_value_proc(th, a), 
                m_fu(th->m_converter.fu()), 
                m_bu(th->m_converter.bu()) {}
            void add_dependency(enode * n) { fpa_value_proc::add_dependency(n); }
            virtual ~fpa_rm_value_proc() {}
            virtual app * mk_value(model_generator & mg, ptr_vector<expr> & values);
        };
    
    public:
        class atom {
        public:
            virtual ~atom() {}
        };

        struct pred_atom : public atom {
            literal    m_var;
            literal    m_def;
            pred_atom(literal v, literal d) : m_var(v), m_def(d) {}
            virtual ~pred_atom() {}
        };

        typedef ptr_vector<pred_atom> bool_var2atom;
        void insert_bv2a(bool_var bv, pred_atom * a) { m_bool_var2atom.setx(bv, a, 0); }
        void erase_bv2a(bool_var bv) { m_bool_var2atom[bv] = 0; }
        pred_atom * get_bv2a(bool_var bv) const { return m_bool_var2atom.get(bv, 0); }
        region & get_region() { return m_trail_stack.get_region(); }        

    protected:
        fpa2bv_converter_wrapped  m_converter;
        fpa2bv_rewriter           m_rw;
        th_rewriter               m_th_rw;
        th_trail_stack            m_trail_stack;
        bool_var2atom             m_bool_var2atom;
        enode_vector              m_temporaries;
        vector<theory_var>        m_tvars;        
        fpa_factory *             m_factory;
        obj_map<sort, func_decl*> m_wraps;
        obj_map<sort, func_decl*> m_unwraps;
        float_decl_plugin         m_flt_plugin;

        virtual final_check_status final_check_eh() { return FC_DONE; }
        virtual bool internalize_atom(app * atom, bool gate_ctx);
        virtual bool internalize_term(app * term);
        virtual void apply_sort_cnstr(enode * n, sort * s);
        virtual void new_eq_eh(theory_var, theory_var);
        virtual void new_diseq_eh(theory_var, theory_var);
        virtual void push_scope_eh();
        virtual void pop_scope_eh(unsigned num_scopes);
        virtual void reset_eh();
        virtual theory* mk_fresh(context*) { return alloc(theory_fpa, get_manager()); }
        virtual char const * get_name() const { return "fpa"; }        

        virtual model_value_proc * mk_value(enode * n, model_generator & mg);
        
        void assign_eh(bool_var v, bool is_true);
        virtual void relevant_eh(app * n);
        virtual void init_model(model_generator & m);
        virtual void finalize_model(model_generator & mg);

    public:
        theory_fpa(ast_manager& m);
        virtual ~theory_fpa();

        virtual void display(std::ostream & out) const;

    protected:
        expr_ref mk_side_conditions();
        expr_ref convert_atom(expr * e);
        expr_ref convert_term(expr * e);
        void get_wrap(sort * s, func_decl *& wrap, func_decl *& unwrap);
        void add_trail(ast * a);

        void mk_bv_eq(expr * x, expr * y);
        void attach_new_th_var(enode * n);
        void assert_cnstr(expr * e);
    };

};

#endif /* _THEORY_FPA_H_ */
