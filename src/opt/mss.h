/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    mss.h

Abstract:
   
    Maximal satisfying subset/minimal correction sets: MSS/MCS

Author:

    Nikolaj Bjorner (nbjorner) 2014-2-8

Notes:

--*/
#ifndef _MSS_H_
#define _MSS_H_

namespace opt {
    class mss {
        ref<solver>&  m_s;
        ast_manager&  m;
        volatile bool m_cancel;
        typedef ptr_vector<expr> exprs;
        typedef obj_hashtable<expr>  expr_set;
        exprs         m_mss;
        expr_set      m_mcs;
        model_ref     m_model;
    public:
        mss(ref<solver>& s, ast_manager& m);
        ~mss();
        
        lbool operator()(vector<exprs> const& cores, exprs& literals);
                
        void set_cancel(bool f) { m_cancel = f; }

        void get_model(model_ref& mdl) { mdl = m_model; }

    private:
        void  initialize(vector<exprs>& cores, exprs& literals);
        bool  check_result();
        void  update_model();
        void  update_set(exprs& lits);
        lbool process_core(exprs const& _core);
        lbool process_core(unsigned sz, exprs& core, bool& has_mcs, bool is_last);
        void display(std::ostream& out) const;
        void display_vec(std::ostream& out, unsigned sz, expr* const* args) const;
        bool check_invariant() const;
    };

};

#endif
