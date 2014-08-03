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
        solver&       s;
        ast_manager&  m;
        volatile bool m_cancel;
        typedef ptr_vector<expr> exprs;
        typedef obj_hashtable<expr>  expr_set;
        exprs         m_mss;
        expr_set      m_mcs;
        exprs         m_todo;
        model_ref     m_model;
    public:
        mss(solver& s, ast_manager& m);
        ~mss();
        
        lbool operator()(vector<ptr_vector<expr> > const& cores, ptr_vector<expr>& literals);
                
        void set_cancel(bool f) { m_cancel = f; }

    private:
        void  check_parameters(vector<exprs > const& cores, exprs& literals);
        void  update_model();
        void  update_set(exprs& lits);
        lbool process_core(exprs const& _core);
        lbool process_core(unsigned sz, exprs& core);
        void display(std::ostream& out) const;
    };

};

#endif
