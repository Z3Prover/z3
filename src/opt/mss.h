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
#ifndef MSS_H_
#define MSS_H_

namespace opt {
    class mss {
        solver&       m_s;
        ast_manager&  m;
        typedef ptr_vector<expr> exprs;
        typedef obj_hashtable<expr>  expr_set;
        exprs         m_mss;
        expr_set      m_mcs;
        expr_set      m_mss_set;
        vector<exprs> m_cores;
        exprs         m_todo;
        model_ref     m_model;
    public:
        mss(solver& s, ast_manager& m);
        ~mss();
        
        lbool operator()(model* initial_model, vector<exprs> const& cores, exprs& literals, exprs& mcs);
                

        void get_model(model_ref& mdl) { mdl = m_model; }

    private:
        void  initialize(exprs& literals);
        bool  check_result();
        void  add_mss(expr* n);
        void  update_mss();
        void  update_core(exprs& core);
        lbool process_core(unsigned sz, exprs& core, bool& has_mcs, bool is_last);
        void display(std::ostream& out) const;
        void display_vec(std::ostream& out, unsigned sz, expr* const* args) const;
        bool check_invariant() const;
    };

};

#endif
