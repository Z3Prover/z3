
/*++
Copyright (c) 2015 Microsoft Corporation

--*/

/*--
 Module Name:
 
     hnf.h
 
 Abstract:
 
     Horn normal form convertion.

 Author:
 
 
 Notes:
 
     Very similar to NNF.
 
--*/
 
#ifndef HNF_H_
#define HNF_H_
 
#include"ast.h"
#include"params.h"
#include"defined_names.h"
#include"proof_converter.h"
 
class hnf {
    class imp;
    imp *  m_imp;
 public:
    hnf(ast_manager & m);
    ~hnf();
     
    void operator()(expr * n,                          // [IN] expression that should be put into Horn NF
                    proof* p,                          // [IN] proof of n
                    expr_ref_vector & rs,              // [OUT] resultant (conjunction) of expressions
                    proof_ref_vector& ps               // [OUT] proofs of rs
                    );

    void set_name(symbol const& name);    
    void reset();
    func_decl_ref_vector const& get_fresh_predicates();
};
 
#endif /* HNF_H_ */
