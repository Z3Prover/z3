#include "ackermanize.h"
#include "smtparser.h"
#include "ast_pp.h"

void tst_ackermanize()
{
    ast_manager manager;
    
    smtlib::parser* parser = smtlib::parser::create(manager);
    ackermanize ack(manager);

    ast_ref<const_decl_ast> fD(manager);
    ast_ref<const_decl_ast> xD(manager);
    ast_ref<type_decl_ast> AD(manager);
    ast_ref<type_ast> A(manager);
    ast_ref<> a1(manager), a2(manager), a3(manager), a4(manager), 
        a5(manager), a6(manager), a7(manager);
    ast_ref<> r(manager);

    AD  = manager.mk_type_decl(symbol("A"));
    A   = manager.mk_type(AD.get());
    fD  = manager.mk_const_decl(symbol("f"), A.get(), A.get(), A.get());
    a1  = manager.mk_const(manager.mk_const_decl(symbol("a1"), A.get()));
    a2  = manager.mk_const(manager.mk_const_decl(symbol("a2"), A.get()));
    a3  = manager.mk_const(manager.mk_const_decl(symbol("a3"), A.get()));
    a4  = manager.mk_const(manager.mk_const_decl(symbol("a4"), A.get()));
    a5  = manager.mk_const(manager.mk_const_decl(symbol("a5"), A.get()));
    a6  = manager.mk_const(manager.mk_const_decl(symbol("a6"), A.get()));
    a7  = manager.mk_const(manager.mk_const_decl(symbol("a7"), A.get()));
    
    r = manager.mk_const(manager.get_basic_family_id(),
                         OP_EQ,
                         manager.mk_const(fD.get(), a1.get(), a2.get()),
                         manager.mk_const(fD.get(), a2.get(), a3.get()));             

    TRACE("ackermanize", tout << mk_pp(r.get()) << std::endl;);

    ack.reduce(r);

    TRACE("ackermanize", tout << mk_pp(r.get()) << std::endl;);

}
