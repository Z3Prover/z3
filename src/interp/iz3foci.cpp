/*++
  Copyright (c) 2011 Microsoft Corporation

  Module Name:

  iz3foci.cpp

  Abstract:

  Implements a secondary solver using foci2.

  Author:

  Ken McMillan (kenmcmil)

  Revision History:

  --*/

#include <sstream>
#include <iostream>

#include "iz3hash.h"
#include "foci2.h"
#include "iz3foci.h"

using namespace stl_ext;

class iz3foci_impl : public iz3secondary {

    int frames;
    int *parents;
    foci2 *foci;
    foci2::symb select_op;
    foci2::symb store_op;
    foci2::symb mod_op;

public:
    iz3foci_impl(iz3mgr *mgr, int _frames, int *_parents) : iz3secondary(*mgr) {
        frames = _frames;
        parents = _parents;
        foci = 0;
    }

    typedef hash_map<ast,foci2::ast> AstToNode;
    AstToNode ast_to_node;                    // maps Z3 ast's to foci expressions

    typedef hash_map<foci2::ast,ast> NodeToAst;
    NodeToAst node_to_ast;                    // maps Z3 ast's to foci expressions

    // We only use this for FuncDeclToSymbol, which has no range destructor
    struct symb_hash {
        size_t operator()(const symb &s) const {
            return (size_t) s;
        }
    };

    typedef hash_map<symb,foci2::symb> FuncDeclToSymbol; 
    FuncDeclToSymbol func_decl_to_symbol;     // maps Z3 func decls to symbols

    typedef hash_map<foci2::symb,symb> SymbolToFuncDecl; 
    SymbolToFuncDecl symbol_to_func_decl;     // maps symbols to Z3 func decls

    int from_symb(symb func){
        std::string name = string_of_symbol(func);
        bool is_bool = is_bool_type(get_range_type(func));
        foci2::symb f;
        if(is_bool)
            f = foci->mk_pred(name);
        else
            f = foci->mk_func(name);
        symbol_to_func_decl[f] = func;
        func_decl_to_symbol[func] = f;
        return f;
    }
  
    // create a symbol corresponding to a DeBruijn index of a particular type
    // the type has to be encoded into the name because the same index can
    // occur with different types
    foci2::symb make_deBruijn_symbol(int index, type ty){
        std::ostringstream s;
        // s << "#" << index << "#" << type;
        return foci->mk_func(s.str());
    }

    int from_Z3_ast(ast t){
        std::pair<ast,foci2::ast> foo(t,0);
        std::pair<AstToNode::iterator, bool> bar = ast_to_node.insert(foo);
        int &res = bar.first->second;
        if(!bar.second) return res;
        int nargs = num_args(t);
        std::vector<foci2::ast> args(nargs);
        for(int i = 0; i < nargs; i++)
            args[i] = from_Z3_ast(arg(t,i));
    
        switch(op(t)){
        case True:
            res = foci->mk_true(); break;
        case False:
            res = foci->mk_false(); break;
        case And:
            res = foci->mk_op(foci2::And,args); break;
        case Or:
            res = foci->mk_op(foci2::Or,args); break;
        case Not:
            res = foci->mk_op(foci2::Not,args[0]); break;
        case Iff:
            res = foci->mk_op(foci2::Iff,args); break;
        case OP_OEQ: // bit of a mystery, this one...
            if(args[0] == args[1]) res = foci->mk_true(); 
            else res = foci->mk_op(foci2::Iff,args);
            break;
        case Ite:
            if(is_bool_type(get_type(t)))
                res = foci->mk_op(foci2::And,foci->mk_op(foci2::Or,foci->mk_op(foci2::Not,args[0]),args[1]),foci->mk_op(foci2::Or,args[0],args[2]));
            else
                res = foci->mk_op(foci2::Ite,args);
            break;
        case Equal:
            res = foci->mk_op(foci2::Equal,args); break;
        case Implies:
            args[0] = foci->mk_op(foci2::Not,args[0]); res = foci->mk_op(foci2::Or,args); break;
        case Xor:
            res = foci->mk_op(foci2::Not,foci->mk_op(foci2::Iff,args)); break;
        case Leq:
            res = foci->mk_op(foci2::Leq,args); break;
        case Geq:
            std::swap(args[0],args[1]); res = foci->mk_op(foci2::Leq,args); break;
        case Gt:
            res = foci->mk_op(foci2::Not,foci->mk_op(foci2::Leq,args)); break;
        case Lt:
            std::swap(args[0],args[1]); res = foci->mk_op(foci2::Not,foci->mk_op(foci2::Leq,args)); break;
        case Plus:
            res = foci->mk_op(foci2::Plus,args); break;
        case Sub:
            args[1] = foci->mk_op(foci2::Times,foci->mk_int("-1"),args[1]); res = foci->mk_op(foci2::Plus,args); break;
        case Uminus: 
            res = foci->mk_op(foci2::Times,foci->mk_int("-1"),args[0]); break;
        case Times:
            res = foci->mk_op(foci2::Times,args); break;
        case Idiv:
            res = foci->mk_op(foci2::Div,args); break;
        case Mod:
            res = foci->mk_app(mod_op,args); break;
        case Select:
            res = foci->mk_app(select_op,args); break;
        case Store:
            res = foci->mk_app(store_op,args); break;
        case Distinct:
            res = foci->mk_op(foci2::Distinct,args); break;
        case Uninterpreted: {
            symb func = sym(t);
            FuncDeclToSymbol::iterator it = func_decl_to_symbol.find(func);
            foci2::symb f = (it == func_decl_to_symbol.end()) ? from_symb(func) : it->second;
            if(foci->get_symb(f).substr(0,3) == "lbl" && args.size()==1) // HACK to handle Z3 labels
                res = args[0];
            else if(foci->get_symb(f).substr(0,3) == "lbl" && args.size()==0) // HACK to handle Z3 labels
                res = foci->mk_true();
            else res = foci->mk_app(f,args);
            break;
        }
        case Numeral: {
            std::string s = string_of_numeral(t);
            res = foci->mk_int(s);
            break;
        }
        case Forall: 
        case Exists: {
            bool is_forall = op(t) == Forall;
            foci2::ops qop = is_forall ? foci2::Forall : foci2::Exists;
            int bvs = get_quantifier_num_bound(t);
            std::vector<int> foci_bvs(bvs);
            for(int i = 0; i < bvs; i++){
                std::string name = get_quantifier_bound_name(t,i);
                //Z3_string name = Z3_get_symbol_string(ctx,sym);
                // type ty = get_quantifier_bound_type(t,i);
                foci2::symb f = foci->mk_func(name);
                foci2::ast v = foci->mk_app(f,std::vector<foci2::ast>());
                foci_bvs[i] = v;
            }
            foci2::ast body = from_Z3_ast(get_quantifier_body(t));
            foci_bvs.push_back(body);
            res = foci->mk_op(qop,foci_bvs);
            node_to_ast[res] = t; // desperate
            break;
        }
        case Variable: {  // a deBruijn index
            int index = get_variable_index_value(t);
            type ty = get_type(t);
            foci2::symb symbol = make_deBruijn_symbol(index,ty);
            res = foci->mk_app(symbol,std::vector<foci2::ast>());
            break;
        }
        default:
            {
                std::cerr << "iZ3: unsupported Z3 operator in expression\n ";
                print_expr(std::cerr,t);
                std::cerr << "\n";
                SASSERT(0 && "iZ3: unsupported Z3 operator");
            }
        }
        return res;
    }

    // convert an expr to Z3 ast
    ast to_Z3_ast(foci2::ast i){
        std::pair<foci2::ast,ast> foo(i,ast());
        std::pair<NodeToAst::iterator,bool> bar = node_to_ast.insert(foo);
        if(!bar.second) return bar.first->second;
        ast &res = bar.first->second;

        if(i < 0){
            res = mk_not(to_Z3_ast(-i));
            return res;
        }

        // get the arguments
        unsigned n = foci->get_num_args(i);
        std::vector<ast> args(n);
        for(unsigned j = 0; j < n; j++)
            args[j] = to_Z3_ast(foci->get_arg(i,j));

        // handle operators
        foci2::ops o;
        foci2::symb f;
        std::string nval;
        if(foci->get_true(i))
            res = mk_true();
        else if(foci->get_false(i))
            res = mk_false();
        else if(foci->get_op(i,o)){
            switch(o){
            case foci2::And:
                res = make(And,args); break; 
            case foci2::Or:
                res = make(Or,args); break; 
            case foci2::Not:
                res = mk_not(args[0]); break; 
            case foci2::Iff:
                res = make(Iff,args[0],args[1]); break; 
            case foci2::Ite:
                res = make(Ite,args[0],args[1],args[2]); break;
            case foci2::Equal:
                res = make(Equal,args[0],args[1]); break; 
            case foci2::Plus:
                res = make(Plus,args); break; 
            case foci2::Times:
                res = make(Times,args); break; 
            case foci2::Div:
                res = make(Idiv,args[0],args[1]); break;
            case foci2::Leq:
                res = make(Leq,args[0],args[1]); break; 
            case foci2::Distinct:
                res = make(Distinct,args);
                break;
            case foci2::Tsym:
                res = mk_true();
                break;
            case foci2::Fsym:
                res = mk_false();
                break;
            case foci2::Forall:
            case foci2::Exists:
                {
                    int nargs = n;
                    std::vector<ast> bounds(nargs-1);
                    for(int i = 0; i < nargs-1; i++)
                        bounds[i] = args[i];
                    opr oz = o == foci2::Forall ? Forall : Exists;
                    res = make_quant(oz,bounds,args[nargs-1]);
                }
                break;
            default:
                SASSERT(false && "unknown built-in op");
            }
        }
        else if(foci->get_int(i,nval)){
            res = make_int(nval);
        }
        else if(foci->get_func(i,f)){
            if(f == select_op){
                SASSERT(n == 2);
                res = make(Select,args[0],args[1]);
            }
            else if(f == store_op){
                SASSERT(n == 3);
                res = make(Store,args[0],args[1],args[2]);
            }
            else if(f == mod_op){
                SASSERT(n == 2);
                res = make(Mod,args[0],args[1]);
            }
            else {
                std::pair<int,symb> foo(f,(symb)0);
                std::pair<SymbolToFuncDecl::iterator,bool> bar = symbol_to_func_decl.insert(foo);
                symb &func_decl = bar.first->second;
                if(bar.second){
                    std::cout << "unknown function symbol:\n";
                    foci->show_ast(i);
                    SASSERT(0);
                }
                res = make(func_decl,args);
            }
        }
        else {
            std::cerr << "iZ3: unknown FOCI expression kind\n";
            SASSERT(0 && "iZ3: unknown FOCI expression kind");
        }
        return res;
    }

    int interpolate(const std::vector<ast> &cnsts, std::vector<ast> &itps){
        SASSERT((int)cnsts.size() == frames);
        std::string lia("lia");
#ifdef _FOCI2
        foci = foci2::create(lia);
#else
        foci = 0;
#endif
        if(!foci){
            std::cerr << "iZ3: cannot find foci lia solver.\n";
            SASSERT(0);
        }
        select_op = foci->mk_func("select");
        store_op = foci->mk_func("store");
        mod_op = foci->mk_func("mod");
        std::vector<foci2::ast> foci_cnsts(frames), foci_itps(frames-1), foci_parents;
        if(parents)
            foci_parents.resize(frames);
        for(int i = 0; i < frames; i++){
            foci_cnsts[i] = from_Z3_ast(cnsts[i]);
            if(parents)
                foci_parents[i] = parents[i];
        }
        int res = foci->interpolate(foci_cnsts, foci_itps, foci_parents);
        if(res == 0){
            SASSERT((int)foci_itps.size() == frames-1);
            itps.resize(frames-1);
            for(int i = 0; i < frames-1; i++){
                // foci->show_ast(foci_itps[i]);
                itps[i] = to_Z3_ast(foci_itps[i]);
            }
        }
        ast_to_node.clear();
        node_to_ast.clear();
        func_decl_to_symbol.clear();
        symbol_to_func_decl.clear();
        delete foci;
        return res;
    }

};

iz3secondary *iz3foci::create(iz3mgr *mgr, int num, int *parents){
    return new iz3foci_impl(mgr,num,parents);
}
