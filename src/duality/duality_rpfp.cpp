/*++
  Copyright (c) 2012 Microsoft Corporation

  Module Name:

  duality_rpfp.h

  Abstract:

  implements relational post-fixedpoint problem
  (RPFP) data structure.

  Author:

  Ken McMillan (kenmcmil)

  Revision History:


  --*/



#ifdef _WINDOWS
#pragma warning(disable:4996)
#pragma warning(disable:4800)
#pragma warning(disable:4267)
#endif

#include <algorithm>
#include <fstream>
#include <set>
#include <iterator>


#include "duality.h"
#include "duality_profiling.h"

// TODO: do we need these?
#ifdef Z3OPS

class Z3_subterm_truth {
public:
    virtual bool eval(Z3_ast f) = 0;
    ~Z3_subterm_truth(){}
};

Z3_subterm_truth *Z3_mk_subterm_truth(Z3_context ctx, Z3_model model);

#endif

#include <stdio.h>

// TODO: use something official for this
int debug_gauss = 0;

namespace Duality {

    static char string_of_int_buffer[20];

    const char *Z3User::string_of_int(int n){
        sprintf(string_of_int_buffer,"%d",n);
        return string_of_int_buffer;
    }

    RPFP::Term RPFP::SuffixVariable(const Term &t, int n)
    {
        std::string name = t.decl().name().str() + "_" + string_of_int(n);
        return ctx.constant(name.c_str(), t.get_sort());
    }

    RPFP::Term RPFP::HideVariable(const Term &t, int n)
    {
        std::string name = std::string("@p_") + t.decl().name().str() + "_" + string_of_int(n);
        return ctx.constant(name.c_str(), t.get_sort());
    }

    void RPFP::RedVars(Node *node, Term &b, std::vector<Term> &v)
    {
        int idx = node->number;
        if(HornClauses)
            b = ctx.bool_val(true);
        else {
            std::string name = std::string("@b_") + string_of_int(idx);
            symbol sym = ctx.str_symbol(name.c_str());
            b = ctx.constant(sym,ctx.bool_sort());
        }
        // ctx.constant(name.c_str(), ctx.bool_sort());
        v = node->Annotation.IndParams;
        for(unsigned i = 0; i < v.size(); i++)
            v[i] = SuffixVariable(v[i],idx);
    }

    void Z3User::SummarizeRec(hash_set<ast> &memo, std::vector<expr> &lits, int &ops, const Term &t){
        if(memo.find(t) != memo.end())
            return;
        memo.insert(t);
        if(t.is_app()){
            decl_kind k = t.decl().get_decl_kind();
            if (k == And || k == Or || k == Not || k == Implies || k == Iff) {
                ops++;
                int nargs = t.num_args();
                for (int i = 0; i < nargs; i++)
                    SummarizeRec(memo, lits, ops, t.arg(i));
                return;
            }
        }
        lits.push_back(t);
    }

    int RPFP::CumulativeDecisions(){
#if 0
        std::string stats = Z3_statistics_to_string(ctx);
        int pos = stats.find("decisions:");
        pos += 10;
        int end = stats.find('\n',pos);
        std::string val = stats.substr(pos,end-pos);
        return atoi(val.c_str());
#endif
        return slvr().get_num_decisions();
    }


    void Z3User::Summarize(const Term &t){
        hash_set<ast> memo; std::vector<expr> lits; int ops = 0;
        SummarizeRec(memo, lits, ops, t);
        std::cout << ops << ": ";
        for(unsigned i = 0; i < lits.size(); i++){
            if(i > 0) std::cout << ", ";
            std::cout << lits[i];
        }
    }

    int Z3User::CountOperatorsRec(hash_set<ast> &memo, const Term &t){
        if(memo.find(t) != memo.end())
            return 0;
        memo.insert(t);
        if(t.is_app()){
            decl_kind k = t.decl().get_decl_kind();
            if (k == And || k == Or) {
                int count = 1;
                int nargs = t.num_args();
                for (int i = 0; i < nargs; i++)
                    count += CountOperatorsRec(memo, t.arg(i));
                return count;
            }
            return 0;
        }
        if(t.is_quantifier()){
            int nbv = t.get_quantifier_num_bound();
            return CountOperatorsRec(memo,t.body()) + 2 * nbv; // count 2 for each quantifier
        }
        return 0;
    }

    int Z3User::CountOperators(const Term &t){
        hash_set<ast> memo;
        return CountOperatorsRec(memo,t);
    }


    Z3User::Term Z3User::conjoin(const std::vector<Term> &args){
        return ctx.make(And,args);
    }
  
    Z3User::Term Z3User::sum(const std::vector<Term> &args){
        return ctx.make(Plus,args);
    }

    RPFP::Term RPFP::RedDualRela(Edge *e, std::vector<Term> &args, int idx){
        Node *child = e->Children[idx];
        Term b(ctx);
        std::vector<Term> v;
        RedVars(child, b, v);
        for (unsigned i = 0; i < args.size(); i++) {
            if (eq(args[i].get_sort(), ctx.bool_sort()))
                args[i] = ctx.make(Iff, args[i], v[i]);
            else
                args[i] = args[i] == v[i];
        }
        return args.size() > 0 ? (b && conjoin(args)) : b;
    }

    Z3User::Term Z3User::CloneQuantifier(const Term &t, const Term &new_body){
#if 0
        Z3_context c = ctx;
        Z3_ast a = t;
        std::vector<Z3_pattern> pats;
        int num_pats = Z3_get_quantifier_num_patterns(c,a);
        for(int i = 0; i < num_pats; i++)
            pats.push_back(Z3_get_quantifier_pattern_ast(c,a,i));
        std::vector<Z3_ast> no_pats;
        int num_no_pats = Z3_get_quantifier_num_patterns(c,a);
        for(int i = 0; i < num_no_pats; i++)
            no_pats.push_back(Z3_get_quantifier_no_pattern_ast(c,a,i));
        int bound = Z3_get_quantifier_num_bound(c,a);
        std::vector<Z3_sort> sorts;
        std::vector<Z3_symbol> names;
        for(int i = 0; i < bound; i++){
            sorts.push_back(Z3_get_quantifier_bound_sort(c,a,i));
            names.push_back(Z3_get_quantifier_bound_name(c,a,i));
        }
        Z3_ast foo = Z3_mk_quantifier_ex(c,
                                         Z3_is_quantifier_forall(c,a),
                                         Z3_get_quantifier_weight(c,a),
                                         0,
                                         0,
                                         num_pats,
                                         VEC2PTR(pats),
                                         num_no_pats,
                                         VEC2PTR(no_pats),
                                         bound,
                                         VEC2PTR(sorts),
                                         VEC2PTR(names),
                                         new_body);
        return expr(ctx,foo);
#endif
        return clone_quantifier(t,new_body);
    }


    RPFP::Term RPFP::LocalizeRec(Edge *e,  hash_map<ast,Term> &memo, const Term &t)
    {
        std::pair<ast,Term> foo(t,expr(ctx));
        std::pair<hash_map<ast,Term>::iterator, bool> bar = memo.insert(foo);
        Term &res = bar.first->second;
        if(!bar.second) return res;
        hash_map<ast,Term>::iterator it = e->varMap.find(t);
        if (it != e->varMap.end()){
            res = it->second;
            return res;
        }
        if (t.is_app()) {
            func_decl f = t.decl();
            std::vector<Term> args;
            int nargs = t.num_args();
            for (int i = 0; i < nargs; i++)
                args.push_back(LocalizeRec(e, memo, t.arg(i)));
            hash_map<func_decl, int>::iterator rit = e->relMap.find(f);
            if (rit != e->relMap.end())
                res = RedDualRela(e, args, (rit->second));
            else {
                if (args.size() == 0 && f.get_decl_kind() == Uninterpreted && !ls->is_constant(f)) {
                    res = HideVariable(t, e->number);
                }
                else {
                    res = f(args.size(), VEC2PTR(args));
                }
            }
        }
        else if (t.is_quantifier()) {
            std::vector<expr> pats;
            t.get_patterns(pats);
            for (unsigned i = 0; i < pats.size(); i++)
                pats[i] = LocalizeRec(e, memo, pats[i]);
            Term body = LocalizeRec(e, memo, t.body());
            res = clone_quantifier(t, body, pats);
        }
        else res = t;
        return res;
    }

    void RPFP::SetEdgeMaps(Edge *e){
        timer_start("SetEdgeMaps");
        e->relMap.clear();
        e->varMap.clear();
        for(unsigned i = 0; i < e->F.RelParams.size(); i++){
            e->relMap[e->F.RelParams[i]] = i;
        }
        Term b(ctx);
        std::vector<Term> v;
        RedVars(e->Parent, b, v);
        for(unsigned i = 0; i < e->F.IndParams.size(); i++){
            // func_decl parentParam = e->Parent.Annotation.IndParams[i];
            expr oldname = e->F.IndParams[i];
            expr newname = v[i];
            e->varMap[oldname] = newname;
        }
        timer_stop("SetEdgeMaps");

    }


    RPFP::Term RPFP::Localize(Edge *e, const Term &t){
        timer_start("Localize");
        hash_map<ast,Term> memo;
        if(e->F.IndParams.size() > 0 && e->varMap.empty())
            SetEdgeMaps(e); // TODO: why is this needed?
        Term res = LocalizeRec(e,memo,t);
        timer_stop("Localize");
        return res;
    }


    RPFP::Term RPFP::ReducedDualEdge(Edge *e)
    {
        SetEdgeMaps(e);
        timer_start("RedVars");
        Term b(ctx);
        std::vector<Term> v;
        RedVars(e->Parent, b, v);
        timer_stop("RedVars");
        // ast_to_track = (ast)b;
        return implies(b, Localize(e, e->F.Formula));
    }

    TermTree *RPFP::ToTermTree(Node *root, Node *skip_descendant)
    {
        if(skip_descendant && root == skip_descendant)
            return new TermTree(ctx.bool_val(true));
        Edge *e = root->Outgoing;
        if(!e) return new TermTree(ctx.bool_val(true), std::vector<TermTree *>());
        std::vector<TermTree *> children(e->Children.size());
        for(unsigned i = 0; i < children.size(); i++)
            children[i] = ToTermTree(e->Children[i],skip_descendant);
        // Term top = ReducedDualEdge(e);
        Term top = e->dual.null() ? ctx.bool_val(true) : e->dual;
        TermTree *res = new TermTree(top, children);
        for(unsigned i = 0; i < e->constraints.size(); i++)
            res->addTerm(e->constraints[i]);
        return res;
    }

    TermTree *RPFP::GetGoalTree(Node *root){
        std::vector<TermTree *> children(1);
        children[0] = ToGoalTree(root);
        return new TermTree(ctx.bool_val(false),children);
    }

    TermTree *RPFP::ToGoalTree(Node *root)
    {
        Term b(ctx);
        std::vector<Term> v;
        RedVars(root, b, v);
        Term goal = root->Name(v);
        Edge *e = root->Outgoing;
        if(!e) return new TermTree(goal, std::vector<TermTree *>());
        std::vector<TermTree *> children(e->Children.size());
        for(unsigned i = 0; i < children.size(); i++)
            children[i] = ToGoalTree(e->Children[i]);
        // Term top = ReducedDualEdge(e);
        return new TermTree(goal, children);
    }

    Z3User::Term Z3User::SubstRec(hash_map<ast, Term> &memo, const Term &t)
    {
        std::pair<ast,Term> foo(t,expr(ctx));
        std::pair<hash_map<ast,Term>::iterator, bool> bar = memo.insert(foo);
        Term &res = bar.first->second;
        if(!bar.second) return res;
        if (t.is_app()) {
            func_decl f = t.decl();
            std::vector<Term> args;
            int nargs = t.num_args();
            for (int i = 0; i < nargs; i++)
                args.push_back(SubstRec(memo, t.arg(i)));
            res = f(args.size(), VEC2PTR(args));
        }
        else if (t.is_quantifier()) {
            std::vector<expr> pats;
            t.get_patterns(pats);
            for (unsigned i = 0; i < pats.size(); i++)
                pats[i] = SubstRec(memo, pats[i]);
            Term body = SubstRec(memo, t.body());
            res = clone_quantifier(t, body, pats);
        }
        // res = CloneQuantifier(t,SubstRec(memo, t.body()));
        else res = t;
        return res;
    }

    Z3User::Term Z3User::SubstRec(hash_map<ast, Term> &memo, hash_map<func_decl, func_decl> &map, const Term &t)
    {
        std::pair<ast,Term> foo(t,expr(ctx));
        std::pair<hash_map<ast,Term>::iterator, bool> bar = memo.insert(foo);
        Term &res = bar.first->second;
        if(!bar.second) return res;
        if (t.is_app()) {
            func_decl f = t.decl();
            std::vector<Term> args;
            int nargs = t.num_args();
            for (int i = 0; i < nargs; i++)
                args.push_back(SubstRec(memo, map, t.arg(i)));
            hash_map<func_decl, func_decl>::iterator it = map.find(f);
            if (it != map.end())
                f = it->second;
            res = f(args.size(), VEC2PTR(args));
        }
        else if (t.is_quantifier()) {
            std::vector<expr> pats;
            t.get_patterns(pats);
            for (unsigned i = 0; i < pats.size(); i++)
                pats[i] = SubstRec(memo, map, pats[i]);
            Term body = SubstRec(memo, map, t.body());
            res = clone_quantifier(t, body, pats);
        }
        // res = CloneQuantifier(t,SubstRec(memo, t.body()));
        else res = t;
        return res;
    }

    Z3User::Term Z3User::ExtractStores(hash_map<ast, Term> &memo, const Term &t, std::vector<expr> &cnstrs, hash_map<ast,expr> &renaming)
    {
        std::pair<ast,Term> foo(t,expr(ctx));
        std::pair<hash_map<ast,Term>::iterator, bool> bar = memo.insert(foo);
        Term &res = bar.first->second;
        if(!bar.second) return res;
        if (t.is_app()) {
            func_decl f = t.decl();
            std::vector<Term> args;
            int nargs = t.num_args();
            for (int i = 0; i < nargs; i++)
                args.push_back(ExtractStores(memo, t.arg(i), cnstrs, renaming));
            res = f(args.size(), VEC2PTR(args));
            if (f.get_decl_kind() == Store) {
                func_decl fresh = ctx.fresh_func_decl("@arr", res.get_sort());
                expr y = fresh();
                expr equ = ctx.make(Equal, y, res);
                cnstrs.push_back(equ);
                renaming[y] = res;
                res = y;
            }
        }
        else res = t;
        return res;
    }


    bool Z3User::IsLiteral(const expr &lit, expr &atom, expr &val){
        if (!(lit.is_quantifier() && IsClosedFormula(lit))) {
            if (!lit.is_app())
                return false;
            decl_kind k = lit.decl().get_decl_kind();
            if (k == Not) {
                if (IsLiteral(lit.arg(0), atom, val)) {
                    val = eq(val, ctx.bool_val(true)) ? ctx.bool_val(false) : ctx.bool_val(true);
                    return true;
                }
                return false;
            }
            if (k == And || k == Or || k == Iff || k == Implies)
                return false;
        }
        atom = lit;
        val = ctx.bool_val(true);
        return true;
    }

    expr Z3User::Negate(const expr &f){
        if(f.is_app() && f.decl().get_decl_kind() == Not)
            return f.arg(0);
        else if(eq(f,ctx.bool_val(true)))
            return ctx.bool_val(false);
        else if(eq(f,ctx.bool_val(false)))
            return ctx.bool_val(true);
        return !f;
    }

    expr Z3User::ReduceAndOr(const std::vector<expr> &args, bool is_and, std::vector<expr> &res){
        for(unsigned i = 0; i < args.size(); i++)
            if (!eq(args[i], ctx.bool_val(is_and))) {
                if (eq(args[i], ctx.bool_val(!is_and)))
                    return ctx.bool_val(!is_and);
                res.push_back(args[i]);
            }
        return expr();
    }

    expr Z3User::FinishAndOr(const std::vector<expr> &args, bool is_and){
        if(args.size() == 0)
            return ctx.bool_val(is_and);
        if(args.size() == 1)
            return args[0];
        return ctx.make(is_and ? And : Or,args);
    }

    expr Z3User::SimplifyAndOr(const std::vector<expr> &args, bool is_and){
        std::vector<expr> sargs;
        expr res = ReduceAndOr(args,is_and,sargs);
        if(!res.null()) return res;
        return FinishAndOr(sargs,is_and);
    }

    expr Z3User::PullCommonFactors(std::vector<expr> &args, bool is_and){
    
        // first check if there's anything to do...
        if(args.size() < 2)
            return FinishAndOr(args,is_and);
        for (unsigned i = 0; i < args.size(); i++) {
            const expr &a = args[i];
            if (!(a.is_app() && a.decl().get_decl_kind() == (is_and ? Or : And)))
                return FinishAndOr(args, is_and);
        }
        std::vector<expr> common;
        for (unsigned i = 0; i < args.size(); i++) {
            unsigned n = args[i].num_args();
            std::vector<expr> v(n), w;
            for (unsigned j = 0; j < n; j++)
                v[j] = args[i].arg(j);
            std::less<ast> comp;
            std::sort(v.begin(), v.end(), comp);
            if (i == 0)
                common.swap(v);
            else {
                std::set_intersection(common.begin(), common.end(), v.begin(), v.end(), std::inserter(w, w.begin()), comp);
                common.swap(w);
            }
        }
        if(common.empty())
            return FinishAndOr(args,is_and);
        std::set<ast> common_set(common.begin(),common.end());
        for(unsigned i = 0; i < args.size(); i++){
            unsigned n = args[i].num_args();
            std::vector<expr> lits;
            for (unsigned j = 0; j < n; j++) {
                const expr b = args[i].arg(j);
                if (common_set.find(b) == common_set.end())
                    lits.push_back(b);
            }
            args[i] = SimplifyAndOr(lits,!is_and);
        }  
        common.push_back(SimplifyAndOr(args,is_and));
        return SimplifyAndOr(common,!is_and);
    }

    expr Z3User::ReallySimplifyAndOr(const std::vector<expr> &args, bool is_and){
        std::vector<expr> sargs;
        expr res = ReduceAndOr(args,is_and,sargs);
        if(!res.null()) return res;
        return PullCommonFactors(sargs,is_and);
    }

    Z3User::Term Z3User::SubstAtomTriv(const expr &foo, const expr &atom, const expr &val){
        if(eq(foo,atom))
            return val;
        else if(foo.is_app() && foo.decl().get_decl_kind() == Not && eq(foo.arg(0),atom))
            return Negate(val);
        else
            return foo;
    }

    Z3User::Term Z3User::PushQuantifier(const expr &t, const expr &body, bool is_forall){
        if (t.get_quantifier_num_bound() == 1) {
            std::vector<expr> fmlas, free, not_free;
            CollectJuncts(body, fmlas, is_forall ? Or : And, false);
            for (unsigned i = 0; i < fmlas.size(); i++) {
                const expr &fmla = fmlas[i];
                if (fmla.has_free(0))
                    free.push_back(fmla);
                else
                    not_free.push_back(fmla);
            }
            decl_kind op = is_forall ? Or : And;
            if (free.empty())
                return DeleteBound(0, 1, SimplifyAndOr(not_free, op == And));
            expr q = clone_quantifier(is_forall ? Forall : Exists, t, SimplifyAndOr(free, op == And));
            if (!not_free.empty())
                q = ctx.make(op, q, DeleteBound(0, 1, SimplifyAndOr(not_free, op == And)));
            return q;
        }
        return clone_quantifier(is_forall ? Forall : Exists,t,body);
    }

    Z3User::Term Z3User::CloneQuantAndSimp(const expr &t, const expr &body, bool is_forall) {
        if (body.is_app()) {
            if (body.decl().get_decl_kind() == (is_forall ? And : Or)) { // quantifier distributes
                int nargs = body.num_args();
                std::vector<expr> args(nargs);
                for (int i = 0; i < nargs; i++)
                    args[i] = CloneQuantAndSimp(t, body.arg(i), is_forall);
                return SimplifyAndOr(args, body.decl().get_decl_kind() == And);
            }
            else if (body.decl().get_decl_kind() == (is_forall ? Or : And)) { // quantifier distributes
                return PushQuantifier(t, body, is_forall); // may distribute partially
            }
            else if (body.decl().get_decl_kind() == Not) {
                return ctx.make(Not, CloneQuantAndSimp(t, body.arg(0), !is_forall));
            }
        }
        if (t.get_quantifier_num_bound() == 1 && !body.has_free(0))
            return DeleteBound(0, 1, body); // drop the quantifier
        return clone_quantifier(is_forall ? Forall : Exists, t, body);
    }

    Z3User::Term Z3User::CloneQuantAndSimp(const expr &t, const expr &body){
        return CloneQuantAndSimp(t,body,t.is_quantifier_forall());
    }

    Z3User::Term Z3User::SubstAtom(hash_map<ast, Term> &memo, const expr &t, const expr &atom, const expr &val) {
        std::pair<ast, Term> foo(t, expr(ctx));
        std::pair<hash_map<ast, Term>::iterator, bool> bar = memo.insert(foo);
        Term &res = bar.first->second;
        if (!bar.second) return res;
        if (t.is_app()) {
            func_decl f = t.decl();
            decl_kind k = f.get_decl_kind();

            // TODO: recur here, but how much? We don't want to be quadractic in formula size

            if (k == And || k == Or) {
                int nargs = t.num_args();
                std::vector<Term> args(nargs);
                for (int i = 0; i < nargs; i++)
                    args[i] = SubstAtom(memo, t.arg(i), atom, val);
                res = ReallySimplifyAndOr(args, k == And);
                return res;
            }
        }
        else if (t.is_quantifier() && atom.is_quantifier()) {
            if (eq(t, atom))
                res = val;
            else
                res = clone_quantifier(t, SubstAtom(memo, t.body(), atom, val));
            return res;
        }
        res = SubstAtomTriv(t, atom, val);
        return res;
    }

    void Z3User::RemoveRedundancyOp(bool pol, std::vector<expr> &args, hash_map<ast, Term> &smemo) {
        for (unsigned i = 0; i < args.size(); i++) {
            const expr &lit = args[i];
            expr atom, val;
            if (IsLiteral(lit, atom, val)) {
                if (atom.is_app() && atom.decl().get_decl_kind() == Equal)
                    if (pol ? eq(val, ctx.bool_val(true)) : eq(val, ctx.bool_val(false))) {
                        expr lhs = atom.arg(0), rhs = atom.arg(1);
                        if (lhs.is_numeral())
                            std::swap(lhs, rhs);
                        if (rhs.is_numeral() && lhs.is_app()) {
                            for (unsigned j = 0; j < args.size(); j++)
                                if (j != i) {
                                    smemo.clear();
                                    smemo[lhs] = rhs;
                                    args[j] = SubstRec(smemo, args[j]);
                                }
                        }
                    }
                for (unsigned j = 0; j < args.size(); j++)
                    if (j != i) {
                        smemo.clear();
                        args[j] = SubstAtom(smemo, args[j], atom, pol ? val : !val);
                    }
            }
        }
    }
  

    Z3User::Term Z3User::RemoveRedundancyRec(hash_map<ast, Term> &memo, hash_map<ast, Term> &smemo, const Term &t) {
        std::pair<ast, Term> foo(t, expr(ctx));
        std::pair<hash_map<ast, Term>::iterator, bool> bar = memo.insert(foo);
        Term &res = bar.first->second;
        if (!bar.second) return res;
        if (t.is_app()) {
            func_decl f = t.decl();
            std::vector<Term> args;
            int nargs = t.num_args();
            for (int i = 0; i < nargs; i++)
                args.push_back(RemoveRedundancyRec(memo, smemo, t.arg(i)));

            decl_kind k = f.get_decl_kind();
            if (k == And) {
                RemoveRedundancyOp(true, args, smemo);
                res = ReallySimplifyAndOr(args, true);
            }
            else if (k == Or) {
                RemoveRedundancyOp(false, args, smemo);
                res = ReallySimplifyAndOr(args, false);
            }
            else {
                if (k == Equal && args[0].get_id() > args[1].get_id())
                    std::swap(args[0], args[1]);
                res = f(args.size(), &args[0]);
            }
        }
        else if (t.is_quantifier()) {
            Term body = RemoveRedundancyRec(memo, smemo, t.body());
            res = CloneQuantAndSimp(t, body);
        }
        else res = t;
        return res;
    }

    Z3User::Term Z3User::RemoveRedundancy(const Term &t){
        hash_map<ast, Term> memo;
        hash_map<ast, Term> smemo;
        return RemoveRedundancyRec(memo,smemo,t);
    }

    Z3User::Term Z3User::AdjustQuantifiers(const Term &t)
    {
        if(t.is_quantifier() || (t.is_app() && t.has_quantifiers()))
            return t.qe_lite();
        return t;
    }

    Z3User::Term Z3User::IneqToEqRec(hash_map<ast, Term> &memo, const Term &t) {
        std::pair<ast, Term> foo(t, expr(ctx));
        std::pair<hash_map<ast, Term>::iterator, bool> bar = memo.insert(foo);
        Term &res = bar.first->second;
        if (!bar.second) return res;
        if (t.is_app()) {
            func_decl f = t.decl();
            std::vector<Term> args;
            int nargs = t.num_args();
            for (int i = 0; i < nargs; i++)
                args.push_back(IneqToEqRec(memo, t.arg(i)));

            decl_kind k = f.get_decl_kind();
            if (k == And) {
                for (int i = 0; i < nargs - 1; i++) {
                    if ((args[i].is_app() && args[i].decl().get_decl_kind() == Geq &&
                         args[i + 1].is_app() && args[i + 1].decl().get_decl_kind() == Leq)
                        ||
                        (args[i].is_app() && args[i].decl().get_decl_kind() == Leq &&
                         args[i + 1].is_app() && args[i + 1].decl().get_decl_kind() == Geq))
                        if (eq(args[i].arg(0), args[i + 1].arg(0)) && eq(args[i].arg(1), args[i + 1].arg(1))) {
                            args[i] = ctx.make(Equal, args[i].arg(0), args[i].arg(1));
                            args[i + 1] = ctx.bool_val(true);
                        }
                }
            }
            res = f(args.size(), VEC2PTR(args));
        }
        else if (t.is_quantifier()) {
            Term body = IneqToEqRec(memo, t.body());
            res = clone_quantifier(t, body);
        }
        else res = t;
        return res;
    }

    Z3User::Term Z3User::IneqToEq(const Term &t){
        hash_map<ast, Term> memo;
        return IneqToEqRec(memo,t);
    }

    Z3User::Term Z3User::SubstRecHide(hash_map<ast, Term> &memo, const Term &t, int number) {
        std::pair<ast, Term> foo(t, expr(ctx));
        std::pair<hash_map<ast, Term>::iterator, bool> bar = memo.insert(foo);
        Term &res = bar.first->second;
        if (!bar.second) return res;
        if (t.is_app()) {
            func_decl f = t.decl();
            std::vector<Term> args;
            int nargs = t.num_args();
            if (nargs == 0 && f.get_decl_kind() == Uninterpreted) {
                std::string name = std::string("@q_") + t.decl().name().str() + "_" + string_of_int(number);
                res = ctx.constant(name.c_str(), t.get_sort());
                return res;
            }
            for (int i = 0; i < nargs; i++)
                args.push_back(SubstRec(memo, t.arg(i)));
            res = f(args.size(), VEC2PTR(args));
        }
        else if (t.is_quantifier())
            res = CloneQuantifier(t, SubstRec(memo, t.body()));
        else res = t;
        return res;
    }

    RPFP::Term RPFP::SubstParams(const std::vector<Term> &from,
                                 const std::vector<Term> &to, const Term &t) {
        hash_map<ast, Term> memo;
        bool some_diff = false;
        for (unsigned i = 0; i < from.size(); i++)
            if (i < to.size() && !eq(from[i], to[i])) {
                memo[from[i]] = to[i];
                some_diff = true;
            }
        return some_diff ? SubstRec(memo, t) : t;
    }

    RPFP::Term RPFP::SubstParamsNoCapture(const std::vector<Term> &from,
                                          const std::vector<Term> &to, const Term &t) {
        hash_map<ast, Term> memo;
        bool some_diff = false;
        for (unsigned i = 0; i < from.size(); i++)
            if (i < to.size() && !eq(from[i], to[i])) {
                memo[from[i]] = to[i];
                // if the new param is not being mapped to anything else, we need to rename it to prevent capture
                // note, if the new param *is* mapped later in the list, it will override this substitution
                const expr &w = to[i];
                if (memo.find(w) == memo.end()) {
                    std::string old_name = w.decl().name().str();
                    func_decl fresh = ctx.fresh_func_decl(old_name.c_str(), w.get_sort());
                    expr y = fresh();
                    memo[w] = y;
                }
                some_diff = true;
            }
        return some_diff ? SubstRec(memo, t) : t;
    }

  

    RPFP::Transformer RPFP::Fuse(const std::vector<Transformer *> &trs) {
        assert(!trs.empty());
        const std::vector<expr> &params = trs[0]->IndParams;
        std::vector<expr> fmlas(trs.size());
        fmlas[0] = trs[0]->Formula;
        for (unsigned i = 1; i < trs.size(); i++)
            fmlas[i] = SubstParamsNoCapture(trs[i]->IndParams, params, trs[i]->Formula);
        std::vector<func_decl> rel_params = trs[0]->RelParams;
        for (unsigned i = 1; i < trs.size(); i++) {
            const std::vector<func_decl> &params2 = trs[i]->RelParams;
            hash_map<func_decl, func_decl> map;
            for (unsigned j = 0; j < params2.size(); j++) {
                func_decl rel = RenumberPred(params2[j], rel_params.size());
                rel_params.push_back(rel);
                map[params2[j]] = rel;
            }
            hash_map<ast, expr> memo;
            fmlas[i] = SubstRec(memo, map, fmlas[i]);
        }
        return Transformer(rel_params, params, ctx.make(Or, fmlas), trs[0]->owner);
    }


    void Z3User::Strengthen(Term &x, const Term &y)
    {
        if (eq(x,ctx.bool_val(true)))
            x = y;
        else
            x = x && y;
    }

    void RPFP::SetAnnotation(Node *root, const expr &t){
        hash_map<ast, Term> memo;
        Term b;
        std::vector<Term> v;
        RedVars(root, b, v);
        memo[b] = ctx.bool_val(true);
        for (unsigned i = 0; i < v.size(); i++)
            memo[v[i]] = root->Annotation.IndParams[i];
        Term annot = SubstRec(memo, t);
        // Strengthen(ref root.Annotation.Formula, annot);
        root->Annotation.Formula = annot;
    }

    void RPFP::DecodeTree(Node *root, TermTree *interp, int persist) {
        std::vector<TermTree *> &ic = interp->getChildren();
        if (ic.size() > 0) {
            std::vector<Node *> &nc = root->Outgoing->Children;
            for (unsigned i = 0; i < nc.size(); i++)
                DecodeTree(nc[i], ic[i], persist);
        }
        SetAnnotation(root, interp->getTerm());
#if 0
        if(persist != 0)
            Z3_persist_ast(ctx,root->Annotation.Formula,persist);
#endif
    }
  
    RPFP::Term RPFP::GetUpperBound(Node *n)
    {
        // TODO: cache this
        Term b(ctx); std::vector<Term> v;
        RedVars(n, b, v);
        hash_map<ast, Term> memo;
        for (unsigned int i = 0; i < v.size(); i++)
            memo[n->Bound.IndParams[i]] = v[i];
        Term cnst = SubstRec(memo, n->Bound.Formula);
        return b && !cnst;
    }

    RPFP::Term RPFP::GetAnnotation(Node *n)
    {
        if(eq(n->Annotation.Formula,ctx.bool_val(true)))
            return n->Annotation.Formula;
        // TODO: cache this
        Term b(ctx); std::vector<Term> v;
        RedVars(n, b, v);
        hash_map<ast, Term> memo;
        for (unsigned i = 0; i < v.size(); i++)
            memo[n->Annotation.IndParams[i]] = v[i];
        Term cnst = SubstRec(memo, n->Annotation.Formula);
        return !b || cnst;
    }

    RPFP::Term RPFP::GetUnderapprox(Node *n)
    {
        // TODO: cache this
        Term b(ctx); std::vector<Term> v;
        RedVars(n, b, v);
        hash_map<ast, Term> memo;
        for (unsigned i = 0; i < v.size(); i++)
            memo[n->Underapprox.IndParams[i]] = v[i];
        Term cnst = SubstRecHide(memo, n->Underapprox.Formula, n->number);
        return !b || cnst;
    }

    TermTree *RPFP::AddUpperBound(Node *root, TermTree *t)
    {
        Term f = !((ast)(root->dual)) ? ctx.bool_val(true) : root->dual;
        std::vector<TermTree *> c(1); c[0] = t;
        return new TermTree(f, c);
    }

#if 0
    void RPFP::WriteInterps(System.IO.StreamWriter f, TermTree t)
    {
        foreach (var c in t.getChildren())
            WriteInterps(f, c);
        f.WriteLine(t.getTerm());
    }
#endif    


    expr RPFP::GetEdgeFormula(Edge *e, int persist, bool with_children, bool underapprox) {
        if (e->dual.null()) {
            timer_start("ReducedDualEdge");
            e->dual = ReducedDualEdge(e);
            timer_stop("ReducedDualEdge");
            timer_start("getting children");
            if (underapprox) {
                std::vector<expr> cus(e->Children.size());
                for (unsigned i = 0; i < e->Children.size(); i++)
                    cus[i] = !UnderapproxFlag(e->Children[i]) || GetUnderapprox(e->Children[i]);
                expr cnst = conjoin(cus);
                e->dual = e->dual && cnst;
            }
            timer_stop("getting children");
            timer_start("Persisting");
            std::list<stack_entry>::reverse_iterator it = stack.rbegin();
            for (int i = 0; i < persist && it != stack.rend(); i++)
                it++;
            if (it != stack.rend())
                it->edges.push_back(e);
            timer_stop("Persisting");
            //Console.WriteLine("{0}", cnst);
        }
        return e->dual;
    }

    /** For incremental solving, asserts the constraint associated
     * with this edge in the SMT context. If this edge is removed,
     * you must pop the context accordingly. The second argument is
     * the number of pushes we are inside. The constraint formula
     * will survive "persist" pops of the context. If you plan
     * to reassert the edge after popping the context once,
     * you can save time re-constructing the formula by setting
     * "persist" to one. If you set "persist" too high, however,
     * you could have a memory leak.
     *
     * The flag "with children" causes the annotations of the children
     * to be asserted. The flag underapprox causes the underapproximations
     * of the children to be asserted *conditionally*. See Check() on
     * how to actually enforce these constraints.
     *
     */

    void RPFP::AssertEdge(Edge *e, int persist, bool with_children, bool underapprox) {
        if (eq(e->F.Formula, ctx.bool_val(true)) && (!with_children || e->Children.empty()))
            return;
        expr fmla = GetEdgeFormula(e, persist, with_children, underapprox);
        timer_start("solver add");
        slvr_add(e->dual);
        timer_stop("solver add");
        if (with_children)
            for (unsigned i = 0; i < e->Children.size(); i++)
                ConstrainParent(e, e->Children[i]);
    }


#ifdef LIMIT_STACK_WEIGHT
    void RPFP_caching::AssertEdge(Edge *e, int persist, bool with_children, bool underapprox)
    {
        unsigned old_new_alits = new_alits.size();
        if(eq(e->F.Formula,ctx.bool_val(true)) && (!with_children || e->Children.empty()))
            return;
        expr fmla = GetEdgeFormula(e, persist, with_children, underapprox);
        timer_start("solver add");
        slvr_add(e->dual);
        timer_stop("solver add");
        if(old_new_alits < new_alits.size())
            weight_added.val++;
        if(with_children)
            for(unsigned i = 0; i < e->Children.size(); i++)
                ConstrainParent(e,e->Children[i]);
    }
#endif

    // caching verion of above
    void RPFP_caching::AssertEdgeCache(Edge *e, std::vector<Term> &lits, bool with_children) {
        if (eq(e->F.Formula, ctx.bool_val(true)) && (!with_children || e->Children.empty()))
            return;
        expr fmla = GetEdgeFormula(e, 0, with_children, false);
        GetAssumptionLits(fmla, lits);
        if (with_children)
            for (unsigned i = 0; i < e->Children.size(); i++)
                ConstrainParentCache(e, e->Children[i], lits);
    }
      
    void RPFP::slvr_add(const expr &e){
        slvr().add(e);
    }

    void RPFP_caching::slvr_add(const expr &e){
        GetAssumptionLits(e,alit_stack);
    }

    void RPFP::slvr_pop(int i){
        slvr().pop(i);
    }

    void RPFP::slvr_push(){
        slvr().push();
    }

    void RPFP_caching::slvr_pop(int i){
        for(int j = 0; j < i; j++){
#ifdef LIMIT_STACK_WEIGHT
            if(alit_stack_sizes.empty()){
                if(big_stack.empty())
                    throw "stack underflow";
                for(unsigned k = 0; k < new_alits.size(); k++){
                    if(AssumptionLits.find(new_alits[k]) == AssumptionLits.end())
                        throw "foo!";
                    AssumptionLits.erase(new_alits[k]);
                }
                big_stack_entry &bsb = big_stack.back();
                bsb.alit_stack_sizes.swap(alit_stack_sizes);
                bsb.alit_stack.swap(alit_stack);
                bsb.new_alits.swap(new_alits);
                bsb.weight_added.swap(weight_added);
                big_stack.pop_back();
                slvr().pop(1);
                continue;
            }
#endif
            alit_stack.resize(alit_stack_sizes.back());
            alit_stack_sizes.pop_back();
        }
    }
  
    void RPFP_caching::slvr_push(){
#ifdef LIMIT_STACK_WEIGHT
        if(weight_added.val > LIMIT_STACK_WEIGHT){
            big_stack.resize(big_stack.size()+1);
            big_stack_entry &bsb = big_stack.back();
            bsb.alit_stack_sizes.swap(alit_stack_sizes);
            bsb.alit_stack.swap(alit_stack);
            bsb.new_alits.swap(new_alits);
            bsb.weight_added.swap(weight_added);
            slvr().push();
            for(unsigned i = 0; i < bsb.alit_stack.size(); i++)
                slvr().add(bsb.alit_stack[i]);
            return;
        }
#endif
        alit_stack_sizes.push_back(alit_stack.size());
    }

    check_result RPFP::slvr_check(unsigned n, expr * const assumptions, unsigned *core_size, expr *core){
        return slvr().check(n, assumptions, core_size, core);
    }

    check_result RPFP_caching::slvr_check(unsigned n, expr * const assumptions, unsigned *core_size, expr *core){
        unsigned oldsiz = alit_stack.size();
        if(n && assumptions)
            std::copy(assumptions,assumptions+n,std::inserter(alit_stack,alit_stack.end()));
        check_result res;
        if (core_size && core) {
            std::vector<expr> full_core(alit_stack.size()), core1(n);
            std::copy(assumptions, assumptions + n, core1.begin());
            res = slvr().check(alit_stack.size(), VEC2PTR(alit_stack), core_size, VEC2PTR(full_core));
            full_core.resize(*core_size);
            if (res == unsat) {
                FilterCore(core1, full_core);
                *core_size = core1.size();
                std::copy(core1.begin(), core1.end(), core);
            }
        }
        else 
            res = slvr().check(alit_stack.size(), VEC2PTR(alit_stack));
        alit_stack.resize(oldsiz);
        return res;
    }

    lbool RPFP::ls_interpolate_tree(TermTree *assumptions,
                                    TermTree *&interpolants,
                                    model &_model,
                                    TermTree *goals,
                                    bool weak) {
        return ls->interpolate_tree(assumptions, interpolants, _model, goals, weak);
    }

    lbool RPFP_caching::ls_interpolate_tree(TermTree *assumptions,
                                            TermTree *&interpolants,
                                            model &_model,
                                            TermTree *goals,
                                            bool weak) {
        GetTermTreeAssertionLiterals(assumptions);
        return ls->interpolate_tree(assumptions, interpolants, _model, goals, weak);
    }

    void RPFP_caching::GetTermTreeAssertionLiteralsRec(TermTree *assumptions){
        std::vector<expr> alits;
        hash_map<ast,expr> map;
        GetAssumptionLits(assumptions->getTerm(),alits,&map);
        std::vector<expr> &ts = assumptions->getTerms();
        for(unsigned i = 0; i < ts.size(); i++)
            GetAssumptionLits(ts[i],alits,&map);
        assumptions->setTerm(ctx.bool_val(true));
        ts = alits;
        for(unsigned i = 0; i < alits.size(); i++)
            ts.push_back(ctx.make(Implies,alits[i],map[alits[i]]));
        for(unsigned i = 0; i < assumptions->getChildren().size(); i++)
            GetTermTreeAssertionLiterals(assumptions->getChildren()[i]);
        return;
    }

    void RPFP_caching::GetTermTreeAssertionLiterals(TermTree *assumptions) {
        // optimize binary case
        if (assumptions->getChildren().size() == 1
            && assumptions->getChildren()[0]->getChildren().size() == 0) {
            hash_map<ast, expr> map;
            TermTree *child = assumptions->getChildren()[0];
            std::vector<expr> dummy;
            GetAssumptionLits(child->getTerm(), dummy, &map);
            std::vector<expr> &ts = child->getTerms();
            for (unsigned i = 0; i < ts.size(); i++)
                GetAssumptionLits(ts[i], dummy, &map);
            std::vector<expr> assumps;
            slvr().get_proof().get_assumptions(assumps);
            if (!proof_core) { // save the proof core for later use
                proof_core = new hash_set < ast > ;
                for (unsigned i = 0; i < assumps.size(); i++)
                    proof_core->insert(assumps[i]);
            }
            std::vector<expr> *cnsts[2] = { &child->getTerms(), &assumptions->getTerms() };
            for (unsigned i = 0; i < assumps.size(); i++) {
                expr &as = assumps[i];
                expr alit = (as.is_app() && as.decl().get_decl_kind() == Implies) ? as.arg(0) : as;
                bool isA = map.find(alit) != map.end();
                cnsts[isA ? 0 : 1]->push_back(as);
            }
        }
        else
            GetTermTreeAssertionLiteralsRec(assumptions);
    }

    void RPFP::AddToProofCore(hash_set<ast> &core){
        std::vector<expr> assumps;
        slvr().get_proof().get_assumptions(assumps);
        for(unsigned i = 0; i < assumps.size(); i++)
            core.insert(assumps[i]);
    }
  
    void RPFP::ComputeProofCore(){
        if(!proof_core){
            proof_core = new hash_set<ast>;
            AddToProofCore(*proof_core);
        }
    }


    void RPFP_caching::GetAssumptionLits(const expr &fmla, std::vector<expr> &lits, hash_map<ast, expr> *opt_map) {
        std::vector<expr> conjs;
        CollectConjuncts(fmla, conjs);
        for (unsigned i = 0; i < conjs.size(); i++) {
            const expr &conj = conjs[i];
            std::pair<ast, Term> foo(conj, expr(ctx));
            std::pair<hash_map<ast, Term>::iterator, bool> bar = AssumptionLits.insert(foo);
            Term &res = bar.first->second;
            if (bar.second) {
                func_decl pred = ctx.fresh_func_decl("@alit", ctx.bool_sort());
                res = pred();
#ifdef LIMIT_STACK_WEIGHT
                new_alits.push_back(conj);
#endif
                slvr().add(ctx.make(Implies, res, conj));
                // std::cout << res << ": " << conj << "\n";
            }
            if (opt_map)
                (*opt_map)[res] = conj;
            lits.push_back(res);
        }
    }

    void RPFP::ConstrainParent(Edge *parent, Node *child){
        ConstrainEdgeLocalized(parent,GetAnnotation(child));
    } 

    void RPFP_caching::ConstrainParentCache(Edge *parent, Node *child, std::vector<Term> &lits){
        ConstrainEdgeLocalizedCache(parent,GetAnnotation(child),lits);
    } 

        
    /** For incremental solving, asserts the negation of the upper bound associated
     * with a node.
     * */

    void RPFP::AssertNode(Node *n)
    {
        if (n->dual.null()) {
            n->dual = GetUpperBound(n);
            stack.back().nodes.push_back(n);
            slvr_add(n->dual);
        }
    }

    // caching version of above
    void RPFP_caching::AssertNodeCache(Node *n, std::vector<Term> lits){
        if (n->dual.null()) {
            n->dual = GetUpperBound(n);
            stack.back().nodes.push_back(n);
            GetAssumptionLits(n->dual, lits);
        }
    }
  
    /** Clone another RPFP into this one, keeping a map */
    void RPFP_caching::Clone(RPFP *other) {
#if 0
        for(unsigned i = 0; i < other->nodes.size(); i++)
            NodeCloneMap[other->nodes[i]] = CloneNode(other->nodes[i]);
#endif
        for (unsigned i = 0; i < other->edges.size(); i++) {
            Edge *edge = other->edges[i];
            Node *parent = CloneNode(edge->Parent);
            std::vector<Node *> cs;
            for (unsigned j = 0; j < edge->Children.size(); j++)
                // cs.push_back(NodeCloneMap[edge->Children[j]]);
                cs.push_back(CloneNode(edge->Children[j]));
            EdgeCloneMap[edge] = CreateEdge(parent, edge->F, cs);
        }
    }
  
    /** Get the clone of a node */
    RPFP::Node *RPFP_caching::GetNodeClone(Node *other_node){
        return NodeCloneMap[other_node];
    }
  
    /** Get the clone of an edge */
    RPFP::Edge *RPFP_caching::GetEdgeClone(Edge *other_edge){
        return EdgeCloneMap[other_edge];
    }  

    /** check assumption lits, and return core */
    check_result RPFP_caching::CheckCore(const std::vector<Term> &assumps, std::vector<Term> &core){
        core.resize(assumps.size());
        unsigned core_size;
        check_result res = slvr().check(assumps.size(),(expr *)VEC2PTR(assumps),&core_size, VEC2PTR(core));
        if(res == unsat)
            core.resize(core_size);
        else
            core.clear();
        return res;
    }
  
      
    /** Assert a constraint on an edge in the SMT context. 
     */

    void RPFP::ConstrainEdge(Edge *e, const Term &t)
    {
        Term tl = Localize(e, t);
        ConstrainEdgeLocalized(e,tl);
    }

    void RPFP::ConstrainEdgeLocalized(Edge *e, const Term &tl)
    {
        e->constraints.push_back(tl);
        stack.back().constraints.push_back(std::pair<Edge *,Term>(e,tl));
        slvr_add(tl);
    }

    void RPFP_caching::ConstrainEdgeLocalizedCache(Edge *e, const Term &tl, std::vector<expr> &lits)
    {
        e->constraints.push_back(tl);
        stack.back().constraints.push_back(std::pair<Edge *,Term>(e,tl));
        GetAssumptionLits(tl,lits);
    }


    /** Declare a constant in the background theory. */

    void RPFP::DeclareConstant(const FuncDecl &f){
        ls->declare_constant(f);
    }

    /** Assert a background axiom. Background axioms can be used to provide the
     *  theory of auxilliary functions or relations. All symbols appearing in
     *  background axioms are considered global, and may appear in both transformer
     *  and relational solutions. Semantically, a solution to the RPFP gives
     *  an interpretation of the unknown relations for each interpretation of the
     *  auxilliary symbols that is consistent with the axioms. Axioms should be
     *  asserted before any calls to Push. They cannot be de-asserted by Pop. */

    void RPFP::AssertAxiom(const Term &t)
    {
        ls->assert_axiom(t);
        axioms.push_back(t); // for printing only
    }

#if 0
    /** Do not call this. */

    void RPFP::RemoveAxiom(const Term &t)
    {
        slvr().RemoveInterpolationAxiom(t);
    }
#endif
  
    /** Solve an RPFP graph. This means either strengthen the annotation
     *  so that the bound at the given root node is satisfied, or
     *  show that this cannot be done by giving a dual solution 
     *  (i.e., a counterexample). 
     *  
     * In the current implementation, this only works for graphs that
     * are:
     * - tree-like
     * 
     * - closed.
     * 
     * In a tree-like graph, every nod has out most one incoming and one out-going edge,
     * and there are no cycles. In a closed graph, every node has exactly one out-going
     * edge. This means that the leaves of the tree are all hyper-edges with no
     * children. Such an edge represents a relation (nullary transformer) and thus
     * a lower bound on its parent. The parameter root must be the root of this tree.
     * 
     * If Solve returns LBool.False, this indicates success. The annotation of the tree
     * has been updated to satisfy the upper bound at the root. 
     * 
     * If Solve returns LBool.True, this indicates a counterexample. For each edge,
     * you can then call Eval to determine the values of symbols in the transformer formula.
     * You can also call Empty on a node to determine if its value in the counterexample
     * is the empty relation.
     * 
     *    \param root The root of the tree
     *    \param persist Number of context pops through which result should persist 
     * 
     * 
     */

    lbool RPFP::Solve(Node *root, int persist)
    {
        timer_start("Solve");
        TermTree *tree = GetConstraintTree(root);
        TermTree *interpolant = NULL;
        TermTree *goals = NULL;
        if(ls->need_goals)
            goals = GetGoalTree(root);
        ClearProofCore();

        // if (dualModel != null) dualModel.Dispose();
        // if (dualLabels != null) dualLabels.Dispose();
    
        timer_start("interpolate_tree");
        lbool res = ls_interpolate_tree(tree, interpolant, dualModel,goals,true);
        timer_stop("interpolate_tree");
        if (res == l_false) {
            DecodeTree(root, interpolant->getChildren()[0], persist);
            delete interpolant;
        }

        delete tree;
        if(goals)
            delete goals;
    
        timer_stop("Solve");
        return res;
    }
  
    void RPFP::CollapseTermTreeRec(TermTree *root, TermTree *node){
        root->addTerm(node->getTerm());
        std::vector<Term> &cnsts = node->getTerms();
        for(unsigned i = 0; i < cnsts.size(); i++)
            root->addTerm(cnsts[i]);
        std::vector<TermTree *> &chs = node->getChildren();
        for(unsigned i = 0; i < chs.size(); i++){
            CollapseTermTreeRec(root,chs[i]);
        }
    }

    TermTree *RPFP::CollapseTermTree(TermTree *node){
        std::vector<TermTree *> &chs = node->getChildren();
        for(unsigned i = 0; i < chs.size(); i++)
            CollapseTermTreeRec(node,chs[i]);
        for(unsigned i = 0; i < chs.size(); i++)
            delete chs[i];
        chs.clear();
        return node;
    }
    
    lbool RPFP::SolveSingleNode(Node *root, Node *node)
    {
        timer_start("Solve");
        TermTree *tree = CollapseTermTree(GetConstraintTree(root,node));
        tree->getChildren().push_back(CollapseTermTree(ToTermTree(node)));
        TermTree *interpolant = NULL;
        ClearProofCore();

        timer_start("interpolate_tree");
        lbool res = ls_interpolate_tree(tree, interpolant, dualModel,0,true);
        timer_stop("interpolate_tree");
        if (res == l_false) {
            DecodeTree(node, interpolant->getChildren()[0], 0);
            delete interpolant;
        }

        delete tree;
        timer_stop("Solve");
        return res;
    }

    /** Get the constraint tree (but don't solve it) */
  
    TermTree *RPFP::GetConstraintTree(Node *root, Node *skip_descendant)
    {
        return AddUpperBound(root, ToTermTree(root,skip_descendant));
    }
  
    /** Dispose of the dual model (counterexample) if there is one. */

    void RPFP::DisposeDualModel()
    {
        dualModel = model(ctx,NULL);
    }
  
    RPFP::Term RPFP::UnderapproxFlag(Node *n){
        expr flag = ctx.constant((std::string("@under") +  string_of_int(n->number)).c_str(), ctx.bool_sort());
        underapprox_flag_rev[flag] = n;
        return flag;
    }

    RPFP::Node *RPFP::UnderapproxFlagRev(const Term &flag){
        return underapprox_flag_rev[flag];
    }

    /** Check satisfiability of asserted edges and nodes. Same functionality as
     * Solve, except no primal solution (interpolant) is generated in the unsat case.
     * The vector underapproxes gives the set of node underapproximations to be enforced
     * (assuming these were conditionally asserted by AssertEdge).
     * 
     */ 

    check_result RPFP::Check(Node *root, std::vector<Node *> underapproxes, std::vector<Node *> *underapprox_core) {
        timer_start("Check");
        ClearProofCore();
        // if (dualModel != null) dualModel.Dispose();
        check_result res;
        if (!underapproxes.size())
            res = slvr_check();
        else {
            std::vector<expr> us(underapproxes.size());
            for (unsigned i = 0; i < underapproxes.size(); i++)
                us[i] = UnderapproxFlag(underapproxes[i]);
            slvr_check(); // TODO: no idea why I need to do this
            if (underapprox_core) {
                std::vector<expr> unsat_core(us.size());
                unsigned core_size = 0;
                res = slvr_check(us.size(), VEC2PTR(us), &core_size, VEC2PTR(unsat_core));
                underapprox_core->resize(core_size);
                for (unsigned i = 0; i < core_size; i++)
                    (*underapprox_core)[i] = UnderapproxFlagRev(unsat_core[i]);
            }
            else {
                res = slvr_check(us.size(), VEC2PTR(us));
                bool dump = false;
                if (dump) {
                    std::vector<expr> cnsts;
                    // cnsts.push_back(axioms[0]);
                    cnsts.push_back(root->dual);
                    cnsts.push_back(root->Outgoing->dual);
                    ls->write_interpolation_problem("temp.smt", cnsts, std::vector<expr>());
                }
            }
            // check_result temp = slvr_check();
        }
        dualModel = slvr().get_model();
        timer_stop("Check");
        return res;
    }

    check_result RPFP::CheckUpdateModel(Node *root, std::vector<expr> assumps){
        // check_result temp1 = slvr_check(); // no idea why I need to do this
        ClearProofCore();
        check_result res = slvr_check(assumps.size(), VEC2PTR(assumps));
        model mod = slvr().get_model();
        if(!mod.null())
            dualModel = mod;;
        return res;
    }      

    /** Determines the value in the counterexample of a symbol occuring in the transformer formula of
     *  a given edge. */

    RPFP::Term RPFP::Eval(Edge *e, Term t)
    {
        Term tl = Localize(e, t);
        return dualModel.eval(tl);
    }

    /** Returns true if the given node is empty in the primal solution. For proecudure summaries,
        this means that the procedure is not called in the current counter-model. */
  
    bool RPFP::Empty(Node *p)
    {
        Term b; std::vector<Term> v;
        RedVars(p, b, v);
        // dualModel.show_internals();
        // std::cout << "b: " << b << std::endl;
        expr bv = dualModel.eval(b);
        // std::cout << "bv: " << bv << std::endl; 
        bool res = !eq(bv,ctx.bool_val(true));
        return res;
    }

    RPFP::Term RPFP::EvalNode(Node *p)
    {
        Term b; std::vector<Term> v;
        RedVars(p, b, v);
        std::vector<Term> args;
        for(unsigned i = 0; i < v.size(); i++)
            args.push_back(dualModel.eval(v[i]));
        return (p->Name)(args);
    }

    void RPFP::EvalArrayTerm(const RPFP::Term &t, ArrayValue &res){
        if (t.is_app()) {
            decl_kind k = t.decl().get_decl_kind();
            if (k == AsArray) {
                func_decl fd = t.decl().get_func_decl_parameter(0);
                func_interp r = dualModel.get_func_interp(fd);
                int num = r.num_entries();
                res.defined = true;
                for (int i = 0; i < num; i++) {
                    expr arg = r.get_arg(i, 0);
                    expr value = r.get_value(i);
                    res.entries[arg] = value;
                }
                res.def_val = r.else_value();
                return;
            }
            else if (k == Store) {
                EvalArrayTerm(t.arg(0), res);
                if (!res.defined)return;
                expr addr = t.arg(1);
                expr val = t.arg(2);
                if (addr.is_numeral() && val.is_numeral()) {
                    if (eq(val, res.def_val))
                        res.entries.erase(addr);
                    else
                        res.entries[addr] = val;
                }
                else
                    res.defined = false;
                return;
            }
        }
        res.defined = false;
    }

    int eae_count = 0;

    RPFP::Term RPFP::EvalArrayEquality(const RPFP::Term &f) {
        ArrayValue lhs, rhs;
        eae_count++;
        EvalArrayTerm(f.arg(0), lhs);
        EvalArrayTerm(f.arg(1), rhs);
        if (lhs.defined && rhs.defined) {
            if (eq(lhs.def_val, rhs.def_val))
                if (lhs.entries == rhs.entries)
                    return ctx.bool_val(true);
            return ctx.bool_val(false);
        }
        return f;
    }

    /** Compute truth values of all boolean subterms in current model.
        Assumes formulas has been simplified by Z3, so only boolean ops
        ands and, or, not. Returns result in memo. 
    */

    int RPFP::SubtermTruth(hash_map<ast, int> &memo, const Term &f) {
        if (memo.find(f) != memo.end()) {
            return memo[f];
        }
        int res;
        if (f.is_app()) {
            int nargs = f.num_args();
            decl_kind k = f.decl().get_decl_kind();
            if (k == Implies) {
                res = SubtermTruth(memo, !f.arg(0) || f.arg(1));
                goto done;
            }
            if (k == And) {
                res = 1;
                for (int i = 0; i < nargs; i++) {
                    int ar = SubtermTruth(memo, f.arg(i));
                    if (ar == 0) {
                        res = 0;
                        goto done;
                    }
                    if (ar == 2)res = 2;
                }
                goto done;
            }
            else if (k == Or) {
                res = 0;
                for (int i = 0; i < nargs; i++) {
                    int ar = SubtermTruth(memo, f.arg(i));
                    if (ar == 1) {
                        res = 1;
                        goto done;
                    }
                    if (ar == 2)res = 2;
                }
                goto done;
            }
            else if (k == Not) {
                int ar = SubtermTruth(memo, f.arg(0));
                res = (ar == 0) ? 1 : ((ar == 1) ? 0 : 2);
                goto done;
            }
        }
        {
            bool pos; std::vector<symbol> names;
            if (f.is_label(pos, names)) {
                res = SubtermTruth(memo, f.arg(0));
                goto done;
            }
        }
        {
            expr bv = dualModel.eval(f);
            if (bv.is_app() && bv.decl().get_decl_kind() == Equal &&
                bv.arg(0).is_array()) {
                bv = EvalArrayEquality(bv);
            }
            // Hack!!!! array equalities can occur negatively!
            if (bv.is_app() && bv.decl().get_decl_kind() == Not &&
                bv.arg(0).decl().get_decl_kind() == Equal &&
                bv.arg(0).arg(0).is_array()) {
                bv = dualModel.eval(!EvalArrayEquality(bv.arg(0)));
            }
            if (eq(bv, ctx.bool_val(true)))
                res = 1;
            else if (eq(bv, ctx.bool_val(false)))
                res = 0;
            else
                res = 2;
        }
    done:
        memo[f] = res;
        return res;
    }

    int RPFP::EvalTruth(hash_map<ast,int> &memo, Edge *e, const Term &f){
        Term tl = Localize(e, f);
        return SubtermTruth(memo,tl);
    }

    /** Compute truth values of all boolean subterms in current model.
        Assumes formulas has been simplified by Z3, so only boolean ops
        ands and, or, not. Returns result in memo. 
    */

#if 0
    int RPFP::GetLabelsRec(hash_map<ast,int> *memo, const Term &f, std::vector<symbol> &labels, bool labpos){
        if(memo[labpos].find(f) != memo[labpos].end()){
            return memo[labpos][f];
        }
        int res;
        if(f.is_app()){
            int nargs = f.num_args();
            decl_kind k = f.decl().get_decl_kind();
            if(k == Implies){
                res = GetLabelsRec(memo,f.arg(1) || !f.arg(0), labels, labpos);
                goto done;
            }
            if(k == And) {
                res = 1; 
                for(int i = 0; i < nargs; i++){
                    int ar = GetLabelsRec(memo,f.arg(i), labels, labpos);
                    if(ar == 0){
                        res = 0;
                        goto done;
                    }
                    if(ar == 2)res = 2; 
                }
                goto done;
            }
            else if(k == Or) {
                res = 0;
                for(int i = 0; i < nargs; i++){
                    int ar = GetLabelsRec(memo,f.arg(i), labels, labpos);
                    if(ar == 1){
                        res = 1;
                        goto done;
                    }
                    if(ar == 2)res = 2; 
                }
                goto done;
            }
            else if(k == Not) {
                int ar = GetLabelsRec(memo,f.arg(0), labels, !labpos);
                res = (ar == 0) ? 1 : ((ar == 1) ? 0 : 2);
                goto done;
            }
        }
        {
            bool pos; std::vector<symbol> names;
            if(f.is_label(pos,names)){
                res = GetLabelsRec(memo,f.arg(0), labels, labpos);
                if(pos == labpos && res == (pos ? 1 : 0))
                    for(unsigned i = 0; i < names.size(); i++)
                        labels.push_back(names[i]);
                goto done;
            }
        }
        {
            expr bv = dualModel.eval(f);
            if(bv.is_app() && bv.decl().get_decl_kind() == Equal && 
               bv.arg(0).is_array()){
                bv = EvalArrayEquality(bv);
            }
            // Hack!!!! array equalities can occur negatively!
            if(bv.is_app() && bv.decl().get_decl_kind() == Not && 
               bv.arg(0).decl().get_decl_kind() == Equal &&
               bv.arg(0).arg(0).is_array()){
                bv = dualModel.eval(!EvalArrayEquality(bv.arg(0)));
            }
            if(eq(bv,ctx.bool_val(true)))
                res = 1;
            else if(eq(bv,ctx.bool_val(false)))
                res = 0;
            else
                res = 2;
        }
    done:
        memo[labpos][f] = res;
        return res;
    }
#endif

    void RPFP::GetLabelsRec(hash_map<ast, int> &memo, const Term &f, std::vector<symbol> &labels,
                            hash_set<ast> *done, bool truth) {
        if (done[truth].find(f) != done[truth].end())
            return; /* already processed */
        if (f.is_app()) {
            int nargs = f.num_args();
            decl_kind k = f.decl().get_decl_kind();
            if (k == Implies) {
                GetLabelsRec(memo, f.arg(1) || !f.arg(0), labels, done, truth);
                goto done;
            }
            if (k == Iff) {
                int b = SubtermTruth(memo, f.arg(0));
                if (b == 2)
                    throw "disaster in GetLabelsRec";
                GetLabelsRec(memo, f.arg(1), labels, done, truth ? b : !b);
                goto done;
            }
            if (truth ? k == And : k == Or) {
                for (int i = 0; i < nargs; i++)
                    GetLabelsRec(memo, f.arg(i), labels, done, truth);
                goto done;
            }
            if (truth ? k == Or : k == And) {
                for (int i = 0; i < nargs; i++) {
                    Term a = f.arg(i);
                    timer_start("SubtermTruth");
                    int b = SubtermTruth(memo, a);
                    timer_stop("SubtermTruth");
                    if (truth ? (b == 1) : (b == 0)) {
                        GetLabelsRec(memo, a, labels, done, truth);
                        goto done;
                    }
                }
                /* Unreachable! */
                // throw "error in RPFP::GetLabelsRec";
                goto done;
            }
            else if (k == Not) {
                GetLabelsRec(memo, f.arg(0), labels, done, !truth);
                goto done;
            }
            else {
                bool pos; std::vector<symbol> names;
                if (f.is_label(pos, names)) {
                    GetLabelsRec(memo, f.arg(0), labels, done, truth);
                    if (pos == truth)
                        for (unsigned i = 0; i < names.size(); i++)
                            labels.push_back(names[i]);
                    goto done;
                }
            }
        }
    done:
        done[truth].insert(f);
    }

    void RPFP::GetLabels(Edge *e, std::vector<symbol> &labels){
        if(!e->map || e->map->labeled.null())
            return;
        Term tl = Localize(e, e->map->labeled);
        hash_map<ast,int> memo;
        hash_set<ast> done[2];
        GetLabelsRec(memo,tl,labels,done,true);
    }

#ifdef Z3OPS
    static Z3_subterm_truth *stt;
#endif

    int ir_count = 0;

    void RPFP::ImplicantRed(hash_map<ast, int> &memo, const Term &f, std::vector<Term> &lits,
                            hash_set<ast> *done, bool truth, hash_set<ast> &dont_cares) {
        if (done[truth].find(f) != done[truth].end())
            return; /* already processed */
#if 0
        int this_count = ir_count++;
        if(this_count == 50092)
            std::cout << "foo!\n";
#endif
        if (f.is_app()) {
            int nargs = f.num_args();
            decl_kind k = f.decl().get_decl_kind();
            if (k == Implies) {
                ImplicantRed(memo, f.arg(1) || !f.arg(0), lits, done, truth, dont_cares);
                goto done;
            }
            if (k == Iff) {
                int b = SubtermTruth(memo, f.arg(0));
                if (b == 2)
                    throw "disaster in ImplicantRed";
                ImplicantRed(memo, f.arg(1), lits, done, truth ? b : !b, dont_cares);
                goto done;
            }
            if (truth ? k == And : k == Or) {
                for (int i = 0; i < nargs; i++)
                    ImplicantRed(memo, f.arg(i), lits, done, truth, dont_cares);
                goto done;
            }
            if (truth ? k == Or : k == And) {
                for (int i = 0; i < nargs; i++) {
                    Term a = f.arg(i);
#if 0
                    if(i == nargs - 1){ // last chance!
                        ImplicantRed(memo,a,lits,done,truth,dont_cares);
                        goto done;
                    }
#endif
                    timer_start("SubtermTruth");
#ifdef Z3OPS
                    bool b = stt->eval(a);
#else
                    int b = SubtermTruth(memo, a);
#endif
                    timer_stop("SubtermTruth");
                    if (truth ? (b == 1) : (b == 0)) {
                        ImplicantRed(memo, a, lits, done, truth, dont_cares);
                        goto done;
                    }
                }
                /* Unreachable! */
                // TODO: need to indicate this failure to caller
                // std::cerr << "error in RPFP::ImplicantRed";
                goto done;
            }
            else if (k == Not) {
                ImplicantRed(memo, f.arg(0), lits, done, !truth, dont_cares);
                goto done;
            }
        }
        {
            if (dont_cares.find(f) == dont_cares.end()) {
                expr rf = ResolveIte(memo, f, lits, done, dont_cares);
                expr bv = truth ? rf : !rf;
                lits.push_back(bv);
            }
        }
    done:
        done[truth].insert(f);
    }

    void RPFP::ImplicantFullRed(hash_map<ast, int> &memo, const Term &f, std::vector<Term> &lits,
                                hash_set<ast> &done, hash_set<ast> &dont_cares, bool extensional) {
        if (done.find(f) != done.end())
            return; /* already processed */
        if (f.is_app()) {
            int nargs = f.num_args();
            decl_kind k = f.decl().get_decl_kind();
            if (k == Implies || k == Iff || k == And || k == Or || k == Not) {
                for (int i = 0; i < nargs; i++)
                    ImplicantFullRed(memo, f.arg(i), lits, done, dont_cares, extensional);
                goto done;
            }
        }
        {
            if (dont_cares.find(f) == dont_cares.end()) {
                int b = SubtermTruth(memo, f);
                if (b != 0 && b != 1) goto done;
                if (f.is_app() && f.decl().get_decl_kind() == Equal && f.arg(0).is_array()) {
                    if (b == 1 && !extensional) {
                        expr x = dualModel.eval(f.arg(0)); expr y = dualModel.eval(f.arg(1));
                        if (!eq(x, y))
                            b = 0;
                    }
                    if (b == 0)
                        goto done;
                }
                expr bv = (b == 1) ? f : !f;
                lits.push_back(bv);
            }
        }
    done:
        done.insert(f);
    }

    RPFP::Term RPFP::ResolveIte(hash_map<ast, int> &memo, const Term &t, std::vector<Term> &lits,
                                hash_set<ast> *done, hash_set<ast> &dont_cares) {
        if (resolve_ite_memo.find(t) != resolve_ite_memo.end())
            return resolve_ite_memo[t];
        Term res;
        if (t.is_app()) {
            func_decl f = t.decl();
            std::vector<Term> args;
            int nargs = t.num_args();
            if (f.get_decl_kind() == Ite) {
                timer_start("SubtermTruth");
#ifdef Z3OPS
                bool sel = stt->eval(t.arg(0));
#else
                int xval = SubtermTruth(memo, t.arg(0));
                bool sel;
                if (xval == 0)sel = false;
                else if (xval == 1)sel = true;
                else
                    throw "unresolved ite in model";
#endif
                timer_stop("SubtermTruth");
                ImplicantRed(memo, t.arg(0), lits, done, sel, dont_cares);
                res = ResolveIte(memo, t.arg(sel ? 1 : 2), lits, done, dont_cares);
            }
            else {
                for (int i = 0; i < nargs; i++)
                    args.push_back(ResolveIte(memo, t.arg(i), lits, done, dont_cares));
                res = f(args.size(), VEC2PTR(args));
            }
        }
        else res = t;
        resolve_ite_memo[t] = res;
        return res;
    }

    RPFP::Term RPFP::ElimIteRec(hash_map<ast, expr> &memo, const Term &t, std::vector<expr> &cnsts) {
        std::pair<ast, Term> foo(t, expr(ctx));
        std::pair<hash_map<ast, Term>::iterator, bool> bar = memo.insert(foo);
        Term &res = bar.first->second;
        if (bar.second) {
            if (t.is_app()) {
                int nargs = t.num_args();
                std::vector<expr> args;
                if (t.decl().get_decl_kind() == Equal) {
                    expr lhs = t.arg(0);
                    expr rhs = t.arg(1);
                    if (rhs.decl().get_decl_kind() == Ite) {
                        expr rhs_args[3];
                        lhs = ElimIteRec(memo, lhs, cnsts);
                        for (int i = 0; i < 3; i++)
                            rhs_args[i] = ElimIteRec(memo, rhs.arg(i), cnsts);
                        res = (rhs_args[0] && (lhs == rhs_args[1])) || ((!rhs_args[0]) && (lhs == rhs_args[2]));
                        goto done;
                    }
                }
                if (t.decl().get_decl_kind() == Ite) {
                    func_decl sym = ctx.fresh_func_decl("@ite", t.get_sort());
                    res = sym();
                    cnsts.push_back(ElimIteRec(memo, ctx.make(Equal, res, t), cnsts));
                }
                else {
                    for (int i = 0; i < nargs; i++)
                        args.push_back(ElimIteRec(memo, t.arg(i), cnsts));
                    res = t.decl()(args.size(), VEC2PTR(args));
                }
            }
            else if (t.is_quantifier())
                res = clone_quantifier(t, ElimIteRec(memo, t.body(), cnsts));
            else
                res = t;
        }
    done:
        return res;
    }

    RPFP::Term RPFP::ElimIte(const Term &t){ 
        hash_map<ast,expr> memo;
        std::vector<expr> cnsts;
        expr res = ElimIteRec(memo,t,cnsts);
        if(!cnsts.empty()){
            cnsts.push_back(res);
            res = ctx.make(And,cnsts);
        }
        return res;
    }

    void RPFP::Implicant(hash_map<ast,int> &memo, const Term &f, std::vector<Term> &lits, hash_set<ast> &dont_cares){
        hash_set<ast> done[2];
        ImplicantRed(memo,f,lits,done,true, dont_cares);
    }


    /** Underapproximate a formula using current counterexample. */

    RPFP::Term RPFP::UnderapproxFormula(const Term &f, hash_set<ast> &dont_cares){
        /* first compute truth values of subterms */
        hash_map<ast,int> memo;
#ifdef Z3OPS
        stt = Z3_mk_subterm_truth(ctx,dualModel);
#endif
        // SubtermTruth(memo,f);
        /* now compute an implicant */
        std::vector<Term> lits;
        Implicant(memo,f,lits, dont_cares);
#ifdef Z3OPS
        delete stt; stt = 0;
#endif
        /* return conjunction of literals */
        return conjoin(lits);
    }

    RPFP::Term RPFP::UnderapproxFullFormula(const Term &f, bool extensional){
        hash_set<ast> dont_cares;
        resolve_ite_memo.clear();
        timer_start("UnderapproxFormula");
        /* first compute truth values of subterms */
        hash_map<ast,int> memo;
        hash_set<ast> done;
        std::vector<Term> lits;
        ImplicantFullRed(memo,f,lits,done,dont_cares, extensional);
        timer_stop("UnderapproxFormula");
        /* return conjunction of literals */
        return conjoin(lits);
    }

    struct VariableProjector : Z3User {
  
        struct elim_cand {
            Term var;
            int sup;
            Term val;
        };
    
        typedef expr Term;

        hash_set<ast> keep;
        hash_map<ast,int> var_ord; 
        int num_vars;
        std::vector<elim_cand> elim_cands;
        hash_map<ast,std::vector<int> > sup_map;
        hash_map<ast,Term> elim_map;
        std::vector<int> ready_cands;
        hash_map<ast,int> cand_map;
        params simp_params;

        VariableProjector(Z3User &_user, std::vector<Term> &keep_vec) :
            Z3User(_user), simp_params() {
            num_vars = 0;
            for (unsigned i = 0; i < keep_vec.size(); i++) {
                keep.insert(keep_vec[i]);
                var_ord[keep_vec[i]] = num_vars++;
            }
        }
        int VarNum(const Term &v) {
            if (var_ord.find(v) == var_ord.end())
                var_ord[v] = num_vars++;
            return var_ord[v];
        }

        bool IsVar(const Term &t){
            return t.is_app() && t.num_args() == 0 && t.decl().get_decl_kind() == Uninterpreted;
        }
    
        bool IsPropLit(const Term &t, Term &a) {
            if (IsVar(t)) {
                a = t;
                return true;
            }
            else if (t.is_app() && t.decl().get_decl_kind() == Not)
                return IsPropLit(t.arg(0), a);
            return false;
        }
    
        void CountOtherVarsRec(hash_map<ast, int> &memo,
                               const Term &t,
                               int id,
                               int &count) {
            std::pair<ast, int> foo(t, 0);
            std::pair<hash_map<ast, int>::iterator, bool> bar = memo.insert(foo);
            // int &res = bar.first->second;
            if (!bar.second) return;
            if (t.is_app()) {
                func_decl f = t.decl();
                std::vector<Term> args;
                int nargs = t.num_args();
                if (nargs == 0 && f.get_decl_kind() == Uninterpreted) {
                    if (cand_map.find(t) != cand_map.end()) {
                        count++;
                        sup_map[t].push_back(id);
                    }
                }
                for (int i = 0; i < nargs; i++)
                    CountOtherVarsRec(memo, t.arg(i), id, count);
            }
            else if (t.is_quantifier())
                CountOtherVarsRec(memo, t.body(), id, count);
        }
    
        void NewElimCand(const Term &lhs, const Term &rhs) {
            if (debug_gauss) {
                std::cout << "mapping " << lhs << " to " << rhs << std::endl;
            }
            elim_cand cand;
            cand.var = lhs;
            cand.sup = 0;
            cand.val = rhs;
            elim_cands.push_back(cand);
            cand_map[lhs] = elim_cands.size() - 1;
        }

        void MakeElimCand(const Term &lhs, const Term &rhs) {
            if (eq(lhs, rhs))
                return;
            if (!IsVar(lhs)) {
                if (IsVar(rhs)) {
                    MakeElimCand(rhs, lhs);
                    return;
                }
                else {
                    std::cout << "would have mapped a non-var\n";
                    return;
                }
            }
            if (IsVar(rhs) && VarNum(rhs) > VarNum(lhs)) {
                MakeElimCand(rhs, lhs);
                return;
            }
            if (keep.find(lhs) != keep.end())
                return;
            if (cand_map.find(lhs) == cand_map.end())
                NewElimCand(lhs, rhs);
            else {
                int cand_idx = cand_map[lhs];
                if (IsVar(rhs) && cand_map.find(rhs) == cand_map.end()
                    && keep.find(rhs) == keep.end())
                    NewElimCand(rhs, elim_cands[cand_idx].val);
                elim_cands[cand_idx].val = rhs;
            }
        }

        Term FindRep(const Term &t) {
            if (cand_map.find(t) == cand_map.end())
                return t;
            Term &res = elim_cands[cand_map[t]].val;
            if (IsVar(res)) {
                assert(VarNum(res) < VarNum(t));
                res = FindRep(res);
                return res;
            }
            return t;
        }

        void GaussElimCheap(const std::vector<Term> &lits_in,
                            std::vector<Term> &lits_out) {
            for (unsigned i = 0; i < lits_in.size(); i++) {
                Term lit = lits_in[i];
                if (lit.is_app()) {
                    decl_kind k = lit.decl().get_decl_kind();
                    if (k == Equal || k == Iff)
                        MakeElimCand(FindRep(lit.arg(0)), FindRep(lit.arg(1)));
                }
            }

            for (unsigned i = 0; i < elim_cands.size(); i++) {
                elim_cand &cand = elim_cands[i];
                hash_map<ast, int> memo;
                CountOtherVarsRec(memo, cand.val, i, cand.sup);
                if (cand.sup == 0)
                    ready_cands.push_back(i);
            }

            while (!ready_cands.empty()) {
                elim_cand &cand = elim_cands[ready_cands.back()];
                ready_cands.pop_back();
                Term rep = FindRep(cand.var);
                if (!eq(rep, cand.var))
                    if (cand_map.find(rep) != cand_map.end()) {
                        int rep_pos = cand_map[rep];
                        cand.val = elim_cands[rep_pos].val;
                    }
                Term val = SubstRec(elim_map, cand.val);
                if (debug_gauss) {
                    std::cout << "subbing " << cand.var << " --> " << val << std::endl;
                }
                elim_map[cand.var] = val;
                std::vector<int> &sup = sup_map[cand.var];
                for (unsigned i = 0; i < sup.size(); i++) {
                    int c = sup[i];
                    if ((--elim_cands[c].sup) == 0)
                        ready_cands.push_back(c);
                }
            }

            for (unsigned i = 0; i < lits_in.size(); i++) {
                Term lit = lits_in[i];
                lit = SubstRec(elim_map, lit);
                lit = lit.simplify();
                if (eq(lit, ctx.bool_val(true)))
                    continue;
                Term a;
                if (IsPropLit(lit, a))
                    if (keep.find(lit) == keep.end())
                        continue;
                lits_out.push_back(lit);
            }
        }

        // maps variables to constrains in which the occur pos, neg
        hash_map<ast,int> la_index[2];
        hash_map<ast,Term> la_coeffs[2];
        std::vector<Term> la_pos_vars;
        bool fixing;
    
        void IndexLAcoeff(const Term &coeff1, const Term &coeff2, Term t, int id) {
            Term coeff = coeff1 * coeff2;
            coeff = coeff.simplify();
            Term is_pos = (coeff >= ctx.int_val(0));
            is_pos = is_pos.simplify();
            if (eq(is_pos, ctx.bool_val(true)))
                IndexLA(true, coeff, t, id);
            else
                IndexLA(false, coeff, t, id);
        }

        void IndexLAremove(const Term &t) {
            if (IsVar(t)) {
                la_index[0][t] = -1;  // means ineligible to be eliminated
                la_index[1][t] = -1;  // (more that one occurrence, or occurs not in linear comb)
            }
            else if (t.is_app()) {
                int nargs = t.num_args();
                for (int i = 0; i < nargs; i++)
                    IndexLAremove(t.arg(i));
            }
            // TODO: quantifiers?
        }


        void IndexLA(bool pos, const Term &coeff, const Term &t, int id) {
            if (t.is_numeral())
                return;
            if (t.is_app()) {
                int nargs = t.num_args();
                switch (t.decl().get_decl_kind()) {
                case Plus:
                    for (int i = 0; i < nargs; i++)
                        IndexLA(pos, coeff, t.arg(i), id);
                    break;
                case Sub:
                    IndexLA(pos, coeff, t.arg(0), id);
                    IndexLA(!pos, coeff, t.arg(1), id);
                    break;
                case Times:
                    if (t.arg(0).is_numeral())
                        IndexLAcoeff(coeff, t.arg(0), t.arg(1), id);
                    else if (t.arg(1).is_numeral())
                        IndexLAcoeff(coeff, t.arg(1), t.arg(0), id);
                    break;
                default:
                    if (IsVar(t) && (fixing || la_index[pos].find(t) == la_index[pos].end())) {
                        la_index[pos][t] = id;
                        la_coeffs[pos][t] = coeff;
                        if (pos && !fixing)
                            la_pos_vars.push_back(t);  // this means we only add a var once
                    }
                    else
                        IndexLAremove(t);
                }
            }
        }

        void IndexLAstart(bool pos, const Term &t, int id){
            IndexLA(pos,(pos ? ctx.int_val(1) : ctx.int_val(-1)), t, id);
        }

        void IndexLApred(bool pos, const Term &p, int id) {
            if (p.is_app()) {
                switch (p.decl().get_decl_kind()) {
                case Not:
                    IndexLApred(!pos, p.arg(0), id);
                    break;
                case Leq:
                case Lt:
                    IndexLAstart(!pos, p.arg(0), id);
                    IndexLAstart(pos, p.arg(1), id);
                    break;
                case Geq:
                case Gt:
                    IndexLAstart(pos, p.arg(0), id);
                    IndexLAstart(!pos, p.arg(1), id);
                    break;
                default:
                    IndexLAremove(p);
                }
            }
        }

        void IndexLAfix(const Term &p, int id){
            fixing = true;
            IndexLApred(true,p,id);
            fixing = false;
        }

        bool IsCanonIneq(const Term &lit, Term &term, Term &bound) {
            // std::cout << Z3_simplify_get_help(ctx) << std::endl;
            bool pos = lit.decl().get_decl_kind() != Not;
            Term atom = pos ? lit : lit.arg(0);
            if (atom.decl().get_decl_kind() == Leq) {
                if (pos) {
                    bound = atom.arg(0);
                    term = atom.arg(1).simplify(simp_params);
#if Z3_MAJOR_VERSION < 4
                    term = SortSum(term);
#endif
                }
                else {
                    bound = (atom.arg(1) + ctx.int_val(1));
                    term = atom.arg(0);
                    // std::cout << "simplifying bound: " << bound << std::endl;
                    bound = bound.simplify();
                    term = term.simplify(simp_params);
#if Z3_MAJOR_VERSION < 4
                    term = SortSum(term);
#endif
                }
                return true;
            }
            else if (atom.decl().get_decl_kind() == Geq) {
                if (pos) {
                    bound = atom.arg(1);  // integer axiom
                    term = atom.arg(0).simplify(simp_params);
#if Z3_MAJOR_VERSION < 4
                    term = SortSum(term);
#endif
                    return true;
                }
                else {
                    bound = -(atom.arg(1) - ctx.int_val(1));  // integer axiom
                    term = -atom.arg(0);
                    bound = bound.simplify();
                    term = term.simplify(simp_params);
#if Z3_MAJOR_VERSION < 4
                    term = SortSum(term);
#endif
                }
                return true;
            }
            return false;
        }

        Term CanonIneqTerm(const Term &p){
            Term term,bound;
            Term ps = p.simplify();
            bool ok = IsCanonIneq(ps,term,bound);
            assert(ok);
            return term - bound;
        }

        void ElimRedundantBounds(std::vector<Term> &lits) {
            hash_map<ast, int> best_bound;
            for (unsigned i = 0; i < lits.size(); i++) {
                lits[i] = lits[i].simplify(simp_params);
                Term term, bound;
                if (IsCanonIneq(lits[i], term, bound)) {
                    if (best_bound.find(term) == best_bound.end())
                        best_bound[term] = i;
                    else {
                        int best = best_bound[term];
                        Term bterm, bbound;
                        IsCanonIneq(lits[best], bterm, bbound);
                        Term comp = bound > bbound;
                        comp = comp.simplify();
                        if (eq(comp, ctx.bool_val(true))) {
                            lits[best] = ctx.bool_val(true);
                            best_bound[term] = i;
                        }
                        else {
                            lits[i] = ctx.bool_val(true);
                        }
                    }
                }
            }
        }

        void FourierMotzkinCheap(const std::vector<Term> &lits_in,
                                 std::vector<Term> &lits_out) {
            simp_params.set(":som", true);
            simp_params.set(":sort-sums", true);
            fixing = false; lits_out = lits_in;
            ElimRedundantBounds(lits_out);
            for (unsigned i = 0; i < lits_out.size(); i++)
                IndexLApred(true, lits_out[i], i);

            for (unsigned i = 0; i < la_pos_vars.size(); i++) {
                Term var = la_pos_vars[i];
                if (la_index[false].find(var) != la_index[false].end()) {
                    int pos_idx = la_index[true][var];
                    int neg_idx = la_index[false][var];
                    if (pos_idx >= 0 && neg_idx >= 0) {
                        if (keep.find(var) != keep.end()) {
                            std::cout << "would have eliminated keep var\n";
                            continue;
                        }
                        Term tpos = CanonIneqTerm(lits_out[pos_idx]);
                        Term tneg = CanonIneqTerm(lits_out[neg_idx]);
                        Term pos_coeff = la_coeffs[true][var];
                        Term neg_coeff = -la_coeffs[false][var];
                        Term comb = neg_coeff * tpos + pos_coeff * tneg;
                        Term ineq = ctx.int_val(0) <= comb;
                        ineq = ineq.simplify();
                        lits_out[pos_idx] = ineq;
                        lits_out[neg_idx] = ctx.bool_val(true);
                        IndexLAfix(ineq, pos_idx);
                    }
                }
            }
        }

        Term ProjectFormula(const Term &f){
            std::vector<Term> lits, new_lits1, new_lits2;
            CollectConjuncts(f,lits);
            timer_start("GaussElimCheap");
            GaussElimCheap(lits,new_lits1);
            timer_stop("GaussElimCheap");
            timer_start("FourierMotzkinCheap");
            FourierMotzkinCheap(new_lits1,new_lits2);
            timer_stop("FourierMotzkinCheap");
            return conjoin(new_lits2);
        }
    }; 
    
    void Z3User::CollectConjuncts(const Term &f, std::vector<Term> &lits, bool pos) {
        if (f.is_app() && f.decl().get_decl_kind() == Not)
            CollectConjuncts(f.arg(0), lits, !pos);
        else if (pos && f.is_app() && f.decl().get_decl_kind() == And) {
            int num_args = f.num_args();
            for (int i = 0; i < num_args; i++)
                CollectConjuncts(f.arg(i), lits, true);
        }
        else if (!pos && f.is_app() && f.decl().get_decl_kind() == Or) {
            int num_args = f.num_args();
            for (int i = 0; i < num_args; i++)
                CollectConjuncts(f.arg(i), lits, false);
        }
        else if (pos) {
            if (!eq(f, ctx.bool_val(true)))
                lits.push_back(f);
        }
        else {
            if (!eq(f, ctx.bool_val(false)))
                lits.push_back(!f);
        }
    }

    void Z3User::CollectJuncts(const Term &f, std::vector<Term> &lits, decl_kind op, bool negate) {
        if (f.is_app() && f.decl().get_decl_kind() == Not)
            CollectJuncts(f.arg(0), lits, (op == And) ? Or : And, !negate);
        else if (f.is_app() && f.decl().get_decl_kind() == op) {
            int num_args = f.num_args();
            for (int i = 0; i < num_args; i++)
                CollectJuncts(f.arg(i), lits, op, negate);
        }
        else {
            expr junct = negate ? Negate(f) : f;
            lits.push_back(junct);
        }
    }

    struct TermLt {
        bool operator()(const expr &x, const expr &y){
            unsigned xid = x.get_id();
            unsigned yid = y.get_id();
            return xid < yid;
        }
    };

    void Z3User::SortTerms(std::vector<Term> &terms){
        TermLt foo;
        std::sort(terms.begin(),terms.end(),foo);
    }

    Z3User::Term Z3User::SortSum(const Term &t){
        if(!(t.is_app() && t.decl().get_decl_kind() == Plus))
            return t;
        int nargs = t.num_args();
        if(nargs < 2) return t;
        std::vector<Term> args(nargs);
        for(int i = 0; i < nargs; i++)
            args[i] = t.arg(i);
        SortTerms(args);
        if(nargs == 2)
            return args[0] + args[1];
        return sum(args);
    }
  

    RPFP::Term RPFP::ProjectFormula(std::vector<Term> &keep_vec, const Term &f){
        VariableProjector vp(*this,keep_vec);
        return vp.ProjectFormula(f);
    }

    /** Compute an underapproximation of every node in a tree rooted at "root",
        based on a previously computed counterexample. The underapproximation
        may contain free variables that are implicitly existentially quantified.
    */

    RPFP::Term RPFP::ComputeUnderapprox(Node *root, int persist){
        /* if terminated underapprox is empty set (false) */
        bool show_model = false;
        if(show_model)
            std::cout << dualModel << std::endl;
        if(!root->Outgoing){
            root->Underapprox.SetEmpty();
            return ctx.bool_val(true);
        }
        /* if not used in cex, underapprox is empty set (false) */
        if(Empty(root)){
            root->Underapprox.SetEmpty();
            return ctx.bool_val(true);
        }
        /* compute underapprox of children first */
        std::vector<Node *> &chs = root->Outgoing->Children;
        std::vector<Term> chu(chs.size());
        for(unsigned i = 0; i < chs.size(); i++)
            chu[i] = ComputeUnderapprox(chs[i],persist);

        Term b; std::vector<Term> v;
        RedVars(root, b, v);
        /* underapproximate the edge formula */
        hash_set<ast> dont_cares;
        dont_cares.insert(b);
        resolve_ite_memo.clear();
        timer_start("UnderapproxFormula");
        Term dual = root->Outgoing->dual.null() ? ctx.bool_val(true) : root->Outgoing->dual;
        Term eu = UnderapproxFormula(dual,dont_cares);
        timer_stop("UnderapproxFormula");
        /* combine with children */
        chu.push_back(eu);
        eu = conjoin(chu);
        /* project onto appropriate variables */
        eu = ProjectFormula(v,eu);
        eu = eu.simplify();

#if 0
        /* check the result is consistent */
        {
            hash_map<ast,int> memo;
            int res = SubtermTruth(memo, eu);
            if(res != 1)
                throw "inconsistent projection";
        }
#endif

        /* rename to appropriate variable names */
        hash_map<ast,Term> memo;
        for (unsigned i = 0; i < v.size(); i++)
            memo[v[i]] = root->Annotation.IndParams[i];  /* copy names from annotation */
        Term funder = SubstRec(memo, eu);
        root->Underapprox = CreateRelation(root->Annotation.IndParams,funder);
#if 0
        if(persist)
            Z3_persist_ast(ctx,root->Underapprox.Formula,persist);
#endif
        return eu;
    }

    void RPFP::FixCurrentState(Edge *edge){
        hash_set<ast> dont_cares;
        resolve_ite_memo.clear();
        timer_start("UnderapproxFormula");
        Term dual = edge->dual.null() ? ctx.bool_val(true) : edge->dual;
        Term eu = UnderapproxFormula(dual,dont_cares);
        timer_stop("UnderapproxFormula");
        ConstrainEdgeLocalized(edge,eu);
    }

    void RPFP::GetGroundLitsUnderQuants(hash_set<ast> *memo, const Term &f, std::vector<Term> &res, int under){
        if(memo[under].find(f) != memo[under].end())
            return;
        memo[under].insert(f);
        if (f.is_app()) {
            if (!under && !f.has_quantifiers())
                return;
            decl_kind k = f.decl().get_decl_kind();
            if (k == And || k == Or || k == Implies || k == Iff) {
                int num_args = f.num_args();
                for (int i = 0; i < num_args; i++)
                    GetGroundLitsUnderQuants(memo, f.arg(i), res, under);
                return;
            }
        }
        else if (f.is_quantifier()){
#if 0
            // treat closed quantified formula as a literal 'cause we hate nested quantifiers
            if(under && IsClosedFormula(f)) 
                res.push_back(f);
            else
#endif
                GetGroundLitsUnderQuants(memo,f.body(),res,1);
            return;
        }
        if(f.is_var()){
            //      std::cout << "foo!\n";
            return;
        }
        if(under && f.is_ground())
            res.push_back(f);
    }

    RPFP::Term RPFP::StrengthenFormulaByCaseSplitting(const Term &f, std::vector<expr> &case_lits){
        hash_set<ast> memo[2];
        std::vector<Term> lits;
        GetGroundLitsUnderQuants(memo, f, lits, 0);
        hash_set<ast> lits_hash;
        for(unsigned i = 0; i < lits.size(); i++)
            lits_hash.insert(lits[i]);
        hash_map<ast,expr> subst;
        hash_map<ast,int> stt_memo;
        std::vector<expr> conjuncts;
        for(unsigned i = 0; i < lits.size(); i++){
            const expr &lit = lits[i];
            if(lits_hash.find(NegateLit(lit)) == lits_hash.end()){
                case_lits.push_back(lit);
                bool tval = false;
                expr atom = lit;
                if(lit.is_app() && lit.decl().get_decl_kind() == Not){
                    tval = true;
                    atom = lit.arg(0);
                }
                expr etval = ctx.bool_val(tval);
                if(atom.is_quantifier())
                    subst[atom] = etval; // this is a bit desperate, since we can't eval quants
                else {
                    int b = SubtermTruth(stt_memo,atom);
                    if(b == (tval ? 1 : 0))
                        subst[atom] = etval;
                    else {
                        if(b == 0 || b == 1){
                            etval = ctx.bool_val(b ? true : false);
                            subst[atom] = etval;
                            conjuncts.push_back(b ? atom : !atom);
                        }
                    }
                }
            }
        }
        expr g = f;
        if(!subst.empty()){
            g = SubstRec(subst,f);
            if(conjuncts.size())
                g = g && ctx.make(And,conjuncts);
            g = g.simplify();
        }
#if 1
        expr g_old = g;
        g = RemoveRedundancy(g);
        bool changed = !eq(g,g_old);
        g = g.simplify();
        if(changed) {  // a second pass can get some more simplification
            g = RemoveRedundancy(g);
            g = g.simplify();
        }
#else
        g = RemoveRedundancy(g);
        g = g.simplify();
#endif
        g = AdjustQuantifiers(g);
        return g;
    }

    RPFP::Term RPFP::ModelValueAsConstraint(const Term &t) {
        if (t.is_array()) {
            ArrayValue arr;
            Term e = dualModel.eval(t);
            EvalArrayTerm(e, arr);
            if (arr.defined) {
                std::vector<expr> cs;
                for (std::map<ast, ast>::iterator it = arr.entries.begin(), en = arr.entries.end(); it != en; ++it) {
                    expr foo = select(t, expr(ctx, it->first)) == expr(ctx, it->second);
                    cs.push_back(foo);
                }
                return conjoin(cs);
            }
        }
        else {
            expr r = dualModel.get_const_interp(t.decl());
            if (!r.null()) {
                expr res = t == expr(ctx, r);
                return res;
            }
        }
        return ctx.bool_val(true);
    }

    void RPFP::EvalNodeAsConstraint(Node *p, Transformer &res)
    {
        Term b; std::vector<Term> v;
        RedVars(p, b, v);
        std::vector<Term> args;
        for(unsigned i = 0; i < v.size(); i++){
            expr val = ModelValueAsConstraint(v[i]);
            if(!eq(val,ctx.bool_val(true)))
                args.push_back(val);
        }
        expr cnst = conjoin(args);
        hash_map<ast,Term> memo;
        for (unsigned i = 0; i < v.size(); i++)
            memo[v[i]] = p->Annotation.IndParams[i];  /* copy names from annotation */
        Term funder = SubstRec(memo, cnst);
        res = CreateRelation(p->Annotation.IndParams,funder);
    }

#if 0
    void RPFP::GreedyReduce(solver &s, std::vector<expr> &conjuncts){
        // verify
        s.push();
        expr conj = ctx.make(And,conjuncts);
        s.add(conj);
        check_result res = s.check();
        if(res != unsat)
            throw "should be unsat";
        s.pop(1);

        for(unsigned i = 0; i < conjuncts.size(); ){
            std::swap(conjuncts[i],conjuncts.back());
            expr save = conjuncts.back();
            conjuncts.pop_back();
            s.push();
            expr conj = ctx.make(And,conjuncts);
            s.add(conj);
            check_result res = s.check();
            s.pop(1);
            if(res != unsat){
                conjuncts.push_back(save);
                std::swap(conjuncts[i],conjuncts.back());
                i++;
            }
        }
    }
#endif

    void RPFP::GreedyReduce(solver &s, std::vector<expr> &conjuncts){
        std::vector<expr> lits(conjuncts.size());
        for(unsigned i = 0; i < lits.size(); i++){
            func_decl pred = ctx.fresh_func_decl("@alit", ctx.bool_sort());
            lits[i] = pred();
            s.add(ctx.make(Implies,lits[i],conjuncts[i]));
        }
    
        // verify
        check_result res = s.check(lits.size(), VEC2PTR(lits));
        if(res != unsat){
            // add the axioms in the off chance they are useful
            const std::vector<expr> &theory = ls->get_axioms();
            for(unsigned i = 0; i < theory.size(); i++)
                s.add(theory[i]);
            for(int k = 0; k < 100; k++) // keep trying, maybe MBQI will do something!
                if(s.check(lits.size(), VEC2PTR(lits)) == unsat)
                    goto is_unsat;
            throw "should be unsat";
        }
    is_unsat:
        for(unsigned i = 0; i < conjuncts.size(); ){
            std::swap(conjuncts[i],conjuncts.back());
            std::swap(lits[i],lits.back());
            check_result res = s.check(lits.size()-1, VEC2PTR(lits));
            if(res != unsat){
                std::swap(conjuncts[i],conjuncts.back());
                std::swap(lits[i],lits.back());
                i++;
            }
            else {
                conjuncts.pop_back();
                lits.pop_back();
            }
        }
    }

    void foobar(){
    }

    void RPFP::GreedyReduceNodes(std::vector<Node *> &nodes){
        std::vector<expr> lits;
        for(unsigned i = 0; i < nodes.size(); i++){
            Term b; std::vector<Term> v;
            RedVars(nodes[i], b, v);
            lits.push_back(!b);
            expr bv = dualModel.eval(b);
            if(eq(bv,ctx.bool_val(true))){
                check_result  res = slvr_check(lits.size(), VEC2PTR(lits));
                if(res == unsat)
                    lits.pop_back();
                else
                    foobar();
            }
        }
    }

    check_result RPFP::CheckWithConstrainedNodes(std::vector<Node *> &posnodes,std::vector<Node *> &negnodes){
        timer_start("Check");
        std::vector<expr> lits;
        for(unsigned i = 0; i < posnodes.size(); i++){
            Term b; std::vector<Term> v;
            RedVars(posnodes[i], b, v);
            lits.push_back(b);
        }
        for(unsigned i = 0; i < negnodes.size(); i++){
            Term b; std::vector<Term> v;
            RedVars(negnodes[i], b, v);
            lits.push_back(!b);
        }
        check_result res = slvr_check(lits.size(), VEC2PTR(lits));
        if(res == unsat && posnodes.size()){
            lits.resize(posnodes.size());
            res = slvr_check(lits.size(), VEC2PTR(lits));
        }
        dualModel = slvr().get_model();
#if 0
        if(!dualModel.null()){
            std::cout << "posnodes called:\n";
            for(unsigned i = 0; i < posnodes.size(); i++)
                if(!Empty(posnodes[i]))
                    std::cout << posnodes[i]->Name.name() << "\n";
            std::cout << "negnodes called:\n";
            for(unsigned i = 0; i < negnodes.size(); i++)
                if(!Empty(negnodes[i]))
                    std::cout << negnodes[i]->Name.name() << "\n";
        }
#endif
        timer_stop("Check");
        return res;
    }


    void RPFP_caching::FilterCore(std::vector<expr> &core, std::vector<expr> &full_core){
        hash_set<ast> core_set;
        std::copy(full_core.begin(),full_core.end(),std::inserter(core_set,core_set.begin()));
        std::vector<expr> new_core;
        for(unsigned i = 0; i < core.size(); i++)
            if(core_set.find(core[i]) != core_set.end())
                new_core.push_back(core[i]);
        core.swap(new_core);
    }

    void RPFP_caching::GreedyReduceCache(std::vector<expr> &assumps, std::vector<expr> &core){
        std::vector<expr> lits = assumps, full_core; 
        std::copy(core.begin(),core.end(),std::inserter(lits,lits.end()));
    
        // verify
        check_result res = CheckCore(lits,full_core);
        if(res != unsat){
            // add the axioms in the off chance they are useful
            const std::vector<expr> &theory = ls->get_axioms();
            for(unsigned i = 0; i < theory.size(); i++)
                GetAssumptionLits(theory[i],assumps);
            lits = assumps; 
            std::copy(core.begin(),core.end(),std::inserter(lits,lits.end()));
      
            for(int k = 0; k < 4; k++) // keep trying, maybe MBQI will do something!
                if((res = CheckCore(lits,full_core)) == unsat)
                    goto is_unsat;
            throw greedy_reduce_failed();
        }
    is_unsat:
        FilterCore(core,full_core);
    
        std::vector<expr> dummy;
        if(CheckCore(full_core,dummy) != unsat)
            throw "should be unsat";

        for(unsigned i = 0; i < core.size(); ){
            expr temp = core[i];
            std::swap(core[i],core.back());
            core.pop_back();
            lits.resize(assumps.size());
            std::copy(core.begin(),core.end(),std::inserter(lits,lits.end()));
            res = CheckCore(lits,full_core);
            if(res != unsat){
                core.push_back(temp);
                std::swap(core[i],core.back());
                i++;
            }
        }
    }

    expr RPFP::NegateLit(const expr &f){
        if(f.is_app() && f.decl().get_decl_kind() == Not)
            return f.arg(0);
        else
            return !f;
    }

    void RPFP::NegateLits(std::vector<expr> &lits){
        for(unsigned i = 0; i < lits.size(); i++){
            expr &f = lits[i];
            if(f.is_app() && f.decl().get_decl_kind() == Not)
                f = f.arg(0);
            else
                f = !f;
        }
    }

    expr RPFP::SimplifyOr(std::vector<expr> &lits){
        if(lits.size() == 0)
            return ctx.bool_val(false);
        if(lits.size() == 1)
            return lits[0];
        return ctx.make(Or,lits);
    }

    expr RPFP::SimplifyAnd(std::vector<expr> &lits){
        if(lits.size() == 0)
            return ctx.bool_val(true);
        if(lits.size() == 1)
            return lits[0];
        return ctx.make(And,lits);
    }


    /* This is a wrapper for a solver that is intended to compute
       implicants from models. It works around a problem in Z3 with
       models in the non-extensional array theory. It does this by
       naming all of the store terms in a formula. That is, (store ...)
       is replaced by "name" with an added constraint name = (store
       ...). This allows us to determine from the model whether an array
       equality is true or false (it is false if the two sides are
       mapped to different function symbols, even if they have the same
       contents).
    */

    struct implicant_solver {
        RPFP *owner;
        solver &aux_solver;
        std::vector<expr> assumps, namings;
        std::vector<int> assump_stack, naming_stack;
        hash_map<ast,expr> renaming, renaming_memo;
    
        void add(const expr &e){
            expr t = e;
            if(!aux_solver.extensional_array_theory()){
                unsigned i = namings.size();
                t = owner->ExtractStores(renaming_memo,t,namings,renaming);
                for(; i < namings.size(); i++)
                    aux_solver.add(namings[i]);
            }
            assumps.push_back(t);
            aux_solver.add(t);
        }

        void push() {
            assump_stack.push_back(assumps.size());
            naming_stack.push_back(namings.size());
            aux_solver.push();
        }

        // When we pop the solver, we have to re-add any namings that were lost

        void pop(int n) {
            aux_solver.pop(n);
            int new_assumps = assump_stack[assump_stack.size()-n];
            int new_namings = naming_stack[naming_stack.size()-n];
            for(unsigned i = new_namings; i < namings.size(); i++)
                aux_solver.add(namings[i]);
            assumps.resize(new_assumps);
            namings.resize(new_namings);
            assump_stack.resize(assump_stack.size()-1);
            naming_stack.resize(naming_stack.size()-1);
        }

        check_result check() {
            return aux_solver.check();
        }

        model get_model() {
            return aux_solver.get_model();
        }
    
        expr get_implicant() {
            owner->dualModel = aux_solver.get_model();
            expr dual = owner->ctx.make(And,assumps);
            bool ext = aux_solver.extensional_array_theory();
            expr eu = owner->UnderapproxFullFormula(dual,ext);
            // if we renamed store terms, we have to undo
            if(!ext)
                eu = owner->SubstRec(renaming,eu);
            return eu;
        }
    
        implicant_solver(RPFP *_owner, solver &_aux_solver) 
            : owner(_owner), aux_solver(_aux_solver)
        {}
    };

    // set up edge constraint in aux solver
    void RPFP::AddEdgeToSolver(implicant_solver &aux_solver, Edge *edge){
        if(!edge->dual.null())
            aux_solver.add(edge->dual);
        for(unsigned i = 0; i < edge->constraints.size(); i++){
            expr tl = edge->constraints[i];
            aux_solver.add(tl);
        }
    }

    void RPFP::AddEdgeToSolver(Edge *edge){
        if(!edge->dual.null())
            aux_solver.add(edge->dual);
        for(unsigned i = 0; i < edge->constraints.size(); i++){
            expr tl = edge->constraints[i];
            aux_solver.add(tl);
        }
    }

    static int by_case_counter = 0;

    void RPFP::InterpolateByCases(Node *root, Node *node){
        timer_start("InterpolateByCases");
        bool axioms_added = false;
        hash_set<ast> axioms_needed;
        const std::vector<expr> &theory = ls->get_axioms();
        for(unsigned i = 0; i < theory.size(); i++)
            axioms_needed.insert(theory[i]);
        implicant_solver is(this,aux_solver);
        is.push();
        AddEdgeToSolver(is,node->Outgoing);
        node->Annotation.SetEmpty();
        hash_set<ast> *core = new hash_set<ast>;
        core->insert(node->Outgoing->dual);
        expr prev_annot = ctx.bool_val(false);
        expr prev_impl = ctx.bool_val(false);
        int repeated_case_count = 0;
        while(1){
            by_case_counter++;
            is.push();
            expr annot = !GetAnnotation(node);
            Transformer old_annot = node->Annotation;
            is.add(annot);
            if(is.check() == unsat){
                is.pop(1);
                break;
            }
            is.pop(1);
            Push();
            expr the_impl = is.get_implicant();
            if(eq(the_impl,prev_impl)){
                // std::cout << "got old implicant\n";
                repeated_case_count++;
            }
            prev_impl = the_impl;
            ConstrainEdgeLocalized(node->Outgoing,the_impl);
            ConstrainEdgeLocalized(node->Outgoing,!GetAnnotation(node)); //TODO: need this?
      
            {
                check_result foo = Check(root);
                if(foo != unsat){
                    Pop(1);
                    is.pop(1);
                    delete core;
                    timer_stop("InterpolateByCases");
                    throw ReallyBad();
                    // slvr().print("should_be_unsat.smt2");
                    // throw "should be unsat";
                }
                std::vector<expr> assumps, axioms_to_add;
                slvr().get_proof().get_assumptions(assumps);
                for(unsigned i = 0; i < assumps.size(); i++){
                    (*core).insert(assumps[i]);
                    if(axioms_needed.find(assumps[i]) != axioms_needed.end()){
                        axioms_to_add.push_back(assumps[i]);
                        axioms_needed.erase(assumps[i]);
                    }
                }
                // AddToProofCore(*core);
                
                try {
                    SolveSingleNode(root,node);
                }
                catch (char const *msg){
                    // This happens if interpolation fails
                    Pop(1);
                    is.pop(1);
                    delete core;
                    timer_stop("InterpolateByCases");
                    throw msg;
                }
                {
                    expr itp = GetAnnotation(node);
                    dualModel = is.get_model(); // TODO: what does this mean?
                    std::vector<expr> case_lits;
                    itp = StrengthenFormulaByCaseSplitting(itp, case_lits);
                    SetAnnotation(node,itp);
                    node->Annotation.Formula = node->Annotation.Formula.simplify();
                }

                for(unsigned i = 0; i < axioms_to_add.size(); i++)
                    is.add(axioms_to_add[i]);
      
#define TEST_BAD
#ifdef TEST_BAD
                {
                    static int bad_count = 0, num_bads = 1;
                    if(bad_count >= num_bads){
                        bad_count = 0;
                        num_bads = num_bads * 2;
                        Pop(1);
                        is.pop(1);
                        delete core;
                        timer_stop("InterpolateByCases");
                        throw Bad();
                    }
                    bad_count++;
                }
#endif
            }

            if(node->Annotation.IsEmpty() || eq(node->Annotation.Formula,prev_annot) || (repeated_case_count > 0 && !axioms_added) || (repeated_case_count >= 10)){
                //looks_bad:
                if(!axioms_added){
                    // add the axioms in the off chance they are useful
                    const std::vector<expr> &theory = ls->get_axioms();
                    for(unsigned i = 0; i < theory.size(); i++)
                        is.add(theory[i]);
                    axioms_added = true;
                }
                else {
                    //#define KILL_ON_BAD_INTERPOLANT   
#ifdef KILL_ON_BAD_INTERPOLANT 
                    std::cout << "bad in InterpolateByCase -- core:\n";
#if 0
                    std::vector<expr> assumps;
                    slvr().get_proof().get_assumptions(assumps);
                    for(unsigned i = 0; i < assumps.size(); i++)
                        assumps[i].show();
#endif
                    std::cout << "checking for inconsistency\n";
                    std::cout << "model:\n";
                    is.get_model().show(); 
                    expr impl = is.get_implicant();
                    std::vector<expr> conjuncts;
                    CollectConjuncts(impl,conjuncts,true);
                    std::cout << "impl:\n";
                    for(unsigned i = 0; i < conjuncts.size(); i++)
                        conjuncts[i].show();
                    std::cout << "annot:\n";
                    annot.show();
                    is.add(annot);
                    for(unsigned i = 0; i < conjuncts.size(); i++)
                        is.add(conjuncts[i]);
                    if(is.check() == unsat){
                        std::cout << "inconsistent!\n";
                        std::vector<expr> is_assumps;
                        is.aux_solver.get_proof().get_assumptions(is_assumps);
                        std::cout << "core:\n";
                        for(unsigned i = 0; i < is_assumps.size(); i++)
                            is_assumps[i].show();
                    }
                    else {
                        std::cout << "consistent!\n";
                        is.aux_solver.print("should_be_inconsistent.smt2");
                    }
                    std::cout << "by_case_counter = " << by_case_counter << "\n";
                    throw "ack!";
#endif
                    Pop(1);
                    is.pop(1);
                    delete core;
                    timer_stop("InterpolateByCases");
                    throw ReallyBad();
                }
            }
            Pop(1);
            prev_annot = node->Annotation.Formula;
            node->Annotation.UnionWith(old_annot);
        }
        if(proof_core)
            delete proof_core; // shouldn't happen
        proof_core = core;
        is.pop(1);
        timer_stop("InterpolateByCases");
    }

    void RPFP::Generalize(Node *root, Node *node){
        timer_start("Generalize");
        aux_solver.push();
        AddEdgeToSolver(node->Outgoing);
        expr fmla = GetAnnotation(node);
        std::vector<expr> conjuncts;
        CollectConjuncts(fmla,conjuncts,false);
        GreedyReduce(aux_solver,conjuncts);     // try to remove conjuncts one at a tme
        aux_solver.pop(1);
        NegateLits(conjuncts);
        SetAnnotation(node,SimplifyOr(conjuncts));
        timer_stop("Generalize");
    }

    RPFP_caching::edge_solver &RPFP_caching::SolverForEdge(Edge *edge, bool models, bool axioms){
        edge_solver &es = edge_solvers[edge];
        uptr<solver> &p = es.slvr;
        if(!p.get()){
            scoped_no_proof no_proofs_please(ctx.m()); // no proofs
            p.set(new solver(ctx,true,models)); // no models
            if(axioms){
                RPFP::LogicSolver *ls = edge->owner->ls;
                const std::vector<expr> &axs = ls->get_axioms();
                for(unsigned i = 0; i < axs.size(); i++)
                    p.get()->add(axs[i]);
            }
        }
        return es;
    }


    // caching version of above
    void RPFP_caching::GeneralizeCache(Edge *edge){
        timer_start("Generalize");
        scoped_solver_for_edge ssfe(this,edge);
        Node *node = edge->Parent;
        std::vector<expr> assumps, core, conjuncts;
        AssertEdgeCache(edge,assumps);
        for(unsigned i = 0; i < edge->Children.size(); i++){
            expr as = GetAnnotation(edge->Children[i]);
            std::vector<expr> clauses;
            if(!as.is_true()){
                CollectConjuncts(as.arg(1),clauses);
                for(unsigned j = 0; j < clauses.size(); j++)
                    GetAssumptionLits(as.arg(0) || clauses[j],assumps);
            }
        }
        expr fmla = GetAnnotation(node);
        std::vector<expr> lits;
        if(fmla.is_true()){
            timer_stop("Generalize");
            return;
        }
        assumps.push_back(fmla.arg(0).arg(0));
        CollectConjuncts(!fmla.arg(1),lits);
#if 0
        for(unsigned i = 0; i < lits.size(); i++){
            const expr &lit = lits[i];
            if(lit.is_app() && lit.decl().get_decl_kind() == Equal){
                lits[i] = ctx.make(Leq,lit.arg(0),lit.arg(1));
                lits.push_back(ctx.make(Leq,lit.arg(1),lit.arg(0)));
            }
        }
#endif
        hash_map<ast,expr> lit_map;
        for(unsigned i = 0; i < lits.size(); i++)
            GetAssumptionLits(lits[i],core,&lit_map);
        GreedyReduceCache(assumps,core);
        for(unsigned i = 0; i < core.size(); i++)
            conjuncts.push_back(lit_map[core[i]]); 
        NegateLits(conjuncts);
        SetAnnotation(node,SimplifyOr(conjuncts));
        timer_stop("Generalize");
    }

    // caching version of above
    bool RPFP_caching::PropagateCache(Edge *edge){
        timer_start("PropagateCache");
        scoped_solver_for_edge ssfe(this,edge);
        bool some = false;
        {
            std::vector<expr> candidates, skip;
            Node *node = edge->Parent;
            CollectConjuncts(node->Annotation.Formula,skip);
            for(unsigned i = 0; i < edge->Children.size(); i++){
                Node *child = edge->Children[i];
                if(child->map == node->map){
                    CollectConjuncts(child->Annotation.Formula,candidates);
                    break;
                }
            }
            if(candidates.empty()) goto done;
            hash_set<ast> skip_set;
            std::copy(skip.begin(),skip.end(),std::inserter(skip_set,skip_set.begin()));
            std::vector<expr> new_candidates;
            for(unsigned i = 0; i < candidates.size(); i++)
                if(skip_set.find(candidates[i]) == skip_set.end())
                    new_candidates.push_back(candidates[i]);
            candidates.swap(new_candidates);
            if(candidates.empty()) goto done;
            std::vector<expr> assumps, core, conjuncts;
            AssertEdgeCache(edge,assumps);
            for(unsigned i = 0; i < edge->Children.size(); i++){
                expr ass = GetAnnotation(edge->Children[i]);
                if(eq(ass,ctx.bool_val(true)))
                    continue;
                std::vector<expr> clauses;
                CollectConjuncts(ass.arg(1),clauses);
                for(unsigned j = 0; j < clauses.size(); j++)
                    GetAssumptionLits(ass.arg(0) || clauses[j],assumps);
            }
            for(unsigned i = 0; i < candidates.size(); i++){
                unsigned old_size = assumps.size();
                node->Annotation.Formula = candidates[i];
                expr fmla = GetAnnotation(node);
                assumps.push_back(fmla.arg(0).arg(0));
                GetAssumptionLits(!fmla.arg(1),assumps);
                std::vector<expr> full_core; 
                check_result res = CheckCore(assumps,full_core);
                if(res == unsat)
                    conjuncts.push_back(candidates[i]);
                assumps.resize(old_size);
            }
            if(conjuncts.empty())
                goto done;
            SetAnnotation(node,SimplifyAnd(conjuncts));
            some = true;
        }
    done:
        timer_stop("PropagateCache");
        return some;
    }


    /** Push a scope. Assertions made after Push can be undone by Pop. */

    void RPFP::Push()
    {
        stack.push_back(stack_entry());
        slvr_push();
    }
  
    /** Pop a scope (see Push). Note, you cannot pop axioms. */

    void RPFP::Pop(int num_scopes)
    {
        slvr_pop(num_scopes);
        for (int i = 0; i < num_scopes; i++)
            {
                stack_entry &back = stack.back();
                for(std::list<Edge *>::iterator it = back.edges.begin(), en = back.edges.end(); it != en; ++it)
                    (*it)->dual = expr(ctx,NULL);
                for(std::list<Node *>::iterator it = back.nodes.begin(), en = back.nodes.end(); it != en; ++it)
                    (*it)->dual = expr(ctx,NULL);
                for(std::list<std::pair<Edge *,Term> >::iterator it = back.constraints.begin(), en = back.constraints.end(); it != en; ++it)
                    (*it).first->constraints.pop_back();
                stack.pop_back();
            }
    }
  
    /** Erase the proof by performing a Pop, Push and re-assertion of
        all the popped constraints */

    void RPFP::PopPush(){
        slvr_pop(1);
        slvr_push();
        stack_entry &back = stack.back();
        for(std::list<Edge *>::iterator it = back.edges.begin(), en = back.edges.end(); it != en; ++it)
            slvr_add((*it)->dual);
        for(std::list<Node *>::iterator it = back.nodes.begin(), en = back.nodes.end(); it != en; ++it)
            slvr_add((*it)->dual);
        for(std::list<std::pair<Edge *,Term> >::iterator it = back.constraints.begin(), en = back.constraints.end(); it != en; ++it)
            slvr_add((*it).second);
    }
  
  
  
    // This returns a new FuncDel with same sort as top-level function
    // of term t, but with numeric suffix appended to name.

    Z3User::FuncDecl Z3User::SuffixFuncDecl(Term t, int n)
    {
        std::string name = t.decl().name().str() + "_" + string_of_int(n);
        std::vector<sort> sorts;
        int nargs = t.num_args();
        for(int i = 0; i < nargs; i++)
            sorts.push_back(t.arg(i).get_sort());
        return ctx.function(name.c_str(), nargs, VEC2PTR(sorts), t.get_sort());
    }

    Z3User::FuncDecl Z3User::RenumberPred(const FuncDecl &f, int n)
    {
        std::string name = f.name().str();
        name = name.substr(0,name.rfind('_')) + "_" + string_of_int(n);
        int arity = f.arity();
        std::vector<sort> domain;
        for(int i = 0; i < arity; i++)
        domain.push_back(f.domain(i));
        return ctx.function(name.c_str(), arity, VEC2PTR(domain), f.range());
    }

    Z3User::FuncDecl Z3User::NumberPred(const FuncDecl &f, int n)
    {
        std::string name = f.name().str();
        name = name + "_" + string_of_int(n);
        int arity = f.arity();
        std::vector<sort> domain;
        for(int i = 0; i < arity; i++)
        domain.push_back(f.domain(i));
        return ctx.function(name.c_str(), arity, VEC2PTR(domain), f.range());
    }

    // Scan the clause body for occurrences of the predicate unknowns

    RPFP::Term RPFP::ScanBody(hash_map<ast,Term> &memo, 
                              const Term &t,
                              hash_map<func_decl,Node *> &pmap,
                              std::vector<func_decl> &parms,
                              std::vector<Node *> &nodes)
    {
        if(memo.find(t) != memo.end())
            return memo[t];
        Term res(ctx);
        if (t.is_app()) {
            func_decl f = t.decl();
            if(pmap.find(f) != pmap.end()){
                nodes.push_back(pmap[f]);
                f = SuffixFuncDecl(t,parms.size());
                parms.push_back(f);
            }
            int nargs = t.num_args();
            std::vector<Term> args;
            for(int i = 0; i < nargs; i++)
                args.push_back(ScanBody(memo,t.arg(i),pmap,parms,nodes));
            res = f(nargs, VEC2PTR(args));
        }
        else if (t.is_quantifier())
            res = CloneQuantifier(t,ScanBody(memo,t.body(),pmap,parms,nodes));
        else
            res = t;
        memo[t] = res;
        return res;
    }

    // return the func_del of an app if it is uninterpreted

    bool Z3User::get_relation(const Term &t, func_decl &R){
        if(!t.is_app())
            return false;
        R = t.decl();
        return R.get_decl_kind() == Uninterpreted;
    }

    // return true if term is an individual variable
    // TODO: have to check that it is not a background symbol

    bool Z3User::is_variable(const Term &t){
        if(!t.is_app())
            return t.is_var();
        return t.decl().get_decl_kind() == Uninterpreted
            && t.num_args() == 0;
    }

    RPFP::Term RPFP::RemoveLabelsRec(hash_map<ast,Term> &memo, const Term &t, 
                                     std::vector<label_struct > &lbls){
        if(memo.find(t) != memo.end())
            return memo[t];
        Term res(ctx);
        if (t.is_app()){
            func_decl f = t.decl();
            std::vector<symbol> names;
            bool pos;
            if(t.is_label(pos,names)){
                res = RemoveLabelsRec(memo,t.arg(0),lbls);
                for(unsigned i = 0; i < names.size(); i++)
                    lbls.push_back(label_struct(names[i],res,pos));
            }
            else {
                int nargs = t.num_args();
                std::vector<Term> args;
                for(int i = 0; i < nargs; i++)
                    args.push_back(RemoveLabelsRec(memo,t.arg(i),lbls));
                res = f(nargs, VEC2PTR(args));
            }
        }
        else if (t.is_quantifier())
            res = CloneQuantifier(t,RemoveLabelsRec(memo,t.body(),lbls));
        else
            res = t;
        memo[t] = res;
        return res;
    }

    RPFP::Term RPFP::RemoveLabels(const Term &t, std::vector<label_struct > &lbls){
        hash_map<ast,Term> memo ;
        return RemoveLabelsRec(memo,t,lbls);
    }

    RPFP::Term RPFP::SubstBoundRec(hash_map<int,hash_map<ast,Term> > &memo, hash_map<int,Term> &subst, int level, const Term &t)
    {
        std::pair<ast,Term> foo(t,expr(ctx));
        std::pair<hash_map<ast,Term>::iterator, bool> bar = memo[level].insert(foo);
        Term &res = bar.first->second;
        if(!bar.second) return res;
        if (t.is_app())
            {
                func_decl f = t.decl();
                std::vector<Term> args;
                int nargs = t.num_args();
                if(nargs == 0 && f.get_decl_kind() == Uninterpreted)
                    ls->declare_constant(f);  // keep track of background constants
                for(int i = 0; i < nargs; i++)
                    args.push_back(SubstBoundRec(memo, subst, level, t.arg(i)));
                res = f(args.size(), VEC2PTR(args));
            }
        else if (t.is_quantifier()){
            int bound = t.get_quantifier_num_bound();
            std::vector<expr> pats;
            t.get_patterns(pats);
            for(unsigned i = 0; i < pats.size(); i++)
                pats[i] = SubstBoundRec(memo, subst, level + bound, pats[i]);
            res = clone_quantifier(t, SubstBoundRec(memo, subst, level + bound, t.body()), pats);
        }
        else if (t.is_var()) {
            int idx = t.get_index_value();
            if(idx >= level && subst.find(idx-level) != subst.end()){
                res = subst[idx-level];
            }
            else res = t;
        }
        else res = t;
        return res;
    }

    RPFP::Term RPFP::SubstBound(hash_map<int,Term> &subst, const Term &t){
        hash_map<int,hash_map<ast,Term> > memo;
        return SubstBoundRec(memo, subst, 0, t);
    }

    // Eliminate the deBruijn indices from level to level+num-1
    Z3User::Term Z3User::DeleteBoundRec(hash_map<int,hash_map<ast,Term> > &memo, int level, int num, const Term &t)
    {
        std::pair<ast,Term> foo(t,expr(ctx));
        std::pair<hash_map<ast,Term>::iterator, bool> bar = memo[level].insert(foo);
        Term &res = bar.first->second;
        if(!bar.second) return res;
        if (t.is_app())
            {
                func_decl f = t.decl();
                std::vector<Term> args;
                int nargs = t.num_args();
                for(int i = 0; i < nargs; i++)
                    args.push_back(DeleteBoundRec(memo, level, num, t.arg(i)));
                res = f(args.size(), VEC2PTR(args));
            }
        else if (t.is_quantifier()){
            int bound = t.get_quantifier_num_bound();
            std::vector<expr> pats;
            t.get_patterns(pats);
            for(unsigned i = 0; i < pats.size(); i++)
                pats[i] = DeleteBoundRec(memo, level + bound, num, pats[i]);
            res = clone_quantifier(t, DeleteBoundRec(memo, level + bound, num, t.body()), pats);
        }
        else if (t.is_var()) {
            int idx = t.get_index_value();
            if(idx >= level){
                res = ctx.make_var(idx-num,t.get_sort());
            }
            else res = t;
        }
        else res = t;
        return res;
    }
  
    Z3User::Term Z3User::DeleteBound(int level, int num, const Term &t){
        hash_map<int,hash_map<ast,Term> > memo;
        return DeleteBoundRec(memo, level, num, t);
    }

    int Z3User::MaxIndex(hash_map<ast,int> &memo, const Term &t)
    {
        std::pair<ast,int> foo(t,-1);
        std::pair<hash_map<ast,int>::iterator, bool> bar = memo.insert(foo);
        int &res = bar.first->second;
        if(!bar.second) return res;
        if (t.is_app()){
            func_decl f = t.decl();
            int nargs = t.num_args();
            for(int i = 0; i < nargs; i++){
                int m = MaxIndex(memo, t.arg(i));
                if(m > res)
                    res = m;
            }
        }
        else if (t.is_quantifier()){
            int bound = t.get_quantifier_num_bound();
            res = MaxIndex(memo,t.body()) - bound;
        }
        else if (t.is_var()) {
            res = t.get_index_value();
        }
        return res;
    }

    bool Z3User::IsClosedFormula(const Term &t){
        hash_map<ast,int> memo;
        return MaxIndex(memo,t) < 0;
    }
  

    /** Convert a collection of clauses to Nodes and Edges in the RPFP.

        Predicate unknowns are uninterpreted predicates not
        occurring in the background theory.
            
        Clauses are of the form 
              
        B => P(t_1,...,t_k)

        where P is a predicate unknown and predicate unknowns
        occur only positivey in H and only under existential
        quantifiers in prenex form.

        Each predicate unknown maps to a node. Each clause maps to
        an edge. Let C be a clause B => P(t_1,...,t_k) where the
        sequence of predicate unknowns occurring in B (in order
        of occurrence) is P_1..P_n. The clause maps to a transformer
        T where:

        T.Relparams = P_1..P_n
        T.Indparams = x_1...x+k
        T.Formula = B /\ t_1 = x_1 /\ ... /\ t_k = x_k

        Throws exception bad_clause(msg,i) if a clause i is
        in the wrong form.

    */

                
    static bool canonical_clause(const expr &clause){
        if(clause.decl().get_decl_kind() != Implies)
            return false;
        expr arg = clause.arg(1);
        return arg.is_app() && (arg.decl().get_decl_kind() == False ||
                                arg.decl().get_decl_kind() == Uninterpreted);
    }

#define USE_QE_LITE

    void RPFP::FromClauses(const std::vector<Term> &unskolemized_clauses, const std::vector<unsigned> *bounds){
        hash_map<func_decl,Node *> pmap;
        func_decl fail_pred = ctx.fresh_func_decl("@Fail", ctx.bool_sort());
    
        std::vector<expr> clauses(unskolemized_clauses);
        // first, skolemize the clauses

#ifndef USE_QE_LITE
        for(unsigned i = 0; i < clauses.size(); i++){
            expr &t = clauses[i];
            if (t.is_quantifier() && t.is_quantifier_forall()) {
                int bound = t.get_quantifier_num_bound();
                std::vector<sort> sorts;
                std::vector<symbol> names;
                hash_map<int,expr> subst;
                for(int j = 0; j < bound; j++){
                    sort the_sort = t.get_quantifier_bound_sort(j);
                    symbol name = t.get_quantifier_bound_name(j);
                    expr skolem = ctx.constant(symbol(ctx,name),sort(ctx,the_sort));
                    subst[bound-1-j] = skolem;
                }
                t = SubstBound(subst,t.body());
            }
        }    
#else
        std::vector<hash_map<int,expr> > substs(clauses.size());
#endif

        // create the nodes from the heads of the clauses

        for(unsigned i = 0; i < clauses.size(); i++){
            Term &clause = clauses[i];

#ifdef USE_QE_LITE
            Term &t = clause;
            if (t.is_quantifier() && t.is_quantifier_forall()) {
                int bound = t.get_quantifier_num_bound();
                std::vector<sort> sorts;
                std::vector<symbol> names;
                for(int j = 0; j < bound; j++){
                    sort the_sort = t.get_quantifier_bound_sort(j);
                    symbol name = t.get_quantifier_bound_name(j);
                    expr skolem = ctx.constant(symbol(ctx,name),sort(ctx,the_sort));
                    substs[i][bound-1-j] = skolem;
                }
                clause = t.body();
            }
      
#endif
      
            if(clause.is_app() && clause.decl().get_decl_kind() == Uninterpreted)
                clause = implies(ctx.bool_val(true),clause);
            if(!canonical_clause(clause))
                clause = implies((!clause).simplify(),ctx.bool_val(false));
            Term head = clause.arg(1);
            func_decl R(ctx);
            bool is_query = false;
            if (eq(head,ctx.bool_val(false))){
                R = fail_pred;
                // R = ctx.constant("@Fail", ctx.bool_sort()).decl();
                is_query = true;
            }
            else if(!get_relation(head,R))
                throw bad_clause("rhs must be a predicate application",i);
            if(pmap.find(R) == pmap.end()){

                // If the node doesn't exitst, create it. The Indparams
                // are arbitrary, but we use the rhs arguments if they
                // are variables for mnomonic value.

                hash_set<ast> seen;
                std::vector<Term> Indparams;
                for(unsigned j = 0; j < head.num_args(); j++){
                    Term arg = head.arg(j);
                    if(!is_variable(arg) || seen.find(arg) != seen.end()){
                        std::string name = std::string("@a_") + string_of_int(j);
                        arg = ctx.constant(name.c_str(),arg.get_sort());
                    }
                    seen.insert(arg);
                    Indparams.push_back(arg);
                }
#ifdef USE_QE_LITE
                {
                    hash_map<int,hash_map<ast,Term> > sb_memo;
                    for(unsigned j = 0; j < Indparams.size(); j++)
                        Indparams[j] = SubstBoundRec(sb_memo, substs[i], 0, Indparams[j]);
                }
#endif
                Node *node = CreateNode(R(Indparams.size(),VEC2PTR(Indparams)));
                //nodes.push_back(node);
                pmap[R] = node;
                if (is_query)
                    node->Bound = CreateRelation(std::vector<Term>(), ctx.bool_val(false));
                node->recursion_bound = bounds ? 0 : UINT_MAX;
            }
        }

        bool some_labels = false;

        // create the edges

        for(unsigned i = 0; i < clauses.size(); i++){
            Term clause = clauses[i];
            Term body = clause.arg(0);
            Term head = clause.arg(1);
            func_decl R(ctx);
            if (eq(head,ctx.bool_val(false)))
                R = fail_pred;
            //R = ctx.constant("@Fail", ctx.bool_sort()).decl();
            else get_relation(head,R);
            Node *Parent = pmap[R];
            std::vector<Term> Indparams;
            hash_set<ast> seen;
            for(unsigned j = 0; j < head.num_args(); j++){
                Term arg = head.arg(j);
                if(!is_variable(arg) || seen.find(arg) != seen.end()){
                    std::string name = std::string("@a_") + string_of_int(j);
                    Term var = ctx.constant(name.c_str(),arg.get_sort());
                    body = body && (arg == var);
                    arg = var;
                }
                seen.insert(arg);
                Indparams.push_back(arg);
            }

            // We extract the relparams positionally

            std::vector<func_decl> Relparams;
            hash_map<ast,Term> scan_memo;
            std::vector<Node *> Children;
            body = ScanBody(scan_memo,body,pmap,Relparams,Children);
            Term labeled = body;
            std::vector<label_struct > lbls;  // TODO: throw this away for now
            body = RemoveLabels(body,lbls);
            if(!eq(labeled,body))
                some_labels = true; // remember if there are labels, as we then can't do qe_lite
            // body = IneqToEq(body); // UFO converts x=y to (x<=y & x >= y). Undo this.
            body = body.simplify();

#ifdef USE_QE_LITE
            std::set<int> idxs;
            if(!some_labels){ // can't do qe_lite if we have to reconstruct labels
                for(unsigned j = 0; j < Indparams.size(); j++)
                    if(Indparams[j].is_var())
                        idxs.insert(Indparams[j].get_index_value());
                body = body.qe_lite(idxs,false);
            }
            hash_map<int,hash_map<ast,Term> > sb_memo;
            body = SubstBoundRec(sb_memo,substs[i],0,body);
            if(some_labels)
                labeled = SubstBoundRec(sb_memo,substs[i],0,labeled);
            for(unsigned j = 0; j < Indparams.size(); j++)
                Indparams[j] = SubstBoundRec(sb_memo, substs[i], 0, Indparams[j]);
#endif

            // Create the edge
            Transformer T = CreateTransformer(Relparams,Indparams,body);
            Edge *edge = CreateEdge(Parent,T,Children);
            edge->labeled = labeled;; // remember for label extraction
            if(bounds)
                Parent->recursion_bound = std::max(Parent->recursion_bound,(*bounds)[i]);
            // edges.push_back(edge);
        }

        // undo hoisting of expressions out of loops
        RemoveDeadNodes();
        Unhoist();
        // FuseEdges();
    }


    // The following mess is used to undo hoisting of expressions outside loops by compilers
  
    expr RPFP::UnhoistPullRec(hash_map<ast,expr> & memo, const expr &w, hash_map<ast,expr> & init_defs, hash_map<ast,expr> & const_params, hash_map<ast,expr> &const_params_inv, std::vector<expr> &new_params){
        if(memo.find(w) != memo.end())
            return memo[w];
        expr res;
        if(init_defs.find(w) != init_defs.end()){
            expr d = init_defs[w];
            std::vector<expr> vars;
            hash_set<ast> get_vars_memo;
            GetVarsRec(get_vars_memo,d,vars);
            hash_map<ast,expr> map;
            for(unsigned j = 0; j < vars.size(); j++){
                expr x = vars[j];
                map[x] = UnhoistPullRec(memo,x,init_defs,const_params,const_params_inv,new_params);
            }
            expr defn = SubstRec(map,d);
            res = defn;
        }
        else if(const_params_inv.find(w) == const_params_inv.end()){
            std::string old_name = w.decl().name().str();
            func_decl fresh = ctx.fresh_func_decl(old_name.c_str(), w.get_sort());
            expr y = fresh();
            const_params[y] = w;
            const_params_inv[w] = y;
            new_params.push_back(y);
            res = y;
        }
        else
            res = const_params_inv[w];
        memo[w] = res;
        return res;
    }

    void RPFP::AddParamsToTransformer(Transformer &trans, const std::vector<expr> &params){
        std::copy(params.begin(),params.end(),std::inserter(trans.IndParams,trans.IndParams.end()));
    }

    expr RPFP::AddParamsToApp(const expr &app, const func_decl &new_decl, const std::vector<expr> &params){
        int n = app.num_args();
        std::vector<expr> args(n);
        for (int i = 0; i < n; i++)
            args[i] = app.arg(i);
        std::copy(params.begin(),params.end(),std::inserter(args,args.end()));
        return new_decl(args);
    }

    expr RPFP::GetRelRec(hash_set<ast> &memo, const expr &t, const func_decl &rel){
        if(memo.find(t) != memo.end())
            return expr();
        memo.insert(t);
        if (t.is_app())
            {
                func_decl f = t.decl();
                if(f == rel)
                    return t;
                int nargs = t.num_args();
                for(int i = 0; i < nargs; i++){
                    expr res = GetRelRec(memo,t.arg(i),rel);
                    if(!res.null())
                        return res;
                }
            }
        else if (t.is_quantifier())
            return GetRelRec(memo,t.body(),rel);
        return expr();
    }

    expr RPFP::GetRel(Edge *edge, int child_idx){
        func_decl &rel = edge->F.RelParams[child_idx];
        hash_set<ast> memo;
        return GetRelRec(memo,edge->F.Formula,rel);
    }

    void RPFP::GetDefsRec(const expr &cnst, hash_map<ast,expr> &defs){
        if(cnst.is_app()){
            switch(cnst.decl().get_decl_kind()){
            case And: {
                int n = cnst.num_args();
                for(int i = 0; i < n; i++)
                    GetDefsRec(cnst.arg(i),defs);
                break;
            }
            case Equal: {
                expr lhs = cnst.arg(0);
                expr rhs = cnst.arg(1);
                if(IsVar(lhs))
                    defs[lhs] = rhs;
                break;
            }
            default:
                break;
            }
        }
    }
  
    void RPFP::GetDefs(const expr &cnst, hash_map<ast,expr> &defs){
        // GetDefsRec(IneqToEq(cnst),defs);
        GetDefsRec(cnst,defs);
    }

    bool RPFP::IsVar(const expr &t){
        return t.is_app() && t.num_args() == 0 && t.decl().get_decl_kind() == Uninterpreted;
    }

    void RPFP::GetVarsRec(hash_set<ast> &memo, const expr &t, std::vector<expr> &vars){
        if(memo.find(t) != memo.end())
            return;
        memo.insert(t);
        if (t.is_app())
            {
                if(IsVar(t)){
                    vars.push_back(t);
                    return;
                }
                int nargs = t.num_args();
                for(int i = 0; i < nargs; i++){
                    GetVarsRec(memo,t.arg(i),vars);
                }
            }
        else if (t.is_quantifier())
            GetVarsRec(memo,t.body(),vars);
    }

    void RPFP::AddParamsToNode(Node *node, const std::vector<expr> &params){
        int arity = node->Annotation.IndParams.size();
        std::vector<sort> domain;
        for(int i = 0; i < arity; i++)
            domain.push_back(node->Annotation.IndParams[i].get_sort());
        for(unsigned i = 0; i < params.size(); i++)
            domain.push_back(params[i].get_sort());
        std::string old_name = node->Name.name().str();
        func_decl fresh = ctx.fresh_func_decl(old_name.c_str(), domain, ctx.bool_sort());
        node->Name = fresh;
        AddParamsToTransformer(node->Annotation,params);
        AddParamsToTransformer(node->Bound,params);
        AddParamsToTransformer(node->Underapprox,params);
    }

    void RPFP::UnhoistLoop(Edge *loop_edge, Edge *init_edge){
        loop_edge->F.Formula = IneqToEq(loop_edge->F.Formula);
        init_edge->F.Formula = IneqToEq(init_edge->F.Formula);
        expr pre = GetRel(loop_edge,0);
        if(pre.null())
            return; // this means the loop got simplified away
        int nparams = loop_edge->F.IndParams.size();
        hash_map<ast,expr> const_params, const_params_inv;
        std::vector<expr> work_list;
        // find the parameters that are constant in the loop
        for(int i = 0; i < nparams; i++){
            if(eq(pre.arg(i),loop_edge->F.IndParams[i])){
                const_params[pre.arg(i)] = init_edge->F.IndParams[i];
                const_params_inv[init_edge->F.IndParams[i]] = pre.arg(i);
                work_list.push_back(pre.arg(i));
            }
        }
        // get the definitions in the initialization
        hash_map<ast,expr> defs,memo,subst;
        GetDefs(init_edge->F.Formula,defs);
        // try to pull them inside the loop
        std::vector<expr> new_params;
        for(unsigned i = 0; i < work_list.size(); i++){
            expr v = work_list[i];
            expr w = const_params[v];
            expr def = UnhoistPullRec(memo,w,defs,const_params,const_params_inv,new_params);
            if(!eq(def,v))
                subst[v] = def;
        }
        // do the substitutions
        if(subst.empty())
            return;
        subst[pre] = pre; // don't substitute inside the precondition itself
        loop_edge->F.Formula = SubstRec(subst,loop_edge->F.Formula);
        loop_edge->F.Formula = ElimIte(loop_edge->F.Formula);
        init_edge->F.Formula = ElimIte(init_edge->F.Formula);
        // add the new parameters
        if(new_params.empty())
            return;
        Node *parent = loop_edge->Parent;
        AddParamsToNode(parent,new_params);
        AddParamsToTransformer(loop_edge->F,new_params);
        AddParamsToTransformer(init_edge->F,new_params);
        std::vector<Edge *> &incoming = parent->Incoming;
        for(unsigned i = 0; i < incoming.size(); i++){
            Edge *in_edge = incoming[i];
            std::vector<Node *> &chs = in_edge->Children;
            for(unsigned j = 0; j < chs.size(); j++)
                if(chs[j] == parent){
                    expr lit = GetRel(in_edge,j);
                    expr new_lit = AddParamsToApp(lit,parent->Name,new_params);
                    func_decl fd = SuffixFuncDecl(new_lit,j);
                    int nargs = new_lit.num_args();
                    std::vector<Term> args;
                    for(int k = 0; k < nargs; k++)
                        args.push_back(new_lit.arg(k));
                    new_lit = fd(nargs, VEC2PTR(args));
                    in_edge->F.RelParams[j] = fd;
                    hash_map<ast,expr> map;
                    map[lit] = new_lit;
                    in_edge->F.Formula = SubstRec(map,in_edge->F.Formula);
                }
        }
    }

    void RPFP::Unhoist(){
        hash_map<Node *,std::vector<Edge *> > outgoing;
        for(unsigned i = 0; i < edges.size(); i++)
            outgoing[edges[i]->Parent].push_back(edges[i]);
        for(unsigned i = 0; i < nodes.size(); i++){
            Node *node = nodes[i];
            std::vector<Edge *> &outs = outgoing[node];
            // if we're not a simple loop with one entry, give up
            if(outs.size() == 2){
                for(int j = 0; j < 2; j++){
                    Edge *loop_edge = outs[j];
                    Edge *init_edge = outs[1-j];
                    if(loop_edge->Children.size() == 1 && loop_edge->Children[0] == loop_edge->Parent){
                        UnhoistLoop(loop_edge,init_edge);
                        break;
                    }
                }
            }
        }
    }

    void RPFP::FuseEdges(){
        hash_map<Node *,std::vector<Edge *> > outgoing;
        for(unsigned i = 0; i < edges.size(); i++){
            outgoing[edges[i]->Parent].push_back(edges[i]);
        }
        hash_set<Edge *> edges_to_delete;
        for(unsigned i = 0; i < nodes.size(); i++){
            Node *node = nodes[i];
            std::vector<Edge *> &outs = outgoing[node];
            if(outs.size() > 1 && outs.size() <= 16){
                std::vector<Transformer *> trs(outs.size());
                for(unsigned j = 0; j < outs.size(); j++)
                    trs[j] = &outs[j]->F;
                Transformer tr = Fuse(trs);
                std::vector<Node *> chs;
                for(unsigned j = 0; j < outs.size(); j++)
                    for(unsigned k = 0; k < outs[j]->Children.size(); k++)
                        chs.push_back(outs[j]->Children[k]);
                CreateEdge(node,tr,chs);
                for(unsigned j = 0; j < outs.size(); j++)
                    edges_to_delete.insert(outs[j]);
            }
        }
        std::vector<Edge *> new_edges;
        hash_set<Node *> all_nodes;
        for(unsigned j = 0; j < edges.size(); j++){
            if(edges_to_delete.find(edges[j]) == edges_to_delete.end()){
#if 0
                if(all_nodes.find(edges[j]->Parent) != all_nodes.end())
                    throw "help!";
                all_nodes.insert(edges[j]->Parent);
#endif
                new_edges.push_back(edges[j]);
            }
            else
                delete edges[j];
        }
        edges.swap(new_edges);
    }

    void RPFP::MarkLiveNodes(hash_map<Node *,std::vector<Edge *> > &outgoing, hash_set<Node *> &live_nodes, Node *node){
        if(live_nodes.find(node) != live_nodes.end())
            return;
        live_nodes.insert(node);
        std::vector<Edge *> &outs = outgoing[node];
        for(unsigned i = 0; i < outs.size(); i++)
            for(unsigned j = 0; j < outs[i]->Children.size(); j++)
                MarkLiveNodes(outgoing, live_nodes,outs[i]->Children[j]);
    }

    void RPFP::RemoveDeadNodes(){
        hash_map<Node *,std::vector<Edge *> > outgoing;
        for(unsigned i = 0; i < edges.size(); i++)
            outgoing[edges[i]->Parent].push_back(edges[i]);
        hash_set<Node *> live_nodes;
        for(unsigned i = 0; i < nodes.size(); i++)
            if(!nodes[i]->Bound.IsFull())
                MarkLiveNodes(outgoing,live_nodes,nodes[i]);
        std::vector<Edge *> new_edges;
        for(unsigned j = 0; j < edges.size(); j++){
            if(live_nodes.find(edges[j]->Parent) != live_nodes.end())
                new_edges.push_back(edges[j]);
            else {
                Edge *edge = edges[j];
                for(unsigned int i = 0; i < edge->Children.size(); i++){
                    std::vector<Edge *> &ic = edge->Children[i]->Incoming;
                    for(std::vector<Edge *>::iterator it = ic.begin(), en = ic.end(); it != en; ++it){
                        if(*it == edge){
                            ic.erase(it);
                            break;
                        }
                    }
                }
                delete edge;
            }
        }
        edges.swap(new_edges);
        std::vector<Node *> new_nodes;
        for(unsigned j = 0; j < nodes.size(); j++){
            if(live_nodes.find(nodes[j]) != live_nodes.end())
                new_nodes.push_back(nodes[j]);
            else
                delete nodes[j];
        }
        nodes.swap(new_nodes);
    }

    void RPFP::WriteSolution(std::ostream &s){
        for(unsigned i = 0; i < nodes.size(); i++){
            Node *node = nodes[i];
            Term asgn = (node->Name)(node->Annotation.IndParams) == node->Annotation.Formula;
            s << asgn << std::endl;
        }
    }
  
    void RPFP::WriteEdgeVars(Edge *e,  hash_map<ast,int> &memo, const Term &t, std::ostream &s)
    {
        std::pair<ast,int> foo(t,0);
        std::pair<hash_map<ast,int>::iterator, bool> bar = memo.insert(foo);
        // int &res = bar.first->second;
        if(!bar.second) return;
        hash_map<ast,Term>::iterator it = e->varMap.find(t);
        if (it != e->varMap.end()){
            return;
        }
        if (t.is_app())
            {
                func_decl f = t.decl();
                // int idx;
                int nargs = t.num_args();
                for(int i = 0; i < nargs; i++)
                    WriteEdgeVars(e, memo, t.arg(i),s);
                if (nargs == 0 && f.get_decl_kind() == Uninterpreted && !ls->is_constant(f)){
                    Term rename = HideVariable(t,e->number);
                    Term value = dualModel.eval(rename);
                    s << " (= " << t << " " << value << ")\n";
                }
            }
        else if (t.is_quantifier())
            WriteEdgeVars(e,memo,t.body(),s);
        return;
    }

    void RPFP::WriteEdgeAssignment(std::ostream &s, Edge *e){
        s << "(\n";
        hash_map<ast, int> memo;
        WriteEdgeVars(e, memo, e->F.Formula ,s);
        s << ")\n";
    }

    void RPFP::WriteCounterexample(std::ostream &s, Node *node){
        for(unsigned i = 0; i < node->Outgoing->Children.size(); i++){
            Node *child = node->Outgoing->Children[i];
            if(!Empty(child))
                WriteCounterexample(s,child);
        }
        s << "(" << node->number << " : " << EvalNode(node) << " <- ";
        for(unsigned i = 0; i < node->Outgoing->Children.size(); i++){
            Node *child = node->Outgoing->Children[i];
            if(!Empty(child))
                s << " " << node->Outgoing->Children[i]->number;
        }
        s << ")" << std::endl;
        WriteEdgeAssignment(s,node->Outgoing);
    }

    RPFP::Term RPFP::ToRuleRec(Edge *e,  hash_map<ast,Term> &memo, const Term &t, std::vector<expr> &quants)
    {
        std::pair<ast,Term> foo(t,expr(ctx));
        std::pair<hash_map<ast,Term>::iterator, bool> bar = memo.insert(foo);
        Term &res = bar.first->second;
        if(!bar.second) return res;
        if (t.is_app())
            {
                func_decl f = t.decl();
                // int idx;
                std::vector<Term> args;
                int nargs = t.num_args();
                for(int i = 0; i < nargs; i++)
                    args.push_back(ToRuleRec(e, memo, t.arg(i),quants));
                hash_map<func_decl,int>::iterator rit = e->relMap.find(f);                 
                if(rit != e->relMap.end()){
                    Node* child = e->Children[rit->second];
                    FuncDecl op = child->Name;
                    res = op(args.size(), VEC2PTR(args));
                }
                else {
                    res = f(args.size(), VEC2PTR(args));
                    if(nargs == 0 && t.decl().get_decl_kind() == Uninterpreted)
                        quants.push_back(t);
                }
            }
        else if (t.is_quantifier())
            {
                Term body = ToRuleRec(e,memo,t.body(),quants);
                res = CloneQuantifier(t,body);
            }
        else res = t;
        return res;
    }

  
    void RPFP::ToClauses(std::vector<Term> &cnsts, FileFormat format){
        cnsts.resize(edges.size());
        for(unsigned i = 0; i < edges.size(); i++){
            Edge *edge = edges[i];
            SetEdgeMaps(edge);
            std::vector<expr> quants;
            hash_map<ast,Term> memo;
            Term lhs = ToRuleRec(edge, memo, edge->F.Formula,quants);
            Term rhs = (edge->Parent->Name)(edge->F.IndParams.size(),&edge->F.IndParams[0]);
            for(unsigned j = 0; j < edge->F.IndParams.size(); j++)
                ToRuleRec(edge,memo,edge->F.IndParams[j],quants); // just to get quants
            Term cnst = implies(lhs,rhs);
#if 0
            for(unsigned i = 0; i < quants.size(); i++){
                std::cout << expr(ctx,(Z3_ast)quants[i]) << " : " << sort(ctx,Z3_get_sort(ctx,(Z3_ast)quants[i])) << std::endl;
            }
#endif
            if(format != DualityFormat)
                cnst= forall(quants,cnst);
            cnsts[i] = cnst;
        }
        // int num_rules = cnsts.size();
    
        for(unsigned i = 0; i < nodes.size(); i++){
            Node *node = nodes[i];
            if(!node->Bound.IsFull()){
                Term lhs = (node->Name)(node->Bound.IndParams) && !node->Bound.Formula;
                Term cnst = implies(lhs,ctx.bool_val(false));
                if(format != DualityFormat){
                    std::vector<expr> quants;
                    for(unsigned j = 0; j < node->Bound.IndParams.size(); j++)
                        quants.push_back(node->Bound.IndParams[j]);
                    if(format == HornFormat)
                        cnst= exists(quants,!cnst);
                    else
                        cnst= forall(quants, cnst);
                }
                cnsts.push_back(cnst);
            }
        }
    
    }


    bool RPFP::proof_core_contains(const expr &e){
        return proof_core->find(e) != proof_core->end();
    }

    bool RPFP_caching::proof_core_contains(const expr &e){
        std::vector<expr> foo;
        GetAssumptionLits(e,foo);
        for(unsigned i = 0; i < foo.size(); i++)
            if(proof_core->find(foo[i]) != proof_core->end())
                return true;
        return false;
    }

    bool RPFP::EdgeUsedInProof(Edge *edge){
        ComputeProofCore();
        if(!edge->dual.null() && proof_core_contains(edge->dual))
            return true;
        for(unsigned i = 0; i < edge->constraints.size(); i++)
            if(proof_core_contains(edge->constraints[i]))
                return true;
        return false;
    }

    RPFP::~RPFP(){
        ClearProofCore();
        for(unsigned i = 0; i < nodes.size(); i++)
            delete nodes[i];
        for(unsigned i = 0; i < edges.size(); i++)
            delete edges[i];
    }
}

#if 0
void show_ast(expr *a){
    std::cout << *a;
}
#endif
