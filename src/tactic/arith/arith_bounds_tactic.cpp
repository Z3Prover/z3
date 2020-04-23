
/*++
Copyright (c) 2015 Microsoft Corporation

--*/



#include "tactic/arith/arith_bounds_tactic.h"
#include "ast/arith_decl_plugin.h"

struct arith_bounds_tactic : public tactic {

    ast_manager& m;
    arith_util   a;

    arith_bounds_tactic(ast_manager& m):
        m(m),
        a(m)
    {
    }        

    ast_manager& get_manager() { return m; }


    void operator()(/* in */  goal_ref const & in, 
                    /* out */ goal_ref_buffer & result) override {        
        bounds_arith_subsumption(in, result);
    }
    
    tactic* translate(ast_manager & mgr) override {
        return alloc(arith_bounds_tactic, mgr);
    }
    
    void checkpoint() {
        tactic::checkpoint(m);
    }
    
    
    struct info { rational r; unsigned idx; bool is_strict;};
    
    /**
       \brief Basic arithmetic subsumption simplification based on bounds.
    */
    
    void mk_proof(proof_ref& pr, goal_ref const& s, unsigned i, unsigned j) {
        if (s->proofs_enabled()) {
            proof* th_lemma = m.mk_th_lemma(a.get_family_id(), m.mk_implies(s->form(i), s->form(j)), 0, nullptr);
            pr = m.mk_modus_ponens(s->pr(i), th_lemma);
        }        
    }
    
    
    bool is_le_or_lt(expr* e, expr*& e1, expr*& e2, bool& is_strict) {
        bool is_negated = m.is_not(e, e);
        if ((!is_negated && (a.is_le(e, e1, e2) || a.is_ge(e, e2, e1))) ||
            (is_negated && (a.is_lt(e, e2, e1) || a.is_gt(e, e1, e2)))) {
            is_strict = false;
            return true;
        }
        if ((!is_negated && (a.is_lt(e, e1, e2) || a.is_gt(e, e2, e1))) ||
                 (is_negated && (a.is_le(e, e2, e1) || a.is_ge(e, e1, e2)))) {
            is_strict = true;
            return true;
        }
        return false;
    }



    void bounds_arith_subsumption(goal_ref const& g, goal_ref_buffer& result) {
        info inf;
        rational r;
        goal_ref s(g); // initialize result.
        obj_map<expr, info> lower, upper;
        expr* e1, *e2;
        TRACE("arith_subsumption", s->display(tout); );
        for (unsigned i = 0; i < s->size(); ++i) {
            checkpoint();
            expr* lemma = s->form(i);
            bool is_strict  = false;
            bool is_lower   = false;
            if (!is_le_or_lt(lemma, e1, e2, is_strict)) {
                continue;
            }
            // e1 <= e2 or e1 < e2
            if (a.is_numeral(e2, r)) {
                is_lower = true;
            }
            else if (a.is_numeral(e1, r)) {
                is_lower = false;
            }
            else {
                continue;
            }
            proof_ref new_pr(m);
            
            if (is_lower && upper.find(e1, inf)) {            
                if (inf.r > r || (inf.r == r && is_strict && !inf.is_strict)) {
                    mk_proof(new_pr, s, i, inf.idx);
                    s->update(inf.idx, m.mk_true(), new_pr);
                    inf.r = r;
                    inf.is_strict = is_strict;
                    inf.idx = i;
                    upper.insert(e1, inf);
                }
                else {
                    mk_proof(new_pr, s, inf.idx, i);
                    s->update(i, m.mk_true(), new_pr);
                }
            }
            else if (is_lower) {
                inf.r = r;
                inf.is_strict = is_strict;
                inf.idx = i;
                upper.insert(e1, inf);
            }
            else if (!is_lower && lower.find(e2, inf)) {
                if (inf.r < r || (inf.r == r && is_strict && !inf.is_strict)) {
                    mk_proof(new_pr, s, i, inf.idx);
                    s->update(inf.idx, m.mk_true(), new_pr);
                    inf.r = r;
                    inf.is_strict = is_strict;
                    inf.idx = i;
                    lower.insert(e2, inf);
                }
                else {
                    mk_proof(new_pr, s, inf.idx, i);
                    s->update(i, m.mk_true());
                }
            }
            else if (!is_lower) {
                inf.r = r;
                inf.is_strict = is_strict;
                inf.idx = i;
                lower.insert(e2, inf);                
            }            
        }
        s->elim_true();
        result.push_back(s.get());
        TRACE("arith_subsumption", s->display(tout); );
    }

    void cleanup() override {}

};


tactic * mk_arith_bounds_tactic(ast_manager & m, params_ref const & p) {
    return alloc(arith_bounds_tactic, m);
}


