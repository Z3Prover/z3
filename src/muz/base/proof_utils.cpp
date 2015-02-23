#include "dl_util.h"
#include "proof_utils.h"
#include "ast_smt2_pp.h"
#include "var_subst.h"

class reduce_hypotheses {
    typedef obj_hashtable<expr> expr_set;
    ast_manager&          m;
    expr_ref_vector       m_refs;
    obj_map<proof,proof*> m_cache;
    obj_map<expr, proof*> m_units;
    ptr_vector<expr>      m_units_trail;
    unsigned_vector       m_limits;
    obj_map<proof, expr_set*> m_hypmap;
    ptr_vector<expr_set>  m_hyprefs;
    ptr_vector<expr>      m_literals;
    
    void reset() {
        m_refs.reset();
        m_cache.reset();
        m_units.reset();
        m_units_trail.reset();
        m_limits.reset();
        std::for_each(m_hyprefs.begin(), m_hyprefs.end(), delete_proc<expr_set>());
        m_hypmap.reset();
        m_hyprefs.reset();
        m_literals.reset();
    }
    
    void push() {
        m_limits.push_back(m_units_trail.size());
    }
    
    void pop() {
        unsigned sz = m_limits.back();
        while (m_units_trail.size() > sz) {
            m_units.remove(m_units_trail.back());
            m_units_trail.pop_back();
        }
        m_limits.pop_back();
    }
    
    void get_literals(expr* clause) {
        m_literals.reset();
        if (m.is_or(clause)) {
            m_literals.append(to_app(clause)->get_num_args(), to_app(clause)->get_args());                
        }
        else {
            m_literals.push_back(clause);
        }
    }
    
    void add_hypotheses(proof* p) {
        expr_set* hyps = 0;
        bool inherited = false;
        if (p->get_decl_kind() == PR_HYPOTHESIS) {
            hyps = alloc(expr_set);
            hyps->insert(m.get_fact(p));
            m_hyprefs.push_back(hyps);
        }
        else {
            for (unsigned i = 0; i < m.get_num_parents(p); ++i) {
                expr_set* hyps1 = m_hypmap.find(m.get_parent(p, i));
                if (hyps1) {
                    if (!hyps) {
                        hyps = hyps1;
                        inherited = true;
                        continue;
                    }
                    if (inherited) {
                        hyps = alloc(expr_set,*hyps);
                        m_hyprefs.push_back(hyps);
                        inherited = false;
                    }
                    datalog::set_union(*hyps, *hyps1);
                }
            }
        }
        m_hypmap.insert(p, hyps);
    }

    expr_ref complement_lit(expr* e) {
        expr* e1;
        if (m.is_not(e, e1)) {
            return expr_ref(e1, m);
        }
        else {
            return expr_ref(m.mk_not(e), m);
        }
    }
    
    bool in_hypotheses(expr* e, expr_set* hyps) {
        if (!hyps) {
            return false;
        }
        expr_ref not_e = complement_lit(e);
        return hyps->contains(not_e);
    }

    bool contains_hypothesis(proof* p) {
        ptr_vector<proof> todo;
        ast_mark visit;
        todo.push_back(p);
        while (!todo.empty()) {
            p = todo.back();
            todo.pop_back();
            if (visit.is_marked(p)) {
                continue;
            }
            visit.mark(p, true);
            if (PR_HYPOTHESIS == p->get_decl_kind()) {
                return true;
            }
            for (unsigned i = 0; i < m.get_num_parents(p); ++i) {
                todo.push_back(m.get_parent(p, i));
            }
        }
        return false;
    }

    bool is_closed(proof* p) {
        expr_set* hyps = m_hypmap.find(p);
        return !hyps || hyps->empty();
    }    
    
public:
    reduce_hypotheses(ast_manager& m): m(m), m_refs(m) {}
    
    void operator()(proof_ref& pr) {
        proof_ref tmp(m);
        tmp = pr;
        elim(pr);
        reset();
        CTRACE("proof_utils", contains_hypothesis(pr),
            tout << "Contains hypothesis:\n";
            tout << mk_ismt2_pp(tmp, m) << "\n====>\n";
            tout << mk_ismt2_pp(pr, m) << "\n";);
        
    }
    
    void elim(proof_ref& p) {
        proof_ref tmp(m);
        proof* result = p.get();
        if (m_cache.find(p, result)) {
            p = result;
            return;
        }
        switch(p->get_decl_kind()) {
        case PR_HYPOTHESIS:
            if (!m_units.find(m.get_fact(p), result)) {
                result = p.get();
            }
            add_hypotheses(result);
            break;
        case PR_LEMMA: {
            SASSERT(m.get_num_parents(p) == 1);
            tmp = m.get_parent(p, 0);
            elim(tmp);
            expr_set* hyps = m_hypmap.find(tmp);
            expr_set* new_hyps = 0;
            if (hyps) {
                new_hyps = alloc(expr_set, *hyps);
            }
            expr* fact = m.get_fact(p);
            // when hypothesis is a single literal of the form 
            // (or A B), and the fact of p is (or A B).            
            if (hyps && hyps->size() == 1 && in_hypotheses(fact, hyps)) {
                m_literals.reset();
                m_literals.push_back(fact);
            }
            else {
                get_literals(fact);
            }

            for (unsigned i = 0; i < m_literals.size(); ++i) {
                expr* e = m_literals[i];
                if (!in_hypotheses(e, hyps)) {
                    m_literals[i] = m_literals.back();
                    m_literals.pop_back();
                    --i;
                }
                else {
                    SASSERT(new_hyps);
                    expr_ref not_e = complement_lit(e);
                    SASSERT(new_hyps->contains(not_e));
                    new_hyps->remove(not_e);
                }
            }
            if (m_literals.empty()) {
                result = tmp;
            }
            else {
                expr_ref clause(m);
                if (m_literals.size() == 1) {
                    clause = m_literals[0];
                }
                else {
                    clause = m.mk_or(m_literals.size(), m_literals.c_ptr());
                }
                tmp = m.mk_lemma(tmp, clause);
                m_refs.push_back(tmp);
                result = tmp;
            }
            if (new_hyps && new_hyps->empty()) {
                dealloc(new_hyps);
                new_hyps = 0;
            }
            m_hypmap.insert(result, new_hyps);
            m_hyprefs.push_back(new_hyps);
            TRACE("proof_utils",            
                    tout << "New lemma: " << mk_pp(m.get_fact(p), m) 
                      << "\n==>\n" 
                      << mk_pp(m.get_fact(result), m) << "\n";
                if (hyps) {
                    expr_set::iterator it = hyps->begin();
                    expr_set::iterator end = hyps->end();
                    for (; it != end; ++it) {
                        tout << "Hypothesis: " << mk_pp(*it, m) << "\n";
                    }
                });                               
            
            break;
        }
        case PR_UNIT_RESOLUTION: {
            proof_ref_vector parents(m);
            parents.push_back(m.get_parent(p, 0));
            push();
            bool found_false = false;
            for (unsigned i = 1; i < m.get_num_parents(p); ++i) {
                tmp = m.get_parent(p, i);
                elim(tmp);
                if (m.is_false(m.get_fact(tmp))) {
                    result = tmp;
                    found_false = true;
                    break;
                }
                SASSERT(m.get_fact(tmp) == m.get_fact(m.get_parent(p, i)));
                parents.push_back(tmp);          
                if (is_closed(tmp) && !m_units.contains(m.get_fact(tmp))) {
                    m_units.insert(m.get_fact(tmp), tmp);
                    m_units_trail.push_back(m.get_fact(tmp));
                }
            }
            if (found_false) {
                pop();
                break;
            }
            tmp = m.get_parent(p, 0);
            expr* old_clause = m.get_fact(tmp);
            elim(tmp);
            parents[0] = tmp;
            expr* clause = m.get_fact(tmp);
            if (m.is_false(clause)) {
                m_refs.push_back(tmp);
                result = tmp;
                pop();
                break;
            }
            //
            // case where clause is a literal in the old clause.
            //
            if (is_literal_in_clause(clause, old_clause)) {
                bool found = false;
                for (unsigned i = 1; !found && i < parents.size(); ++i) {
                    if (m.is_complement(clause, m.get_fact(parents[i].get()))) {
                        parents[1] = parents[i].get();
                        parents.resize(2);
                        result = m.mk_unit_resolution(parents.size(), parents.c_ptr());
                        m_refs.push_back(result);               
                        add_hypotheses(result);
                        found = true;
                    }                    
                }
                if (!found) {
                    result = parents[0].get();
                }
                pop(); 
                break;
            }
            //
            // case where new clause is a subset of old clause.
            // the literals in clause should be a subset of literals in old_clause.
            // 
            get_literals(clause);
            for (unsigned i = 1; i < parents.size(); ++i) {
                bool found = false;
                for (unsigned j = 0; j < m_literals.size(); ++j) {
                    if (m.is_complement(m_literals[j], m.get_fact(parents[i].get()))) {
                        found = true;
                        break;
                    }
                }
                if (!found) {
                    // literal was removed as hypothesis.
                    parents[i] = parents.back();
                    parents.pop_back();
                    --i;
                }
            }
            if (parents.size() == 1) {
                result = parents[0].get();
            }
            else {
                result = m.mk_unit_resolution(parents.size(), parents.c_ptr());
                m_refs.push_back(result);               
                add_hypotheses(result);
            }
            pop();
            break;
        }                
        default: {
            ptr_buffer<expr> args;
            bool change = false;
            bool found_false = false;
            for (unsigned i = 0; i < m.get_num_parents(p); ++i) {
                tmp = m.get_parent(p, i);
                elim(tmp);
                if (m.is_false(m.get_fact(tmp))) {
                    result = tmp;
                    found_false = true;
                    break;
                }
                // SASSERT(m.get_fact(tmp) == m.get_fact(m.get_parent(p, i)));
                change = change || (tmp != m.get_parent(p, i));
                args.push_back(tmp);
            }
            if (found_false) {
                break;
            }
            if (m.has_fact(p)) {
                args.push_back(m.get_fact(p));
            }
            if (change) {
                tmp = m.mk_app(p->get_decl(), args.size(), args.c_ptr());
                m_refs.push_back(tmp);
            }
            else {
                tmp = p;
            }
            result = tmp;                
            add_hypotheses(result);
            break;
        }
        }          
        SASSERT(m_hypmap.contains(result));
        m_cache.insert(p, result);
        p = result;
    }        

    bool is_literal_in_clause(expr* fml, expr* clause) {
        if (!m.is_or(clause)) {
            return false;
        }
        app* cl = to_app(clause);
        for (unsigned i = 0; i < cl->get_num_args(); ++i) {
            if (cl->get_arg(i) == fml) {
                return true;
            }
        }
        return false;
    }
};

void proof_utils::reduce_hypotheses(proof_ref& pr) {
    ast_manager& m = pr.get_manager();
    class reduce_hypotheses reduce(m);
    reduce(pr);
    CTRACE("proof_utils", !is_closed(m, pr), tout << mk_pp(pr, m) << "\n";);
}

class proof_is_closed {
    ast_manager&     m;
    ptr_vector<expr> m_literals;
    ast_mark         m_visit;

    void reset() {
        m_literals.reset();
        m_visit.reset();
    }

    bool check(proof* p) {
        // really just a partial check because nodes may be visited 
        // already under a different lemma scope.
        if (m_visit.is_marked(p)) {
            return true;
        }
        bool result = false;
        m_visit.mark(p, true);
        switch(p->get_decl_kind()) {
        case PR_LEMMA: {
            unsigned sz = m_literals.size();
            expr* cls = m.get_fact(p);
            m_literals.push_back(cls);
            if (m.is_or(cls)) {
                m_literals.append(to_app(cls)->get_num_args(), to_app(cls)->get_args());
            }
            SASSERT(m.get_num_parents(p) == 1);
            result = check(m.get_parent(p, 0));
            m_literals.resize(sz);
            break;            
        }
        case PR_HYPOTHESIS: {
            expr* fact = m.get_fact(p);
            for (unsigned i = 0; i < m_literals.size(); ++i) {
                if (m.is_complement(m_literals[i], fact)) {
                    result = true;
                    break;
                }
            }
            break;
        }
        default: 
            result = true;
            for (unsigned i = 0; i < m.get_num_parents(p); ++i) {
                if (!check(m.get_parent(p, i))) {
                    result = false;
                    break;
                }
            }
            break;
        }
        
        return result;
    }
    
public:
    proof_is_closed(ast_manager& m): m(m) {}

    bool operator()(proof *p) {
        bool ok = check(p);
        reset();
        return ok;
    }
};

bool proof_utils::is_closed(ast_manager& m, proof* p) {
    proof_is_closed checker(m);
    return checker(p);
}


static void permute_unit_resolution(expr_ref_vector& refs, obj_map<proof,proof*>& cache, proof_ref& pr) {
    ast_manager& m = pr.get_manager();
    proof* pr2 = 0;
    proof_ref_vector parents(m);
    proof_ref prNew(pr); 
    if (cache.find(pr, pr2)) {
        pr = pr2;
        return;
    }
    
    for (unsigned i = 0; i < m.get_num_parents(pr); ++i) {
        prNew = m.get_parent(pr, i);
        permute_unit_resolution(refs, cache, prNew);
        parents.push_back(prNew);
    }
    
    prNew = pr;
    if (pr->get_decl_kind() == PR_UNIT_RESOLUTION &&
        parents[0]->get_decl_kind() == PR_TH_LEMMA) { 
        /*
          Unit resolution:
          T1:      (or l_1 ... l_n l_1' ... l_m')
          T2:      (not l_1)
          ...
          T(n+1):  (not l_n)
                   [unit-resolution T1 ... T(n+1)]: (or l_1' ... l_m')
          Th lemma:
          T1:      (not l_1)
          ...
          Tn:      (not l_n)
          [th-lemma T1 ... Tn]: (or l_{n+1} ... l_m)
                    
          Such that (or l_1 .. l_n l_{n+1} .. l_m) is a theory axiom.
                    
          Implement conversion:
                    
                 T1 |- not l_1 ... Tn |- not l_n  
                 -------------------------------  TH_LEMMA
                          (or k_1 .. k_m j_1 ... j_m)    S1 |- not k_1 ... Sm |- not k_m
                          -------------------------------------------------------------- UNIT_RESOLUTION
                                        (or j_1 .. j_m)


            |-> 

                    T1 |- not l_1 ... Tn |- not l_n S1 |- not k_1 ... Sm |- not k_m
                    ---------------------------------------------------------------- TH_LEMMA
                                        (or j_1 .. j_m)

        */
        proof_ref_vector premises(m);
        proof* thLemma = parents[0].get();
        for (unsigned i = 0; i < m.get_num_parents(thLemma); ++i) {
            premises.push_back(m.get_parent(thLemma, i));
        }
        for (unsigned i = 1; i < parents.size(); ++i) {
            premises.push_back(parents[i].get());
        }
        parameter const* params = thLemma->get_decl()->get_parameters();
        unsigned num_params = thLemma->get_decl()->get_num_parameters();
        SASSERT(params[0].is_symbol());
        family_id tid = m.mk_family_id(params[0].get_symbol());
        SASSERT(tid != null_family_id);
        prNew = m.mk_th_lemma(tid, m.get_fact(pr), 
                              premises.size(), premises.c_ptr(), num_params-1, params+1);
    }
    else {
        ptr_vector<expr> args;
        for (unsigned i = 0; i < parents.size(); ++i) {
            args.push_back(parents[i].get());
        }
        if (m.has_fact(pr)) {
            args.push_back(m.get_fact(pr));
        }
        prNew = m.mk_app(pr->get_decl(), args.size(), args.c_ptr());
    }    
    
    cache.insert(pr, prNew);
    refs.push_back(prNew);
    pr = prNew;
}	


// permute unit resolution over Theory lemmas to track premises.
void proof_utils::permute_unit_resolution(proof_ref& pr) {
    expr_ref_vector refs(pr.get_manager());
    obj_map<proof,proof*> cache;
    ::permute_unit_resolution(refs, cache, pr);
}

class push_instantiations_up_cl {
    ast_manager& m;
public:
    push_instantiations_up_cl(ast_manager& m): m(m) {}

    void operator()(proof_ref& p) {
        expr_ref_vector s0(m);
        p = push(p, s0);
    }

private:

    proof* push(proof* p, expr_ref_vector const& sub) {
        proof_ref_vector premises(m);
        expr_ref conclusion(m);
        svector<std::pair<unsigned, unsigned> >  positions;
        vector<expr_ref_vector> substs;

        if (m.is_hyper_resolve(p, premises, conclusion, positions, substs)) {
            for (unsigned i = 0; i < premises.size(); ++i) {
                compose(substs[i], sub);
                premises[i] = push(premises[i].get(), substs[i]);
                substs[i].reset();
            }
            instantiate(sub, conclusion);
            return 
                m.mk_hyper_resolve(premises.size(), premises.c_ptr(), conclusion, 
                                   positions, 
                                   substs);
        }        
        if (sub.empty()) {
            return p;
        }
        if (m.is_modus_ponens(p)) {
            SASSERT(m.get_num_parents(p) == 2);
            proof* p0 = m.get_parent(p, 0);
            proof* p1 = m.get_parent(p, 1);
            if (m.get_fact(p0) == m.get_fact(p)) {
                return push(p0, sub);
            }
            expr* e1, *e2;
            if (m.is_rewrite(p1, e1, e2) && 
                is_quantifier(e1) && is_quantifier(e2) &&
                to_quantifier(e1)->get_num_decls() == to_quantifier(e2)->get_num_decls()) {
                expr_ref r1(e1,m), r2(e2,m);
                instantiate(sub, r1);
                instantiate(sub, r2);
                p1 = m.mk_rewrite(r1, r2);
                return m.mk_modus_ponens(push(p0, sub), p1);
            }
        }
        premises.push_back(p);
        substs.push_back(sub);
        conclusion = m.get_fact(p);
        instantiate(sub, conclusion);
        return m.mk_hyper_resolve(premises.size(), premises.c_ptr(), conclusion, positions, substs);
    }

    void compose(expr_ref_vector& sub, expr_ref_vector const& s0) {
        for (unsigned i = 0; i < sub.size(); ++i) {
            expr_ref e(m);
            var_subst(m, false)(sub[i].get(), s0.size(), s0.c_ptr(), e);
            sub[i] = e;            
        }
    }

    void instantiate(expr_ref_vector const& sub, expr_ref& fml) {
        if (sub.empty()) {
            return;
        }
        if (!is_forall(fml)) {
            return;
        }
        quantifier* q = to_quantifier(fml);
        if (q->get_num_decls() != sub.size()) {
            TRACE("proof_utils", tout << "quantifier has different number of variables than substitution";
                  tout << mk_pp(q, m) << "\n";
                  tout << sub.size() << "\n";);
            return;
        }
        var_subst(m, false)(q->get_expr(), sub.size(), sub.c_ptr(), fml);
    }

};

void proof_utils::push_instantiations_up(proof_ref& pr) {
    push_instantiations_up_cl push(pr.get_manager());
    push(pr);
}


