/**

Example from Boogie:

(derivation
(step s!4 (main_loop_LoopHead true true)
 rule!3  (subst
    (= assertsPassed@@1 true)
    (= assertsPassed@2@@0 true)
    (= main_loop_LoopHead_assertsPassed true)
  )
  (labels @950 +895 +668 +670 +893 +899  )
  (ref  true  ))
(step s!3 (main true false)
 rule!1  (subst
    (= assertsPassed true)
    (= assertsPassed@0 true)
    (= assertsPassed@2 false)
    (= main_assertsPassed false)
  )
  (labels @839 +763 +547 +546 +761 +544 +545 +si_fcall_805 +681 +768  )
  (ref  s!4  ))
(step s!2 (main_SeqInstr true false)
 rule!2  (subst
    (= assertsPassed@@0 true)
    (= assertsPassed@0@@0 false)
    (= main_SeqInstr_assertsPassed false)
  )
  (labels @890 +851 +572 +si_fcall_883 +853  )
  (ref  s!3  ))
(step s!1 (@Fail!0)
 rule!4  (subst
    (= assertsPassed@@2 true)
    (= main_SeqInstr_assertsPassed@@0 false)
  )
  (labels  )
  (ref  s!2  ))
)
(model
"tickleBool -> {
  true -> true
  false -> true
  else -> true
}
")
*/

#include "dl_boogie_proof.h"
#include "model_pp.h"
#include "proof_utils.h"
#include "ast_pp.h"
#include "qe_util.h"

namespace datalog {
    
    /**
       \brief push hyper-resolution steps upwards such that every use of
       hyper-resolution uses a premise that is not derived from hyper-resolution.
              
       perform the following rewrite:
       
       hr(hr(p1,p2,p3,..),p4,p5) => hr(p1,hr(p2,p4),p3,..,p5)
      
    */

    void mk_input_resolution(proof_ref& pr) {
        ast_manager& m = pr.get_manager();
        proof_ref pr1(m);
        proof_ref_vector premises1(m), premises2(m), premises(m);
        expr_ref conclusion1(m), conclusion2(m), conclusion(m);
        svector<std::pair<unsigned, unsigned> > positions1, positions2, positions;
        vector<expr_ref_vector> substs1, substs2, substs;
        
        if (m.is_hyper_resolve(pr, premises1, conclusion1, positions1, substs1) &&
            m.is_hyper_resolve(premises1[0].get(), premises, conclusion2, positions, substs2)) {
            for (unsigned i = 1; i < premises1.size(); ++i) {
                pr1 = premises1[i].get();
                mk_input_resolution(pr1);
                premises1[i] = pr1;
            }
            for (unsigned i = 0; i < premises.size(); ++i) {
                pr1 = premises[i].get();
                mk_input_resolution(pr1);
                premises[i] = pr1;
            }
            unsigned sz = premises.size();
            for (unsigned i = 1; i < sz; ++i) {
                proof* premise = premises[i].get();
                expr_ref_vector literals(m);
                expr* l1, *l2;
                if (!m.is_implies(premise, l1, l2)) {
                    continue;
                }
                qe::flatten_and(l1, literals);
                positions2.reset();
                premises2.reset();
                premises2.push_back(premise);       
                substs2.reset();
                for (unsigned j = 0; j < literals.size(); ++j) {
                    expr* lit = literals[j].get();
                    for (unsigned k = 1; k < premises1.size(); ++k) {
                        if (m.get_fact(premises1[k].get()) == lit) {
                            premises2.push_back(premises1[k].get());
                            positions2.push_back(std::make_pair(j+1,0));
                            substs2.push_back(expr_ref_vector(m));
                            break;
                        }
                    }
                }
                premises[i] = m.mk_hyper_resolve(premises2.size(), premises2.c_ptr(), l2, positions2, substs2);
            }        
            conclusion = conclusion1;
            pr = m.mk_hyper_resolve(premises.size(), premises.c_ptr(), conclusion, positions, substs);
        }
    }
    
    void boogie_proof::set_proof(proof* p) {
        std::cout << "set proof\n";
        m_proof = p;
        proof_utils::push_instantiations_up(m_proof);
        mk_input_resolution(m_proof);
        std::cout << "proof set\n";
    }
        
    void boogie_proof::set_model(model* m) {
        m_model = m;
    }
    
    void boogie_proof::pp(std::ostream& out) {
        if (m_proof) {
            pp_proof(out);
        }
        if (m_model) {
            model_pp(out, *m_model);
        }
    }

    void boogie_proof::pp_proof(std::ostream& out) {
        vector<step> steps;
        ptr_vector<proof> rules;
        rules.push_back(m_proof);
        steps.push_back(step());
        obj_map<proof, unsigned> index;
        index.insert(m_proof, 0);
        
        for (unsigned j = 0; j < rules.size(); ++j) {
            proof* p = rules[j];
            proof_ref_vector premises(m);
            expr_ref conclusion(m);
            svector<std::pair<unsigned, unsigned> >  positions;
            vector<expr_ref_vector> substs;

            expr* tmp;
            steps[j].m_fact = m.get_fact(p);
            m.is_implies(steps[j].m_fact, tmp, steps[j].m_fact);
            get_subst(p, steps[j].m_subst);
            get_labels(p, steps[j].m_labels);

            if (m.is_hyper_resolve(p, premises, conclusion, positions, substs)) {
                for (unsigned i = 1; i < premises.size(); ++i) {
                    proof* premise = premises[i].get();
                    unsigned position = 0;
                    if (!index.find(premise, position)) {
                        position = rules.size();
                        rules.push_back(premise);
                        steps.push_back(step());
                        index.insert(premise, position);
                    }   
                    steps[j].m_refs.push_back(position);
                }
                get_rule_name(premises[0].get(), steps[j].m_rule_name);
            }
        }
        for (unsigned j = steps.size(); j > 0; ) {
            --j;
            step &s = steps[j];

            // TBD
            // s.m_labels;

            // set references, compensate for reverse ordering.
            for (unsigned i = 0; i < s.m_refs.size(); ++i) {
                s.m_refs[i] = rules.size()-1-s.m_refs[i];
            }
        }
        steps.reverse();
        pp_steps(out, steps);
    }

    /**
       \brief extract the instantiation by searching for the first occurrence of a hyper-resolution
       rule that produces an instance.
     */
    void boogie_proof::get_subst(proof* p, subst& s) {
        ptr_vector<proof> todo;
        todo.push_back(p);
        ast_mark visited;
        std::cout << "get_subst\n" << mk_pp(p, m) << "\n";
        while (!todo.empty()) {
            proof* p = todo.back();
            todo.pop_back();
            if (visited.is_marked(p)) {
                continue;
            }
            visited.mark(p, true);
            proof_ref_vector premises(m);
            expr_ref conclusion(m);
            svector<std::pair<unsigned, unsigned> >  positions;
            vector<expr_ref_vector> substs;
            if (m.is_hyper_resolve(p, premises, conclusion, positions, substs)) {               
                expr_ref_vector const& sub = substs[0];
                if (!sub.empty()) {
                    quantifier* q = to_quantifier(m.get_fact(premises[0].get()));
                    unsigned sz = sub.size();
                    SASSERT(sz == q->get_num_decls());
                    for (unsigned i = 0; i < sz; ++i) {
                        s.push_back(std::make_pair(q->get_decl_name(sz-1-i), sub[i]));
                    }
                    return;
                }
            }
            unsigned sz = m.get_num_parents(p);
            for (unsigned i = 0; i < sz; ++i) {
                todo.push_back(m.get_parent(p, i));
            }
        }
    }

    void boogie_proof::get_rule_name(proof* p, symbol& n) {

    }

    void boogie_proof::get_labels(proof* p, labels& lbls) {
        
    }

    void boogie_proof::pp_steps(std::ostream& out, vector<step>& steps) {
        out << "(derivation\n";
        for (unsigned i = 0; i < steps.size(); ++i) {
            pp_step(out, i, steps[i]);
        }
        out << ")\n";

    }

    // step       :: "(" "step" step-name fact rule-name subst labels premises ")"
    void boogie_proof::pp_step(std::ostream& out, unsigned id, step& s) {
        out << "(step\n";
        out << " s!" << id << " "; 
        pp_fact(out, s.m_fact);
        out << " " << s.m_rule_name << "\n";
        pp_subst(out << " ", s.m_subst);
        pp_labels(out << " ", s.m_labels);
        pp_premises(out << " ", s.m_refs);
        out << ")\n";
    }

    // fact       :: "(" predicate theory-term* ")"
    void boogie_proof::pp_fact(std::ostream& out, expr* fact) {
        out << mk_pp(fact, m) << "\n";
    }

    // subst      :: "(" "subst" assignment* ")"
    void boogie_proof::pp_subst(std::ostream& out, subst& s) {
        out << "(subst";
        for (unsigned i = 0; i < s.size(); ++i) {
            pp_assignment(out, s[i].first, s[i].second);
        }
        out << ")\n";
    }

    // assignment :: "(" "=" variable theory-term ")"
    void boogie_proof::pp_assignment(std::ostream& out, symbol const& v, expr* t) {
        out << "\n  (= " << v << " " << mk_pp(t, m) << ")";
    }


    // labels     :: "(" "labels" label* ")"
    void boogie_proof::pp_labels(std::ostream& out, labels& lbls) {
        out << "(labels";
        for (unsigned i = 0; i < lbls.size(); ++i) {
            out << " " << lbls[i];
        }
        out << ")\n";
    }

    // premises "(" "ref" step-name* ")"
    void boogie_proof::pp_premises(std::ostream& out, refs& refs) {
        out << "(ref";
        for (unsigned i = 0; i < refs.size(); ++i) {
            out << " s!" << refs[i];
        }
        out << ")\n";
    }


}
