/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    xor_solver.h

Abstract:

    XOR solver.
    Interface outline.

--*/


#include "sat/smt/xor_solver.h"
#include "sat/sat_simplifier_params.hpp"
#include "sat/sat_xor_finder.h"

namespace xr {
    
    solver::solver(euf::solver& ctx):
        solver(ctx.get_manager(), ctx.get_si(), ctx.get_manager().get_family_id("xor")) {
        m_ctx = &ctx;
    }

    solver::solver(ast_manager& m, sat::sat_internalizer& si, euf::theory_id id)
        : euf::th_solver(m, symbol("xor"), id),
          si(si) {
    }
    
    solver::~solver() {
        /*for (justification* j : m_justifications) {
            j->deallocate(m_allocator);
        }*/
        clear_gauss_matrices(true);
    }

    euf::th_solver* solver::clone(euf::solver& ctx) {
        // and relevant copy internal state
        return alloc(solver, ctx);
    }
    
    void solver::add_every_combination_xor(const sat::literal_vector& lits, const bool attach) {
        unsigned at = 0, num = 0;
        sat::literal_vector xorlits;
        m_tmp_xor_clash_vars.clear();
        sat::literal lastlit_added = sat::null_literal;
        while (at != lits.size()) {
            xorlits.clear();
            for (unsigned last_at = at; at < last_at + s().get_config().m_xor_gauss_var_per_cut && at < lits.size(); at++) {
                xorlits.push_back(lits[at]);
            }
    
            //Connect to old cut
            if (lastlit_added != sat::null_literal) {
                xorlits.push_back(lastlit_added);
            } else if (at < lits.size()) {
                xorlits.push_back(lits[at]);
                at++;
            }
    
            if (at + 1 == lits.size()) {
                xorlits.push_back(lits[at]);
                at++;
            }
    
            //New lit to connect to next cut
            if (at != lits.size()) {
                const sat::bool_var new_var = m_solver->mk_var();
                m_tmp_xor_clash_vars.push_back(new_var);
                const sat::literal to_add = sat::literal(new_var, false);
                xorlits.push_back(to_add);
                lastlit_added = to_add;
            }
    
            // TODO: Do we really need this? Makes it very complicated to port
            // add_xor_clause_inter_cleaned_cut(xorlits, attach);
            if (s().inconsistent())
                break;
    
            num++;
        }
    }
    
    void solver::add_xor_clause(const sat::literal_vector& lits, bool rhs, const bool attach) {
        if (s().inconsistent())
            return;
        TRACE("xor", tout << "adding xor: " << lits << " rhs: " << rhs << "\n");
        SASSERT(!attach || m_prop_queue_head == m_prop_queue.size());
        SASSERT(s().at_search_lvl());
    
        sat::literal_vector ps(lits);
        for(sat::literal& lit: ps) {
            if (lit.sign()) {
                rhs ^= true;
                lit.neg();
            }
        }
        clean_xor_no_prop(ps, rhs);
    
        if (ps.size() >= (0x01UL << 28)) 
            throw default_exception("xor clause too long");
    
        if (ps.empty()) {
            if (rhs)
                m_solver->set_conflict();
            return;
        }
    
        if (rhs)
            ps[0].neg();
    
        add_every_combination_xor(ps, attach);
        if (ps.size() > 2) {
            m_xor_clauses_updated = true;
            m_xorclauses.push_back(xor_clause(ps, rhs, m_tmp_xor_clash_vars));
            m_xorclauses_orig.push_back(xor_clause(ps, rhs, m_tmp_xor_clash_vars));
        }
    }

    void solver::asserted(sat::literal l) {        
        TRACE("xor", tout << "asserted: " << l << "\n";);
        force_push();
        m_prop_queue.push_back(l);
    }

    bool solver::unit_propagate() {
        if (m_prop_queue_head == m_prop_queue.size())
            return false;
        force_push();
        m_ctx->push(value_trail<unsigned>(m_prop_queue_head));
        for (; m_prop_queue_head < m_prop_queue.size() && !s().inconsistent(); ++m_prop_queue_head) {
            sat::literal const p = m_prop_queue[m_prop_queue_head];
            sat::justification conflict = gauss_jordan_elim(p, m_num_scopes);
            if (conflict.is_none()) {
                m_prop_queue_head = m_prop_queue.size();
                s().set_conflict(conflict);
            }
        }
        return true;
    }
    
    sat::justification solver::gauss_jordan_elim(const sat::literal p, const unsigned currLevel) {
        if (gmatrices.empty()) 
            return sat::justification(-1);
        for (unsigned i = 0; i < gqueuedata.size(); i++) {
            if (gqueuedata[i].disabled || !gmatrices[i]->is_initialized()) continue;
            gqueuedata[i].reset();
            gmatrices[i]->update_cols_vals_set();
        }
        
        bool confl_in_gauss = false;
        SASSERT(gwatches.size() > p.var());
        svector<gauss_watched>& ws = gwatches[p.var()];
        gauss_watched* i = ws.begin();
        gauss_watched* j = i;
        const gauss_watched* end = ws.end();
        
        for (; i != end; i++) {
            if (gqueuedata[i->matrix_num].disabled || !gmatrices[i->matrix_num]->is_initialized())
                continue; //remove watch and continue
        
            gqueuedata[i->matrix_num].new_resp_var = UINT_MAX;
            gqueuedata[i->matrix_num].new_resp_row = UINT_MAX;
            gqueuedata[i->matrix_num].do_eliminate = false;
            gqueuedata[i->matrix_num].currLevel = currLevel;
        
            if (gmatrices[i->matrix_num]->find_truths(i, j, p.var(), i->row_n, gqueuedata[i->matrix_num])) {
                continue;
            } else {
                confl_in_gauss = true;
                i++;
                break;
            }
        }
        
        for (; i != end; i++) *j++ = *i;
        ws.shrink(i - j);
        
        for (unsigned g = 0; g < gqueuedata.size(); g++) {
            if (gqueuedata[g].disabled || !gmatrices[g]->is_initialized())
                continue;
        
            if (gqueuedata[g].do_eliminate) {
                gmatrices[g]->eliminate_col(p.var(), gqueuedata[g]);
                confl_in_gauss |= (gqueuedata[g].status == gauss_res::confl);
            }
        }
        
        for (gauss_data& gqd: gqueuedata) {
            if (gqd.disabled) continue;
        
            //There was a conflict but this is not that matrix.
            //Just skip.
            if (confl_in_gauss && gqd.status != gauss_res::confl) 
                continue;
        
            switch (gqd.status) {
                case gauss_res::confl:
                    gqd.num_conflicts++;
                    return gqd.conflict;
        
                case gauss_res::prop:
                    gqd.num_props++;
                    break;
        
                case gauss_res::none:
                    //nothing
                    break;
        
                default:
                    UNREACHABLE();
            }
        }
        return sat::justification(-1);
    }
    
    void solver::get_antecedents(sat::literal l, sat::ext_justification_idx idx,
                                 sat::literal_vector & r, bool probing) {
        
    }
    
    sat::check_result solver::check() {
        return sat::check_result::CR_DONE;
    }
    
    // TODO: we should separate this parts from the euf_solver. Other non-euf theories might need it as well
    // Similar: Attaching "theory_var"s in non-euf/enode cases  
    void solver::force_push() {
        for (; m_num_scopes > 0; --m_num_scopes) {
            push_core();
        }
    }
    
    void solver::push_core() {
        m_prop_queue_lim.push_back(m_prop_queue.size());
        //m_justifications_lim.push_back(m_justifications.size());
    }
    
    void solver::pop_core(unsigned num_scopes) {
        SASSERT(m_num_scopes == 0);
        unsigned old_sz = m_prop_queue_lim.size() - num_scopes;
        m_prop_queue.shrink(m_prop_queue_lim[old_sz]);
        m_prop_queue_lim.shrink(old_sz);
        
        /*old_sz = m_justifications_lim.size() - num_scopes;
        unsigned lim = m_justifications_lim[old_sz];
        for (unsigned i = m_justifications.size(); i > lim; i--) {
            m_justifications[i - 1].destroy(m_allocator);
        }
        m_justifications_lim.shrink(old_sz);
        m_justifications.shrink(old_sz);*/
    }
    
    void solver::push() {
        m_num_scopes++; 
    }
    
    void solver::pop(unsigned n) {
        unsigned k = std::min(m_num_scopes, n);
        m_num_scopes -= k;
        n -= k;
        if (n > 0)
            pop_core(n);
    }

    // inprocessing
    // pre_simplify: decompile all xor constraints to allow other in-processing.
    // simplify: recompile clauses to xor constraints
    // literals that get added to xor constraints are tagged with the theory.
    void solver::pre_simplify() {
        
    }

    void solver::simplify() {
        
    }

    std::ostream& solver::display(std::ostream& out) const {
        return out;
    }
    
    bool solver::clear_gauss_matrices(const bool destruct) {
        // TODO: Include; ignored for now. Maybe we can ignore the detached clauses
        /*if (!destruct) {
            if (!fully_undo_xor_detach()) 
                return false;
        }*/
        m_xor_clauses_updated = true;
    
        for (EGaussian* g: gmatrices) 
            g->move_back_xor_clauses();
        for (EGaussian* g: gmatrices) 
            memory::deallocate(g);
        for (auto& w: gwatches) 
            w.clear();
        
        gmatrices.clear();
        gqueuedata.clear();
        
        m_xorclauses.clear(); // we rely on xorclauses_orig now
        m_xorclauses_unused.clear();
        
        if (!destruct) {
            for (const auto& x: m_xorclauses_orig) {
                m_xorclauses.push_back(x);
            }
        }
    
        return !s().inconsistent();
    }
    
    bool solver::find_and_init_all_matrices() {
        if (!m_xor_clauses_updated/* && (!m_detached_xor_clauses || !assump_contains_xor_clash())*/)
            return true;
        
        bool can_detach;
        if (!clear_gauss_matrices(false)) 
            return false;
        
        xor_matrix_finder mfinder(solver);
        ok = mfinder.find_matrices(can_detach);
        if (!ok) return false;
        if (!init_all_matrices()) return false;
        
        bool ret_no_irred_nonxor_contains_clash_vars;
        
        /* TODO: Make this work (ignored for now)
        if (can_detach &&
            s().get_config().m_xor_gauss_detach_reattach &&
            !s().get_config().autodisable &&
            (ret_no_irred_nonxor_contains_clash_vars = no_irred_nonxor_contains_clash_vars())) {
            detach_xor_clauses(mfinder.clash_vars_unused);
            unset_clash_decision_vars(xorclauses);
            rebuildOrderHeap();
        }*/
        m_xor_clauses_updated = false;
        return true;
    }
    
    bool solver::init_all_matrices() {
        SASSERT(!s().inconsistent());
        SASSERT(s().at_search_lvl());
        SASSERT(gmatrices.size() == gqueuedata.size());
        
        for (unsigned i = 0; i < gmatrices.size(); i++) {
            auto& g = gmatrices[i];
            bool created = false;
            if (!g->full_init(created)) 
                return false;
            SASSERT(!s().inconsistent());
    
            if (!created) {
                gqueuedata[i].disabled = true;
                memory::deallocate(g);
                g = nullptr;
            }
        }
    
        unsigned j = 0;
        bool modified = false;
        for (unsigned i = 0; i < gqueuedata.size(); i++) {
            if (gmatrices[i] == nullptr) {
                modified = true;
                continue;
            }
            gmatrices[j] = gmatrices[i];
            gmatrices[j]->update_matrix_no(j);
            gqueuedata[j] = gqueuedata[i];
            
            if (modified) {
                for (unsigned var = 0; var < s().num_vars(); var++) {
                    for (gauss_watched& k : gwatches[var]) {
                        if (k.matrix_num == i) {
                            k.matrix_num = j;
                        }
                    }
                }
            }
            j++;
        }
        gqueuedata.resize(j);
        gmatrices.resize(j);
        
        return !s().inconsistent();
    }
    
    sat::justification solver::mk_justification(const int level, const unsigned int matrix_no, const unsigned int row_i) {
        void* mem = m_ctx->get_region().allocate(justification::get_obj_size());
        sat::constraint_base::initialize(mem, this);
        auto* constraint = new (sat::constraint_base::ptr2mem(mem)) justification(matrix_no, row_i);
        return sat::justification::mk_ext_justification(level, constraint->to_index()); 
    }
    
    void solver::clean_xor_no_prop(sat::literal_vector & ps, bool & rhs) {
        std::sort(ps.begin(), ps.end());
        sat::literal p = sat::null_literal;
        unsigned i = 0, j = 0;
        for (; i != ps.size(); i++) {
            SASSERT(!ps[i].sign());
            if (ps[i].var() == p.var()) {
                //added, but easily removed
                j--;
                p = sat::null_literal;
                //Flip rhs if necessary
                if (s().value(ps[i]) != l_undef) {
                    rhs ^= s().value(ps[i]) == l_true;
                }
            } else if (s().value(ps[i]) == l_undef) {
                //Add and remember as last one to have been added
                ps[j++] = p = ps[i];
            } else {
                //modify rhs instead of adding
                rhs ^= s().value(ps[i]) == l_true;
            }
        }
        ps.resize(ps.size() - (i - j));
    }
    
    std::ostream& solver::display_justification(std::ostream& out, sat::ext_justification_idx idx) const  {
        return out;
    }
    
    std::ostream& solver::display_constraint(std::ostream& out, sat::ext_constraint_idx idx) const {
        return out;
    }
#if 0
    void xor_finder::grab_mem() {
        occcnt.clear();
        occcnt.resize(m_solver.s().num_vars(), 0);
    }
    
    void xor_finder::move_xors_without_connecting_vars_to_unused() {
        if (solver->xorclauses.empty()) 
            return;
        
        double myTime = cpuTime();
        svector<Xor> cleaned;
        SASSERT(toClear.empty());
        
        //Fill "seen" with vars used
        unsigned non_empty = 0;
        for (const Xor& x: solver->xorclauses) {
            if (x.size() != 0) {
                non_empty++;
            }
        
            for (unsigned v: x) {
                if (solver->seen[v] == 0) {
                    toClear.push_back(Lit(v, false));
                }
        
                if (solver->seen[v] < 2) {
                    solver->seen[v]++;
                }
            }
        }
        
        //has at least 1 var with occur of 2
        for(const Xor& x: solver->xorclauses) {
            if (xor_has_interesting_var(x) || x.detached) 
                cleaned.push_back(x);
            else 
                solver->xorclauses_unused.push_back(x);
        }
        
        //clear "seen"
        for(Lit l: toClear) solver->seen[l.var()] = 0;
        toClear.clear();
        
        solver->xorclauses = cleaned;
        
        double time_used = cpuTime() - myTime;
        if (solver->conf.verbosity) {
            cout << "c [xor-rem-unconnected] left with " <<  solver->xorclauses.size()
            << " xors from " << non_empty << " non-empty xors"
            << solver->conf.print_times(time_used)
            << endl;
        }
        if (solver->sqlStats) {
            solver->sqlStats->time_passed_min(
                solver
                , "xor-rem-no-connecting-vars"
                , time_used
            );
        }
    }
    
    bool xor_finder::xor_together_xors(vector<Xor> & this_xors) {
        if (occcnt.size() != solver->nVars())
            grab_mem();
    
        if (this_xors.empty())
            return solver->okay();
    
        if (solver->conf.verbosity >= 5) {
            cout << "c XOR-ing together XORs. Starting with: " << endl;
            for(const auto& x: this_xors) {
                cout << "c XOR before xor-ing together: " << x << endl;
            }
        }
    
        assert(solver->okay());
        assert(solver->s().at_search_lvl());
        assert(solver->watches.get_smudged_list().empty());
        const size_t origsize = this_xors.size();
    
        uint32_t xored = 0;
        const double myTime = cpuTime();
        assert(toClear.empty());
    
        //Link in xors into watchlist
        for(size_t i = 0; i < this_xors.size(); i++) {
            const Xor& x = this_xors[i];
            for(uint32_t v: x) {
                if (occcnt[v] == 0) {
                    toClear.push_back(Lit(v, false));
                }
                occcnt[v]++;
    
                Lit l(v, false);
                assert(solver->watches.size() > l.toInt());
                solver->watches[l].push(Watched(i, WatchType::watch_idx_t));
                solver->watches.smudge(l);
            }
        }
    
        vector<unsigned> to_clear_2;
        
        for(const auto& ws: solver->watches) {
            for(const auto& w: ws) {
                if (w.isBin() && !w.red()) {
                    uint32_t v = w.lit2().var();
                    if (!seen2[v]) {
                        seen2[v] = 1;
                        to_clear_2.push_back(v);
                    }
                }
            }
        }
    
        for(const auto& offs: solver->longIrredCls) {
            Clause* cl = solver->cl_alloc.ptr(offs);
            if (cl->red() || cl->used_in_xor()) {
                continue;
            }
            for(Lit l: *cl) {
                if (!seen2[l.var()]) {
                    seen2[l.var()] = 1;
                    to_clear_2.push_back(l.var());
                    //cout << "Not XORing together over var: " << l.var()+1 << endl;
                }
            }
        }
    
        //until fixedpoint
        bool changed = true;
        while(changed) {
            changed = false;
            interesting.clear();
            for(const Lit l: toClear) {
                if (occcnt[l.var()] == 2 && !seen2[l.var()]) {
                    interesting.push_back(l.var());
                }
            }
    
            while(!interesting.empty()) {
                #ifdef SLOW_DEBUG
                {
                    vector<uint32_t> check;
                    check.resize(solver->nVars(), 0);
                    for(size_t i = 0; i < this_xors.size(); i++) {
                        const Xor& x = this_xors[i];
                        for(uint32_t v: x) {
                            check[v]++;
                        }
                    }
                    for(size_t i = 0; i < solver->nVars(); i++) {
                        assert(check[i] == occcnt[i]);
                    }
                }
                #endif
    
                //Pop and check if it can be XOR-ed together
                const uint32_t v = interesting.back();
                interesting.resize(interesting.size()-1);
                if (occcnt[v] != 2)
                    continue;
    
                size_t idxes[2];
                unsigned at = 0;
                size_t i2 = 0;
                assert(solver->watches.size() > Lit(v, false).toInt());
                watch_subarray ws = solver->watches[Lit(v, false)];
    
                //Remove the 2 indexes from the watchlist
                for(size_t i = 0; i < ws.size(); i++) {
                    const Watched& w = ws[i];
                    if (!w.isIdx()) {
                        ws[i2++] = ws[i];
                    } else if (!this_xors[w.get_idx()].empty()) {
                        assert(at < 2);
                        idxes[at] = w.get_idx();
                        at++;
                    }
                }
                assert(at == 2);
                ws.resize(i2);
    
                Xor& x0 = this_xors[idxes[0]];
                Xor& x1 = this_xors[idxes[1]];
                uint32_t clash_var;
                uint32_t clash_num = xor_two(&x0, &x1, clash_var);
    
                //If they are equivalent
                if (x0.size() == x1.size()
                    && x0.rhs == x1.rhs
                    && clash_num == x0.size()
                ) {
                    //Update clash values & detached values
                    x1.merge_clash(x0, seen);
                    x1.detached |= x0.detached;
    
                    VERBOSE_PRINT("after merge: " << x1 <<  " -- at idx: " << idxes[1]);
    
                    //Equivalent, so delete one
                    x0 = Xor();
    
                    //Re-attach the other, remove the occur of the one we deleted
                    solver->watches[Lit(v, false)].push(Watched(idxes[1], WatchType::watch_idx_t));
    
                    for(uint32_t v2: x1) {
                        Lit l(v2, false);
                        assert(occcnt[l.var()] >= 2);
                        occcnt[l.var()]--;
                        if (occcnt[l.var()] == 2 && !seen2[l.var()]) {
                            interesting.push_back(l.var());
                        }
                    }
                } else if (clash_num > 1 || x0.detached || x1.detached) {
                    //add back to ws, can't do much
                    ws.push(Watched(idxes[0], WatchType::watch_idx_t));
                    ws.push(Watched(idxes[1], WatchType::watch_idx_t));
                    continue;
                } else {
                    occcnt[v] -= 2;
                    assert(occcnt[v] == 0);
    
                    Xor x_new(tmp_vars_xor_two, x0.rhs ^ x1.rhs, clash_var);
                    x_new.merge_clash(x0, seen);
                    x_new.merge_clash(x1, seen);
                    
                    changed = true;
                    this_xors.push_back(x_new);
                    for(uint32_t v2: x_new) {
                        Lit l(v2, false);
                        solver->watches[l].push(Watched(this_xors.size()-1, WatchType::watch_idx_t));
                        assert(occcnt[l.var()] >= 1);
                        if (occcnt[l.var()] == 2 && !seen2[l.var()]) {
                            interesting.push_back(l.var());
                        }
                    }
                    this_xors[idxes[0]] = Xor();
                    this_xors[idxes[1]] = Xor();
                    xored++;
                }
            }
        }
        
        //Clear
        for(const Lit l: toClear) occcnt[l.var()] = 0;
        toClear.clear();
        for(const auto& x: to_clear_2) seen2[x] = 0;
    
        solver->clean_occur_from_idx_types_only_smudged();
        clean_xors_from_empty(this_xors);
    
        return solver->okay();
    }
    
    void xor_finder::clean_xors_from_empty(vector<Xor> & thisxors) {
        size_t j = 0;
        for(size_t i = 0;i < thisxors.size(); i++) {
            Xor& x = thisxors[i];
            if (x.size() == 0 && x.rhs == false) {
                if (!x.clash_vars.empty()) {
                    solver->xorclauses_unused.push_back(x);
                } else {
                    TBUDDY_DO(solver->frat->flush());
                    TBUDDY_DO(delete x.bdd);
                }
            } else {
                verb_print(4, "xor after clean: " << thisxors[i]);
                thisxors[j++] = thisxors[i];
            }
        }
        thisxors.resize(j);
    }
    
    unsigned xor_finder::xor_two(const Xor *x1_p, const Xor *x2_p, uint32_t & clash_var) {
        tmp_vars_xor_two.clear();
        if (x1_p->size() > x2_p->size()) {
            std::swap(x1_p, x2_p);
        }
        const Xor& x1 = *x1_p;
        const Xor& x2 = *x2_p;
        
        uint32_t clash_num = 0;
        for(uint32_t v: x1) {
            assert(seen[v] == 0);
            seen[v] = 1;
        }
        
        uint32_t i_x2;
        bool early_abort = false;
        for(i_x2 = 0; i_x2 < x2.size(); i_x2++) {
            uint32_t v = x2[i_x2];
            assert(seen[v] != 2);
            if (seen[v] == 0) {
                tmp_vars_xor_two.push_back(v);
            } else {
                clash_var = v;
                if (clash_num > 0 &&
                    clash_num != i_x2 //not equivalent by chance
                ) {
                    //early abort, it's never gonna be good
                    clash_num++;
                    early_abort = true;
                    break;
                }
                clash_num++;
            }
            seen[v] = 2;
        }
        
        if (!early_abort) {
            for(uint32_t v: x1) {
                if (seen[v] != 2) {
                    tmp_vars_xor_two.push_back(v);
               }
                seen[v] = 0;
            }
        } else {
            for(uint32_t v: x1) {
                seen[v] = 0;
            }
        }
        
        for(uint32_t i = 0; i < i_x2; i++) {
            seen[x2[i]] = 0;
        }
        
        return clash_num;
    }
#endif
}

