/*++
Copyright (c) 2013 Microsoft Corporation

Module Name:

    maxsmt.cpp

Abstract:
   
    MaxSMT optimization context.

Author:

    Nikolaj Bjorner (nbjorner) 2013-11-7

Notes:

--*/

#include <typeinfo>
#include "util/uint_set.h"
#include "ast/ast_pp.h"
#include "ast/ast_util.h"
#include "ast/pb_decl_plugin.h"
#include "opt/maxsmt.h"
#include "opt/maxcore.h"
#include "opt/maxlex.h"
#include "opt/wmax.h"
#include "opt/opt_params.hpp"
#include "opt/opt_context.h"
#include "opt/opt_preprocess.h"
#include "smt/theory_wmaxsat.h"
#include "smt/theory_pb.h"


namespace opt {

    maxsmt_solver_base::maxsmt_solver_base(maxsat_context& c, vector<soft>& s, unsigned index):
        m(c.get_manager()), 
        m_c(c),
        m_index(index),
        m_soft(s),
        m_assertions(m),
        m_trail(m) {
        c.get_base_model(m_model);
        SASSERT(m_model);
        updt_params(c.params());
    }
    
    void maxsmt_solver_base::updt_params(params_ref& p) {
        m_params.copy(p);
    }

    void maxsmt_solver_base::reset_upper() {
        m_upper = m_lower;
        for (soft& s : m_soft) 
            m_upper += s.weight;
    }

    solver& maxsmt_solver_base::s() {
        return m_c.get_solver(); 
    }

    void maxsmt_solver_base::commit_assignment() {
        expr_ref tmp(m);
        expr_ref_vector fmls(m);
        rational k(0), cost(0);
        vector<rational> weights;
        for (soft const& s : m_soft) {
            if (s.is_true()) {
                k += s.weight;
            }
            else {
                cost += s.weight;
            }
            weights.push_back(s.weight);
            fmls.push_back(s.s);
        }       
        pb_util pb(m);
        tmp = pb.mk_ge(weights.size(), weights.data(), fmls.data(), k);
        TRACE("opt", tout << "cost: " << cost << "\n" << tmp << "\n";);
        s().assert_expr(tmp);
    }

    bool maxsmt_solver_base::init() {
        m_lower.reset();
        m_upper.reset();
        for (soft& s : m_soft) {
            s.set_value(m.is_true(s.s));
            if (!s.is_true())
                m_upper += s.weight;
        }

        // return true;

        preprocess pp(s());
        rational lower(0);
        bool r = pp(m_soft, lower);

        m_c.add_offset(m_index, lower);
        m_upper -= lower;
        
        TRACE("opt", 
              tout << "lower " << lower << " upper: " << m_upper << " assignments: ";
              for (soft& s : m_soft) tout << (s.is_true()?"T":"F");              
              tout << "\n";);
        return r;
    }

    void maxsmt_solver_base::set_mus(bool f) {
        params_ref p;
        p.set_bool("minimize_core", f);
        // p.set_bool("minimize_core_partial", f);
        s().updt_params(p);
    }

    void maxsmt_solver_base::enable_sls(bool force) {
        m_c.enable_sls(force);
    }

    app* maxsmt_solver_base::mk_fresh_bool(char const* name) {
        app* result = m.mk_fresh_const(name, m.mk_bool_sort());
        m_c.fm().hide(result);
        return result;
    }

    smt::theory_wmaxsat* maxsmt_solver_base::get_wmax_theory() const {
        smt::theory_id th_id = m.get_family_id("weighted_maxsat");
        smt::theory* th = m_c.smt_context().get_theory(th_id);               
        if (th) {
            return dynamic_cast<smt::theory_wmaxsat*>(th);
        }
        else {
            return nullptr;
        }
    }

    smt::theory_wmaxsat* maxsmt_solver_base::ensure_wmax_theory() {
        smt::theory_wmaxsat* wth = get_wmax_theory();
        if (wth) {
            wth->reset_local();
        }
        else {
            wth = alloc(smt::theory_wmaxsat, m_c.smt_context(), m, m_c.fm());
            m_c.smt_context().register_plugin(wth);
        }
        smt::theory_id th_pb = m.get_family_id("pb");
        smt::theory_pb* pb = dynamic_cast<smt::theory_pb*>(m_c.smt_context().get_theory(th_pb));
        if (!pb) {
            theory_pb_params params;
            pb = alloc(smt::theory_pb, m_c.smt_context());
            m_c.smt_context().register_plugin(pb);
        }
        return wth;
    }

    maxsmt_solver_base::scoped_ensure_theory::scoped_ensure_theory(maxsmt_solver_base& s) {
        m_wth = s.ensure_wmax_theory();
    }

    maxsmt_solver_base::scoped_ensure_theory::~scoped_ensure_theory() {
        if (m_wth) {
            m_wth->reset_local();
        }
    }
    smt::theory_wmaxsat& maxsmt_solver_base::scoped_ensure_theory::operator()() { return *m_wth; }


    void maxsmt_solver_base::trace_bounds(char const * solver) {
        IF_VERBOSE(1, 
                   rational l = m_c.adjust(m_index, m_lower);
                   rational u = m_c.adjust(m_index, m_upper);
                   if (l > u) std::swap(l, u);
                   verbose_stream() << "(opt." << solver << " [" << l << ":" << u << "])\n";);                
    }


    maxsmt::maxsmt(maxsat_context& c, unsigned index):
        m(c.get_manager()), m_c(c), m_index(index), m_answer(m) {}

    lbool maxsmt::operator()(bool committed) {
        lbool is_sat = l_undef;
        m_msolver = nullptr;
        opt_params optp(m_params);
        symbol const& maxsat_engine = m_c.maxsat_engine();
        IF_VERBOSE(1, verbose_stream() << "(maxsmt)\n";);
        TRACE("opt_verbose", s().display(tout << "maxsmt\n") << "\n";);
        if (!committed && optp.maxlex_enable() && is_maxlex(m_soft)) 
            m_msolver = mk_maxlex(m_c, m_index, m_soft);            
        else if (m_soft.empty() || maxsat_engine == symbol("maxres") || maxsat_engine == symbol::null)             
            m_msolver = mk_maxres(m_c, m_index, m_soft);            
        else if (maxsat_engine == symbol("maxres-bin"))             
            m_msolver = mk_maxres_binary(m_c, m_index, m_soft);
        else if (maxsat_engine == symbol("rc2"))             
            m_msolver = mk_rc2(m_c, m_index, m_soft);
        else if (maxsat_engine == symbol("rc2bin"))             
            m_msolver = mk_rc2bin(m_c, m_index, m_soft);
        else if (maxsat_engine == symbol("pd-maxres"))             
            m_msolver = mk_primal_dual_maxres(m_c, m_index, m_soft);
        else if (maxsat_engine == symbol("wmax")) 
            m_msolver = mk_wmax(m_c, m_soft, m_index);
        else if (maxsat_engine == symbol("sortmax")) 
            m_msolver = mk_sortmax(m_c, m_soft, m_index);
        else {
            auto str = maxsat_engine.str();
            warning_msg("solver %s is not recognized, using default 'maxres'", str.c_str());
            m_msolver = mk_maxres(m_c, m_index, m_soft);
        }

        if (m_msolver) {
            m_msolver->updt_params(m_params);
            is_sat = l_undef;
            try {
                is_sat = (*m_msolver)();
            }
            catch (z3_exception& ex) {
                IF_VERBOSE(1, verbose_stream() << ex.what() << "\n");
                is_sat = l_undef;
            }
            if (is_sat != l_false) {
                m_msolver->get_model(m_model, m_labels);
            }
        }

        IF_VERBOSE(5, verbose_stream() << "is-sat: " << is_sat << "\n";
                   if (is_sat == l_true) {
                       verbose_stream() << "Satisfying soft constraints\n";
                       display_answer(verbose_stream());
                   });

        DEBUG_CODE(if (is_sat == l_true) verify_assignment(););
        
        return is_sat;
    }

    void maxsmt::reset_upper() {
        if (m_msolver) {
            m_msolver->reset_upper();
            m_upper = m_msolver->get_upper();
        }
    }

    void maxsmt::verify_assignment() {
        // TBD: have to use a different solver 
        // because we don't push local scope any longer.
        return;
    }

    bool maxsmt::get_assignment(unsigned idx) const {
        if (m_msolver) {
            return m_msolver->get_assignment(idx);
        }
        else {
            return true;
        }
    } 

    rational maxsmt::get_lower() const {
        rational r = m_lower;
        if (m_msolver) {
            rational q = m_msolver->get_lower();
            if (q > r) r = q;
        }
        return m_c.adjust(m_index, r);
    }

    rational maxsmt::get_upper() const {
        rational r = m_upper;
        if (m_msolver) {
            rational q = m_msolver->get_upper();
            if (q < r) r = q; 
        }
        return m_c.adjust(m_index, r);
    }

    void maxsmt::update_lower(rational const& r) {
        m_lower = r;
    }

    void maxsmt::update_upper(rational const& r) {
        m_upper = r;
    }    

    void maxsmt::get_model(model_ref& mdl, svector<symbol>& labels) {
        mdl = m_model.get();
        labels = m_labels;
    }

    void maxsmt::commit_assignment() {
        if (m_msolver) {
            m_msolver->commit_assignment();
        }
    }

    void maxsmt::add(expr* f, rational const& w) {
        TRACE("opt", tout << mk_pp(f, m) << " weight: " << w << "\n";);
        SASSERT(m.is_bool(f));
        SASSERT(w.is_pos());
        unsigned index = 0;
        if (m_soft_constraint_index.find(f, index)) {
            m_soft[index].weight += w;
        }
        else {
            m_soft_constraint_index.insert(f, m_soft.size());
            m_soft.push_back(soft(expr_ref(f, m), w, false));
        }
        m_upper += w;
    }

    struct cmp_first {
        bool operator()(std::pair<unsigned, rational> const& x, std::pair<unsigned, rational> const& y) const {
            return x.second < y.second;
        }
    };

    void maxsmt::display_answer(std::ostream& out) const {

        unsigned idx = 0;
        for (auto const & [_e, w, t] : m_soft) {
            expr* e = _e.get();
            bool is_not = m.is_not(e, e);
            out << w << ": " << mk_pp(e, m)
                << ((is_not != get_assignment(idx))?" |-> true ":" |-> false ")
                << "\n";
            ++idx;
        }       
    }
    
    
    bool maxsmt::is_maxsat_problem(vector<rational> const& ws) const {
        for (unsigned i = 0; i < ws.size(); ++i) {
            if (!ws[i].is_one()) {
                return false;
            }
        }
        return true;
    }

    void maxsmt::updt_params(params_ref& p) {
        m_params.append(p);
        if (m_msolver) 
            m_msolver->updt_params(p);
    }

    void maxsmt::collect_statistics(statistics& st) const {
        if (m_msolver) 
            m_msolver->collect_statistics(st);
    }

    solver& maxsmt::s() {
        return m_c.get_solver(); 
    }

    void maxsmt::model_updated(model* mdl) {
        m_c.model_updated(mdl);
    }

    class solver_maxsat_context : public maxsat_context {
        params_ref m_params;
        solver_ref m_solver;
        model_ref  m_model;
        ref<generic_model_converter> m_fm; 
        symbol m_maxsat_engine;
        vector<rational> m_offsets;
    public:
        solver_maxsat_context(params_ref& p, solver* s, model * m): 
            m_params(p), 
            m_solver(s),
            m_model(m),
            m_fm(alloc(generic_model_converter, s->get_manager(), "maxsmt")) {
            opt_params _p(p);
            m_maxsat_engine = _p.maxsat_engine();            
        }
        generic_model_converter& fm() override { return *m_fm.get(); }
        bool sat_enabled() const override { return false; }
        solver& get_solver() override { return *m_solver.get(); }
        ast_manager& get_manager() const override { return m_solver->get_manager(); }
        params_ref& params() override { return m_params; }
        void enable_sls(bool force) override { } // no op
        symbol const& maxsat_engine() const override { return m_maxsat_engine; }
        void get_base_model(model_ref& _m) override { _m = m_model; };  
        smt::context& smt_context() override { 
            throw default_exception("stand-alone maxsat context does not support wmax"); 
        }
        unsigned num_objectives() override { return 1; }
        bool verify_model(unsigned id, model* mdl, rational const& v) override { return true; };
        void set_model(model_ref& _m) override { m_model = _m; }
        void model_updated(model* mdl) override { } // no-op
        rational adjust(unsigned id, rational const& r) override {
            m_offsets.reserve(id+1);
            return r + m_offsets[id];
        }
        void add_offset(unsigned id, rational const& r) override {
            m_offsets.reserve(id+1);
            m_offsets[id] += r;
        }
    };

    lbool maxsmt_wrapper::operator()(vector<std::pair<expr*,rational>>& soft) {
        solver_maxsat_context ctx(m_params, m_solver.get(), m_model.get());
        maxsmt maxsmt(ctx, 0);
        for (auto const& p : soft) {
            maxsmt.add(p.first, p.second);
        }
        lbool r = maxsmt(true);
        if (r == l_true) {
            svector<symbol> labels;
            maxsmt.get_model(m_model, labels);
            // TBD: is m_fm applied or not?
            unsigned j = 0;
            for (auto const& p : soft) {
                if (m_model->is_true(p.first)) {
                    soft[j++] = p;
                }
            }
            soft.shrink(j);
        }
        return r;
    }
};
