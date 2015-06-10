
/*++
Copyright (c) 2015 Microsoft Corporation

--*/


#include "qe.h"
#include "expr_safe_replace.h"
#include "dl_decl_plugin.h"
#include "obj_pair_hashtable.h"
#include "ast_pp.h"


namespace qe {

    // ---------------------
    // dl_plugin

    class eq_atoms {
        expr_ref_vector m_eqs;
        expr_ref_vector m_neqs;
        app_ref_vector m_eq_atoms;
        app_ref_vector m_neq_atoms;
    public:
        eq_atoms(ast_manager& m):
          m_eqs(m),
          m_neqs(m),
          m_eq_atoms(m), 
          m_neq_atoms(m) {}

          unsigned num_eqs() const { return m_eqs.size(); }
          expr* eq(unsigned i) const { return m_eqs[i]; }
          app* eq_atom(unsigned i) const { return m_eq_atoms[i]; }
          unsigned num_neqs() const { return m_neqs.size(); }
          app* neq_atom(unsigned i) const { return m_neq_atoms[i]; }
          expr* neq(unsigned i) const { return m_neqs[i]; }
          void add_eq(app* atom, expr * e) { m_eq_atoms.push_back(atom); m_eqs.push_back(e); }
          void add_neq(app* atom, expr* e) { m_neq_atoms.push_back(atom); m_neqs.push_back(e); }
    };

    class dl_plugin : public qe_solver_plugin {
        typedef obj_pair_map<app,  expr, eq_atoms*> eqs_cache;
        expr_safe_replace         m_replace;
        datalog::dl_decl_util     m_util;
        expr_ref_vector           m_trail;
        eqs_cache                 m_eqs_cache;

        
    public:
        dl_plugin(i_solver_context& ctx, ast_manager& m) : 
            qe_solver_plugin(m, m.mk_family_id("datalog_relation"), ctx),
            m_replace(m),
            m_util(m),
            m_trail(m)
        {
        }

        virtual ~dl_plugin() {
            eqs_cache::iterator it = m_eqs_cache.begin(), end = m_eqs_cache.end();
            for (; it != end; ++it) {
                dealloc(it->get_value());
            }
        }



        bool get_num_branches(contains_app & x,expr * fml,rational & num_branches) {
            if (!update_eqs(x, fml)) {
                return false;
            }
            eq_atoms& eqs = get_eqs(x.x(), fml);
            uint64 domain_size;
            if (is_small_domain(x, eqs, domain_size)) {
                num_branches = rational(domain_size, rational::ui64());
            }
            else {
                num_branches = rational(eqs.num_eqs() + 1);
            }
            return true;
        }

        void assign(contains_app & x,expr * fml,const rational & v) {
            SASSERT(v.is_unsigned());
            eq_atoms& eqs = get_eqs(x.x(), fml);            
            unsigned uv = v.get_unsigned();
            uint64 domain_size;
            if (is_small_domain(x, eqs, domain_size)) {
                SASSERT(v < rational(domain_size, rational::ui64()));
                assign_small_domain(x, eqs, uv);
            }
            else {
                assign_large_domain(x, eqs, uv);
            }
        }

        void subst(contains_app & x,const rational & v,expr_ref & fml, expr_ref* def) {
            SASSERT(v.is_unsigned());
            eq_atoms& eqs = get_eqs(x.x(), fml);           
            unsigned uv = v.get_unsigned();
            uint64 domain_size;
            if (is_small_domain(x, eqs, domain_size)) {
                SASSERT(uv < domain_size);
                subst_small_domain(x, eqs, uv, fml);
            }
            else {
                subst_large_domain(x, eqs, uv, fml);
            }
            if (def) {
                *def = 0; // TBD
            }
        }

        virtual bool solve(conj_enum& conjs, expr* fml) { return false; }

    private:

        bool is_small_domain(contains_app& x, eq_atoms& eqs, uint64& domain_size) {
            VERIFY(m_util.try_get_size(m.get_sort(x.x()), domain_size));
            return domain_size < eqs.num_eqs() + eqs.num_neqs();
        }

        void assign_small_domain(contains_app & x,eq_atoms& eqs, unsigned value) {
            expr_ref vl(m_util.mk_numeral(value, m.get_sort(x.x())), m);
            expr_ref eq(m.mk_eq(x.x(), vl), m);
            m_ctx.add_constraint(true, eq);
        }

        void assign_large_domain(contains_app & x,eq_atoms& eqs, unsigned v) {
            if (v < eqs.num_eqs()) {
                m_ctx.add_constraint(true, eqs.eq_atom(v));
            }
            else {
                SASSERT(v == eqs.num_eqs());
                for (unsigned i = 0; i < eqs.num_eqs(); ++i) {
                    expr_ref neq(m.mk_not(eqs.eq_atom(i)), m);
                    m_ctx.add_constraint(true, neq);
                }

                for (unsigned i = 0; i < eqs.num_neqs(); ++i) {
                    expr_ref neq(m.mk_not(eqs.neq_atom(i)), m);
                    m_ctx.add_constraint(true, neq);
                }
            }
        }

        void subst_small_domain(contains_app & x,eq_atoms& eqs, unsigned v,expr_ref & fml) {
            expr_ref vl(m_util.mk_numeral(v, m.get_sort(x.x())), m);
            m_replace.apply_substitution(x.x(), vl, fml);
        }

        // assumes that all disequalities can be satisfied.
        void subst_large_domain(contains_app & x,eq_atoms& eqs, unsigned w,expr_ref & fml) {
            SASSERT(w <= eqs.num_eqs());
            if (w < eqs.num_eqs()) {
                expr* e = eqs.eq(w);
                m_replace.apply_substitution(x.x(), e, fml);
            }
            else {               
                for (unsigned i = 0; i < eqs.num_eqs(); ++i) {
                    m_replace.apply_substitution(eqs.eq_atom(i), m.mk_false(), fml);
                }

                for (unsigned i = 0; i < eqs.num_neqs(); ++i) {
                    m_replace.apply_substitution(eqs.neq_atom(i), m.mk_true(), fml);
                }
            }
        }


        eq_atoms& get_eqs(app* x, expr* fml) {
            eq_atoms* eqs = 0;
            VERIFY(m_eqs_cache.find(x, fml, eqs));
            return *eqs;
        }

        bool update_eqs(contains_app& contains_x, expr* fml) {
            eq_atoms* eqs = 0;
            if (m_eqs_cache.find(contains_x.x(), fml, eqs)) {
                return true;
            }
            eqs = alloc(eq_atoms, m);

            if (!update_eqs(*eqs, contains_x, fml, m_ctx.pos_atoms(), true)) {
                dealloc(eqs);
                return false;
            }
            if (!update_eqs(*eqs, contains_x, fml, m_ctx.neg_atoms(), false)) {
                dealloc(eqs);
                return false;
            }

            m_trail.push_back(contains_x.x());
            m_trail.push_back(fml);
            m_eqs_cache.insert(contains_x.x(), fml, eqs);
            return true;
        }

        bool update_eqs(eq_atoms& eqs, contains_app& contains_x, expr* fml, atom_set const& tbl, bool is_pos) {
            atom_set::iterator it = tbl.begin(), end = tbl.end();
            expr* x = contains_x.x();
            for (; it != end; ++it) {
                app* e = *it; 
                if (!contains_x(e)) {
                    continue;
                }
                if (m_util.is_lt(e)) {
                    NOT_IMPLEMENTED_YET();
                }
                expr* e1, *e2;
                if (!m.is_eq(e, e1, e2)) {
                    TRACE("quant_elim", tout << "Cannot handle: " << mk_pp(e, m) << "\n";);
                    return false;
                }
                if (x == e2) {
                    std::swap(e1, e2);
                }
                if (contains_x(e2) || x != e1) {
                    TRACE("quant_elim", tout << "Cannot handle: " << mk_pp(e, m) << "\n";);
                    return false;
                }
                if (is_pos) {
                    eqs.add_eq(e, e2);
                }
                else {
                    eqs.add_neq(e, e2);
                }
            }    
            return true;
        }

    };

    qe_solver_plugin* mk_dl_plugin(i_solver_context& ctx) {
        return alloc(dl_plugin, ctx, ctx.get_manager());
    }
}
