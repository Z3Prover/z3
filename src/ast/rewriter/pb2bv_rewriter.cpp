/*++
Copyright (c) 2016 Microsoft Corporation

Module Name:

    pb2bv_rewriter.cpp

Abstract:

    Conversion from pseudo-booleans to bit-vectors.

Author:

    Nikolaj Bjorner (nbjorner) 2016-10-23

Notes:

--*/

#include"rewriter.h"
#include"rewriter_def.h"
#include"statistics.h"
#include"pb2bv_rewriter.h"
#include"sorting_network.h"
#include"ast_util.h"
#include"ast_pp.h"
#include"lbool.h"

const unsigned g_primes[7] = { 2, 3, 5, 7, 11, 13, 17};


struct pb2bv_rewriter::imp {

    ast_manager&              m;
    params_ref                m_params;
    expr_ref_vector           m_lemmas;
    func_decl_ref_vector      m_fresh;       // all fresh variables
    unsigned_vector           m_fresh_lim;
    unsigned                  m_num_translated;

    struct card2bv_rewriter {               
        typedef expr* literal;
        typedef ptr_vector<expr> literal_vector;
        psort_nw<card2bv_rewriter> m_sort;
        ast_manager& m;
        imp&         m_imp;
        arith_util   au;
        pb_util      pb;
        bv_util      bv;
        expr_ref_vector m_trail;
        expr_ref_vector m_args;
        rational     m_k;
        vector<rational> m_coeffs;
        bool m_keep_cardinality_constraints;
        unsigned m_min_arity;

        template<lbool is_le>
        expr_ref mk_le_ge(expr_ref_vector& fmls, expr* a, expr* b, expr* bound) {
            expr_ref x(m), y(m), result(m);
            unsigned nb = bv.get_bv_size(a);
            x = bv.mk_zero_extend(1, a);
            y = bv.mk_zero_extend(1, b);
            result = bv.mk_bv_add(x, y);
            x = bv.mk_extract(nb, nb, result);
            result = bv.mk_extract(nb-1, 0, result);
            if (is_le != l_false) {
                fmls.push_back(m.mk_eq(x, bv.mk_numeral(rational::zero(), 1)));
                fmls.push_back(bv.mk_ule(result, bound));
            }
            else {
                fmls.push_back(m.mk_eq(x, bv.mk_numeral(rational::one(), 1)));
                fmls.push_back(bv.mk_ule(bound, result));
            }
            return result;

        }

        // 
        // create a circuit of size sz*log(k) 
        // by forming a binary tree adding pairs of values that are assumed <= k, 
        // and in each step we check that the result is <= k by checking the overflow
        // bit and that the non-overflow bits are <= k.
        // The procedure for checking >= k is symmetric and checking for = k is
        // achieved by checking <= k on intermediary addends and the resulting sum is = k.
        // 
        // is_le = l_true  -  <=
        // is_le = l_undef -  =
        // is_le = l_false -  >= 
        //
        template<lbool is_le>
        expr_ref mk_le_ge(unsigned sz, expr * const* args, rational const & k) {
            TRACE("pb", 
                  for (unsigned i = 0; i < sz; ++i) {
                      tout << m_coeffs[i] << "*" << mk_pp(args[i], m) << " ";
                      if (i + 1 < sz && !m_coeffs[i+1].is_neg()) tout << "+ ";
                  }
                  switch (is_le) {
                  case l_true: tout << "<= "; break;
                  case l_undef: tout << "= "; break;
                  case l_false: tout << ">= "; break;
                  }
                  tout << k << "\n";);
            if (k.is_zero()) {
                if (is_le != l_false) {
                    return expr_ref(m.mk_not(::mk_or(m, sz, args)), m);
                }
                else {
                    return expr_ref(m.mk_true(), m);
                }
            }
            if (k.is_neg()) {
                return expr_ref((is_le == l_false)?m.mk_true():m.mk_false(), m);
            }
            
#if 0
            expr_ref result(m);
            switch (is_le) {
            case l_true:  if (mk_le(sz, args, k, result)) return result; else break;
            case l_false: if (mk_ge(sz, args, k, result)) return result; else break;
            case l_undef: if (mk_eq(sz, args, k, result)) return result; else break;
            }
#endif
            // fall back to divide and conquer encoding.
            SASSERT(k.is_pos());
            expr_ref zero(m), bound(m);
            expr_ref_vector es(m), fmls(m);
            unsigned nb = k.get_num_bits();            
            zero = bv.mk_numeral(rational(0), nb);
            bound = bv.mk_numeral(k, nb);
            for (unsigned i = 0; i < sz; ++i) {
                SASSERT(!m_coeffs[i].is_neg());
                if (m_coeffs[i] > k) {
                    if (is_le != l_false) {
                        fmls.push_back(m.mk_not(args[i]));
                    }
                    else {
                        fmls.push_back(args[i]);
                    }
                }
                else {
                    es.push_back(mk_ite(args[i], bv.mk_numeral(m_coeffs[i], nb), zero));
                }
            }
            while (es.size() > 1) {
                for (unsigned i = 0; i + 1 < es.size(); i += 2) {
                    es[i/2] = mk_le_ge<is_le>(fmls, es[i].get(), es[i+1].get(), bound);
                }
                if ((es.size() % 2) == 1) {
                    es[es.size()/2] = es.back();
                }
                es.shrink((1 + es.size())/2);
            }
            switch (is_le) {
            case l_true: 
                return ::mk_and(fmls);
            case l_false:
                if (!es.empty()) {
                    fmls.push_back(bv.mk_ule(bound, es.back()));
                }
                return ::mk_or(fmls);
            case l_undef:
                if (es.empty()) {
                    fmls.push_back(m.mk_bool_val(k.is_zero()));
                }
                else {
                    fmls.push_back(m.mk_eq(bound, es.back()));
                }
                return ::mk_and(fmls);
            default:
                UNREACHABLE();
                return expr_ref(m.mk_true(), m);
            }
        }

        /**
           \brief MiniSat+ based encoding of PB constraints. 
           The procedure is described in "Translating Pseudo-Boolean Constraints into SAT "
           Niklas Een, Niklas Sörensson, JSAT 2006.
         */


        vector<rational> m_min_base;
        rational         m_min_cost;
        vector<rational> m_base;

        void create_basis(vector<rational> const& seq, rational carry_in, rational cost) {
            if (cost >= m_min_cost) {
                return;
            }
            rational delta_cost(0);
            for (unsigned i = 0; i < seq.size(); ++i) {
                delta_cost += seq[i];
            }
            if (cost + delta_cost < m_min_cost) {
                m_min_cost = cost + delta_cost;
                m_min_base = m_base;             
                m_min_base.push_back(delta_cost + rational::one());
            }
            
            for (unsigned i = 0; i < sizeof(g_primes)/sizeof(*g_primes); ++i) {
                vector<rational> seq1;
                rational p(g_primes[i]);
                rational rest = carry_in;
                // create seq1
                for (unsigned j = 0; j < seq.size(); ++j) {
                    rest += seq[j] % p;
                    if (seq[j] >= p) {
                        seq1.push_back(div(seq[j],  p));
                    }
                }
                
                m_base.push_back(p);
                create_basis(seq1, div(rest, p), cost + rest);
                m_base.pop_back();
            }
        }

        bool create_basis() {
            m_base.reset();
            m_min_cost = rational(INT_MAX);
            m_min_base.reset();
            rational cost(0);
            create_basis(m_coeffs, rational::zero(), cost);
            m_base = m_min_base;
            TRACE("pb",
                  tout << "Base: ";
                  for (unsigned i = 0; i < m_base.size(); ++i) {
                      tout << m_base[i] << " ";
                  }
                  tout << "\n";);
            return 
                !m_base.empty() && 
                m_base.back().is_unsigned() &&
                m_base.back().get_unsigned() <= 20*m_base.size();
        }

        /**
           \brief Check if 'out mod n >= lim'. 
         */
        expr_ref mod_ge(ptr_vector<expr> const& out, unsigned n, unsigned lim) {
            TRACE("pb", for (unsigned i = 0; i < out.size(); ++i) tout << mk_pp(out[i], m) << " "; tout << "\n";
                  tout << "n:" << n << " lim: " << lim << "\n";);
            if (lim == n) {
                return expr_ref(m.mk_false(), m);
            }
            if (lim == 0) {
                return expr_ref(m.mk_true(), m);
            }
            SASSERT(0 < lim && lim < n);
            expr_ref_vector ors(m);
            for (unsigned j = 0; j + lim - 1 < out.size(); j += n) {
                expr_ref tmp(m);
                tmp = out[j + lim - 1];
                if (j + n < out.size()) {
                    tmp = m.mk_and(tmp, m.mk_not(out[j + n]));
                }
                ors.push_back(tmp);
            }
            return ::mk_or(ors);
        }

        bool mk_ge(unsigned sz, expr * const* args, rational bound, expr_ref& result) {
            if (!create_basis()) return false;
            if (!bound.is_unsigned()) return false;
            vector<rational> coeffs(m_coeffs);
            result = m.mk_true();
            expr_ref_vector carry(m), new_carry(m);
            for (unsigned i = 0; i < m_base.size(); ++i) {
                rational b_i = m_base[i];
                unsigned B   = b_i.get_unsigned();
                unsigned d_i = (bound % b_i).get_unsigned();
                bound = div(bound, b_i);                
                for (unsigned j = 0; j < coeffs.size(); ++j) {
                    rational c = coeffs[j] % b_i;                    
                    SASSERT(c.is_unsigned());
                    for (unsigned k = 0; k < c.get_unsigned(); ++k) {
                        carry.push_back(args[j]);
                    }
                    coeffs[j] = div(coeffs[j], b_i);
                }
                TRACE("pb", tout << "Carry: " << carry << "\n";
                      for (unsigned j = 0; j < coeffs.size(); ++j) tout << coeffs[j] << " ";
                      tout << "\n";
                      );
                ptr_vector<expr> out;
                m_sort.sorting(carry.size(), carry.c_ptr(), out);

                expr_ref gt = mod_ge(out, B, d_i + 1);
                expr_ref ge = mod_ge(out, B, d_i);
                result = mk_or(gt, mk_and(ge, result));                
                TRACE("pb", tout << result << "\n";);

                new_carry.reset();
                for (unsigned j = B - 1; j < out.size(); j += B) {
                    new_carry.push_back(out[j]);
                }
                carry.reset();
                carry.append(new_carry);
            }
            TRACE("pb", tout << result << "\n";);
            return true;
        }

        expr_ref mk_and(expr_ref& a, expr_ref& b) {
            if (m.is_true(a)) return b;
            if (m.is_true(b)) return a;
            if (m.is_false(a)) return a;
            if (m.is_false(b)) return b;
            return expr_ref(m.mk_and(a, b), m);
        }

        expr_ref mk_or(expr_ref& a, expr_ref& b) {
            if (m.is_true(a)) return a;
            if (m.is_true(b)) return b;
            if (m.is_false(a)) return b;
            if (m.is_false(b)) return a;
            return expr_ref(m.mk_or(a, b), m);
        }

        bool mk_le(unsigned sz, expr * const* args, rational const& k, expr_ref& result) {
            expr_ref_vector args1(m);
            rational bound(-k);            
            for (unsigned i = 0; i < sz; ++i) {
                args1.push_back(mk_not(args[i]));
                bound += m_coeffs[i];
            }
            return mk_ge(sz, args1.c_ptr(), bound, result);
        }

        bool mk_eq(unsigned sz, expr * const* args, rational const& k, expr_ref& result) {
            expr_ref r1(m), r2(m);
            if (mk_ge(sz, args, k, r1) && mk_le(sz, args, k, r2)) {
                result = m.mk_and(r1, r2);
                return true;
            }
            else {
                return false;
            }
        }

        expr_ref mk_bv(func_decl * f, unsigned sz, expr * const* args) {
            decl_kind kind = f->get_decl_kind();
            rational k = pb.get_k(f);
            m_coeffs.reset();
            for (unsigned i = 0; i < sz; ++i) {
                m_coeffs.push_back(pb.get_coeff(f, i));
            }
            SASSERT(!k.is_neg());
            switch (kind) {
            case OP_PB_GE:
            case OP_AT_LEAST_K: {
                expr_ref_vector nargs(m);
                nargs.append(sz, args);
                dualize(f, nargs, k);
                SASSERT(!k.is_neg());
                return mk_le_ge<l_true>(sz, nargs.c_ptr(), k);
            }
            case OP_PB_LE:
            case OP_AT_MOST_K:
                return mk_le_ge<l_true>(sz, args, k);
            case OP_PB_EQ:
                return mk_le_ge<l_undef>(sz, args, k);
            default:
                UNREACHABLE();
                return expr_ref(m.mk_true(), m);
            }
        }

        void dualize(func_decl* f, expr_ref_vector & args, rational & k) {
            k.neg();
            for (unsigned i = 0; i < args.size(); ++i) {
                k += pb.get_coeff(f, i);
                args[i] = ::mk_not(m, args[i].get());
            }            
        }

        expr* negate(expr* e) {
            if (m.is_not(e, e)) return e;
            return m.mk_not(e);
        }
        expr* mk_ite(expr* c, expr* hi, expr* lo) {
            while (m.is_not(c, c)) {
                std::swap(hi, lo);
            }
            if (hi == lo) return hi;
            if (m.is_true(hi) && m.is_false(lo)) return c;
            if (m.is_false(hi) && m.is_true(lo)) return negate(c);
            if (m.is_true(hi)) return m.mk_or(c, lo);
            if (m.is_false(lo)) return m.mk_and(c, hi);
            if (m.is_false(hi)) return m.mk_and(negate(c), lo);
            if (m.is_true(lo)) return m.mk_implies(c, hi);
            return m.mk_ite(c, hi, lo);
        }
        
        bool is_or(func_decl* f) {
            switch (f->get_decl_kind()) {
            case OP_AT_MOST_K:
            case OP_PB_LE:
                return false;
            case OP_AT_LEAST_K:
            case OP_PB_GE: 
                return pb.get_k(f).is_one();
            case OP_PB_EQ:
                return false;
            default:
                UNREACHABLE();
                return false;
            }
        }

    public:

        card2bv_rewriter(imp& i, ast_manager& m):
            m_sort(*this),
            m(m),
            m_imp(i),
            au(m),
            pb(m),
            bv(m),
            m_trail(m),
            m_args(m),
            m_keep_cardinality_constraints(false),
            m_min_arity(2)
        {}

        bool mk_app(bool full, func_decl * f, unsigned sz, expr * const* args, expr_ref & result) {
            if (f->get_family_id() == pb.get_family_id() && mk_pb(full, f, sz, args, result)) {
                // skip
            }
            else if (au.is_le(f) && is_pb(args[0], args[1])) {
                result = mk_le_ge<l_true>(m_args.size(), m_args.c_ptr(), m_k);
            }
            else if (au.is_lt(f) && is_pb(args[0], args[1])) {
                ++m_k;
                result = mk_le_ge<l_true>(m_args.size(), m_args.c_ptr(), m_k);
            }
            else if (au.is_ge(f) && is_pb(args[1], args[0])) {
                result = mk_le_ge<l_true>(m_args.size(), m_args.c_ptr(), m_k);
            }
            else if (au.is_gt(f) && is_pb(args[1], args[0])) {
                ++m_k;
                result = mk_le_ge<l_true>(m_args.size(), m_args.c_ptr(), m_k);
            }
            else if (m.is_eq(f) && is_pb(args[0], args[1])) {
                result = mk_le_ge<l_undef>(m_args.size(), m_args.c_ptr(), m_k);
            }
            else {
                return false;
            }
            ++m_imp.m_num_translated;
            return true;
        }

        br_status mk_app_core(func_decl * f, unsigned sz, expr * const* args, expr_ref & result) {
            if (mk_app(true, f, sz, args, result)) {
                return BR_DONE;
            }
            else {
                return BR_FAILED;
            }
        }

        bool is_pb(expr* x, expr* y) {
            m_args.reset();
            m_coeffs.reset();
            m_k.reset();
            return is_pb(x, rational::one()) && is_pb(y, rational::minus_one());
        }

        bool is_pb(expr* e, rational const& mul) {
            if (!is_app(e)) {
                return false;
            }
            app* a = to_app(e);
            rational r, r1, r2;
            expr* c, *th, *el;
            unsigned sz = a->get_num_args();
            if (a->get_family_id() == au.get_family_id()) {
                switch (a->get_decl_kind()) {
                case OP_ADD:
                    for (unsigned i = 0; i < sz; ++i) {
                        if (!is_pb(a->get_arg(i), mul)) return false;
                    }
                    return true;
                case OP_SUB: {
                    if (!is_pb(a->get_arg(0), mul)) return false;
                    r = -mul;
                    for (unsigned i = 1; i < sz; ++i) {
                        if (!is_pb(a->get_arg(1), r)) return false;
                    }
                    return true;
                }
                case OP_UMINUS:
                    return is_pb(a->get_arg(0), -mul);
                case OP_NUM:
                    VERIFY(au.is_numeral(a, r));
                    m_k -= mul * r;
                    return true;
                case OP_MUL:
                    if (sz != 2) {
                        return false;
                    }
                    if (au.is_numeral(a->get_arg(0), r)) {
                        r *= mul;
                        return is_pb(a->get_arg(1), r);
                    }
                    if (au.is_numeral(a->get_arg(1), r)) {
                        r *= mul;
                        return is_pb(a->get_arg(0), r);
                    }
                    return false;
                default:
                    return false;
                }
            }
            if (m.is_ite(a, c, th, el) && au.is_numeral(th, r1) && au.is_numeral(el, r2)) {
                r1 *= mul;
                r2 *= mul;
                if (r1 < r2) {
                    m_args.push_back(::mk_not(m, c));
                    m_coeffs.push_back(r2-r1);
                    m_k -= r1;
                }
                else {
                    m_args.push_back(c);
                    m_coeffs.push_back(r1-r2);
                    m_k -= r2;
                }
                return true;
            }
            return false;
        }

        bool mk_pb(bool full, func_decl * f, unsigned sz, expr * const* args, expr_ref & result) {
            SASSERT(f->get_family_id() == pb.get_family_id());
            if (is_or(f)) {
                result = m.mk_or(sz, args);
            }
            else if (pb.is_at_most_k(f) && pb.get_k(f).is_unsigned()) {
                if (m_keep_cardinality_constraints && f->get_arity() >= m_min_arity) return false;
                result = m_sort.le(full, pb.get_k(f).get_unsigned(), sz, args);
            }
            else if (pb.is_at_least_k(f) && pb.get_k(f).is_unsigned()) {
                if (m_keep_cardinality_constraints && f->get_arity() >= m_min_arity) return false;
                result = m_sort.ge(full, pb.get_k(f).get_unsigned(), sz, args);
            }
            else if (pb.is_eq(f) && pb.get_k(f).is_unsigned() && pb.has_unit_coefficients(f)) {
                if (m_keep_cardinality_constraints && f->get_arity() >= m_min_arity) return false;
                result = m_sort.eq(full, pb.get_k(f).get_unsigned(), sz, args);
            }
            else if (pb.is_le(f) && pb.get_k(f).is_unsigned() && pb.has_unit_coefficients(f)) {
                if (m_keep_cardinality_constraints && f->get_arity() >= m_min_arity) return false;
                result = m_sort.le(full, pb.get_k(f).get_unsigned(), sz, args);
            }
            else if (pb.is_ge(f) && pb.get_k(f).is_unsigned() && pb.has_unit_coefficients(f)) {
                if (m_keep_cardinality_constraints && f->get_arity() >= m_min_arity) return false;
                result = m_sort.ge(full, pb.get_k(f).get_unsigned(), sz, args);
            }
            else {
                result = mk_bv(f, sz, args);
            }
            return true;
        }
   
        // definitions used for sorting network
        literal mk_false() { return m.mk_false(); }
        literal mk_true() { return m.mk_true(); }
        literal mk_max(literal a, literal b) { return trail(m.mk_or(a, b)); }
        literal mk_min(literal a, literal b) { return trail(m.mk_and(a, b)); }
        literal mk_not(literal a) { if (m.is_not(a,a)) return a; return trail(m.mk_not(a)); }

        std::ostream& pp(std::ostream& out, literal lit) {  return out << mk_ismt2_pp(lit, m);  }
        
        literal trail(literal l) {
            m_trail.push_back(l);
            return l;
        }
        literal fresh() {
            expr_ref fr(m.mk_fresh_const("sn", m.mk_bool_sort()), m);
            m_imp.m_fresh.push_back(to_app(fr)->get_decl());
            return trail(fr);
        }
        
        void mk_clause(unsigned n, literal const* lits) {
            m_imp.m_lemmas.push_back(::mk_or(m, n, lits));
        }        

        void keep_cardinality_constraints(bool f) {
            m_keep_cardinality_constraints = f;
        }
    };

    struct card2bv_rewriter_cfg : public default_rewriter_cfg {
        card2bv_rewriter m_r;
        bool rewrite_patterns() const { return false; }
        bool flat_assoc(func_decl * f) const { return false; }
        br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
            result_pr = 0;
            return m_r.mk_app_core(f, num, args, result);
        }
        card2bv_rewriter_cfg(imp& i, ast_manager & m):m_r(i, m) {}
        void keep_cardinality_constraints(bool f) { m_r.keep_cardinality_constraints(f); }
    };
    
    class card_pb_rewriter : public rewriter_tpl<card2bv_rewriter_cfg> {
    public:
        card2bv_rewriter_cfg m_cfg;
        card_pb_rewriter(imp& i, ast_manager & m):
            rewriter_tpl<card2bv_rewriter_cfg>(m, false, m_cfg),
            m_cfg(i, m) {}
        void keep_cardinality_constraints(bool f) { m_cfg.keep_cardinality_constraints(f); }
    };

    card_pb_rewriter m_rw;
    
    imp(ast_manager& m, params_ref const& p): 
        m(m), m_params(p), m_lemmas(m),
        m_fresh(m),
        m_num_translated(0), 
        m_rw(*this, m) {
        m_rw.keep_cardinality_constraints(p.get_bool("keep_cardinality_constraints", false));
    }

    void updt_params(params_ref const & p) {
        m_params.append(p);
        m_rw.keep_cardinality_constraints(m_params.get_bool("keep_cardinality_constraints", false));
    }
    void collect_param_descrs(param_descrs& r) const {
        r.insert("keep_cardinality_constraints", CPK_BOOL, "(default: true) retain cardinality constraints (don't bit-blast them) and use built-in cardinality solver");
    }

    unsigned get_num_steps() const { return m_rw.get_num_steps(); }
    void cleanup() { m_rw.cleanup(); }
    void operator()(expr * e, expr_ref & result, proof_ref & result_proof) {
        m_rw(e, result, result_proof);
    }
    void push() {
        m_fresh_lim.push_back(m_fresh.size());
    }
    void pop(unsigned num_scopes) {
        SASSERT(m_lemmas.empty()); // lemmas must be flushed before pop.
        if (num_scopes > 0) {
            SASSERT(num_scopes <= m_fresh_lim.size());
            unsigned new_sz = m_fresh_lim.size() - num_scopes;
            unsigned lim = m_fresh_lim[new_sz];
            m_fresh.resize(lim);
            m_fresh_lim.resize(new_sz);
        }
        m_rw.reset();
    }

    void flush_side_constraints(expr_ref_vector& side_constraints) { 
        side_constraints.append(m_lemmas);  
        m_lemmas.reset(); 
    }

    void collect_statistics(statistics & st) const {
        st.update("pb-aux-variables", m_fresh.size());
        st.update("pb-aux-clauses", m_rw.m_cfg.m_r.m_sort.m_stats.m_num_compiled_clauses);
    }

};


pb2bv_rewriter::pb2bv_rewriter(ast_manager & m, params_ref const& p) {  m_imp = alloc(imp, m, p); }
pb2bv_rewriter::~pb2bv_rewriter() { dealloc(m_imp); }
void pb2bv_rewriter::updt_params(params_ref const & p) { m_imp->updt_params(p); }
void pb2bv_rewriter::collect_param_descrs(param_descrs& r) const { m_imp->collect_param_descrs(r); }

ast_manager & pb2bv_rewriter::m() const { return m_imp->m; }
unsigned pb2bv_rewriter::get_num_steps() const { return m_imp->get_num_steps(); }
void pb2bv_rewriter::cleanup() { ast_manager& mgr = m(); params_ref p = m_imp->m_params; dealloc(m_imp); m_imp = alloc(imp, mgr, p);  }
func_decl_ref_vector const& pb2bv_rewriter::fresh_constants() const { return m_imp->m_fresh; }
void pb2bv_rewriter::operator()(expr * e, expr_ref & result, proof_ref & result_proof) { (*m_imp)(e, result, result_proof); }
void pb2bv_rewriter::push() { m_imp->push(); }
void pb2bv_rewriter::pop(unsigned num_scopes) { m_imp->pop(num_scopes); }
void pb2bv_rewriter::flush_side_constraints(expr_ref_vector& side_constraints) { m_imp->flush_side_constraints(side_constraints); } 
unsigned pb2bv_rewriter::num_translated() const { return m_imp->m_num_translated; }


void pb2bv_rewriter::collect_statistics(statistics & st) const { m_imp->collect_statistics(st); }
