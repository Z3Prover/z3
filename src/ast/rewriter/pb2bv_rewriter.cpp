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

#include "ast/rewriter/rewriter.h"
#include "ast/rewriter/rewriter_def.h"
#include "util/statistics.h"
#include "ast/rewriter/pb2bv_rewriter.h"
#include "util/sorting_network.h"
#include "ast/ast_util.h"
#include "ast/ast_pp.h"
#include "util/lbool.h"
#include "util/uint_set.h"
#include "util/gparams.h"

const unsigned g_primes[7] = { 2, 3, 5, 7, 11, 13, 17};


struct pb2bv_rewriter::imp {

    ast_manager&              m;
    params_ref                m_params;
    expr_ref_vector           m_lemmas;
    func_decl_ref_vector      m_fresh;       // all fresh variables
    unsigned_vector           m_fresh_lim;
    unsigned                  m_num_translated;
    unsigned                  m_compile_bv;
    unsigned                  m_compile_card;

    struct card2bv_rewriter {               
        typedef expr* pliteral;
        typedef ptr_vector<expr> pliteral_vector;
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
        symbol m_pb_solver;
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

        typedef std::pair<rational, expr_ref> ca;

        struct compare_coeffs {
            bool operator()(ca const& x, ca const& y) const {
                return x.first > y.first;
            }
        };

        void sort_args() {
            vector<ca> cas;
            for (unsigned i = 0; i < m_args.size(); ++i) {
                cas.push_back(std::make_pair(m_coeffs[i], expr_ref(m_args[i].get(), m)));
            }
            std::sort(cas.begin(), cas.end(), compare_coeffs());
            m_coeffs.reset();
            m_args.reset();
            for (ca const& ca : cas) {
                m_coeffs.push_back(ca.first);
                m_args.push_back(ca.second);
            }
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
        expr_ref mk_le_ge(rational const & k) {
            //sort_args();
            unsigned sz = m_args.size();
            expr * const* args = m_args.c_ptr();
            TRACE("pb", 
                  for (unsigned i = 0; i < sz; ++i) {
                      tout << m_coeffs[i] << "*" << mk_pp(args[i], m) << " ";
                      if (i + 1 < sz && !m_coeffs[i+1].is_neg()) tout << "+ ";
                  }
                  switch (is_le) {
                  case l_true:  tout << "<= "; break;
                  case l_undef: tout << "= "; break;
                  case l_false: tout << ">= "; break;
                  }
                  tout << k << "\n";);

            if (k.is_zero()) {
                if (is_le != l_false) {
                    return expr_ref(m.mk_not(::mk_or(m_args)), m);
                }
                else {
                    return expr_ref(m.mk_true(), m);
                }
            }
            if (k.is_neg()) {
                return expr_ref((is_le == l_false)?m.mk_true():m.mk_false(), m);
            }

            if (m_pb_solver == "totalizer") {
                expr_ref result(m);
                switch (is_le) {
                case l_true:  if (mk_le_tot(sz, args, k, result)) return result; else break;
                case l_false: if (mk_ge_tot(sz, args, k, result)) return result; else break;
                case l_undef: break;
                }
            }
            
            if (m_pb_solver == "sorting") {
                expr_ref result(m);
                switch (is_le) {
                case l_true:  if (mk_le(sz, args, k, result)) return result; else break;
                case l_false: if (mk_ge(sz, args, k, result)) return result; else break;
                case l_undef: if (mk_eq(sz, args, k, result)) return result; else break;
                }
            }

            if (m_pb_solver == "segmented") {
                expr_ref result(m);
                switch (is_le) {
                case l_true:  return mk_seg_le(k);
                case l_false: return mk_seg_ge(k);
                case l_undef: break;
                }
            }

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
           \brief Totalizer encoding. Based on a version by Miguel.
         */

        bool mk_le_tot(unsigned sz, expr * const * args, rational const& _k, expr_ref& result) {
            SASSERT(sz == m_coeffs.size());
            if (!_k.is_unsigned() || sz == 0) return false;
            unsigned k = _k.get_unsigned();
            expr_ref_vector args1(m);
            rational bound;
            flip(sz, args, args1, _k, bound);
            if (bound.get_unsigned() < k) {
                return mk_ge_tot(sz, args1.c_ptr(), bound, result);
            }
            if (k > 20) {
                return false;
            }
            result = m.mk_not(bounded_addition(sz, args, k + 1));
            TRACE("pb", tout << result << "\n";);
            return true;
        }

        bool mk_ge_tot(unsigned sz, expr * const * args, rational const& _k, expr_ref& result) {
            SASSERT(sz == m_coeffs.size());
            if (!_k.is_unsigned() || sz == 0) return false;
            unsigned k = _k.get_unsigned();
            expr_ref_vector args1(m);
            rational bound;
            flip(sz, args, args1, _k, bound);
            if (bound.get_unsigned() < k) {
                return mk_le_tot(sz, args1.c_ptr(), bound, result);
            }
            if (k > 20) {
                return false;
            }
            result = bounded_addition(sz, args, k);
            TRACE("pb", tout << result << "\n";);
            return true;
        }

        void flip(unsigned sz, expr* const* args, expr_ref_vector& args1, rational const& k, rational& bound) {
            bound = -k;
            for (unsigned i = 0; i < sz; ++i) {
                args1.push_back(mk_not(args[i]));
                bound += m_coeffs[i];
            }
        }

        expr_ref bounded_addition(unsigned sz, expr * const * args, unsigned k) {
            SASSERT(sz > 0);
            expr_ref result(m);
            vector<expr_ref_vector> es;
            vector<unsigned_vector> coeffs;
            for (unsigned i = 0; i < m_coeffs.size(); ++i) {
                unsigned_vector v;
                expr_ref_vector e(m);
                unsigned c = m_coeffs[i].get_unsigned();
                v.push_back(c >= k ? k : c);
                e.push_back(args[i]);   
                es.push_back(e);
                coeffs.push_back(v);
            }
            while (es.size() > 1) {
                for (unsigned i = 0; i + 1 < es.size(); i += 2) {
                    expr_ref_vector o(m);
                    unsigned_vector oc;
                    tot_adder(es[i], coeffs[i], es[i + 1], coeffs[i + 1], k, o, oc);
                    es[i / 2].set(o);
                    coeffs[i / 2] = oc;
                }
                if ((es.size() % 2) == 1) {
                    es[es.size() / 2].set(es.back());
                    coeffs[es.size() / 2] = coeffs.back();
                }
                es.shrink((1 + es.size())/2);
                coeffs.shrink((1 + coeffs.size())/2);
            }
            SASSERT(coeffs.size() == 1);
            SASSERT(coeffs[0].back() <= k);
            if (coeffs[0].back() == k) {
                result = es[0].back();
            }
            else {
                result = m.mk_false();
            }
            return result;
        }

        void tot_adder(expr_ref_vector const& l, unsigned_vector const& lc,
                       expr_ref_vector const& r, unsigned_vector const& rc,
                       unsigned k,
                       expr_ref_vector& o, unsigned_vector & oc) {
            SASSERT(l.size() == lc.size());
            SASSERT(r.size() == rc.size());
            uint_set sums;
            vector<expr_ref_vector> trail;
            u_map<unsigned> sum2def;
            for (unsigned i = 0; i <= l.size(); ++i) {
                for (unsigned j = (i == 0) ? 1 : 0; j <= r.size(); ++j) {
                    unsigned sum = std::min(k, ((i == 0) ? 0 : lc[i - 1]) + ((j == 0) ? 0 : rc[j - 1]));
                    sums.insert(sum);                        
                }
            }
            for (unsigned u : sums) {
                oc.push_back(u);
            }            
            std::sort(oc.begin(), oc.end());
            DEBUG_CODE(                
                for (unsigned i = 0; i + 1 < oc.size(); ++i) {
                    SASSERT(oc[i] < oc[i+1]);
                });
            for (unsigned i = 0; i < oc.size(); ++i) {
                sum2def.insert(oc[i], i);
                trail.push_back(expr_ref_vector(m));
            }
            for (unsigned i = 0; i <= l.size(); ++i) {
                for (unsigned j = (i == 0) ? 1 : 0; j <= r.size(); ++j) {
                    if (i != 0 && j != 0 && (lc[i - 1] >= k || rc[j - 1] >= k)) continue;
                    unsigned sum = std::min(k, ((i == 0) ? 0 : lc[i - 1]) + ((j == 0) ? 0 : rc[j - 1]));
                    expr_ref_vector ands(m);
                    if (i != 0) {
                        ands.push_back(l[i - 1]);
                    }
                    if (j != 0) {
                        ands.push_back(r[j - 1]);
                    }
                    trail[sum2def.find(sum)].push_back(::mk_and(ands));
                }
            }
            for (unsigned i = 0; i < oc.size(); ++i) {
                o.push_back(::mk_or(trail[sum2def.find(oc[i])]));
            }
        }

        /**
           \brief MiniSat+ based encoding of PB constraints. 
           Translating Pseudo-Boolean Constraints into SAT,
           Niklas Een, Niklas Soerensson, JSAT 2006.
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
                if (j + n - 1 < out.size()) {
                    tmp = m.mk_and(tmp, m.mk_not(out[j + n - 1]));
                }
                ors.push_back(tmp);
            }
            return ::mk_or(ors);
        }

        // x0 + 5x1 + 3x2 >= k
        // x0 x1 x1 -> s0 s1 s2
        // s2 x1 x2 -> s3 s4 s5
        // k = 7: s5 or (s4 & not s2 & s0)
        // k = 6: s4
        // k = 5: s4 or (s3 & not s2 & s1)
        // k = 4: s4 or (s3 & not s2 & s0)
        // k = 3: s3
        // 
        bool mk_ge(unsigned sz, expr * const* args, rational bound, expr_ref& result) {
            if (!create_basis()) return false;
            if (!bound.is_unsigned()) return false;
            vector<rational> coeffs(m_coeffs);
            result = m.mk_true();
            expr_ref_vector carry(m), new_carry(m);
            m_base.push_back(bound + rational::one());
            for (rational b_i : m_base) {
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
                      for (auto c : coeffs) tout << c << " ";
                      tout << "\n";
                      );
                ptr_vector<expr> out;
                m_sort.sorting(carry.size(), carry.c_ptr(), out);
                
                expr_ref gt = mod_ge(out, B, d_i + 1);
                expr_ref ge = mod_ge(out, B, d_i);
                result = mk_and(ge, result);
                result = mk_or(gt, result);                
                TRACE("pb", tout << "b: " << b_i << " d: " << d_i << " gt: " << gt << " ge: " << ge << " " << result << "\n";);

                new_carry.reset();
                for (unsigned j = B - 1; j < out.size(); j += B) {
                    new_carry.push_back(out[j]);
                }
                carry.reset();
                carry.append(new_carry);
            }
            TRACE("pb", tout << "bound: " << bound << " Carry: " << carry << " result: " << result << "\n";);
            return true;
        }

        /**
           \brief Segment based encoding.
           The PB terms are partitoned into segments, such that each segment contains arguments with the same cofficient.
           The segments are sorted, such that the segment with highest coefficient is first.
           Then for each segment create circuits based on sorting networks the arguments of the segment.           
        */

        expr_ref mk_seg_ge(rational const& k) {
            rational bound(-k);
            for (unsigned i = 0; i < m_args.size(); ++i) {
                m_args[i] = mk_not(m_args[i].get());
                bound += m_coeffs[i];
            }
            return mk_seg_le(bound);
        }
        
        expr_ref mk_seg_le(rational const& k) {
            sort_args();
            unsigned sz = m_args.size();            
            expr* const* args = m_args.c_ptr();

            // Create sorted entries.
            vector<ptr_vector<expr>> outs;
            vector<rational> coeffs;
            for (unsigned i = 0, seg_size = 0; i < sz; i += seg_size) {
                seg_size = segment_size(i);
                ptr_vector<expr> out;
                m_sort.sorting(seg_size, args + i, out);
                out.push_back(m.mk_false());
                outs.push_back(out);
                coeffs.push_back(m_coeffs[i]);
            }
            return mk_seg_le_rec(outs, coeffs, 0, k);
        }

        expr_ref mk_seg_le_rec(vector<ptr_vector<expr>> const& outs, vector<rational> const& coeffs, unsigned i, rational const& k) {
            rational const& c = coeffs[i];
            ptr_vector<expr> const& out = outs[i];     
            if (k.is_neg()) {
                return expr_ref(m.mk_false(), m);
            }
            if (i == outs.size()) {
                return expr_ref(m.mk_true(), m);
            }
            if (i + 1 == outs.size() && k >= rational(out.size()-1)*c) {
                return expr_ref(m.mk_true(), m);
            }
            expr_ref_vector fmls(m);
            fmls.push_back(m.mk_implies(m.mk_not(out[0]), mk_seg_le_rec(outs, coeffs, i + 1, k)));
            rational k1;
            for (unsigned j = 0; j + 1 < out.size(); ++j) {
                k1 = k - rational(j+1)*c;
                if (k1.is_neg()) {
                    fmls.push_back(m.mk_not(out[j]));
                    break;
                }
                fmls.push_back(m.mk_implies(m.mk_and(out[j], m.mk_not(out[j+1])), mk_seg_le_rec(outs, coeffs, i + 1, k1)));
            }
            return ::mk_and(fmls);
        }

        // The number of arguments with the same coefficient.
        unsigned segment_size(unsigned start) const {
            unsigned i = start;
            while (i < m_args.size() && m_coeffs[i] == m_coeffs[start]) ++i;
            return i - start;
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
            ++m_imp.m_compile_bv;
            decl_kind kind = f->get_decl_kind();
            rational k = pb.get_k(f);
            m_coeffs.reset();
            m_args.reset();
            for (unsigned i = 0; i < sz; ++i) {
                m_coeffs.push_back(pb.get_coeff(f, i));
                m_args.push_back(args[i]);
            }
            CTRACE("pb", k.is_neg(), tout << expr_ref(m.mk_app(f, sz, args), m) << "\n";);
            SASSERT(!k.is_neg());
            switch (kind) {
            case OP_PB_GE:
            case OP_AT_LEAST_K: {
                dualize(f, m_args, k);
                SASSERT(!k.is_neg());
                return mk_le_ge<l_true>(k);
            }
            case OP_PB_LE:
            case OP_AT_MOST_K:
                return mk_le_ge<l_true>(k);
            case OP_PB_EQ:
                return mk_le_ge<l_undef>(k);
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
            m_pb_solver(symbol("solver")),
            m_min_arity(9)
        {}

        void set_pb_solver(symbol const& s) { m_pb_solver = s; }

        bool mk_app(bool full, func_decl * f, unsigned sz, expr * const* args, expr_ref & result) {
            if (f->get_family_id() == pb.get_family_id() && mk_pb(full, f, sz, args, result)) {
                // skip
            }
            else if (au.is_le(f) && is_pb(args[0], args[1])) {
                result = mk_le_ge<l_true>(m_k);
            }
            else if (au.is_lt(f) && is_pb(args[0], args[1])) {
                ++m_k;
                result = mk_le_ge<l_true>(m_k);
            }
            else if (au.is_ge(f) && is_pb(args[1], args[0])) {
                result = mk_le_ge<l_true>(m_k);
            }
            else if (au.is_gt(f) && is_pb(args[1], args[0])) {
                ++m_k;
                result = mk_le_ge<l_true>(m_k);
            }
            else if (m.is_eq(f) && is_pb(args[0], args[1])) {
                result = mk_le_ge<l_undef>(m_k);
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

        bool mk_app(bool full, expr* e, expr_ref& r) {
            app* a;
            return (is_app(e) && (a = to_app(e), mk_app(full, a->get_decl(), a->get_num_args(), a->get_args(), r)));
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
                ++m_imp.m_compile_card;
            }
            else if (pb.is_at_least_k(f) && pb.get_k(f).is_unsigned()) {
                if (m_keep_cardinality_constraints && f->get_arity() >= m_min_arity) return false;
                result = m_sort.ge(full, pb.get_k(f).get_unsigned(), sz, args);
                ++m_imp.m_compile_card;
            }
            else if (pb.is_eq(f) && pb.get_k(f).is_unsigned() && pb.has_unit_coefficients(f)) {
                if (m_keep_cardinality_constraints && f->get_arity() >= m_min_arity) return false;
                result = m_sort.eq(full, pb.get_k(f).get_unsigned(), sz, args);
                ++m_imp.m_compile_card;
            }
            else if (pb.is_le(f) && pb.get_k(f).is_unsigned() && pb.has_unit_coefficients(f)) {
                if (m_keep_cardinality_constraints && f->get_arity() >= m_min_arity) return false;
                result = m_sort.le(full, pb.get_k(f).get_unsigned(), sz, args);
                ++m_imp.m_compile_card;
            }
            else if (pb.is_ge(f) && pb.get_k(f).is_unsigned() && pb.has_unit_coefficients(f)) {
                if (m_keep_cardinality_constraints && f->get_arity() >= m_min_arity) return false;
                result = m_sort.ge(full, pb.get_k(f).get_unsigned(), sz, args);
                ++m_imp.m_compile_card;
            }
            else if (pb.is_eq(f) && pb.get_k(f).is_unsigned() && has_small_coefficients(f) && m_pb_solver == "solver") {
                return false;
            }
            else if (pb.is_le(f) && pb.get_k(f).is_unsigned() && has_small_coefficients(f) && m_pb_solver == "solver") {
                return false;
            }
            else if (pb.is_ge(f) && pb.get_k(f).is_unsigned() && has_small_coefficients(f) && m_pb_solver == "solver") {
                return false;
            }
            else {
                result = mk_bv(f, sz, args);
            }
            TRACE("pb", tout << "full: " << full << " " << expr_ref(m.mk_app(f, sz, args), m) << " " << result << "\n";
                  );
            return true;
        }

        bool has_small_coefficients(func_decl* f) {
            unsigned sz = f->get_arity();
            unsigned sum = 0;
            for (unsigned i = 0; i < sz; ++i) {
                rational c = pb.get_coeff(f, i);
                if (!c.is_unsigned()) return false;
                unsigned sum1 = sum + c.get_unsigned();
                if (sum1 < sum) return false;
                sum = sum1;
            }
            return true;
        }
   
        // definitions used for sorting network
        pliteral mk_false() { return m.mk_false(); }
        pliteral mk_true() { return m.mk_true(); }
        pliteral mk_max(unsigned n, pliteral const* lits) { return trail(m.mk_or(n, lits)); }
        pliteral mk_min(unsigned n, pliteral const* lits) { return trail(m.mk_and(n, lits)); }
        pliteral mk_not(pliteral a) { if (m.is_not(a,a)) return a; return trail(m.mk_not(a)); }

        std::ostream& pp(std::ostream& out, pliteral lit) {  return out << mk_ismt2_pp(lit, m);  }
        
        pliteral trail(pliteral l) {
            m_trail.push_back(l);
            return l;
        }
        pliteral fresh(char const* n) {                      
            expr_ref fr(m.mk_fresh_const(n, m.mk_bool_sort()), m);
            m_imp.m_fresh.push_back(to_app(fr)->get_decl());
            return trail(fr);
        }
        
        void mk_clause(unsigned n, pliteral const* lits) {
            m_imp.m_lemmas.push_back(::mk_or(m, n, lits));
        }        

        void keep_cardinality_constraints(bool f) {
            m_keep_cardinality_constraints = f;
        }

        void set_cardinality_encoding(sorting_network_encoding enc) { m_sort.cfg().m_encoding = enc; }

    };

    struct card2bv_rewriter_cfg : public default_rewriter_cfg {
        card2bv_rewriter m_r;
        bool rewrite_patterns() const { return false; }
        bool flat_assoc(func_decl * f) const { return false; }
        br_status reduce_app(func_decl * f, unsigned num, expr * const * args, expr_ref & result, proof_ref & result_pr) {
            result_pr = nullptr;
            return m_r.mk_app_core(f, num, args, result);
        }
        card2bv_rewriter_cfg(imp& i, ast_manager & m):m_r(i, m) {}
        void keep_cardinality_constraints(bool f) { m_r.keep_cardinality_constraints(f); }
        void set_pb_solver(symbol const& s) { m_r.set_pb_solver(s); }
        void set_cardinality_encoding(sorting_network_encoding enc) { m_r.set_cardinality_encoding(enc); }

    };
    
    class card_pb_rewriter : public rewriter_tpl<card2bv_rewriter_cfg> {
    public:
        card2bv_rewriter_cfg m_cfg;
        card_pb_rewriter(imp& i, ast_manager & m):
            rewriter_tpl<card2bv_rewriter_cfg>(m, false, m_cfg),
            m_cfg(i, m) {}
        void keep_cardinality_constraints(bool f) { m_cfg.keep_cardinality_constraints(f); }
        void set_pb_solver(symbol const& s) { m_cfg.set_pb_solver(s); }
        void set_cardinality_encoding(sorting_network_encoding e) { m_cfg.set_cardinality_encoding(e); }
        void rewrite(bool full, expr* e, expr_ref& r, proof_ref& p) {
            expr_ref ee(e, m());
            if (m_cfg.m_r.mk_app(full, e, r)) {
                ee = r;
                // mp proof?
            }
            (*this)(ee, r, p);
        }
    };

    card_pb_rewriter m_rw;
    
    bool keep_cardinality() const {
        params_ref const& p = m_params;
        return 
            p.get_bool("keep_cardinality_constraints", false) ||
            p.get_bool("sat.cardinality.solver", false) ||
            p.get_bool("cardinality.solver", false) || 
            gparams::get_module("sat").get_bool("cardinality.solver", false);
    }

    symbol pb_solver() const {
        params_ref const& p = m_params;
        symbol s = p.get_sym("sat.pb.solver", symbol());
        if (s != symbol()) return s;
        s = p.get_sym("pb.solver", symbol());
        if (s != symbol()) return s;
        return gparams::get_module("sat").get_sym("pb.solver", symbol("solver"));
    }

    sorting_network_encoding cardinality_encoding() const {
        symbol enc = m_params.get_sym("cardinality.encoding", symbol());
        if (enc == symbol()) {
            enc = gparams::get_module("sat").get_sym("cardinality.encoding", symbol());
        }
        if (enc == symbol("grouped")) return sorting_network_encoding::grouped_at_most;
        if (enc == symbol("bimander")) return sorting_network_encoding::bimander_at_most;
        if (enc == symbol("ordered")) return sorting_network_encoding::ordered_at_most;
        if (enc == symbol("unate")) return sorting_network_encoding::unate_at_most;
        if (enc == symbol("circuit")) return sorting_network_encoding::circuit_at_most;
        return grouped_at_most;
    }
    

    imp(ast_manager& m, params_ref const& p): 
        m(m), m_params(p), m_lemmas(m),
        m_fresh(m),
        m_num_translated(0), 
        m_rw(*this, m) {
        updt_params(p);
        m_compile_bv = 0;
        m_compile_card = 0;
    }

    void updt_params(params_ref const & p) {
        m_params.append(p);
        m_rw.keep_cardinality_constraints(keep_cardinality());
        m_rw.set_pb_solver(pb_solver());
        m_rw.set_cardinality_encoding(cardinality_encoding());
    }

    void collect_param_descrs(param_descrs& r) const {
        r.insert("keep_cardinality_constraints", CPK_BOOL, "(default: false) retain cardinality constraints (don't bit-blast them) and use built-in cardinality solver");
        r.insert("pb.solver", CPK_SYMBOL, "(default: solver) retain pb constraints (don't bit-blast them) and use built-in pb solver");
    }

    unsigned get_num_steps() const { return m_rw.get_num_steps(); }
    void cleanup() { m_rw.cleanup(); }
    void operator()(bool full, expr * e, expr_ref & result, proof_ref & result_proof) {
        // m_rw(e, result, result_proof);
        m_rw.rewrite(full, e, result, result_proof);
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
        st.update("pb-compile-bv", m_compile_bv);
        st.update("pb-compile-card", m_compile_card);
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
void pb2bv_rewriter::operator()(bool full, expr * e, expr_ref & result, proof_ref & result_proof) { (*m_imp)(full, e, result, result_proof); }
void pb2bv_rewriter::push() { m_imp->push(); }
void pb2bv_rewriter::pop(unsigned num_scopes) { m_imp->pop(num_scopes); }
void pb2bv_rewriter::flush_side_constraints(expr_ref_vector& side_constraints) { m_imp->flush_side_constraints(side_constraints); } 
unsigned pb2bv_rewriter::num_translated() const { return m_imp->m_num_translated; }


void pb2bv_rewriter::collect_statistics(statistics & st) const { m_imp->collect_statistics(st); }
