/*++
Copyright (c) 2014 Microsoft Corporation

Module Name:

    doc.cpp

Abstract:

    difference of cubes.

Author:

    Nuno Lopes (a-nlopes) 2013-03-01
    Nikolaj Bjorner (nbjorner) 2014-09-15

Revision History:

    Based on ternary_diff_bitvector by Nuno Lopes.

--*/

#include "doc.h"
void doc_manager::reset() {
}
doc* doc_manager::allocate() {
    return 0;
}
doc* doc_manager::allocate1() {
    return 0;
}
doc* doc_manager::allocate0() {
    return 0;                                                
}
doc* doc_manager::allocateX() {
    return 0;
}
doc* doc_manager::allocate(doc const& src) {
    return 0;
}
doc* doc_manager::allocate(uint64 n) {
    return 0;
}
doc* doc_manager::allocate(rational const& r) {
    return 0;
}
doc* doc_manager::allocate(uint64 n, unsigned hi, unsigned lo) {
    return 0;
}
doc* doc_manager::allocate(doc, unsigned const* permutation) {
    return 0;
}
void doc_manager::deallocate(doc* src) {
}
void doc_manager::copy(doc& dst, doc const& src) const {
}
doc& doc_manager::fill0(doc& src) const {
    return src;
}
doc& doc_manager::fill1(doc& src) const {
    return src;
}
doc& doc_manager::fillX(doc& src) const {
    return src;
}
bool doc_manager::set_and(doc& dst, doc const& src) const {
    return false;
}
bool doc_manager::fold_neg(doc& dst) {
 start_over:
    for (unsigned i = 0; i < dst.neg().size(); ++i) {
        unsigned index;
        unsigned count = diff_by_012(dst.pos(), dst.neg()[i], index);
        if (count != 2) {
            if (count == 0) {
                return false;
            }
            else if (count == 3) {
                dst.neg().erase(tbvm(), i);
                --i;
            }
            else { // count == 1:
                dst.pos().set(index, neg(dst.neg()[i][index]));
                dst.neg().erase(tbvm(), i);
                goto start_over;
            }
        }
    }
    return true;
}

unsigned doc_manager::diff_by_012(tbv const& pos, tbv const& neg, unsigned& index) {
    unsigned n = num_tbits();
    unsigned count = 0;
    for (unsigned i = 0; i < n; ++i) {
        tbit b1 = pos[i];
        tbit b2 = neg[i];
        SASSERT(b1 != BIT_z && b2 != BIT_z);
        if (b1 != b2) {
            if (count == 1) return 2;
            if (b1 == BIT_x) {
                index = i;
                count = 1;
            }
            else if (b2 != BIT_x) {
                return 3;
            }
        }
    }
    return count;
}
doc* doc_manager::project(unsigned n, bool const* to_delete, doc const& src) {
    tbv* p = tbvm().project(n, to_delete, src.pos());
    if (src.neg().is_empty()) {
        // build doc from p.
        return 0;
    }
    ptr_vector<tbv> todo;
#if 0
    // tbv & ~tbv1 & ~tbv2 & ..
    // Semantics of ~tbv1 is that it is a clause of literals.
    //   indices where BIT_1 is set are negative.
    //   indices where BIT_0 is set are positive.
    // The first loop is supposed to project tbv_i directly
    // when some safety condition is met.
    // The second loop handles the remaining tbv_i that
    // don't meet the safety condition.
    for (unsigned i = 0; i < src.neg().size(); ++i) {
        if (can_project_neg(n, to_delete, src.neg()[i])) {
            
        }
    }
#endif
#if 0
    // REVIEW: what is the spec for this code?
    ternary_diff_bitvector TBV(*this);
    if (!TBV.fold_neg())
        return false;
    
    std::set<ternary_bitvector*> todo;
    cpy_bits_t cpy_bits;
    ternary_bitvector newneg;
    for (union_ternary_bitvector<ternary_bitvector>::iterator I = TBV.m_neg.begin(),
             E = TBV.m_neg.end(); I != E; ++I) {
        // check if subtract TBV should be skiped
        for (unsigned i = 0; i < delcols.size()-1; ++i) {
            unsigned idx = delcols[i];
            if (I->get(idx) != TBV.m_pos.get(idx)) { // xx \ 1x
                if (analyze_copy_bit(TBV.m_pos, *I, delcols, cpy_bits))
                    todo.insert(&*I);
                goto skip_row;
            }
        }
        
        newneg.reset();
        I->project(delcols, new_size, newneg);
        result.m_neg.add_fact(newneg);
    skip_row:   ;
    }
    
    if (!todo.empty()) {
        for (std::set<ternary_bitvector*>::iterator I = todo.begin(),
                 E = todo.end(); I != E; ++I) {
            for (unsigned i = 0; i < delcols.size()-1; ++i) {
                unsigned idx = delcols[i];
                if ((*I)->get(idx) != TBV.m_pos.get(idx)) {
                    cpy_bits_t::iterator II = cpy_bits.find(idx);
                    if (II == cpy_bits.end())
                        goto skip_bv;
                    
                    unsigned idx_keep = II->second.first;
                    unsigned cpy_val = II->second.second;
                    
                    if (!((*I)->get(idx) & cpy_val) || (*I)->get(idx_keep) != BIT_x)
                        goto skip_bv;
                    
                    (*I)->set(idx_keep, (*I)->get(idx));
                }
            }
            
            newneg.reset();
            (*I)->project(delcols, new_size, newneg);
            result.m_neg.add_fact(newneg);
        skip_bv:        ;
        }
    }

    return !result.is_empty();


    // idx_del -> <idx_keep, val>
    // val -> BIT_*
    typedef std::map<unsigned, std::pair<unsigned, unsigned char> > cpy_bits_t;

    static bool analyze_copy_bit(const ternary_bitvector& pos, const ternary_bitvector& neg,
                                 const unsigned_vector& delcols, cpy_bits_t& cpy_bits) {
      unsigned *del = delcols.c_ptr();
      bool got_del_col = false, got_keep_col = false;
      unsigned del_col = 0, keep_col = 0;

      for (unsigned i = 0; i < pos.size(); ++i) {
        if (pos.get(i) != neg.get(i)) {
          if (*del == i) {
            if (got_del_col)
              return true;
            del_col = i;
            got_del_col = true;
          } else {
            if (got_keep_col)
              return true;
            keep_col = i;
            got_keep_col = true;
          }
        }

        if (i == *del)
          ++del;
      }

      if (!got_del_col || !got_keep_col)
        return true;
      if (neg.get(keep_col) == neg.get(del_col))
        return false;


      unsigned char val = neg.get(del_col);
      cpy_bits_t::iterator I = cpy_bits.find(del_col);
      if (I == cpy_bits.end())
          cpy_bits[del_col] = std::make_pair(keep_col, val);
      else {
          // FIXME: eq classes with size > 1 not supported for now
          SASSERT(I->second.first == keep_col);
          I->second.second |= val;
      }

      return false;
    }

#endif
    return 0;
}

void doc_manager::complement(doc const& src, ptr_vector<doc>& result) {
}
void doc_manager::subtract(doc const& A, doc const& B, ptr_vector<doc>& result) {
}
bool doc_manager::equals(doc const& a, doc const& b) const {
    return false;
}
bool doc_manager::is_full(doc const& src) const {
    return false;
}
unsigned doc_manager::hash(doc const& src) const {
    return 0;
}
bool doc_manager::contains(doc const& a, doc const& b) const {
    return false;
}
std::ostream& doc_manager::display(std::ostream& out, doc const& b) const {
    return out;
}

