/**++
  Copyright (c) 2017 Arie Gurfinkel

  Legacy implementations of frames. To be removed.

  Notes: this file is included from the middle of spacer_context.h
*/

class legacy_frames
{
    pred_transformer &m_pt;

    /// level formulas
    vector<expr_ref_vector>      m_levels;
    /// map property to level where it occurs.
    obj_map<expr, unsigned>      m_prop2level;
    /// properties that are invariant.
    expr_ref_vector              m_invariants;

    void simplify_formulas (tactic& tac, expr_ref_vector& v);

public:
    legacy_frames (pred_transformer &pt) :
    m_pt(pt), m_invariants (m_pt.get_ast_manager ()) {}
    pred_transformer& pt () const {return m_pt;}
    bool add_lemma (expr * lemma, unsigned level);
    void get_frame_lemmas (unsigned level, expr_ref_vector &out)
    {
        if(is_infty_level(level)) { out.append(m_invariants); }
        else if(level < m_levels.size()) { out.append(m_levels [level]); }
    }

    void get_frame_geq_lemmas (unsigned level, expr_ref_vector &out);
    void add_frame () {m_levels.push_back (expr_ref_vector (m_pt.get_ast_manager ()));}

    unsigned size () const {return m_levels.size ();}
    unsigned lemma_size () const {return m_prop2level.size ();}


    void propagate_to_infinity (unsigned level);
    bool propagate_to_next_level (unsigned level);

    void simplify_formulas ();

    void inherit_frames (legacy_frames& other);

};
