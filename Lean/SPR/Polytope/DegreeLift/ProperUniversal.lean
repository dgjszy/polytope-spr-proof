import SPR.Polytope.DegreeLift.SegmentProper
import SPR.Polytope.Common.SegmentExistence
import SPR.Polytope.Common.NecessaryClassification

/-! # The lower-degree positive column for at most two vertices. -/
namespace SPR.Polytope
open Polynomial
noncomputable section

theorem at_most_two_proper {n m : ℕ} (hn : 1 ≤ n) (hm : m ≤ 2) :
    Universal n m (n-1) := by
  intro r hr hrm a ha hs
  have hsmall : r=1 ∨ r=2 := by omega
  rcases hsmall with h | h
  · subst r
    refine ⟨(a 0).derivative,?_,?_⟩
    · rw [Hurwitz.derivative_natDegree_exact (by rw [(ha 0).2]; omega),(ha 0).2]
    · apply common_of_vertices a hs _
      · intro i
        have hi : i=0 := Subsingleton.elim _ _
        subst i
        exact DegreeLift.derivative_spr (vertex_hurwitz hs 0) (by rw [(ha 0).2]; exact hn)
      · exact vertex_hurwitz hs
  · subst r
    have hsegment : Segment.Stable (a 0) (a 1) := by
      intro θ hθ
      let weights : Fin 2 → ℝ := ![1-θ,θ]
      have hw : Weights weights := by
        constructor
        · intro i; fin_cases i
          · exact sub_nonneg.mpr hθ.2
          · exact hθ.1
        · simp [weights,Fin.sum_univ_succ]
      have hh := hs weights hw
      simpa [blend,weights,Segment.blend,Fin.sum_univ_succ] using hh
    obtain ⟨b,hbd,hb0,hb1⟩ := DegreeLift.segment_exact_proper (ha 0).1 (ha 1).1
      ((ha 0).2.trans (ha 1).2.symm) (by rw [(ha 0).2]; exact hn) hsegment
    refine ⟨b,by simpa [(ha 0).2] using hbd,?_⟩
    apply common_of_vertices a hs b
    · intro i; fin_cases i
      · exact hb0
      · exact hb1
    · exact vertex_hurwitz hs

/-- The entire n-1 column is now classified for every n≥1 and m≥1. -/
theorem lower_classification {n m : ℕ} (hn : 1 ≤ n) :
    Universal n m (n-1) ↔ n ≤ 2 ∨ m ≤ 2 := by
  constructor
  · intro h
    exact lower_classification_necessary (Or.inl h)
  · rintro (h | h)
    · exact (low_order_classification hn h).1
    · exact at_most_two_proper hn h

/-- The same-degree column has the identical complete classification. -/
theorem same_classification {n m : ℕ} (hn : 1 ≤ n) :
    Universal n m n ↔ n ≤ 2 ∨ m ≤ 2 := by
  constructor
  · intro h
    exact lower_classification_necessary (Or.inr h)
  · rintro (h | h)
    · exact (low_order_classification hn h).2.1
    · exact at_most_two_same_degree hn h

end
end SPR.Polytope
