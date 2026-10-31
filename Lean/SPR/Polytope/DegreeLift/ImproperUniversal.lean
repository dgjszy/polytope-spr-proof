import SPR.Polytope.DegreeLift.SegmentImproper
import SPR.Polytope.DegreeLift.ProperUniversal

/-! # The upper-degree positive column for every arbitrary-order stable segment. -/
namespace SPR.Polytope
open Polynomial
noncomputable section

theorem at_most_two_improper {n m : ℕ} (hn : 1 ≤ n) (hm : m ≤ 2) :
    Universal n m (n+1) := by
  intro r hr hrm a ha hs
  have hsmall : r=1 ∨ r=2 := by omega
  rcases hsmall with h | h
  · subst r
    have hseg : Segment.Stable (a 0) (a 0) := by
      intro θ _
      simpa using vertex_hurwitz hs (0:Fin 1)
    obtain ⟨b,hbd,hb,_⟩ := DegreeLift.segment_exact_improper (ha 0).1 (ha 0).1 rfl
      (by rw [(ha 0).2]; exact hn) hseg
    refine ⟨b,by simpa [(ha 0).2] using hbd,?_⟩
    apply common_of_vertices a hs _
    · intro i
      have hi : i=0 := Subsingleton.elim _ _
      subst i
      exact hb
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
    obtain ⟨b,hbd,hb0,hb1⟩ := DegreeLift.segment_exact_improper (ha 0).1 (ha 1).1
      ((ha 0).2.trans (ha 1).2.symm) (by rw [(ha 0).2]; exact hn) hsegment
    refine ⟨b,by simpa [(ha 0).2] using hbd,?_⟩
    apply common_of_vertices a hs b
    · intro i; fin_cases i
      · exact hb0
      · exact hb1
    · exact vertex_hurwitz hs

theorem at_most_two_three_degrees {n m : ℕ} (hn : 1 ≤ n) (hm : m ≤ 2) :
    Universal n m (n-1) ∧ Universal n m n ∧ Universal n m (n+1) :=
  ⟨at_most_two_proper hn hm,at_most_two_same_degree hn hm,at_most_two_improper hn hm⟩

end
end SPR.Polytope
