import SPR.Polytope.Common.Definitions
import SPR.Segment.Synthesis

/-! # Same-degree universal existence for at most two vertices, in all positive orders. -/
namespace SPR.Polytope
open Polynomial
noncomputable section

theorem vertex_hurwitz {r : ℕ} {a : Fin r → ℝ[X]} (hs : Stable a) (i : Fin r) :
    IsHurwitz (a i) := by
  classical
  let weights : Fin r → ℝ := fun j => if j=i then 1 else 0
  have hw : Weights weights := by
    constructor
    · intro j; dsimp [weights]; split_ifs <;> norm_num
    · simp [weights]
  simpa [blend,weights] using hs weights hw

theorem at_most_two_same_degree {n m : ℕ} (hn : 1 ≤ n) (hm : m ≤ 2) :
    Universal n m n := by
  intro r hr hrm a ha hs
  have hsmall : r=1 ∨ r=2 := by omega
  rcases hsmall with h | h
  · subst r
    refine ⟨a 0,(ha 0).2,?_⟩
    apply common_of_vertices a hs _
    · intro i
      have hi : i=0 := Subsingleton.elim _ _
      subst i
      exact Segment.synthesis_self (vertex_hurwitz hs 0)
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
    obtain ⟨b,hbd,hb⟩ := Segment.synthesis (ha 0).1 (ha 1).1
      ((ha 0).2.trans (ha 1).2.symm) (by rw [(ha 0).2]; exact hn) hsegment
    refine ⟨b,hbd.trans (ha 0).2,?_⟩
    apply common_of_vertices a hs b
    · intro i; fin_cases i
      · simpa using hb 0 ⟨le_rfl,zero_le_one⟩
      · simpa using hb 1 ⟨zero_le_one,le_rfl⟩
    · exact vertex_hurwitz hs

end
end SPR.Polytope
