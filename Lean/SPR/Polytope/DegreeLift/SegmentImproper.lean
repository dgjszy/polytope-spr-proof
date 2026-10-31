import SPR.Polytope.DegreeLift.ImproperPerturbation
import SPR.Polytope.DegreeLift.SegmentProper

/-! # Actual degree n+1 common numerators for stable segments with fixed denominators. -/
namespace SPR.Polytope.DegreeLift
open Polynomial
noncomputable section

theorem segment_exact_improper {a₀ a₁ : ℝ[X]} (hm₀ : a₀.Monic) (hm₁ : a₁.Monic)
    (hd : a₀.natDegree=a₁.natDegree) (hn : 1 ≤ a₀.natDegree) (hs : Segment.Stable a₀ a₁) :
    ∃ b : ℝ[X], b.natDegree=a₀.natDegree+1 ∧
      Segment.FrequencySPR a₀ b ∧ Segment.FrequencySPR a₁ b := by
  obtain ⟨c,hcd,hc0,hc1⟩ := segment_strictly_proper hm₀ hm₁ hd hn hs
  let α₀ := a₀.coeff (a₀.natDegree-1)
  let α₁ := a₁.coeff (a₁.natDegree-1)
  have hα₀ : 0 < α₀ := Hurwitz.hurwitz_coeff_pos hs.left
    (by rw [hm₀.leadingCoeff]; norm_num) _ (by omega)
  have hα₁ : 0 < α₁ := Hurwitz.hurwitz_coeff_pos hs.right
    (by rw [hm₁.leadingCoeff]; norm_num) _ (by omega)
  let gain := 1/(2*(α₀+α₁+1))
  have hGain : 0 < gain := by dsimp [gain]; positivity
  have hL0 : 0 < 1-gain*α₀ := by
    have hh : α₀/(2*(α₀+α₁+1)) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
    dsimp [gain]
    rw [one_div_mul_eq_div]
    linarith
  have hL1 : 0 < 1-gain*α₁ := by
    have hh : α₁/(2*(α₀+α₁+1)) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
    dsimp [gain]
    rw [one_div_mul_eq_div]
    linarith
  obtain ⟨δ₀,hδ₀,h0⟩ := endpoint_improper_perturbation hs.left hm₀ hn hc0 hL0
  obtain ⟨δ₁,hδ₁,h1⟩ := endpoint_improper_perturbation hs.right hm₁ (by omega) hc1 hL1
  let ε := min δ₀ δ₁
  have hε : 0 < ε := lt_min hδ₀ hδ₁
  let b := c+ε • improperDirection a₀.natDegree gain
  refine ⟨b,?_,h0 ε hε (min_le_left _ _),?_⟩
  · have hle : b.natDegree ≤ a₀.natDegree+1 := by
      apply natDegree_add_le_of_degree_le (by omega)
      apply (natDegree_smul_le _ _).trans
      apply natDegree_add_le_of_degree_le (by simp)
      exact (natDegree_smul_le _ _).trans (by rw [natDegree_X_pow])
    apply natDegree_eq_of_le_of_coeff_ne_zero hle
    have hc : c.coeff (a₀.natDegree+1)=0 := coeff_eq_zero_of_natDegree_lt (by omega)
    have he : b.coeff (a₀.natDegree+1)=ε*gain := by
      simp only [b,improperDirection,coeff_add,coeff_smul,smul_eq_mul,hc,zero_add,coeff_X_pow]
      rw [if_neg (by omega)]
      simp
    rw [he]
    exact (mul_pos hε hGain).ne'
  · simpa [b,hd] using h1 ε hε (min_le_right _ _)

end
end SPR.Polytope.DegreeLift
