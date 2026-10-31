import SPR.Segment.FrequencyIdentities
import SPR.Segment.RationalLimit
import SPR.Segment.Perturbation

/-!
# Raising one common strictly proper numerator to the exact requested degree

Monic denominators make the quotient with `X^n` tend to one at complex infinity.
A single sufficiently small positive multiple of `X^n` preserves strictness at
both endpoints and gives exact degree `n`.
-/

namespace SPR.Segment

open Polynomial Complex Set Filter Bornology
open scoped Topology

noncomputable section

theorem endpoint_perturbation {a c : ℝ[X]} (ha : IsHurwitz a) (hm : a.Monic)
    (hc : FrequencySPR a c) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      FrequencySPR a (c + ε • (X ^ a.natDegree)) := by
  let s : Set ℂ := {z | z.re = 0}
  let f (z : ℂ) := (value c z / value a z).re
  let g (z : ℂ) := (value (X ^ a.natDegree) z / value a z).re
  have hden (z : ℂ) (hz : z ∈ s) : value a z ≠ 0 :=
    value_ne_zero ha (by rw [show z.re = 0 from hz])
  have hcont (p : ℝ[X]) : ContinuousOn (fun z => (value p z / value a z).re) s :=
    continuous_re.comp_continuousOn
      ((p.continuous_eval₂ _).continuousOn.div (a.continuous_eval₂ _).continuousOn hden)
  have hpos (z : ℂ) (hz : z ∈ s) : 0 < f z := by
    have he : z = I * (z.im : ℂ) := by
      apply Complex.ext <;> simp [show z.re = 0 from hz]
    have hh : f z = f (I * (z.im : ℂ)) := congrArg f he
    rw [hh]
    exact hc z.im
  let P := (X ^ a.natDegree : ℝ[X]).map (algebraMap ℝ ℂ)
  let A := a.map (algebraMap ℝ ℂ)
  have hPm : P.Monic := (monic_X_pow _).map _
  have hAm : A.Monic := hm.map _
  have hd : P.natDegree = A.natDegree := by simp [P, A]
  have hlim : Tendsto g (cobounded ℂ) (𝓝 1) := by
    have hh := Analysis.quotient_tendsto_leadingCoeff (p := P) (q := A) hAm.ne_zero hd
    have hq : Tendsto (fun z => value (X ^ a.natDegree) z / value a z)
        (cobounded ℂ) (𝓝 (1 : ℂ)) := by
      simpa only [P, A, eval_map, value, hPm.leadingCoeff, hAm.leadingCoeff, div_one] using hh
    simpa only [g, ofReal_one, one_re] using continuous_re.continuousAt.tendsto.comp hq
  obtain ⟨δ, hδ, hbound⟩ := Analysis.positive_perturbation_on_closed
    (isClosed_eq continuous_re continuous_const) (hcont c) (hcont (X ^ a.natDegree)) hpos hlim
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ ω
  have hh := hbound ε hε hεδ (I * (ω : ℂ)) (by simp)
  have hvalue : value (c + ε • (X ^ a.natDegree)) (I * (ω : ℂ)) =
      value c (I * (ω : ℂ)) + (ε : ℂ) * value (X ^ a.natDegree) (I * (ω : ℂ)) := by
    simp [value]
  rw [hvalue, add_div, mul_div_assoc, add_re, mul_re, ofReal_re,
    ofReal_im, zero_mul, sub_zero]
  exact hh

/-- Both endpoints keep strict positive realness with the same exact-degree numerator. -/
theorem raise_common_degree {a₀ a₁ c : ℝ[X]} (hm₀ : a₀.Monic) (hm₁ : a₁.Monic)
    (hd : a₀.natDegree = a₁.natDegree) (h₀ : IsHurwitz a₀) (h₁ : IsHurwitz a₁)
    (hdeg : c.natDegree < a₀.natDegree) (hc₀ : FrequencySPR a₀ c)
    (hc₁ : FrequencySPR a₁ c) :
    ∃ b : ℝ[X], b.natDegree = a₀.natDegree ∧ FrequencySPR a₀ b ∧ FrequencySPR a₁ b := by
  obtain ⟨δ₀, hδ₀, hpert₀⟩ := endpoint_perturbation h₀ hm₀ hc₀
  obtain ⟨δ₁, hδ₁, hpert₁⟩ := endpoint_perturbation h₁ hm₁ hc₁
  let δ := min δ₀ δ₁
  have hδ : 0 < δ := lt_min hδ₀ hδ₁
  let b := c + δ • (X ^ a₀.natDegree)
  have hb₀ : FrequencySPR a₀ b := hpert₀ δ hδ (min_le_left _ _)
  have hb₁ : FrequencySPR a₁ b := by
    simpa only [b, hd] using hpert₁ δ hδ (min_le_right _ _)
  have hle : b.natDegree ≤ a₀.natDegree := by
    apply natDegree_add_le_of_degree_le hdeg.le
    exact (natDegree_smul_le _ _).trans (by rw [natDegree_X_pow])
  have hcoeff : b.coeff a₀.natDegree = δ := by
    have hc : c.coeff a₀.natDegree = 0 := coeff_eq_zero_of_natDegree_lt hdeg
    simp [b, coeff_add, coeff_smul, hc]
  refine ⟨b, natDegree_eq_of_le_of_coeff_ne_zero hle (by rw [hcoeff]; exact hδ.ne'), hb₀, hb₁⟩

end
end SPR.Segment
