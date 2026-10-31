import SPR.Segment.FrequencyIdentities

/-!
# Positive endpoint ratios at crossings

The vanishing cross polynomial makes the endpoint quotient real on the imaginary
axis. Segment stability then makes this real ratio strictly positive.
-/

namespace SPR.Segment

open Polynomial Complex

noncomputable section

@[simp] theorem value_sub (p q : ℝ[X]) (z : ℂ) :
    value (p - q) z = value p z - value q z := by simp [value]

/-- The candidate interpolation ratio at squared frequency `t`. -/
def crossingRatio (p₀ p₁ : ℝ[X]) (t : ℝ) : ℝ :=
  (value p₁ (I * (Real.sqrt t : ℂ)) / value p₀ (I * (Real.sqrt t : ℂ))).re

theorem crossing_ratio_collinear {p₀ p₁ : ℝ[X]} (hs : Stable p₀ p₁) {ω : ℝ}
    (hc : value (cross p₀ p₁) (I * (ω : ℂ)) = 0) :
    value p₁ (I * (ω : ℂ)) =
      Complex.ofReal ((value p₁ (I * (ω : ℂ)) / value p₀ (I * (ω : ℂ))).re) *
        value p₀ (I * (ω : ℂ)) := by
  let z := I * (ω : ℂ)
  have hz : 0 ≤ z.re := by simp [z]
  have hp := value_ne_zero hs.left hz
  have hstar : -z = star z := by simp [z]
  have he : star (value p₀ z) * value p₁ z = value p₀ z * star (value p₁ z) := by
    have hh : value (cross p₀ p₁) z = 0 := hc
    simp only [cross, value_sub, value_mul, value_reflect, hstar, value_star] at hh
    exact sub_eq_zero.mp hh
  have hr : star (value p₁ z / value p₀ z) = value p₁ z / value p₀ z := by
    rw [star_div₀]
    apply (div_eq_div_iff (by simpa using hp) hp).mpr
    simpa only [Complex.star_def, mul_comm] using he.symm
  rw [(conj_eq_iff_re.mp (by simpa only [Complex.star_def] using hr)), div_mul_cancel₀ _ hp]

theorem crossing_ratio_positive {p₀ p₁ : ℝ[X]} (hs : Stable p₀ p₁) {t : ℝ}
    (hc : value (cross p₀ p₁) (I * (Real.sqrt t : ℂ)) = 0) :
    0 < crossingRatio p₀ p₁ t :=
  collinear_ratio_pos hs (by simp) (crossing_ratio_collinear hs hc)

end
end SPR.Segment
