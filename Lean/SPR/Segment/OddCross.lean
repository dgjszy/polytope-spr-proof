import SPR.Segment.Elimination
import Mathlib.Algebra.Polynomial.Expand

/-!
# The squared-frequency representation of the cross polynomial

Reflection forces every even coefficient of the cross polynomial to vanish.
Dividing by `X` leaves an even polynomial, recovered by contraction and expansion.
The leading terms of the equal-degree monic endpoints cancel.
-/

namespace SPR.Segment

open Polynomial

noncomputable section

theorem reflect_coeff (p : ℝ[X]) (k : ℕ) :
    (reflect p).coeff k = p.coeff k * (-1) ^ k := by
  have h : (-X : ℝ[X]) = C (-1) * X := by simp
  rw [reflect, h, comp_C_mul_X_coeff]

theorem odd_coeff_even_zero {p : ℝ[X]} (hp : reflect p = -p)
    {k : ℕ} (hk : Even k) : p.coeff k = 0 := by
  have hh := congrArg (fun q : ℝ[X] => q.coeff k) hp
  change (reflect p).coeff k = (-p).coeff k at hh
  rw [reflect_coeff, hk.neg_one_pow, mul_one, coeff_neg] at hh
  linarith

/-- Every odd polynomial has the required real squared-frequency representation. -/
theorem odd_frequency_representation {p : ℝ[X]} (hp : reflect p = -p) :
    ∃ d : ℝ[X], p = X * frequencyLift d := by
  let q := p.divX
  have hq : expand ℝ 2 (contract 2 q) = q := by
    ext k
    rw [coeff_expand (by norm_num : 0 < 2)]
    by_cases hk : 2 ∣ k
    · rw [if_pos hk, coeff_contract (by norm_num : (2 : ℕ) ≠ 0)]
      rw [Nat.div_mul_cancel hk]
    · rw [if_neg hk]
      dsimp [q]
      rw [coeff_divX]
      symm
      apply odd_coeff_even_zero hp
      rw [Nat.even_iff]
      omega
  refine ⟨reflect (contract 2 q), ?_⟩
  have hlift : frequencyLift (reflect (contract 2 q)) = q := by
    rw [frequencyLift, reflect, comp_assoc]
    simpa [expand_eq_comp_X_pow] using hq
  have hzero : p.coeff 0 = 0 := odd_coeff_even_zero hp (Even.zero)
  simpa only [hlift, q, hzero, C_0, add_zero] using (X_mul_divX_add p).symm

/-- The cross polynomial's leading terms cancel, including at arbitrary order. -/
theorem cross_degree_lt {p₀ p₁ : ℝ[X]} (hm₀ : p₀.Monic) (hm₁ : p₁.Monic)
    (hd : p₀.natDegree = p₁.natDegree) :
    (cross p₀ p₁).degree < (2 * p₀.natDegree : ℕ) := by
  have hr₀ : reflect p₀ ≠ 0 := by simpa [reflect] using hm₀.ne_zero
  have hr₁ : reflect p₁ ≠ 0 := by simpa [reflect] using hm₁.ne_zero
  have hdeg₀ : (reflect p₀ * p₁).degree = (2 * p₀.natDegree : ℕ) := by
    rw [degree_mul, reflect, degree_comp_neg_X,
      degree_eq_natDegree hm₀.ne_zero, degree_eq_natDegree hm₁.ne_zero, ← hd]
    simp [two_mul]
  have hdeg₁ : (p₀ * reflect p₁).degree = (reflect p₀ * p₁).degree := by
    simp only [degree_mul, reflect, degree_comp_neg_X]
  have hlc : (reflect p₀ * p₁).leadingCoeff = (p₀ * reflect p₁).leadingCoeff := by
    simp [reflect, leadingCoeff_mul, hm₀.leadingCoeff, hm₁.leadingCoeff, hd]
  exact (degree_sub_lt hdeg₁.symm (mul_ne_zero hr₀ hm₁.ne_zero) hlc).trans_eq hdeg₀

end
end SPR.Segment
