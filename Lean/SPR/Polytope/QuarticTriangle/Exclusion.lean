import SPR.N4.Basic
import SPR.Segment.Definitions

/-!
# Six-frequency obstruction for the quartic triangle

All real polynomials of degree at most five are represented by their coefficients.
The positive certificate excludes the original complex quotient inequalities.
Stability of the full triangle is a separate proof obligation.
-/
namespace SPR.Polytope.QuarticTriangle
open Polynomial Complex
noncomputable section

/-- First monic quartic vertex. -/
def a₁ : N4.Poly4 := ⟨2/7, 37/7, 1, 25/7⟩
/-- Second monic quartic vertex. -/
def a₂ : N4.Poly4 := ⟨11/7, 32/7, 4, 36/7⟩
/-- Third monic quartic vertex. -/
def a₃ : N4.Poly4 := ⟨857/21, 1130/21, 709/3, 576/7⟩

/-- Full coefficient representation, with no sign restrictions. -/
def numerator (p : ℝ[X]) : ℝ[X] :=
  C (p.coeff 5)*X^5 + C (p.coeff 4)*X^4 + C (p.coeff 3)*X^3 +
  C (p.coeff 2)*X^2 + C (p.coeff 1)*X + C (p.coeff 0)

theorem numerator_eq {p : ℝ[X]} (hp : p.natDegree ≤ 5) : numerator p = p := by
  ext n
  by_cases hn : n ≤ 5
  · interval_cases n <;> simp [numerator, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X]
  · have hz := coeff_eq_zero_of_natDegree_lt (p := p) (show p.natDegree < n by omega)
    simp [numerator, coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C, coeff_X,
      hz, show n ≠ 0 by omega, show n ≠ 1 by omega, show 1 ≠ n by omega,
      show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega,
      show n ≠ 5 by omega]

/-- Cleared pairing at squared frequency, on the full six-dimensional space. -/
def G (a : N4.Poly4) (p : ℝ[X]) (t : ℝ) : ℝ :=
  (p.coeff 4-a.a1*p.coeff 5)*t^4 +
  (a.a3*p.coeff 5+a.a1*p.coeff 3-a.a2*p.coeff 4-p.coeff 2)*t^3 +
  (a.a4*p.coeff 4+a.a2*p.coeff 2+p.coeff 0-a.a3*p.coeff 3-a.a1*p.coeff 1)*t^2 +
  (a.a3*p.coeff 1-a.a4*p.coeff 2-a.a2*p.coeff 0)*t+a.a4*p.coeff 0

theorem pairing_eq (a : N4.Poly4) {p : ℝ[X]} (hp : p.natDegree ≤ 5) (ω : ℝ) :
    Segment.pairing a.poly p ω = G a p (ω^2) := by
  conv_lhs => rw [← numerator_eq hp]
  simp [Segment.pairing, Segment.value, numerator, N4.Poly4.poly,
    eval₂_add, eval₂_mul, eval₂_pow, eval₂_C, eval₂_X,
    Complex.mul_re, Complex.mul_im, pow_succ, G]
  <;> ring

/-- Positive rational weights annihilate every allowed numerator coefficient. -/
theorem certificate (p : ℝ[X]) :
    G a₁ p 1/600 + G a₂ p 2/96 + G a₂ p 3/36 +
      G a₃ p 4/4912 + G a₁ p 5/120 + G a₃ p 6/42960 = 0 := by
  norm_num [G, a₁, a₂, a₃]
  <;> ring

theorem necessary_positive (a : N4.Poly4) {p : ℝ[X]} (hp : p.natDegree ≤ 5)
    (hs : Segment.FrequencySPR a.poly p) {t : ℝ} (ht : 0 ≤ t) : 0 < G a p t := by
  have h := hs (Real.sqrt t)
  rw [Segment.real_ratio] at h
  have hpair : 0 < Segment.pairing a.poly p (Real.sqrt t) := by
    rcases (div_pos_iff.mp h) with h | h
    · exact h.1
    · exact False.elim ((not_lt_of_ge (Complex.normSq_nonneg _)) h.2)
  rwa [pairing_eq a hp, Real.sq_sqrt ht] at hpair

/-- Unconditional obstruction for arbitrary real polynomials, including both leading signs. -/
theorem no_common_degree_le_five : ¬ ∃ p : ℝ[X], p.natDegree ≤ 5 ∧
    Segment.FrequencySPR a₁.poly p ∧ Segment.FrequencySPR a₂.poly p ∧
      Segment.FrequencySPR a₃.poly p := by
  rintro ⟨p, hd, h₁, h₂, h₃⟩
  have h1 := necessary_positive a₁ hd h₁ (t := 1) (by norm_num)
  have h2 := necessary_positive a₂ hd h₂ (t := 2) (by norm_num)
  have h3 := necessary_positive a₂ hd h₂ (t := 3) (by norm_num)
  have h4 := necessary_positive a₃ hd h₃ (t := 4) (by norm_num)
  have h5 := necessary_positive a₁ hd h₁ (t := 5) (by norm_num)
  have h6 := necessary_positive a₃ hd h₃ (t := 6) (by norm_num)
  have hc := certificate p
  linarith

end
end SPR.Polytope.QuarticTriangle
