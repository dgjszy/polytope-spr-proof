import SPR.N4.Hurwitz

/-! # A sufficient quartic Hurwitz criterion, proved by excluding roots. -/
namespace SPR.Polytope.QuarticTriangle
open Polynomial Complex N4
noncomputable section

/-- Positive coefficients and the third determinant suffice for strict stability. -/
theorem hurwitz_of_determinant (a : Poly4)
    (h1 : 0 < a.a1) (h2 : 0 < a.a2) (h3 : 0 < a.a3) (h4 : 0 < a.a4)
    (hD : 0 < determinant a) : IsHurwitz a.poly := by
  have hb : 0 < a.a2^2 - 4*a.a4 := by
    have hs := sq_nonneg (a.a1*a.a2-2*a.a3)
    have hh : 0 < a.a1^2*(a.a2^2-4*a.a4) := by
      dsimp [determinant] at hD
      nlinarith
    exact (mul_pos_iff_of_pos_left (sq_pos_of_pos h1)).mp hh
  intro z hz
  by_contra hn
  have hr : 0 ≤ z.re := le_of_not_gt hn
  have hdpos : 0 < determinant (shifted a z.re) := by
    rw [← determinantPolynomial_eval]
    simp only [determinantPolynomial, eval_add, eval_mul, eval_C, eval_pow, eval_X]
    have hc1 : 0 ≤ 2*a.a1*a.a2^2+2*a.a1^2*a.a3-8*a.a1*a.a4 := by
      nlinarith [mul_pos h1 hb, mul_pos (sq_pos_of_pos h1) h3]
    have hc2 : 0 ≤ 4*a.a2^2+8*a.a1^2*a.a2+4*a.a1*a.a3-16*a.a4 := by
      nlinarith [mul_pos (sq_pos_of_pos h1) h2, mul_pos h1 h3]
    positivity
  have he : (shifted a z.re).poly.eval₂ (algebraMap ℝ ℂ)
      ((z.im : ℂ)*I) = 0 := by
    rw [eval_shifted]
    have hez : (z.re : ℂ)+(z.im : ℂ)*I = z := by
      apply Complex.ext <;> simp
    rw [hez]
    simpa [Polynomial.IsRoot, eval_map] using hz
  rw [eval_imaginary] at he
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, I_re, I_im, mul_zero, zero_mul, sub_zero,
    mul_one, add_zero, zero_add, Complex.zero_re, Complex.zero_im] at hre him
  have hs1 : 0 < (shifted a z.re).a1 := by dsimp [shifted]; positivity
  have hs4 : 0 < (shifted a z.re).a4 := by dsimp [shifted]; positivity
  have hv : z.im ≠ 0 := by
    intro hv
    simp [hv, evenPart] at hre
    linarith
  have ho := (mul_eq_zero.mp him).resolve_left hv
  have hd0 : determinant (shifted a z.re) = 0 := by
    dsimp [determinant, evenPart] at *
    rw [sub_eq_zero.mp ho]
    nlinarith [congrArg (fun r : ℝ => (shifted a z.re).a1^2*r) hre]
  linarith

end
end SPR.Polytope.QuarticTriangle
