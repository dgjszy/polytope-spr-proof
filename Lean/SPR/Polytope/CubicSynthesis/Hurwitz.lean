import SPR.Polytope.CubicSynthesis.Pairing

/-! # Strict cubic Routh inequalities derived from the root definition of Hurwitz. -/
namespace SPR.Polytope.CubicSynthesis
open Polynomial Complex
noncomputable section

def determinantPolynomial (α β γ : ℝ) : ℝ[X] :=
  C (α*β-γ)+C (2*α^2+2*β)*X+C (8*α)*X^2+C 8*X^3

theorem hurwitz_inequalities {α β γ : ℝ}
    (hs : IsHurwitz (CubicTriangle.cubic α β γ)) :
    0 < α ∧ 0 < β ∧ 0 < γ ∧ γ < α*β := by
  have hm := (CubicTriangle.cubic_degree α β γ).1
  have hd := (CubicTriangle.cubic_degree α β γ).2
  have hcoeff (j : ℕ) (hj : j ≤ 3) := Hurwitz.hurwitz_coeff_pos hs
    (by rw [hm.leadingCoeff]; norm_num) j (by omega : j ≤ (CubicTriangle.cubic α β γ).natDegree)
  have hα : 0 < α := by simpa [CubicTriangle.cubic,coeff_X] using hcoeff 2 (by omega)
  have hβ : 0 < β := by simpa [CubicTriangle.cubic,coeff_X] using hcoeff 1 (by omega)
  have hγ : 0 < γ := by simpa [CubicTriangle.cubic,coeff_X] using hcoeff 0 (by omega)
  have hroots : ∀ r : ℝ, (determinantPolynomial α β γ).IsRoot r → r < 0 := by
    intro r hr
    by_contra hn
    have hr0 : 0 ≤ r := le_of_not_gt hn
    have hb : 0 < 3*r^2+2*α*r+β := by positivity
    let ω := Real.sqrt (3*r^2+2*α*r+β)
    have hw : ω^2=3*r^2+2*α*r+β := Real.sq_sqrt hb.le
    have hdet : α*β-γ+(2*α^2+2*β)*r+8*α*r^2+8*r^3=0 := by
      simpa [IsRoot,determinantPolynomial,add_assoc] using hr
    have he : Segment.value (CubicTriangle.cubic α β γ) ((r:ℂ)+I*(ω:ℂ))=0 := by
      apply Complex.ext <;>
        simp [Segment.value,CubicTriangle.cubic,pow_succ,Complex.mul_re,Complex.mul_im]
      · nlinarith [congrArg (fun t : ℝ => α*t) hw,congrArg (fun t : ℝ => r*t) hw]
      · nlinarith [congrArg (fun t : ℝ => ω*t) hw]
    have hh := hs ((r:ℂ)+I*(ω:ℂ)) (by simpa [Segment.value,IsRoot,eval_map] using he)
    simp at hh
    linarith
  have hDdegree : (determinantPolynomial α β γ).natDegree=3 := by
    unfold determinantPolynomial
    compute_degree!
  have hlc : 0 ≤ (determinantPolynomial α β γ).leadingCoeff := by
    rw [← coeff_natDegree,hDdegree]
    simp only [determinantPolynomial,coeff_add,coeff_C_mul_X_pow,coeff_C_mul_X,
      coeff_C,coeff_X]
    norm_num
  have hpos := zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg
    (P := determinantPolynomial α β γ) (x := 0) hroots hlc
  have hg : γ < α*β := by simpa [determinantPolynomial] using hpos
  exact ⟨hα,hβ,hγ,hg⟩

end
end SPR.Polytope.CubicSynthesis
