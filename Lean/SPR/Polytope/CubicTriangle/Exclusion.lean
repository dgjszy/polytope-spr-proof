import SPR.Polytope.CubicTriangle.Basic

/-! # Complete degree-at-most-three obstruction, including unrestricted leading sign. -/
namespace SPR.Polytope.CubicTriangle
open Polynomial Complex
noncomputable section

def numerator (p : ℝ[X]) : ℝ[X] :=
  C (p.coeff 3)*X^3+C (p.coeff 2)*X^2+C (p.coeff 1)*X+C (p.coeff 0)

theorem numerator_eq {p : ℝ[X]} (hp : p.natDegree ≤ 3) : numerator p=p := by
  ext n
  by_cases hn : n ≤ 3
  · interval_cases n <;> simp [numerator]
  · have hz := coeff_eq_zero_of_natDegree_lt (p := p) (show p.natDegree < n by omega)
    simp [numerator, coeff_X, coeff_C, hz, show n ≠ 0 by omega,
      show 1 ≠ n by omega, show n ≠ 1 by omega,
      show n ≠ 2 by omega, show n ≠ 3 by omega]

def G (α β γ : ℝ) (p : ℝ[X]) (t : ℝ) : ℝ :=
  (p.coeff 0-p.coeff 2*t)*(γ-α*t)+t*(p.coeff 1-p.coeff 3*t)*(β-t)

theorem pairing_eq (α β γ : ℝ) {p : ℝ[X]} (hp : p.natDegree ≤ 3) (ω : ℝ) :
    Segment.pairing (cubic α β γ) p ω=G α β γ p (ω^2) := by
  conv_lhs => rw [← numerator_eq hp]
  simp [Segment.pairing,Segment.value,cubic,numerator,G,pow_succ,
    Complex.mul_re,Complex.mul_im]
  ring

theorem certificate (p : ℝ[X]) :
    6*G 3 1 2 p 2+8*G 4 4 15 p 3+3*G 1 3 2 p 4+3*G 3 1 2 p 0=0 := by
  unfold G
  ring

theorem necessary_positive {α β γ : ℝ} {p : ℝ[X]} (hp : p.natDegree ≤ 3)
    (hs : Segment.FrequencySPR (cubic α β γ) p) {t : ℝ} (ht : 0 ≤ t) :
    0 < G α β γ p t := by
  have h := hs (Real.sqrt t)
  rw [Segment.real_ratio] at h
  have hpair : 0 < Segment.pairing (cubic α β γ) p (Real.sqrt t) := by
    rcases div_pos_iff.mp h with h | h
    · exact h.1
    · exact False.elim ((not_lt_of_ge (Complex.normSq_nonneg _)) h.2)
  rwa [pairing_eq α β γ hp, Real.sq_sqrt ht] at hpair

theorem no_common_degree_le_three : ¬ ∃ p : ℝ[X], p.natDegree ≤ 3 ∧
    Segment.FrequencySPR a₁ p ∧ Segment.FrequencySPR a₂ p ∧
      Segment.FrequencySPR a₃ p := by
  rintro ⟨p,hd,h1,h2,h3⟩
  have h12 := necessary_positive hd h1 (t := 2) (by norm_num)
  have h23 := necessary_positive hd h2 (t := 3) (by norm_num)
  have h34 := necessary_positive hd h3 (t := 4) (by norm_num)
  have h10 := necessary_positive hd h1 (t := 0) (by norm_num)
  have hc := certificate p
  linarith

theorem affine_independent (r s : ℝ)
    (h : r • (a₂-a₁)+s • (a₃-a₁)=0) : r=0 ∧ s=0 := by
  have h0 := congrArg (fun p : ℝ[X] => p.coeff 0) h
  have h2 := congrArg (fun p : ℝ[X] => p.coeff 2) h
  norm_num [a₁,a₂,a₃,cubic,coeff_X] at h0 h2
  constructor <;> linarith

end
end SPR.Polytope.CubicTriangle
