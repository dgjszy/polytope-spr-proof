import SPR.Polytope.Common.BoundaryDivisibility
import SPR.Segment.FrequencyIdentities

/-! # Removing an imaginary-axis quadratic from a common weak boundary numerator. -/
namespace SPR.Polytope.Transfer
open Polynomial Complex Set
noncomputable section

def quadratic (T : ℝ) : ℝ[X] := X^2+C T

theorem quadratic_value (T ω : ℝ) :
    Segment.value (quadratic T) (I*(ω:ℂ))=(T-ω^2 : ℝ) := by
  apply Complex.ext <;>
    simp [quadratic,Segment.value,pow_succ,Complex.mul_re,Complex.mul_im] <;> ring

theorem continuous_pairing (a B : ℝ[X]) : Continuous (fun ω : ℝ => Segment.pairing a B ω) := by
  unfold Segment.pairing Segment.value
  fun_prop

theorem quadratic_pairing_left (a B : ℝ[X]) (T ω : ℝ) :
    Segment.pairing (quadratic T*a) B ω=(T-ω^2)*Segment.pairing a B ω := by
  unfold Segment.pairing
  rw [Segment.value_mul,quadratic_value]
  simp [Complex.mul_re,Complex.mul_im,pow_succ]
  ring

theorem quadratic_pairing_both (a B : ℝ[X]) (T ω : ℝ) :
    Segment.pairing (quadratic T*a) (quadratic T*B) ω=
      (T-ω^2)^2*Segment.pairing a B ω := by
  unfold Segment.pairing
  rw [Segment.value_mul,Segment.value_mul,quadratic_value]
  simp [Complex.mul_re,Complex.mul_im,pow_succ]
  ring

theorem dense_nonroots (T : ℝ) : Dense {ω : ℝ | T-ω^2 ≠ 0} := by
  have hn : (X^2-C T : ℝ[X]) ≠ 0 := by
    intro h
    have hh := congrArg (fun p : ℝ[X] => p.coeff 2) h
    norm_num at hh
  have hh := (Polynomial.finite_setOf_isRoot hn).countable.dense_compl ℝ
  have he : {ω : ℝ | T-ω^2 ≠ 0}={ω : ℝ | (X^2-C T : ℝ[X]).IsRoot ω}ᶜ := by
    ext ω
    simp [IsRoot,sub_eq_zero,eq_comm]
  rw [he]
  exact hh

theorem weak_cancel_quadratic {a B : ℝ[X]} {T : ℝ}
    (h : ∀ ω, 0 ≤ Segment.pairing (quadratic T*a) (quadratic T*B) ω) :
    ∀ ω, 0 ≤ Segment.pairing a B ω := by
  have hc : IsClosed {ω : ℝ | 0 ≤ Segment.pairing a B ω} :=
    isClosed_le continuous_const (continuous_pairing a B)
  have hs : {ω : ℝ | T-ω^2 ≠ 0} ⊆ {ω : ℝ | 0 ≤ Segment.pairing a B ω} := by
    intro ω hω
    have hh := h ω
    rw [quadratic_pairing_both] at hh
    exact (mul_nonneg_iff_of_pos_left (sq_pos_of_ne_zero hω)).mp hh
  intro ω
  exact (hc.closure_subset_iff.mpr hs) ((dense_nonroots T) ω)

/-- Two independent actual denominator values at the contact force a full real
quadratic divisor; cancellation preserves every frequency, including the contact. -/
theorem remove_quadratic {a : Fin 3 → ℝ[X]} {B : ℝ[X]} {T : ℝ}
    (hT : 0 < T)
    (hdet : (Segment.value (a 0) (I*(Real.sqrt T:ℂ))).re*
        (Segment.value (a 1) (I*(Real.sqrt T:ℂ))).im-
      (Segment.value (a 0) (I*(Real.sqrt T:ℂ))).im*
        (Segment.value (a 1) (I*(Real.sqrt T:ℂ))).re ≠ 0)
    (h : ∀ i ω, 0 ≤ Segment.pairing (quadratic T*a i) B ω) :
    ∃ C : ℝ[X], B=quadratic T*C ∧ ∀ i ω, 0 ≤ Segment.pairing (a i) C ω := by
  have hcontact (i : Fin 3) : Segment.pairing (a i) B (Real.sqrt T)=0 := by
    have hf : Continuous (fun t : ℝ => Segment.pairing (a i) B (Real.sqrt t)) :=
      (continuous_pairing _ _).comp continuous_id.sqrt
    apply zero_of_boundary_sign hf hT
    intro t ht
    have hh := h i (Real.sqrt t)
    rwa [quadratic_pairing_left,Real.sq_sqrt ht] at hh
  have hz : Segment.value B (I*(Real.sqrt T:ℂ))=0 :=
    zero_of_two_orthogonal hdet (hcontact 0) (hcontact 1)
  obtain ⟨D,hD⟩ := quadratic_dvd_of_axis_zero (Real.sqrt_pos.mpr hT).ne' hz
  rw [Real.sq_sqrt hT.le] at hD
  refine ⟨D,hD,?_⟩
  intro i
  apply weak_cancel_quadratic (T := T)
  intro ω
  change 0 ≤ Segment.pairing (quadratic T*a i) ((X^2+Polynomial.C T)*D) ω
  rw [← hD]
  exact h i ω

end
end SPR.Polytope.Transfer
