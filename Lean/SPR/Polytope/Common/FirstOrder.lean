import SPR.Polytope.Common.SegmentExistence

/-! # Every finite first-order stable family admits all three requested degrees. -/
namespace SPR.Polytope
open Polynomial Complex
noncomputable section

theorem linear_representation {p : ℝ[X]} (hm : p.Monic) (hd : p.natDegree=1) :
    p=X+C (p.coeff 0) := by
  ext j
  by_cases h : j ≤ 1
  · interval_cases j
    · simp
    · simpa [hd] using hm.coeff_natDegree
  · have hz := coeff_eq_zero_of_natDegree_lt (p := p) (show p.natDegree < j by omega)
    simp [hz,coeff_X,coeff_C,show j ≠ 0 by omega,show 1 ≠ j by omega]

def linearNumerator (k : ℕ) : ℝ[X] :=
  if k=0 then 1 else if k=1 then X+1 else -X^2+X+1

theorem linearNumerator_degree {k : ℕ} (hk : k ≤ 2) :
    (linearNumerator k).natDegree=k := by
  interval_cases k <;> norm_num [linearNumerator] <;> compute_degree!

theorem linear_spr (α : ℝ) (ha : 0 < α) {k : ℕ} (hk : k ≤ 2) :
    Segment.FrequencySPR (X+C α) (linearNumerator k) := by
  intro ω
  rw [Segment.real_ratio]
  have hden : 0 < Complex.normSq (Segment.value (X+C α) (I*(ω:ℂ))) := by
    simp [Segment.value,Complex.normSq,Complex.mul_re,Complex.mul_im]
    nlinarith [sq_pos_of_pos ha,sq_nonneg ω]
  apply div_pos _ hden
  interval_cases k <;>
    simp [Segment.pairing,Segment.value,linearNumerator,pow_succ,
      Complex.mul_re,Complex.mul_im] <;>
    nlinarith [sq_nonneg ω,mul_nonneg ha.le (sq_nonneg ω)]

theorem first_order_universal (m : ℕ) {k : ℕ} (hk : k ≤ 2) : Universal 1 m k := by
  intro r hr hm a ha hs
  refine ⟨linearNumerator k,linearNumerator_degree hk,?_⟩
  apply common_of_vertices a hs _
  · intro i
    have hstable := vertex_hurwitz hs i
    have hα : 0 < (a i).coeff 0 := Hurwitz.hurwitz_coeff_pos hstable
      (by rw [(ha i).1.leadingCoeff]; norm_num) 0 (by omega)
    rw [linear_representation (ha i).1 (ha i).2]
    exact linear_spr _ hα hk
  · exact vertex_hurwitz hs

end
end SPR.Polytope
