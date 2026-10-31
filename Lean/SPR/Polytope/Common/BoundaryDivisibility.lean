import SPR.Polytope.Common.FirstOrder
import SPR.Polytope.Common.BoundaryContact

/-! # A real imaginary-axis conjugate root forces the whole quadratic factor. -/
namespace SPR.Polytope
open Polynomial Complex
noncomputable section

/-- Quadratic division is proved in the real polynomial ring, without assuming
that a candidate numerator has the factor before passing to a boundary limit. -/
theorem quadratic_dvd_of_axis_zero {p : ℝ[X]} {ω : ℝ} (hω : ω ≠ 0)
    (hz : Segment.value p (I*(ω:ℂ))=0) : X^2+C (ω^2) ∣ p := by
  let q : ℝ[X] := X^2+C (ω^2)
  have hmon : q.Monic := by dsimp [q]; monicity!
  have hdeg : q.natDegree=2 := by dsimp [q]; compute_degree!
  have hq1 : q ≠ 1 := by intro he; have := congrArg Polynomial.natDegree he; simp [hdeg] at this
  let r := p %ₘ q
  have hrdeg : r.natDegree ≤ 1 := by
    have hh := natDegree_modByMonic_lt p hmon hq1
    change (p %ₘ q).natDegree ≤ 1
    rw [hdeg] at hh
    omega
  have hrepr : r=C (r.coeff 1)*X+C (r.coeff 0) := by
    ext j
    by_cases hj : j ≤ 1
    · interval_cases j <;> simp
    · simp [coeff_eq_zero_of_natDegree_lt (show r.natDegree < j by omega),coeff_X,
        coeff_C,show j ≠ 0 by omega,show 1 ≠ j by omega]
  have hqzero : Segment.value q (I*(ω:ℂ))=0 := by
    apply Complex.ext <;> simp [Segment.value,q,pow_succ,Complex.mul_re,Complex.mul_im] <;> ring
  have hzero : Segment.value r (I*(ω:ℂ))=0 := by
    have hh := congrArg (fun b : ℝ[X] => Segment.value b (I*(ω:ℂ)))
      (modByMonic_add_div p q)
    simp only [Segment.value_add,Segment.value_mul,hqzero,zero_mul,add_zero,hz] at hh
    exact hh
  rw [hrepr] at hzero
  have him := congrArg Complex.im hzero
  have hre := congrArg Complex.re hzero
  simp [Segment.value,Complex.mul_re,Complex.mul_im] at him hre
  have hc1 : r.coeff 1=0 := him.resolve_right hω
  have hr0 : r=0 := by rw [hrepr,hc1,hre]; simp
  exact (modByMonic_eq_zero_iff_dvd hmon).mp hr0

end
end SPR.Polytope
