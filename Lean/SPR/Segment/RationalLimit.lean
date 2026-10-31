import SPR.Segment.RationalDecay

/-!
# The limit of an equal-degree polynomial quotient at infinity

The reversal formula has exponent zero when the two degrees agree. Continuity
at zero leaves the ratio of their leading coefficients.
-/

namespace SPR.Segment.Analysis

open Polynomial Filter Bornology
open scoped Topology

noncomputable section

theorem quotient_tendsto_leadingCoeff {p q : ℂ[X]} (hq : q ≠ 0)
    (hdeg : p.natDegree = q.natDegree) :
    Tendsto (fun z : ℂ => p.eval z / q.eval z) (cobounded ℂ)
      (𝓝 (p.leadingCoeff / q.leadingCoeff)) := by
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cobounded ℂ) (𝓝 0) := tendsto_inv₀_cobounded
  have hp := p.reverse.continuous.tendsto 0 |>.comp hi
  have hq' := q.reverse.continuous.tendsto 0 |>.comp hi
  have he (r : ℂ[X]) : r.reverse.eval 0 = r.leadingCoeff := by
    rw [← coeff_zero_eq_eval_zero, coeff_zero_reverse]
  rw [he] at hp hq'
  have hlim := hp.div hq' (leadingCoeff_ne_zero.mpr hq)
  apply hlim.congr'
  filter_upwards [eventually_ne_cobounded (0 : ℂ)] with z hz
  simpa [hdeg] using (quotient_reverse p q hdeg.le hz).symm

end
end SPR.Segment.Analysis
