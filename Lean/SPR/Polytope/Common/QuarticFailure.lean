import SPR.Polytope.Common.Definitions
import SPR.Polytope.QuarticTriangle.Result

/-! # The quartic counterexample in the universal finite-family formulation. -/
namespace SPR.Polytope
open Polynomial
noncomputable section

def quarticFamily : Fin 3 → ℝ[X] :=
  ![QuarticTriangle.a₁.poly, QuarticTriangle.a₂.poly, QuarticTriangle.a₃.poly]

theorem quartic_blend (weights : Fin 3 → ℝ) : blend quarticFamily weights =
    weights 0 • QuarticTriangle.a₁.poly+weights 1 • QuarticTriangle.a₂.poly+
      weights 2 • QuarticTriangle.a₃.poly := by
  simp [blend, quarticFamily, Fin.sum_univ_succ, add_assoc]

theorem quartic_stable : Stable quarticFamily := by
  intro weights hw
  rw [quartic_blend]
  apply QuarticTriangle.counterexample.2.2.2.1
  · exact hw.1 0
  · exact hw.1 1
  · exact hw.1 2
  · simpa [Fin.sum_univ_succ, add_assoc] using hw.2

/-- Every requested degree at most five fails for four-dimensional order and m≥3. -/
theorem quartic_failure {m k : ℕ} (hm : 3 ≤ m) (hk : k ≤ 5) :
    ¬ Universal 4 m k := by
  intro hu
  have ha : ∀ i, (quarticFamily i).Monic ∧ (quarticFamily i).natDegree=4 := by
    intro i
    fin_cases i
    · exact QuarticTriangle.counterexample.1
    · exact QuarticTriangle.counterexample.2.1
    · exact QuarticTriangle.counterexample.2.2.1
  obtain ⟨b,hd,hb⟩ := hu 3 (by omega) hm quarticFamily ha quartic_stable
  apply QuarticTriangle.counterexample.2.2.2.2
  refine ⟨b, hd.le.trans hk, ?_⟩
  intro u v w hu hv hw hs
  have hweights : Weights (![u,v,w] : Fin 3 → ℝ) := by
    constructor
    · intro i; fin_cases i <;> assumption
    · simpa [Fin.sum_univ_succ, add_assoc] using hs
  have h := hb ![u,v,w] hweights
  simpa [quartic_blend] using h

end
end SPR.Polytope
