import SPR.Polytope.Common.SecondOrder
import SPR.Polytope.Common.QuarticFailure
import SPR.Polytope.CubicTriangle.Result

/-!
# Closed cells of the finite-polytope classification

This module collects the low-order cases used by the classification.
-/
namespace SPR.Polytope

/-- Every first- or second-order stable finite family has a numerator of each
of the three requested exact degrees. -/
theorem low_order_classification {n m : ℕ} (hn : 1 ≤ n) (hn2 : n ≤ 2) :
    Universal n m (n-1) ∧ Universal n m n ∧ Universal n m (n+1) := by
  have hc : n=1 ∨ n=2 := by omega
  rcases hc with h | h
  · subst n
    exact ⟨first_order_universal m (by omega),first_order_universal m (by omega),
      first_order_universal m (by omega)⟩
  · subst n
    exact ⟨second_order_universal m (by omega) (by omega),
      second_order_universal m (by omega) (by omega),
      second_order_universal m (by omega) (by omega)⟩

/-- The two lower numerator-degree cells fail for every m≥3 at cubic order. -/
theorem cubic_lower_failure {m : ℕ} (hm : 3 ≤ m) :
    ¬ Universal 3 m 2 ∧ ¬ Universal 3 m 3 :=
  ⟨CubicTriangle.cubic_failure hm (by omega),CubicTriangle.cubic_failure hm (by omega)⟩

/-- All three requested numerator degrees fail for every m≥3 at quartic order. -/
theorem quartic_three_degrees_failure {m : ℕ} (hm : 3 ≤ m) :
    ¬ Universal 4 m 3 ∧ ¬ Universal 4 m 4 ∧ ¬ Universal 4 m 5 :=
  ⟨quartic_failure hm (by omega),quartic_failure hm (by omega),
    quartic_failure hm (by omega)⟩

end SPR.Polytope
