import SPR.Polytope.Transfer.Result
import SPR.Polytope.CubicFourVertices.Result
import SPR.Polytope.Common.VerifiedCells

/-! # The complete necessary half of the n,m classification, without missing inputs. -/
namespace SPR.Polytope

theorem lower_classification_necessary {n m : ℕ}
    (h : Universal n m (n-1) ∨ Universal n m n) : n ≤ 2 ∨ m ≤ 2 := by
  by_contra! hn
  have hn3 : 3 ≤ n := by omega
  have hm3 : 3 ≤ m := by omega
  rcases h with h | h
  · by_cases he : n=3
    · subst n
      exact (cubic_lower_failure hm3).1 h
    · exact higher_failure (by omega) hm3 (by omega) h
  · by_cases he : n=3
    · subst n
      exact (cubic_lower_failure hm3).2 h
    · exact higher_failure (by omega) hm3 (by omega) h

theorem upper_classification_necessary {n m : ℕ} (h : Universal n m (n+1)) :
    n ≤ 2 ∨ m ≤ 2 ∨ (n=3 ∧ m=3) := by
  by_contra! hn
  have hn3 : 3 ≤ n := by omega
  have hm3 : 3 ≤ m := by omega
  by_cases he : n=3
  · subst n
    have hm4 : 4 ≤ m := by omega
    exact CubicFourVertices.cubic_quartic_failure hm4 h
  · exact higher_failure (by omega) hm3 le_rfl h

end SPR.Polytope
