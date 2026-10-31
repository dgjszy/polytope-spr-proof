import SPR.Polytope.CubicSynthesis.Result

/-! # Complete finite-vertex classification for the three exact numerator degrees.

`Universal n m k` quantifies over every nonempty family with at most `m` listed
vertices, monic exact denominator degree `n`, and full convex-hull strict Hurwitz
stability. Its witness has actual degree `k` and works at every finite real frequency.
The original denominator is kept throughout.
-/
namespace SPR.Polytope

/-- The sole additional positive cell in the numerator degree n+1 column is
the cubic triangle. All other high-order polytopes with at least three vertices fail. -/
theorem upper_classification {n m : ℕ} (hn : 1 ≤ n) :
    Universal n m (n+1) ↔ n ≤ 2 ∨ m ≤ 2 ∨ (n=3 ∧ m=3) := by
  constructor
  · exact upper_classification_necessary
  · intro h
    rcases h with hn2 | hm2 | ⟨hn3,hm3⟩
    · exact (low_order_classification hn hn2).2.2
    · exact at_most_two_improper hn hm2
    · subst n; subst m
      exact cubic_triangle_quartic

/-- The whole table as three biconditionals, for every positive denominator
order and every natural vertex bound, including the vacuous zero bound. -/
theorem classification_table {n m : ℕ} (hn : 1 ≤ n) :
    (Universal n m (n-1) ↔ n ≤ 2 ∨ m ≤ 2) ∧
    (Universal n m n ↔ n ≤ 2 ∨ m ≤ 2) ∧
    (Universal n m (n+1) ↔ n ≤ 2 ∨ m ≤ 2 ∨ (n=3 ∧ m=3)) :=
  ⟨lower_classification hn,same_classification hn,upper_classification hn⟩

/-- A single test for any of the three requested actual numerator degrees. -/
theorem requested_degree_classification {n m k : ℕ} (hn : 1 ≤ n)
    (hk : k=n-1 ∨ k=n ∨ k=n+1) :
    Universal n m k ↔ n ≤ 2 ∨ m ≤ 2 ∨ (n=3 ∧ m=3 ∧ k=4) := by
  rcases hk with rfl | rfl | rfl
  · rw [lower_classification hn]
    omega
  · rw [same_classification hn]
    omega
  · rw [upper_classification hn]
    omega

end SPR.Polytope
