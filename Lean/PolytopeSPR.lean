import SPR.Polytope.Classification

namespace SPR.Polytope.Direct

/-- Complete classification for all positive denominator orders and all finite
vertex bounds, with actual numerator degrees n−1, n and n+1, unchanged denominators,
one fixed numerator, full convex hulls and all finite real frequencies. -/
theorem classification {n m : ℕ} (hn : 1 ≤ n) :
    (SPR.Polytope.Universal n m (n-1) ↔ n ≤ 2 ∨ m ≤ 2) ∧
    (SPR.Polytope.Universal n m n ↔ n ≤ 2 ∨ m ≤ 2) ∧
    (SPR.Polytope.Universal n m (n+1) ↔ n ≤ 2 ∨ m ≤ 2 ∨ (n=3 ∧ m=3)) :=
  SPR.Polytope.classification_table hn

end SPR.Polytope.Direct
