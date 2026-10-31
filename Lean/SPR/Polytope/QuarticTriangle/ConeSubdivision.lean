import Mathlib

/-!
# Exhaustive subdivision of the nonnegative three-dimensional cone

The four sub-cones are the three vertex regions and the central region of a
triangle. This is a covering lemma, not a sampled positivity test.
-/
namespace SPR.Polytope.QuarticTriangle

def ConePositive (f : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ u v w, 0 ≤ u → 0 ≤ v → 0 ≤ w → 0 < u+v+w → 0 < f u v w

theorem positive_coordinate {u v w : ℝ} (h : 0 < u+v+w) :
    0 < u ∨ 0 < v ∨ 0 < w := by
  by_contra! hn
  linarith

theorem cone_subdivision (f : ℝ → ℝ → ℝ → ℝ)
    (h0 : ConePositive (fun u v w => f (u+v/2+w/2) (v/2) (w/2)))
    (h1 : ConePositive (fun u v w => f (u/2) (u/2+v+w/2) (w/2)))
    (h2 : ConePositive (fun u v w => f (u/2) (v/2) (u/2+v/2+w)))
    (h3 : ConePositive (fun u v w => f (u/2+v/2) (v/2+w/2) (u/2+w/2))) :
    ConePositive f := by
  intro u v w hu hv hw hs
  by_cases h : v+w ≤ u
  · convert h0 (u-v-w) (2*v) (2*w) (by linarith) (by positivity)
      (by positivity) (by linarith) using 1 <;> congr 1 <;> ring
  by_cases h' : u+w ≤ v
  · convert h1 (2*u) (v-u-w) (2*w) (by positivity) (by linarith)
      (by positivity) (by linarith) using 1 <;> congr 1 <;> ring
  by_cases h'' : u+v ≤ w
  · convert h2 (2*u) (2*v) (w-u-v) (by positivity) (by positivity)
      (by linarith) (by linarith) using 1 <;> congr 1 <;> ring
  · convert h3 (u+w-v) (u+v-w) (v+w-u) (by linarith) (by linarith)
      (by linarith) (by linarith) using 1 <;> congr 1 <;> ring

end SPR.Polytope.QuarticTriangle
