import SPR.Segment.QuadraticDivisibility
import SPR.Segment.OddRootFactorization

/-!
# The simple crossing product and its exact degree

The squared-frequency lift differs from the monic crossing product only by
`(-1)^r`. Its degree is `2r+1`, supplying the degree reduction in elimination.
-/

namespace SPR.Segment

open Polynomial Finset

noncomputable section

/-- The monic product of the simple imaginary crossing factors and zero. -/
def crossingProduct (J : Finset ℝ) : ℝ[X] :=
  X * (∏ t ∈ J, crossingQuadratic t)

theorem crossingProduct_monic (J : Finset ℝ) : (crossingProduct J).Monic :=
  monic_X.mul (monic_prod_of_monic _ _ (fun t _ => crossingQuadratic_monic t))

theorem crossingProduct_degree (J : Finset ℝ) :
    (crossingProduct J).natDegree = 2 * J.card + 1 := by
  rw [crossingProduct, natDegree_mul monic_X.ne_zero
    (monic_prod_of_monic _ _ (fun t _ => crossingQuadratic_monic t)).ne_zero,
    natDegree_X, natDegree_prod_of_monic _ _ (fun t _ => crossingQuadratic_monic t)]
  simp only [crossingQuadratic_degree, sum_const, smul_eq_mul]
  omega

theorem lift_oddRootProduct (d : ℝ[X]) :
    X * frequencyLift (Algebra.oddRootProduct d) =
      C ((-1 : ℝ) ^ (Algebra.positiveOddRoots d).card) *
        crossingProduct (Algebra.positiveOddRoots d) := by
  simp only [Algebra.oddRootProduct, frequencyLift, Polynomial.prod_comp,
    sub_comp, X_comp, C_comp]
  have h (t : ℝ) : -(X ^ 2) - C t = C (-1 : ℝ) * crossingQuadratic t := by
    simp [crossingQuadratic]; ring
  simp_rw [h]
  rw [prod_mul_distrib]
  simp only [prod_const, ← map_pow]
  unfold crossingProduct
  ring

theorem frequencyLift_ne_zero {p : ℝ[X]} (hp : p ≠ 0) : frequencyLift p ≠ 0 := by
  intro hh
  have hc : (frequencyLift p).leadingCoeff ≠ 0 := by
    rw [frequencyLift, leadingCoeff_comp (by simp)]
    exact mul_ne_zero (leadingCoeff_ne_zero.mpr hp)
      (pow_ne_zero _ (by simp))
  exact hc (by rw [hh]; simp)

theorem frequencyLift_degree (p : ℝ[X]) :
    (frequencyLift p).natDegree = 2 * p.natDegree := by
  simp [frequencyLift, natDegree_comp, mul_comm]

end
end SPR.Segment
