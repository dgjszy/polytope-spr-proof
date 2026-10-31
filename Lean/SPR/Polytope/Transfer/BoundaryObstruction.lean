import SPR.Polytope.Transfer.SeedIndependence

/-! # Joint-factor boundary obstruction in every order, for both parities. -/
namespace SPR.Polytope.Transfer
open Polynomial Complex
noncomputable section

def base (odd : Bool) (i : Fin 3) : ℝ[X] := if odd then X*seed i else seed i

def order (r : ℕ) (odd : Bool) : ℕ := (if odd then 5 else 4)+2*r

def boundary (r : ℕ) (odd : Bool) (i : Fin 3) : ℝ[X] := factors (nodes r)*base odd i

theorem base_independent (odd : Bool) {T : ℝ} (hT : 0 < T) (hs : T < 1/100) :
    IndependentAt (base odd) T := by
  cases odd
  · exact seed_independent hT hs
  · apply independent_multiply (a := seed) (g := X) (seed_independent hT hs)
    simp only [Segment.value,eval₂_X]
    exact mul_ne_zero I_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hT).ne')

/-- Every nonzero bounded-degree weak limit is excluded, including the constant
sign retained from zero frequency in the odd case. No approximant is singular. -/
theorem boundary_obstruction (r : ℕ) (odd : Bool) :
    ¬ ∃ B : ℝ[X], B ≠ 0 ∧ B.natDegree ≤ order r odd+1 ∧ 0 ≤ B.coeff 0 ∧
      ∀ i ω, 0 ≤ Segment.pairing (boundary r odd i) B ω := by
  rintro ⟨B,hB,hd,hc,hw⟩
  have hS : ∀ T ∈ nodes r, 0 < T := fun T hT => (node_bounds hT).1
  have hI : ∀ T ∈ nodes r, IndependentAt (base odd) T :=
    fun T hT => base_independent odd (node_bounds hT).1 (node_bounds hT).2
  have hdeg : B.natDegree ≤ (if odd then 6 else 5)+2*(nodes r).card := by
    rw [nodes_card]
    cases odd <;> simp only [order,Bool.false_eq_true,if_false,if_true] at hd ⊢ <;> omega
  obtain ⟨D,hD,hdD,hcD,_,hwD⟩ := joint_remove (nodes r) (base odd)
    (if odd then 6 else 5) hS hI B hB hdeg hc hw
  cases odd
  · apply WeakSeed.no_nonzero_weak_pairing
    refine ⟨D,hD,hdD,?_,?_,?_⟩
    · simpa [base,seed] using hwD 0
    · simpa [base,seed] using hwD 1
    · simpa [base,seed] using hwD 2
  · apply WeakSeed.no_nonzero_odd_boundary
    refine ⟨D,hD,hdD,hcD,?_,?_,?_⟩
    · simpa [base,seed] using hwD 0
    · simpa [base,seed] using hwD 1
    · simpa [base,seed] using hwD 2

end
end SPR.Polytope.Transfer
