import SPR.Polytope.CubicSynthesis.Pairing

/-! # Complete positive contact count for a nonnegative cubic pairing. -/
namespace SPR.Polytope.CubicSynthesis
open Polynomial Filter
open scoped Topology
noncomputable section

theorem derivative_zero_at_positive_contact {p : ℝ[X]}
    (hp : ∀ t : ℝ, 0 ≤ t → 0 ≤ p.eval t) {r : ℝ} (hr : 0 < r) (hz : p.eval r=0) :
    p.derivative.eval r=0 := by
  have hm : IsLocalMin (fun t : ℝ => p.eval t) r := by
    change ∀ᶠ t in 𝓝 r, p.eval r ≤ p.eval t
    filter_upwards [Ioi_mem_nhds hr] with t ht
    rw [hz]
    exact hp t ht.le
  exact hm.hasDerivAt_eq_zero (p.hasDerivAt r)

theorem squared_factor_at_contact {p : ℝ[X]} (hp0 : p ≠ 0)
    (hp : ∀ t : ℝ, 0 ≤ t → 0 ≤ p.eval t) {r : ℝ} (hr : 0 < r) (hz : p.eval r=0) :
    (X-C r)^2 ∣ p := by
  have hm : 1 < p.rootMultiplicity r := (one_lt_rootMultiplicity_iff_isRoot hp0).mpr
    ⟨hz,derivative_zero_at_positive_contact hp hr hz⟩
  exact (le_rootMultiplicity_iff hp0).mp (by omega : 2 ≤ p.rootMultiplicity r)

/-- A nonzero polynomial of degree at most three, nonnegative on the full
half-axis, cannot have two distinct positive contacts. -/
theorem at_most_one_positive_contact {p : ℝ[X]} (hp0 : p ≠ 0) (hd : p.natDegree ≤ 3)
    (hp : ∀ t : ℝ, 0 ≤ t → 0 ≤ p.eval t) {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hpr : p.eval r=0) (hps : p.eval s=0) : r=s := by
  by_contra hne
  have hcop : IsCoprime ((X-C r : ℝ[X])^2) ((X-C s : ℝ[X])^2) :=
    (isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hne))).pow
  have hdiv := hcop.mul_dvd (squared_factor_at_contact hp0 hp hr hpr)
    (squared_factor_at_contact hp0 hp hs hps)
  have hdegree := natDegree_le_of_dvd hdiv hp0
  have hfour : (((X-C r : ℝ[X])^2)*((X-C s)^2)).natDegree=4 := by compute_degree!
  rw [hfour] at hdegree
  omega

def pairPoly (α β γ : ℝ) (v : Vec) : ℝ[X] :=
  C (v 3-α*v 4)*X^3+C (γ*v 4+α*v 2-β*v 3-v 1)*X^2+
    C (β*v 1-γ*v 2-α*v 0)*X+C (γ*v 0)

theorem pairPoly_eval (α β γ : ℝ) (v : Vec) (t : ℝ) :
    (pairPoly α β γ v).eval t=G α β γ v t := by simp [pairPoly,G]

theorem pairPoly_degree (α β γ : ℝ) (v : Vec) : (pairPoly α β γ v).natDegree ≤ 3 := by
  unfold pairPoly
  compute_degree!

end
end SPR.Polytope.CubicSynthesis
