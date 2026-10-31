import SPR.Segment.PositiveCone
import SPR.Segment.DualObstruction
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Positive polynomial ratio interpolation

Evaluation identifies coefficient space with node-value space. Two disjoint
interiors would have a nonzero separating functional, excluded by `no_separator`.
Consequently one common vector is interior-positive before and after diagonal
scaling by the prescribed positive ratios.
-/

namespace SPR.Segment.Interpolation

open Polynomial Set Finset

noncomputable section

/-- Simultaneous evaluation at the interpolation nodes. -/
def nodeEvaluation (r : ℕ) (t : Fin (r + 1) → ℝ) :
    (Fin (r + 1) → ℝ) →ₗ[ℝ] (Fin (r + 1) → ℝ) where
  toFun v i := (poly r v).eval (t i)
  map_add' u v := by ext i; simp
  map_smul' c v := by ext i; simp

theorem nodeEvaluation_injective {r : ℕ} {t : Fin (r + 1) → ℝ}
    (ht : Function.Injective t) : Function.Injective (nodeEvaluation r t) := by
  intro u v huv
  have he : poly r u = poly r v :=
    Polynomial.eq_of_degrees_lt_of_eval_index_eq univ (fun _ _ _ _ he => ht he)
      (by simpa using poly_degree r u) (by simpa using poly_degree r v)
      (fun i _ => congrFun huv i)
  funext i
  simpa using congrArg (fun p : ℝ[X] => p.coeff i) he

/-- Distinct-node evaluation is a linear isomorphism. -/
def nodeEquiv (r : ℕ) (t : Fin (r + 1) → ℝ) (ht : Function.Injective t) :
    (Fin (r + 1) → ℝ) ≃ₗ[ℝ] (Fin (r + 1) → ℝ) :=
  LinearEquiv.ofBijective (nodeEvaluation r t)
    ⟨nodeEvaluation_injective ht,
      LinearMap.injective_iff_surjective.mp (nodeEvaluation_injective ht)⟩

/-- Positive diagonal scaling of node values. -/
def ratioEquiv {r : ℕ} (ρ : Fin (r + 1) → ℝ) (hρ : ∀ i, 0 < ρ i) :
    (Fin (r + 1) → ℝ) ≃ₗ[ℝ] (Fin (r + 1) → ℝ) where
  toFun v i := ρ i * v i
  invFun v i := v i / ρ i
  left_inv v := by ext i; exact mul_div_cancel_left₀ (v i) (hρ i).ne'
  right_inv v := by
    ext i
    change ρ i * (v i / ρ i) = v i
    rw [← mul_div_assoc, mul_comm (ρ i) (v i), mul_div_cancel_right₀ _ (hρ i).ne']
  map_add' u v := by ext i; simp [mul_add]
  map_smul' c v := by ext i; simp [mul_left_comm]

/-- Arbitrary positive ratios at `r+1` distinct nonnegative nodes, including zero,
have two globally positive interpolants of degree at most `r`. -/
theorem positive_ratio_interpolation (r : ℕ) (t ρ : Fin (r + 1) → ℝ)
    (o : Fin (r + 1)) (ht : Function.Injective t) (ho : t o = 0)
    (htpos : ∀ i, 0 ≤ t i) (hρ : ∀ i, 0 < ρ i) :
    ∃ u₀ u₁ : ℝ[X], u₀.degree < r + 1 ∧ u₁.degree < r + 1 ∧
      (∀ x : ℝ, 0 ≤ x → 0 < u₀.eval x) ∧
      (∀ x : ℝ, 0 ≤ x → 0 < u₁.eval x) ∧
      ∀ i, u₁.eval (t i) = ρ i * u₀.eval (t i) := by
  let K := nonnegativeCone r
  let E := (nodeEquiv r t ht).toContinuousLinearEquiv
  let R := (ratioEquiv ρ hρ).toContinuousLinearEquiv
  let S := E '' K
  let T := R '' S
  have hSc : Convex ℝ S := (cone_convex r).linear_image E.toLinearMap
  have hTc : Convex ℝ T := hSc.linear_image R.toLinearMap
  have hSint : E '' interior K = interior S := E.toHomeomorph.image_interior K
  have hTint : R '' interior S = interior T := R.toHomeomorph.image_interior S
  have hSi : (interior S).Nonempty := by
    rw [← hSint]
    exact (cone_interior_nonempty r).image E
  have hTi : (interior T).Nonempty := by
    rw [← hTint]
    exact hSi.image R
  have hS0 : (0 : Fin (r + 1) → ℝ) ∈ S := ⟨0, cone_zero r, E.map_zero⟩
  have hT0 : (0 : Fin (r + 1) → ℝ) ∈ T := ⟨0, hS0, R.map_zero⟩
  have hinter : ¬ Disjoint (interior S) (interior T) := by
    intro hdisj
    obtain ⟨f, a, hfS, hfT⟩ := geometric_hahn_banach_open_open
      hSc.interior isOpen_interior hTc.interior isOpen_interior hdisj
    have hSf : ∀ v ∈ S, f v ≤ a := by
      have hclosed : IsClosed {v | f v ≤ a} := isClosed_le f.continuous continuous_const
      have hsub : closure (interior S) ⊆ {v | f v ≤ a} :=
        closure_minimal (fun v hv => (hfS v hv).le) hclosed
      intro v hv
      apply hsub
      rw [hSc.closure_interior_eq_closure_of_nonempty_interior hSi]
      exact subset_closure hv
    have hTf : ∀ v ∈ T, a ≤ f v := by
      have hclosed : IsClosed {v | a ≤ f v} := isClosed_le continuous_const f.continuous
      have hsub : closure (interior T) ⊆ {v | a ≤ f v} :=
        closure_minimal (fun v hv => (hfT v hv).le) hclosed
      intro v hv
      apply hsub
      rw [hTc.closure_interior_eq_closure_of_nonempty_interior hTi]
      exact subset_closure hv
    have ha : a = 0 := by
      have h₀ := hSf 0 hS0
      have h₁ := hTf 0 hT0
      simp only [map_zero] at h₀ h₁
      linarith
    have hfne : f ≠ 0 := by
      obtain ⟨v, hv⟩ := hSi
      intro hz
      have hh := hfS v hv
      simp [hz, ha] at hh
    let y : Fin (r + 1) → ℝ := fun i => -f (fun j => if i = j then 1 else 0)
    have hexp (v : Fin (r + 1) → ℝ) : f v = -(∑ i, y i * v i) := by
      change f.toLinearMap v = _
      rw [LinearMap.pi_apply_eq_sum_univ f.toLinearMap]
      simp [y, mul_comm, sum_neg_distrib]
    have hsep : Separates r t ρ y := by
      intro p hp hpnonneg
      let w := degreeLTEquiv ℝ (r + 1) ⟨p, mem_degreeLT.mpr hp⟩
      have hwpoly : poly r w = p := by simp [poly, w]
      have hwK : w ∈ K := by intro x hx; rw [hwpoly]; exact hpnonneg x hx
      have hvS : E w ∈ S := mem_image_of_mem E hwK
      have hvT : R (E w) ∈ T := mem_image_of_mem R hvS
      have hleft := hSf (E w) hvS
      have hright := hTf (R (E w)) hvT
      rw [ha, hexp] at hleft hright
      have hE (i : Fin (r + 1)) : E w i = p.eval (t i) := by
        change (poly r w).eval (t i) = _
        rw [hwpoly]
      have hR (i : Fin (r + 1)) : R (E w) i = ρ i * p.eval (t i) := by
        change ρ i * E w i = _
        rw [hE]
      simp only [hE] at hleft
      simp only [hR] at hright
      constructor
      · linarith
      · have heq : ∑ i, y i * (ρ i * p.eval (t i)) =
            ∑ i, ρ i * y i * p.eval (t i) := sum_congr rfl (fun _ _ => by ring)
        rw [heq] at hright
        linarith
    have hy := no_separator r (Fintype.card_fin (r + 1)) t ρ o ht ho htpos hρ y hsep
    apply hfne
    ext v
    rw [hexp, hy]
    simp
  obtain ⟨v, hvS, hvT⟩ := Set.not_disjoint_iff.mp hinter
  rw [← hSint] at hvS
  obtain ⟨w₁, hw₁, hv₁⟩ := hvS
  rw [← hTint, ← hSint] at hvT
  obtain ⟨v₀, ⟨w₀, hw₀, hv₀⟩, hRv⟩ := hvT
  refine ⟨poly r w₀, poly r w₁, poly_degree r w₀, poly_degree r w₁,
    fun x hx => interior_eval_pos hw₀ hx, fun x hx => interior_eval_pos hw₁ hx, ?_⟩
  intro i
  have heq : E w₁ = R (E w₀) := hv₁.trans (hRv.symm.trans (congrArg R hv₀.symm))
  exact congrFun heq i

end
end SPR.Segment.Interpolation
