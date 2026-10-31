import SPR.Polytope.CubicSynthesis.Hurwitz
import Mathlib.LinearAlgebra.Lagrange

/-! # Exact finite moment consequences used by the contact classification. -/
namespace SPR.Polytope.CubicSynthesis
open Polynomial
noncomputable section

/-- Vanishing moments annihilate every test polynomial within their degree range. -/
theorem sum_eval_of_moments (S : Finset ℝ) (u : ℝ → ℝ) (d : ℕ)
    (hm : ∀ k ≤ d, ∑ t ∈ S, t^k*u t=0)
    {p : ℝ[X]} (hd : p.natDegree ≤ d) : ∑ t ∈ S, p.eval t*u t=0 := by
  classical
  simp_rw [eval_eq_sum_range' (show p.natDegree < d+1 by omega),Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro k hk
  calc
    ∑ t ∈ S, p.coeff k*t^k*u t=p.coeff k*∑ t ∈ S,t^k*u t := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      ring
    _=0 := by rw [hm k (by have hh := Finset.mem_range.mp hk; omega)]; ring

/-- This is the exact Vandermonde implication, including arbitrary real nodes
and all small or empty supports. Lagrange polynomials avoid numerical inversion. -/
theorem vanishing_moments (S : Finset ℝ) (u : ℝ → ℝ) (d : ℕ)
    (hc : S.card ≤ d+1) (hm : ∀ k ≤ d, ∑ t ∈ S, t^k*u t=0) :
    ∀ t ∈ S, u t=0 := by
  classical
  intro t ht
  let p : ℝ[X] := Lagrange.basis S id t
  have hp : p.natDegree ≤ d := by
    rw [Lagrange.natDegree_basis (by intro x _ y _ h; exact h) ht]
    omega
  have hh := sum_eval_of_moments S u d hm hp
  have he : ∑ r ∈ S,p.eval r*u r=u t := by
    rw [Finset.sum_eq_single t]
    · have hself : p.eval t=1 := by
        exact Lagrange.eval_basis_self (s := S) (v := id)
          (by intro x _ y _ h; exact h) ht
      rw [hself,one_mul]
    · intro r hr hne
      have hother : p.eval r=0 :=
        Lagrange.eval_basis_of_ne (s := S) (v := id) hne.symm hr
      rw [hother,zero_mul]
    · exact fun hn => (hn ht).elim
  exact he.symm.trans hh

/-- Stable cubic geometry at a merged finite node rules out small supports
once the corresponding moments vanish. -/
theorem no_small_moment_support (S : Finset ℝ) (u v : ℝ → ℝ) (d : ℕ)
    (hne : S.Nonempty) (hc : S.card ≤ d+1)
    (ht : ∀ t ∈ S, 0 ≤ t)
    (hzero : 0 ∈ S → 0 < u 0)
    (hsign : ∀ t ∈ S, 0 < t → 0 ≤ u t → 0 < v t)
    (hv : ∑ t ∈ S,v t=0)
    (hm : ∀ k ≤ d, ∑ t ∈ S,t^k*u t=0) : False := by
  have hu := vanishing_moments S u d hc hm
  have hz : 0 ∉ S := by
    intro hh
    have hp := hzero hh
    rw [hu 0 hh] at hp
    linarith
  have hp (t : ℝ) (htS : t ∈ S) : 0 < v t := by
    have htpos : 0 < t := lt_of_le_of_ne (ht t htS) (by
      intro he
      apply hz
      simpa [← he] using htS)
    exact hsign t htS htpos (by rw [hu t htS])
  have hsum : 0 < ∑ t ∈ S,v t := Finset.sum_pos hp hne
  linarith

/-- At a positive node the cubic Routh inequalities give the required strict sign. -/
theorem cubic_node_sign {α β γ κ t : ℝ} (hα : 0 < α) (hκ : 0 < κ)
    (ht : 0 < t) (hD : γ < α*β) (hu : 0 ≤ κ*(γ-α*t)) :
    0 < κ*t*(β-t) := by
  have hA : 0 ≤ γ-α*t := (mul_nonneg_iff_of_pos_left hκ).mp hu
  have hb : t < β := by nlinarith
  positivity

/-- On a support of size at most d+2 a moment-null vector that vanishes at
one support point is zero everywhere. This includes the degenerate small supports. -/
theorem moment_kernel_zero_of_one_zero (S : Finset ℝ) (f : ℝ → ℝ) (d : ℕ)
    (hc : S.card ≤ d+2) (hm : ∀ k ≤ d,∑ t ∈ S,t^k*f t=0)
    {r : ℝ} (hr : r ∈ S) (hz : f r=0) : ∀ t ∈ S,f t=0 := by
  classical
  have hcard : (S.erase r).card ≤ d+1 := by rw [Finset.card_erase_of_mem hr]; omega
  have hmoment : ∀ k ≤ d,∑ t ∈ S.erase r,t^k*f t=0 := by
    intro k hk
    have hh := hm k hk
    rw [← Finset.sum_erase_add _ _ hr,hz,mul_zero,add_zero] at hh
    exact hh
  have he := vanishing_moments (S.erase r) f d hcard hmoment
  intro t ht
  by_cases htr : t=r
  · simpa [htr] using hz
  · exact he t (Finset.mem_erase.mpr ⟨htr,ht⟩)

theorem sum_scaled_difference (S : Finset ℝ) (p f g : ℝ → ℝ) (A : ℝ) :
    (∑ t ∈ S,p t*(f t-A*g t))=(∑ t ∈ S,p t*f t)-A*(∑ t ∈ S,p t*g t) := by
  rw [Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- The moment kernel on d+2 nodes is at most one-dimensional, proved by
one exact scalar division and the preceding zero lemma. -/
theorem moment_kernel_proportional (S : Finset ℝ) (f g : ℝ → ℝ) (d : ℕ)
    (hc : S.card ≤ d+2) (hf : ∀ k ≤ d,∑ t ∈ S,t^k*f t=0)
    (hg : ∀ k ≤ d,∑ t ∈ S,t^k*g t=0) {r : ℝ} (hr : r ∈ S) (hgr : g r ≠ 0) :
    ∀ t ∈ S,f t=(f r/g r)*g t := by
  let A := f r/g r
  have hzero : f r-A*g r=0 := by dsimp [A]; field_simp; ring
  have hmoment : ∀ k ≤ d,∑ t ∈ S,t^k*(f t-A*g t)=0 := by
    intro k hk
    rw [sum_scaled_difference,hf k hk,hg k hk]
    ring
  have hh := moment_kernel_zero_of_one_zero S (fun t => f t-A*g t) d hc hmoment hr hzero
  intro t ht
  exact sub_eq_zero.mp (hh t ht)

/-- With three distinct nodes, a vector of zero total mass is an affine
multiple of a nonzero vector whose first two moments vanish. -/
theorem affine_moment_representation (S : Finset ℝ) (u v : ℝ → ℝ)
    (hc : S.card ≤ 3) (hu0 : ∑ t ∈ S,u t=0) (hu1 : ∑ t ∈ S,t*u t=0)
    (hv0 : ∑ t ∈ S,v t=0) (M R : ℝ)
    (hu2 : ∑ t ∈ S,t^2*u t=M) (hv1 : ∑ t ∈ S,t*v t=R)
    (hM : 0 < M) (hR : 0 < R) (hne : ∃ r ∈ S,u r ≠ 0) :
    ∃ A D : ℝ,0 < A ∧ A*M=R ∧ ∀ t ∈ S,v t=(A*t+D)*u t := by
  let A := R/M
  have hA : 0 < A := div_pos hR hM
  have hAM : A*M=R := div_mul_cancel₀ _ hM.ne'
  let f : ℝ → ℝ := fun t => v t-A*(t*u t)
  have hf : ∀ k ≤ 1,∑ t ∈ S,t^k*f t=0 := by
    intro k hk
    interval_cases k
    · simp only [pow_zero,one_mul,f]
      rw [Finset.sum_sub_distrib,← Finset.mul_sum,hv0,hu1]
      ring
    · have hh := sum_scaled_difference S id v (fun t => t*u t) A
      have he : ∑ t ∈ S,t*(t*u t)=M := by
        convert hu2 using 1
        apply Finset.sum_congr rfl
        intro t _
        ring
      simpa only [id_eq,pow_one,f,hv1,he,hAM,sub_self] using hh
  obtain ⟨r,hr,hurne⟩ := hne
  have hu : ∀ k ≤ 1,∑ t ∈ S,t^k*u t=0 := by
    intro k hk
    interval_cases k
    · simpa using hu0
    · simpa using hu1
  have hprop := moment_kernel_proportional S f u 1 hc hf hu hr hurne
  refine ⟨A,f r/u r,hA,hAM,?_⟩
  intro t ht
  have hh := hprop t ht
  dsimp [f] at hh
  nlinarith

end
end SPR.Polytope.CubicSynthesis
