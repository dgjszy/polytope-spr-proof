import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Polynomial.Order
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Positive odd-multiplicity roots and the nonnegative remainder

Extract all real roots with their full multiplicities. The root-free remainder
has a constant sign. Each positive odd root contributes one linear factor;
all remaining positive-root powers are even. Nonpositive roots contribute
nonnegative factors on the closed half-line, including a possible zero root.
-/

namespace SPR.Segment.Algebra

open Polynomial Finset

noncomputable section

/-- Distinct positive real roots whose full multiplicity is odd. -/
def positiveOddRoots (p : ℝ[X]) : Finset ℝ :=
  p.roots.toFinset.filter (fun t => 0 < t ∧ Odd (p.roots.count t))

/-- The residual multiplicity after removing one copy of every positive odd root. -/
def residualMultiplicity (p : ℝ[X]) (t : ℝ) : ℕ :=
  p.roots.count t - if t ∈ positiveOddRoots p then 1 else 0

/-- The residual real-root factors. -/
def residualRootProduct (p : ℝ[X]) : ℝ[X] :=
  ∏ t ∈ p.roots.toFinset, (X - C t) ^ residualMultiplicity p t

/-- One simple factor for each distinct positive odd root. -/
def oddRootProduct (p : ℝ[X]) : ℝ[X] :=
  ∏ t ∈ positiveOddRoots p, (X - C t)

theorem positiveOddRoots_pos {p : ℝ[X]} {t : ℝ} (ht : t ∈ positiveOddRoots p) : 0 < t :=
  (mem_filter.mp ht).2.1

theorem residualMultiplicity_even {p : ℝ[X]} {t : ℝ}
    (ht : t ∈ p.roots.toFinset) (hpos : 0 < t) : Even (residualMultiplicity p t) := by
  have hcount : 0 < p.roots.count t := Multiset.count_pos.mpr (Multiset.mem_toFinset.mp ht)
  unfold residualMultiplicity
  by_cases hodd : Odd (p.roots.count t)
  · have hJ : t ∈ positiveOddRoots p := mem_filter.mpr ⟨ht, hpos, hodd⟩
    rw [if_pos hJ]
    rw [Nat.even_iff]
    rw [Nat.odd_iff] at hodd
    omega
  · have hJ : t ∉ positiveOddRoots p := by
      intro hh
      exact hodd (mem_filter.mp hh).2.2
    rw [if_neg hJ, Nat.sub_zero]
    exact (Nat.even_or_odd _).resolve_right hodd

theorem residualRootProduct_nonneg (p : ℝ[X]) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ (residualRootProduct p).eval x := by
  rw [residualRootProduct, eval_prod]
  apply prod_nonneg
  intro t ht
  rw [eval_pow, eval_sub, eval_X, eval_C]
  by_cases hp : 0 < t
  · exact (residualMultiplicity_even ht hp).pow_nonneg _
  · exact pow_nonneg (by linarith [le_of_not_gt hp]) _

theorem residualRootProduct_monic (p : ℝ[X]) : (residualRootProduct p).Monic :=
  monic_prod_of_monic _ _ (fun t _ => (monic_X_sub_C t).pow _)

theorem root_factor_split (p : ℝ[X]) :
    (p.roots.map (fun t => X - C t)).prod = residualRootProduct p * oddRootProduct p := by
  rw [Finset.prod_multiset_map_count]
  have hsplit (t : ℝ) (ht : t ∈ p.roots.toFinset) :
      (X - C t) ^ p.roots.count t =
        (X - C t) ^ residualMultiplicity p t *
          (if t ∈ positiveOddRoots p then X - C t else 1) := by
    unfold residualMultiplicity
    by_cases hJ : t ∈ positiveOddRoots p
    · have hcount : 0 < p.roots.count t :=
        Multiset.count_pos.mpr (Multiset.mem_toFinset.mp ht)
      simp only [if_pos hJ]
      rw [← pow_succ, Nat.sub_add_cancel hcount]
    · simp [hJ]
  calc
    _ = ∏ t ∈ p.roots.toFinset,
        ((X - C t) ^ residualMultiplicity p t *
          (if t ∈ positiveOddRoots p then X - C t else 1)) :=
      Finset.prod_congr rfl (fun t ht => hsplit t ht)
    _ = _ := by
      rw [prod_mul_distrib]
      congr 1
      unfold oddRootProduct
      rw [← Finset.prod_filter]
      congr 1
      ext t
      simp only [mem_filter, and_iff_right_iff_imp]
      exact fun ht => (mem_filter.mp ht).1
/-- Every nonzero real polynomial factors into a nonzero scalar, a nonzero
half-line nonnegative polynomial, and one simple factor per positive odd root. -/
theorem nonnegative_remainder {p : ℝ[X]} (hp : p ≠ 0) :
    ∃ κ : ℝ, ∃ Q : ℝ[X], κ ≠ 0 ∧ Q ≠ 0 ∧
      (∀ x : ℝ, 0 ≤ x → 0 ≤ Q.eval x) ∧
      p = C κ * Q * oddRootProduct p := by
  obtain ⟨q, hq, _, hroots⟩ := p.exists_prod_multiset_X_sub_C_mul
  have hqne : q ≠ 0 := by intro he; apply hp; rw [← hq, he, mul_zero]
  have hno (x : ℝ) : ¬q.IsRoot x := by
    intro hx
    have hm := (mem_roots hqne).mpr hx
    simp [hroots] at hm
  by_cases hsign : 0 ≤ q.leadingCoeff
  · refine ⟨1, q * residualRootProduct p, one_ne_zero,
      mul_ne_zero hqne (residualRootProduct_monic p).ne_zero, ?_, ?_⟩
    · intro x hx
      rw [eval_mul]
      exact mul_nonneg (zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg
        (fun y hy => (hno y hy).elim) hsign).le (residualRootProduct_nonneg p hx)
    · calc
        p = (p.roots.map (fun t => X - C t)).prod * q := hq.symm
        _ = _ := by rw [root_factor_split]; simp only [C_1, one_mul]; ring
  · have hsign' : 0 ≤ (-q).leadingCoeff := by simp [leadingCoeff_neg]; linarith
    have hno' (x : ℝ) : ¬(-q).IsRoot x := by simpa [IsRoot, eval_neg] using hno x
    refine ⟨-1, (-q) * residualRootProduct p, by norm_num,
      mul_ne_zero (neg_ne_zero.mpr hqne) (residualRootProduct_monic p).ne_zero, ?_, ?_⟩
    · intro x hx
      rw [eval_mul]
      exact mul_nonneg (zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg
        (fun y hy => (hno' y hy).elim) hsign').le (residualRootProduct_nonneg p hx)
    · calc
        p = (p.roots.map (fun t => X - C t)).prod * q := hq.symm
        _ = _ := by rw [root_factor_split]; simp; ring

end
end SPR.Segment.Algebra
