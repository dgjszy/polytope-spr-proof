import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity

/-!
# Nonnegative test polynomials and the boundary-node degree budget

For a finite set of nonnegative distinct nodes with a distinguished zero node,
the zero at the boundary costs one degree; all other zeros cost two.
The separating functional contradiction uses these polynomials, not a numerical certificate.
-/

namespace SPR.Segment.Interpolation

open Polynomial Finset

noncomputable section

variable {ι : Type*} [DecidableEq ι]

/-- A boundary node contributes `X`; an interior node contributes a square. -/
def nodeFactor (t : ι → ℝ) (o i : ι) : ℝ[X] :=
  if i = o then X else (X - C (t i)) ^ 2

/-- A nonnegative polynomial vanishing exactly on the specified nodes. -/
def zeroTest (t : ι → ℝ) (o : ι) (J : Finset ι) : ℝ[X] :=
  ∏ i ∈ J, nodeFactor t o i

/-- The exact degree cost, recording the one-degree saving at the zero node. -/
def cost (o : ι) (J : Finset ι) : ℕ :=
  ∑ i ∈ J, if i = o then 1 else 2

theorem nodeFactor_monic (t : ι → ℝ) (o i : ι) : (nodeFactor t o i).Monic := by
  unfold nodeFactor
  split_ifs
  · exact monic_X
  · exact (monic_X_sub_C _).pow _

theorem nodeFactor_natDegree (t : ι → ℝ) (o i : ι) :
    (nodeFactor t o i).natDegree = if i = o then 1 else 2 := by
  unfold nodeFactor
  split_ifs <;> simp

theorem zeroTest_monic (t : ι → ℝ) (o : ι) (J : Finset ι) :
    (zeroTest t o J).Monic := by
  exact monic_prod_of_monic _ _ (fun i _ => nodeFactor_monic t o i)

theorem zeroTest_natDegree (t : ι → ℝ) (o : ι) (J : Finset ι) :
    (zeroTest t o J).natDegree = cost o J := by
  rw [zeroTest, natDegree_prod _ _ (fun i _ => (nodeFactor_monic t o i).ne_zero)]
  simp only [nodeFactor_natDegree, cost]

theorem zeroTest_nonneg (t : ι → ℝ) (o : ι) (J : Finset ι)
    {x : ℝ} (hx : 0 ≤ x) : 0 ≤ (zeroTest t o J).eval x := by
  rw [zeroTest, eval_prod]
  apply prod_nonneg
  intro i hi
  unfold nodeFactor
  split_ifs
  · simpa using hx
  · simp only [eval_pow, eval_sub, eval_X, eval_C]
    exact sq_nonneg _

theorem zeroTest_eval_eq_zero_iff (t : ι → ℝ) (o : ι)
    (ht : Function.Injective t) (ho : t o = 0) (J : Finset ι) (k : ι) :
    (zeroTest t o J).eval (t k) = 0 ↔ k ∈ J := by
  simp only [zeroTest, eval_prod, prod_eq_zero_iff]
  constructor
  · rintro ⟨i, hi, hzero⟩
    by_cases hio : i = o
    · have hk : k = o := ht (by simpa [nodeFactor, hio, ho] using hzero)
      simpa [hk, hio] using hi
    · have hk : k = i := ht (by simpa [nodeFactor, hio, sub_eq_zero] using hzero)
      simpa [hk] using hi
  · intro hk
    refine ⟨k, hk, ?_⟩
    by_cases hko : k = o <;> simp [nodeFactor, hko, ho]

theorem zeroTest_eval_pos (t : ι → ℝ) (o : ι)
    (ht : Function.Injective t) (ho : t o = 0) (hpos : ∀ i, 0 ≤ t i)
    (J : Finset ι) {k : ι} (hk : k ∉ J) : 0 < (zeroTest t o J).eval (t k) := by
  exact lt_of_le_of_ne (zeroTest_nonneg t o J (hpos k))
    (Ne.symm (mt (zeroTest_eval_eq_zero_iff t o ht ho J k).mp hk))

theorem cost_eq (o : ι) (J : Finset ι) :
    cost o J = 2 * J.card - if o ∈ J then 1 else 0 := by
  classical
  induction J using Finset.induction_on with
  | empty => simp [cost]
  | @insert i J hi ih =>
    have hcost : cost o (insert i J) = (if i = o then 1 else 2) + cost o J := by
      simp [cost, hi]
    rw [hcost, card_insert_of_notMem hi, ih]
    by_cases hio : i = o
    · subst i
      simp only [mem_insert_self, if_true, if_neg hi]
      omega
    · have hoi : o ≠ i := Ne.symm hio
      simp only [if_neg hio, mem_insert, hoi, false_or]
      split_ifs with hoJ
      · have hJ : 0 < J.card := card_pos.mpr ⟨o, hoJ⟩
        omega
      · omega

variable [Fintype ι]

/-- Disjoint sign supports cannot both require more than half the available degree budget. -/
theorem cost_budget (o : ι) (P N : Finset ι) (hPN : Disjoint P N) :
    cost o P + cost o N ≤ 2 * Fintype.card ι - 1 := by
  have hu : (P ∪ N).card ≤ Fintype.card ι := card_le_univ _
  have hc : (P ∪ N).card = P.card + N.card := card_union_of_disjoint hPN
  rw [cost_eq, cost_eq]
  by_cases hp : o ∈ P
  · have hn : o ∉ N := fun hn => disjoint_left.mp hPN hp hn
    simp only [if_pos hp, if_neg hn]
    have hpc : 0 < P.card := card_pos.mpr ⟨o, hp⟩
    omega
  · by_cases hn : o ∈ N
    · simp only [if_neg hp, if_pos hn]
      have hnc : 0 < N.card := card_pos.mpr ⟨o, hn⟩
      omega
    · have ho : o ∉ P ∪ N := by simpa using And.intro hp hn
      have hlt : (P ∪ N).card < Fintype.card ι :=
        card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ _, by
          intro he
          exact ho (he.symm ▸ mem_univ o)⟩)
      simp only [if_neg hp, if_neg hn]
      omega

/-- With `r+1` nodes, one of the two disjoint supports admits a degree at most `r` test. -/
theorem one_cost_le (r : ℕ) (hcard : Fintype.card ι = r + 1)
    (o : ι) (P N : Finset ι) (hPN : Disjoint P N) :
    cost o P ≤ r ∨ cost o N ≤ r := by
  have h := cost_budget o P N hPN
  rw [hcard] at h
  omega

end
end SPR.Segment.Interpolation
