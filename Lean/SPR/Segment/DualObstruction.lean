import SPR.Segment.SignCounting
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Excluding the finite-node separating functional

Two opposite positive-weight inequalities on every half-line nonnegative
polynomial of degree at most `r` force the node functional to vanish.
The proof includes zero components and the case `r = 0`.
-/

namespace SPR.Segment.Interpolation

open Polynomial Finset

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- The two inequalities that a separating node functional would satisfy. -/
def Separates (r : ℕ) (t ρ y : ι → ℝ) : Prop :=
  ∀ p : ℝ[X], p.degree < r + 1 → (∀ x : ℝ, 0 ≤ x → 0 ≤ p.eval x) →
    0 ≤ ∑ i, y i * p.eval (t i) ∧ ∑ i, ρ i * y i * p.eval (t i) ≤ 0

/-- Positive and negative supports are both nonempty for a nonzero separator. -/
theorem separator_has_both_signs {r : ℕ} {t ρ y : ι → ℝ}
    (hρ : ∀ i, 0 < ρ i) (hsep : Separates r t ρ y) (hy : y ≠ 0) :
    (∃ i, 0 < y i) ∧ ∃ i, y i < 0 := by
  classical
  have hconst := hsep 1 (by simp only [degree_one]; positivity) (by simp)
  simp only [eval_one, mul_one] at hconst
  constructor
  · by_contra! hn
    have heq : ∑ i, y i = 0 := le_antisymm (sum_nonpos (fun i _ => hn i)) hconst.1
    have hall := (sum_eq_zero_iff_of_nonpos (fun i (_ : i ∈ univ) => hn i)).mp heq
    exact hy (funext (fun i => hall i (mem_univ i)))
  · by_contra! hn
    have hp (i : ι) : 0 ≤ ρ i * y i := mul_nonneg (hρ i).le (hn i)
    have heq : ∑ i, ρ i * y i = 0 := le_antisymm hconst.2 (sum_nonneg (fun i _ => hp i))
    have hall := (sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ univ) => hp i)).mp heq
    apply hy
    funext i
    exact (mul_eq_zero.mp (hall i (mem_univ i))).resolve_left (ne_of_gt (hρ i))

/-- The boundary-node degree budget rules out every nonzero separator. -/
theorem no_separator (r : ℕ) (hcard : Fintype.card ι = r + 1)
    (t ρ : ι → ℝ) (o : ι) (ht : Function.Injective t) (ho : t o = 0)
    (htpos : ∀ i, 0 ≤ t i) (hρ : ∀ i, 0 < ρ i)
    (y : ι → ℝ) (hsep : Separates r t ρ y) : y = 0 := by
  classical
  by_contra hy
  obtain ⟨⟨ip, hip⟩, ⟨ineg, hineg⟩⟩ := separator_has_both_signs hρ hsep hy
  let P : Finset ι := univ.filter (fun i => 0 < y i)
  let N : Finset ι := univ.filter (fun i => y i < 0)
  have hPN : Disjoint P N := by
    rw [disjoint_left]
    intro i hiP hiN
    exact (not_lt_of_ge (mem_filter.mp hiP).2.le) (mem_filter.mp hiN).2
  rcases one_cost_le r hcard o P N hPN with hP | hN
  · let f := zeroTest t o P
    have hdegree : f.degree < r + 1 := by
      rw [degree_eq_natDegree (zeroTest_monic t o P).ne_zero, zeroTest_natDegree]
      exact_mod_cast Nat.lt_succ_of_le hP
    have hle (i : ι) : y i * f.eval (t i) ≤ 0 := by
      by_cases hi : i ∈ P
      · rw [(zeroTest_eval_eq_zero_iff t o ht ho P i).mpr hi]
        simp
      · have hyi : y i ≤ 0 := by simpa [P] using hi
        exact mul_nonpos_of_nonpos_of_nonneg hyi (zeroTest_nonneg t o P (htpos i))
    have hiN : ineg ∉ P := by simp [P, not_lt_of_ge hineg.le]
    have hlt : y ineg * f.eval (t ineg) < 0 :=
      mul_neg_of_neg_of_pos hineg (zeroTest_eval_pos t o ht ho htpos P hiN)
    have hsum : ∑ i, y i * f.eval (t i) < 0 :=
      sum_neg' (fun i _ => hle i) ⟨ineg, mem_univ ineg, hlt⟩
    exact (not_lt_of_ge (hsep f hdegree (fun x hx => zeroTest_nonneg t o P hx)).1) hsum
  · let f := zeroTest t o N
    have hdegree : f.degree < r + 1 := by
      rw [degree_eq_natDegree (zeroTest_monic t o N).ne_zero, zeroTest_natDegree]
      exact_mod_cast Nat.lt_succ_of_le hN
    have hle (i : ι) : -(ρ i * y i * f.eval (t i)) ≤ 0 := by
      by_cases hi : i ∈ N
      · rw [(zeroTest_eval_eq_zero_iff t o ht ho N i).mpr hi]
        simp
      · have hyi : 0 ≤ y i := by simpa [N] using hi
        exact neg_nonpos.mpr (mul_nonneg (mul_nonneg (hρ i).le hyi)
          (zeroTest_nonneg t o N (htpos i)))
    have hiP : ip ∉ N := by simp [N, not_lt_of_ge hip.le]
    have hlt : -(ρ ip * y ip * f.eval (t ip)) < 0 := neg_neg_of_pos
      (mul_pos (mul_pos (hρ ip) hip) (zeroTest_eval_pos t o ht ho htpos N hiP))
    have hsum : ∑ i, -(ρ i * y i * f.eval (t i)) < 0 :=
      sum_neg' (fun i _ => hle i) ⟨ip, mem_univ ip, hlt⟩
    rw [sum_neg_distrib] at hsum
    have hh := (hsep f hdegree (fun x hx => zeroTest_nonneg t o N hx)).2
    linarith

end
end SPR.Segment.Interpolation
