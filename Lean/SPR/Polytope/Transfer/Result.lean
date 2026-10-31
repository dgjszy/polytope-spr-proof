import SPR.Polytope.Transfer.StableApproximants

/-! # Strictly stable three-vertex counterexamples in every order n≥4. -/
namespace SPR.Polytope
open Polynomial
noncomputable section

theorem common_vertex {r : ℕ} {a : Fin r → ℝ[X]} {B : ℝ[X]}
    (h : Common a B) (i : Fin r) : Segment.FrequencySPR (a i) B := by
  classical
  let weights : Fin r → ℝ := fun j => if j=i then 1 else 0
  have hw : Weights weights := by
    constructor
    · intro j; dsimp [weights]; split_ifs <;> norm_num
    · simp [weights]
  simpa [blend,weights] using h weights hw

namespace Transfer

/-- The actual approximant construction retains all three genuine vertices. -/
theorem family_affine_independent (r : ℕ) (odd : Bool) (ε x y : ℝ)
    (h : x • (family r odd ε 1-family r odd ε 0)+
      y • (family r odd ε 2-family r odd ε 0)=0) : x=0 ∧ y=0 := by
  have hm := (multiplier_monic r odd ε).ne_zero
  have he : multiplier r odd ε*
      (x • (seed 1-seed 0)+y • (seed 2-seed 0))=0 := by
    simpa only [family,smul_eq_C_mul,mul_sub,mul_add,mul_left_comm,mul_assoc] using h
  have hc := (mul_eq_zero.mp he).resolve_left hm
  exact WeakSeed.affine_independent x y (by simpa [seed] using hc)

theorem parity_counterexample (r : ℕ) (odd : Bool) :
    ∃ a : Fin 3 → ℝ[X],
      (∀ i, (a i).Monic ∧ (a i).natDegree=order r odd) ∧ Stable a ∧
      ¬ ∃ B : ℝ[X], B.natDegree ≤ order r odd+1 ∧ Common a B := by
  obtain ⟨ε,hε,hno⟩ := exists_infeasible_perturbation (order r odd+1)
    (family r odd) (boundary r odd) (family_value_limit r odd)
    (fun ε hε i => family_constant_pos r odd hε i) (boundary_obstruction r odd)
  refine ⟨family r odd ε,family_degree r odd ε,family_stable r odd hε,?_⟩
  rintro ⟨B,hd,hB⟩
  exact hno ⟨B,hd,fun i => common_vertex hB i⟩

/-- Every n≥4 has a stable three-vertex family that excludes the complete space
of arbitrary real numerator polynomials of degree at most n+1. -/
theorem higher_counterexample (n : ℕ) (hn : 4 ≤ n) :
    ∃ a : Fin 3 → ℝ[X],
      (∀ i, (a i).Monic ∧ (a i).natDegree=n) ∧ Stable a ∧
      ¬ ∃ B : ℝ[X], B.natDegree ≤ n+1 ∧ Common a B := by
  let r := (n-4)/2
  have hmod : (n-4)%2 < 2 := Nat.mod_lt _ (by omega)
  have heq := Nat.mod_add_div (n-4) 2
  have hcases : n=order r false ∨ n=order r true := by
    dsimp [order,r]
    omega
  rcases hcases with h | h
  · rw [h]
    exact parity_counterexample r false
  · rw [h]
    exact parity_counterexample r true

end Transfer

/-- The three negative high-order columns, now with every original quantifier. -/
theorem higher_failure {n m k : ℕ} (hn : 4 ≤ n) (hm : 3 ≤ m) (hk : k ≤ n+1) :
    ¬ Universal n m k := by
  intro hu
  obtain ⟨a,ha,hs,hno⟩ := Transfer.higher_counterexample n hn
  obtain ⟨B,hd,hB⟩ := hu 3 (by omega) hm a ha hs
  exact hno ⟨B,hd.le.trans hk,hB⟩

theorem higher_three_degrees_failure {n m : ℕ} (hn : 4 ≤ n) (hm : 3 ≤ m) :
    ¬ Universal n m (n-1) ∧ ¬ Universal n m n ∧ ¬ Universal n m (n+1) :=
  ⟨higher_failure hn hm (by omega),higher_failure hn hm (by omega),higher_failure hn hm le_rfl⟩

end
end SPR.Polytope
