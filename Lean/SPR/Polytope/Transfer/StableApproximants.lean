import SPR.Polytope.Transfer.BoundaryObstruction
import SPR.Polytope.Transfer.Perturbation
import SPR.Polytope.Common.StableFactor
import SPR.N4.Hurwitz

/-! # Explicit strictly stable approximants of the joint imaginary-axis boundary. -/
namespace SPR.Polytope.Transfer
open Polynomial Complex Filter
open scoped Topology
noncomputable section

def shiftedQuadratic (ε T : ℝ) : ℝ[X] := X^2+C (2*ε)*X+C (ε^2+T)

theorem shiftedQuadratic_degree (ε T : ℝ) :
    (shiftedQuadratic ε T).Monic ∧ (shiftedQuadratic ε T).natDegree=2 := by
  have hm : (shiftedQuadratic ε T).Monic := by dsimp [shiftedQuadratic]; monicity!
  have hd : (shiftedQuadratic ε T).natDegree=2 := by dsimp [shiftedQuadratic]; compute_degree!
  exact ⟨hm,hd⟩

theorem shiftedQuadratic_hurwitz {ε T : ℝ} (hε : 0 < ε) (hT : 0 < T) :
    IsHurwitz (shiftedQuadratic ε T) := by
  intro z hz
  have he : Segment.value (shiftedQuadratic ε T) z=0 := by
    simpa [Segment.value,IsRoot,eval_map] using hz
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  simp [Segment.value,shiftedQuadratic,pow_succ,Complex.mul_re,Complex.mul_im] at hre him
  have hi : 2*(z.re+ε)*z.im=0 := by nlinarith [him]
  rcases mul_eq_zero.mp hi with h | h
  · linarith
  · rw [h] at hre
    nlinarith [sq_nonneg (z.re+ε)]

def multiplier (r : ℕ) (odd : Bool) (ε : ℝ) : ℝ[X] :=
  (if odd then X+C ε else 1)*∏ T ∈ nodes r, shiftedQuadratic ε T

def family (r : ℕ) (odd : Bool) (ε : ℝ) (i : Fin 3) : ℝ[X] :=
  multiplier r odd ε*seed i

theorem seed_stable : Polytope.Stable seed := by
  intro weights hw
  have hh := WeakSeed.stable (hw.1 0) (hw.1 1) (hw.1 2)
    (by simpa [Fin.sum_univ_succ,add_assoc] using hw.2)
  simpa [Polytope.blend,seed,Fin.sum_univ_succ,add_assoc] using hh

theorem seed_degree (i : Fin 3) : (seed i).Monic ∧ (seed i).natDegree=4 := by
  fin_cases i <;> exact (N4.poly_degree _).symm

theorem multiplier_monic (r : ℕ) (odd : Bool) (ε : ℝ) : (multiplier r odd ε).Monic := by
  apply Monic.mul
  · cases odd
    · exact monic_one
    · exact monic_X_add_C ε
  · exact monic_prod_of_monic _ _ (fun T _ => (shiftedQuadratic_degree ε T).1)

theorem multiplier_degree (r : ℕ) (odd : Bool) (ε : ℝ) :
    (multiplier r odd ε).natDegree=(if odd then 1 else 0)+2*r := by
  have hprod : (∏ T ∈ nodes r, shiftedQuadratic ε T).natDegree=2*r := by
    rw [natDegree_prod]
    · simp [shiftedQuadratic_degree,nodes_card,Nat.mul_comm]
    · intro T _
      exact (shiftedQuadratic_degree ε T).1.ne_zero
  have hfirst : (if odd then (X+C ε : ℝ[X]) else 1).Monic := by
    cases odd
    · exact monic_one
    · exact monic_X_add_C ε
  rw [multiplier,natDegree_mul hfirst.ne_zero (monic_prod_of_monic _ _
    (fun T _ => (shiftedQuadratic_degree ε T).1)).ne_zero,hprod]
  cases odd <;> simp

theorem family_degree (r : ℕ) (odd : Bool) (ε : ℝ) (i : Fin 3) :
    (family r odd ε i).Monic ∧ (family r odd ε i).natDegree=order r odd := by
  refine ⟨(multiplier_monic r odd ε).mul (seed_degree i).1,?_⟩
  rw [family,natDegree_mul (multiplier_monic _ _ _).ne_zero (seed_degree i).1.ne_zero,
    multiplier_degree,(seed_degree i).2]
  cases odd <;> simp [order] <;> omega

theorem multiplier_hurwitz (r : ℕ) (odd : Bool) {ε : ℝ} (hε : 0 < ε) :
    IsHurwitz (multiplier r odd ε) := by
  have hfirst : IsHurwitz (if odd then (X+C ε : ℝ[X]) else 1) := by
    cases odd
    · intro z hz; simpa [IsRoot] using hz
    · intro z hz
      have he : z+(ε:ℂ)=0 := by simpa [IsRoot,eval_map] using hz
      have hr := congrArg Complex.re he
      simp at hr
      linarith
  apply Polytope.hurwitz_mul _ hfirst
  have hp (S : Finset ℝ) : (∀ T ∈ S, 0 < T) →
      IsHurwitz (∏ T ∈ S, shiftedQuadratic ε T) := by
    classical
    induction S using Finset.induction_on with
    | empty => intro _ z hz; simpa [IsRoot] using hz
    | @insert T S hnot ih =>
      intro hS
      rw [Finset.prod_insert hnot]
      exact Polytope.hurwitz_mul (ih (fun U hU => hS U (Finset.mem_insert_of_mem hU)))
        (shiftedQuadratic_hurwitz hε (hS T (Finset.mem_insert_self _ _)))
  exact hp _ (fun T hT => (node_bounds hT).1)

theorem family_stable (r : ℕ) (odd : Bool) {ε : ℝ} (hε : 0 < ε) :
    Polytope.Stable (family r odd ε) :=
  Polytope.stable_multiply seed_stable (multiplier_hurwitz r odd hε)

theorem family_constant_pos (r : ℕ) (odd : Bool) {ε : ℝ} (hε : 0 < ε) (i : Fin 3) :
    0 < (family r odd ε i).coeff 0 := by
  have hs : 0 < (seed i).coeff 0 := by fin_cases i <;>
    norm_num [seed,N4.Poly4.poly,WeakSeed.a0,WeakSeed.a1,WeakSeed.a2]
  have hp : 0 < (∏ T ∈ nodes r, shiftedQuadratic ε T).coeff 0 := by
    rw [coeff_zero_prod]
    apply Finset.prod_pos
    intro T hT
    have hcoef : (shiftedQuadratic ε T).coeff 0=ε^2+T := by
      simp only [shiftedQuadratic,coeff_add,coeff_C_mul_X,coeff_X_pow,coeff_C]
      norm_num
    rw [hcoef]
    nlinarith [(node_bounds hT).1,sq_nonneg ε]
  have hf : 0 < (if odd then (X+C ε : ℝ[X]) else 1).coeff 0 := by cases odd <;> simp [hε]
  simpa only [family,multiplier,mul_coeff_zero] using mul_pos (mul_pos hf hp) hs

theorem family_zero (r : ℕ) (odd : Bool) (i : Fin 3) : family r odd 0 i=boundary r odd i := by
  cases odd <;> simp [family,multiplier,boundary,base,factors,shiftedQuadratic,quadratic,
    mul_assoc,mul_comm,mul_left_comm]

theorem family_value_limit (r : ℕ) (odd : Bool) (i : Fin 3) (ω : ℝ) :
    Tendsto (fun n => Segment.value (family r odd (epsilon n) i) (I*(ω:ℂ))) atTop
      (𝓝 (Segment.value (boundary r odd i) (I*(ω:ℂ)))) := by
  have hc : Continuous (fun ε : ℝ => Segment.value (family r odd ε i) (I*(ω:ℂ))) := by
    cases odd <;>
      simp only [family,multiplier,Segment.value,shiftedQuadratic,eval₂_mul,eval₂_finset_prod,
        eval₂_add,eval₂_pow,eval₂_C,eval₂_X,Bool.false_eq_true,if_false,if_true,eval₂_one]
    all_goals fun_prop
  have hh := hc.tendsto 0 |>.comp epsilon_limit
  simpa only [family_zero] using hh

end
end SPR.Polytope.Transfer
