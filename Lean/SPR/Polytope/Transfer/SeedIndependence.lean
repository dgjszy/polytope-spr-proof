import SPR.Polytope.Transfer.JointRemoval
import SPR.Polytope.Common.WeakSeedStable
import SPR.Polytope.Common.WeakSeedOdd

/-! # Explicit low-frequency independence for the fixed weak-obstruction seed. -/
namespace SPR.Polytope.Transfer
open Polynomial Complex
noncomputable section

def seed : Fin 3 → ℝ[X] := ![WeakSeed.a0.poly,WeakSeed.a1.poly,WeakSeed.a2.poly]

theorem seed_independent {T : ℝ} (hT : 0 < T) (hsmall : T < 1/100) :
    IndependentAt seed T := by
  let ω := Real.sqrt T
  have hw : 0 < ω := Real.sqrt_pos.mpr hT
  have hsq : ω^2=T := Real.sq_sqrt hT.le
  have hT1 : T < 1 := by linarith
  have hT2 : T^2 < 1 := by nlinarith [sq_nonneg T]
  have hT3 : T^3 < 1 := by nlinarith [mul_nonneg hT.le (sub_nonneg.mpr hT1.le)]
  have hpoly : 0 < -8999991*T^3+69999911*T^2-144999791*T+63999875 := by
    nlinarith [sq_nonneg T]
  unfold IndependentAt
  have he :
      (Segment.value (seed 0) (I*(Real.sqrt T:ℂ))).re*
          (Segment.value (seed 1) (I*(Real.sqrt T:ℂ))).im-
        (Segment.value (seed 0) (I*(Real.sqrt T:ℂ))).im*
          (Segment.value (seed 1) (I*(Real.sqrt T:ℂ))).re =
      ω*1000000*(-8999991*T^3+69999911*T^2-144999791*T+63999875)/6999986000007 := by
    change (Segment.value (seed 0) (I*(ω:ℂ))).re*
        (Segment.value (seed 1) (I*(ω:ℂ))).im-
      (Segment.value (seed 0) (I*(ω:ℂ))).im*
        (Segment.value (seed 1) (I*(ω:ℂ))).re = _
    rw [← hsq]
    simp [seed,Segment.value,N4.Poly4.poly,WeakSeed.a0,WeakSeed.a1,
      pow_succ,Complex.mul_re,Complex.mul_im]
    ring
  rw [he]
  exact (div_pos (mul_pos (mul_pos hw (by norm_num)) hpoly) (by norm_num)).ne'

def nodes (r : ℕ) : Finset ℝ :=
  Finset.univ.image (fun j : Fin r => ((j:ℝ)+1)/(100*((r:ℝ)+1)))

theorem node_bounds {r : ℕ} {T : ℝ} (h : T ∈ nodes r) : 0 < T ∧ T < 1/100 := by
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp h
  have hj : (j:ℝ) < (r:ℝ) := by exact_mod_cast j.isLt
  constructor
  · positivity
  · apply (div_lt_iff₀ (by positivity : 0 < 100*((r:ℝ)+1))).mpr
    linarith

theorem nodes_card (r : ℕ) : (nodes r).card=r := by
  have hinj : Function.Injective (fun j : Fin r => ((j:ℝ)+1)/(100*((r:ℝ)+1))) := by
    intro i j h
    have hh := (div_left_inj' (by positivity : (100*((r:ℝ)+1)) ≠ 0)).mp h
    have hv : (i:ℝ)=(j:ℝ) := by linarith
    exact Fin.ext (by exact_mod_cast hv)
  rw [nodes,Finset.card_image_of_injective _ hinj,Finset.card_univ,Fintype.card_fin]

end
end SPR.Polytope.Transfer
