import SPR.Polytope.CubicTriangle.Basic
import SPR.Polytope.QuarticTriangle.Exclusion
import SPR.Polytope.Transfer.Perturbation

/-! # Complete quartic weak obstruction on the four-vertex cubic boundary. -/
namespace SPR.Polytope.CubicFourVertices
open Polynomial Complex
noncomputable section

def resonator (r c : ℝ) : ℝ[X] := (X+C r)*(X^2+C c)

def boundary : Fin 4 → ℝ[X] := ![resonator 2 1,resonator 2 2,resonator 1 3,resonator 1 4]

def R (r : ℝ) (B : ℝ[X]) (t : ℝ) : ℝ :=
  r*(B.coeff 0-B.coeff 2*t+B.coeff 4*t^2)+t*(B.coeff 1-B.coeff 3*t)

theorem pairing_resonator (r c : ℝ) {B : ℝ[X]} (hd : B.natDegree ≤ 4) (ω : ℝ) :
    Segment.pairing (resonator r c) B ω=(c-ω^2)*R r B (ω^2) := by
  have hc5 : B.coeff 5=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  conv_lhs => rw [← QuarticTriangle.numerator_eq (show B.natDegree ≤ 5 by omega)]
  simp [Segment.pairing,Segment.value,resonator,QuarticTriangle.numerator,hc5,R,
    pow_succ,Complex.mul_re,Complex.mul_im]
  ring

theorem band_zero {B : ℝ[X]} (hd : B.natDegree ≤ 4) (r c d t : ℝ)
    (ht : 0 ≤ t) (hc : c < t) (hd' : t < d)
    (h1 : ∀ ω, 0 ≤ Segment.pairing (resonator r c) B ω)
    (h2 : ∀ ω, 0 ≤ Segment.pairing (resonator r d) B ω) : R r B t=0 := by
  have hleft := h1 (Real.sqrt t)
  have hright := h2 (Real.sqrt t)
  rw [pairing_resonator r c hd,Real.sq_sqrt ht] at hleft
  rw [pairing_resonator r d hd,Real.sq_sqrt ht] at hright
  have hpos : 0 ≤ R r B t := (mul_nonneg_iff_of_pos_left (sub_pos.mpr hd')).mp hright
  have hneg : R r B t ≤ 0 := by
    by_contra hn
    exact (not_lt_of_ge hleft) (mul_neg_of_neg_of_pos (sub_neg.mpr hc) (lt_of_not_ge hn))
  exact le_antisymm hneg hpos

theorem no_nonzero_weak : ¬ ∃ B : ℝ[X], B ≠ 0 ∧ B.natDegree ≤ 4 ∧
    ∀ i ω, 0 ≤ Segment.pairing (boundary i) B ω := by
  rintro ⟨B,hne,hd,hw⟩
  have h2 (t : ℝ) (ht0 : 0 ≤ t) (ht1 : 1 < t) (ht2 : t < 2) : R 2 B t=0 :=
    band_zero hd 2 1 2 t ht0 ht1 ht2 (hw 0) (hw 1)
  have h1 (t : ℝ) (ht0 : 0 ≤ t) (ht1 : 3 < t) (ht2 : t < 4) : R 1 B t=0 :=
    band_zero hd 1 3 4 t ht0 ht1 ht2 (hw 2) (hw 3)
  have z21 := h2 (5/4) (by norm_num) (by norm_num) (by norm_num)
  have z22 := h2 (3/2) (by norm_num) (by norm_num) (by norm_num)
  have z23 := h2 (7/4) (by norm_num) (by norm_num) (by norm_num)
  have z11 := h1 (13/4) (by norm_num) (by norm_num) (by norm_num)
  have z12 := h1 (7/2) (by norm_num) (by norm_num) (by norm_num)
  have z13 := h1 (15/4) (by norm_num) (by norm_num) (by norm_num)
  dsimp [R] at z21 z22 z23 z11 z12 z13
  have c0 : B.coeff 0=0 := by linarith
  have c1 : B.coeff 1=0 := by linarith
  have c2 : B.coeff 2=0 := by linarith
  have c3 : B.coeff 3=0 := by linarith
  have c4 : B.coeff 4=0 := by linarith
  have c5 : B.coeff 5=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  apply hne
  rw [← QuarticTriangle.numerator_eq (show B.natDegree ≤ 5 by omega)]
  simp [QuarticTriangle.numerator,c0,c1,c2,c3,c4,c5]

end
end SPR.Polytope.CubicFourVertices
