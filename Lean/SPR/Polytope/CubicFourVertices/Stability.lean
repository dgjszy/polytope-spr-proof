import SPR.Polytope.CubicFourVertices.Boundary

/-! # Strict stability of the full shifted four-vertex cubic polytope. -/
namespace SPR.Polytope.CubicFourVertices
open Polynomial Complex
open scoped Topology
noncomputable section

def radii : Fin 4 → ℝ := ![2,2,1,1]
def bands : Fin 4 → ℝ := ![1,2,3,4]

def family (ε : ℝ) (i : Fin 4) : ℝ[X] := CubicTriangle.cubic
  (radii i+3*ε) (bands i+2*radii i*ε+3*ε^2)
  (radii i*bands i+bands i*ε+radii i*ε^2+ε^3)

theorem degree (ε : ℝ) (i : Fin 4) : (family ε i).Monic ∧ (family ε i).natDegree=3 :=
  CubicTriangle.cubic_degree _ _ _

theorem blend_cubics {r : ℕ} (α β γ weights : Fin r → ℝ)
    (hs : ∑ i, weights i=1) :
    Polytope.blend (fun i => CubicTriangle.cubic (α i) (β i) (γ i)) weights=
      CubicTriangle.cubic (∑ i,weights i*α i) (∑ i,weights i*β i) (∑ i,weights i*γ i) := by
  ext j
  simp only [Polytope.blend,CubicTriangle.cubic,finsetSum_coeff,coeff_smul,smul_eq_mul,
    coeff_add,coeff_C_mul_X_pow,coeff_C_mul_X,coeff_X_pow,coeff_C,coeff_X]
  by_cases hj : j ≤ 3
  · interval_cases j <;> simp [hs]
  · simp [
      show j ≠ 0 by omega,show 1 ≠ j by omega,show j ≠ 2 by omega,
      show j ≠ 3 by omega]

theorem stable {ε : ℝ} (hε : 0 < ε) : Polytope.Stable (family ε) := by
  intro weights hw
  let u := weights 0+weights 1
  let L := weights 0+2*weights 1
  let H := 3*weights 2+4*weights 3
  have h0 := hw.1 0
  have h1 := hw.1 1
  have h2 := hw.1 2
  have h3 := hw.1 3
  have hs : weights 0+weights 1+weights 2+weights 3=1 := by
    simpa [Fin.sum_univ_succ,add_assoc] using hw.2
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : u ≤ 1 := by dsimp [u]; linarith
  have hL : L ≤ 2*u := by dsimp [L,u]; linarith
  have hH : 3*(1-u) ≤ H := by dsimp [H,u]; linarith
  have ha : 0 < 1+u := by linarith
  have hb : 0 < L+H := by dsimp [L,H]; linarith
  have hc : 0 < 2*L+H := by dsimp [L,H]; linarith
  have hD : 0 ≤ (1+u)*(L+H)-(2*L+H) := by
    have hA := mul_nonneg hu0 (sub_nonneg.mpr hH)
    have hB := mul_nonneg (sub_nonneg.mpr hu1) (sub_nonneg.mpr hL)
    nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hu1)]
  have he : Polytope.blend (family ε) weights=CubicTriangle.cubic
      (1+u+3*ε) (L+H+2*(1+u)*ε+3*ε^2)
      (2*L+H+(L+H)*ε+(1+u)*ε^2+ε^3) := by
    unfold family
    rw [blend_cubics _ _ _ _ hw.2]
    congr 1
    · dsimp [radii,u]
      simp only [Fin.sum_univ_succ,Fin.val_zero,Fin.val_one,Matrix.cons_val_zero,
        Matrix.cons_val_succ,Fin.succ_zero_eq_one,Fin.isValue,Fin.succ_one_eq_two,
        Fin.sum_univ_zero,add_zero]
      norm_num
      simp only [Fin.succ_zero_eq_one,Fin.succ_one_eq_two,
        show Fin.succ (2:Fin 3)=(3:Fin 4) from rfl]
      linear_combination (1+3*ε)*hs
    · dsimp [radii,bands,u,L,H]
      simp only [Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
        Fin.sum_univ_zero,add_zero]
      norm_num
      simp only [Fin.succ_zero_eq_one,Fin.succ_one_eq_two,
        show Fin.succ (2:Fin 3)=(3:Fin 4) from rfl]
      linear_combination (2*ε+3*ε^2)*hs
    · dsimp [radii,bands,u,L,H]
      simp only [Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
        Fin.sum_univ_zero,add_zero]
      norm_num
      simp only [Fin.succ_zero_eq_one,Fin.succ_one_eq_two,
        show Fin.succ (2:Fin 3)=(3:Fin 4) from rfl]
      linear_combination (ε^2+ε^3)*hs
  rw [he]
  apply CubicTriangle.cubic_hurwitz
  · positivity
  · have : 0 < 2*(1+u)*ε := by positivity
    nlinarith [sq_nonneg ε]
  · have : 0 ≤ (L+H)*ε+(1+u)*ε^2+ε^3 := by positivity
    linarith
  · have hid :
        (1+u+3*ε)*(L+H+2*(1+u)*ε+3*ε^2)-
          (2*L+H+(L+H)*ε+(1+u)*ε^2+ε^3)=
        ((1+u)*(L+H)-(2*L+H))+(2*(1+u)^2+2*(L+H))*ε+
          8*(1+u)*ε^2+8*ε^3 := by ring
    have hp : 0 < ((1+u)*(L+H)-(2*L+H))+(2*(1+u)^2+2*(L+H))*ε+
        8*(1+u)*ε^2+8*ε^3 := by positivity
    linarith

theorem family_zero (i : Fin 4) : family 0 i=boundary i := by
  fin_cases i <;> simp [family,boundary,radii,bands,resonator,CubicTriangle.cubic] <;> ring

theorem value_limit (i : Fin 4) (ω : ℝ) :
    Filter.Tendsto (fun n => Segment.value (family (Transfer.epsilon n) i) (I*(ω:ℂ)))
      Filter.atTop (𝓝 (Segment.value (boundary i) (I*(ω:ℂ)))) := by
  have hh : Continuous (fun ε : ℝ => Segment.value (family ε i) (I*(ω:ℂ))) := by
    dsimp [family,Segment.value,CubicTriangle.cubic]
    simp only [eval₂_add,eval₂_mul,eval₂_C,eval₂_pow,eval₂_X]
    fun_prop
  simpa only [family_zero] using hh.tendsto 0 |>.comp Transfer.epsilon_limit

end
end SPR.Polytope.CubicFourVertices
