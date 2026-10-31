import SPR.Polytope.CubicSynthesis.ContactCases
import SPR.Polytope.DegreeLift.ImproperUniversal

/-! # Every strictly stable cubic triangle has one actual quartic numerator.

The denominator is unchanged. A stronger compact strict solution is continued
from a coincident triple, then a small coefficient perturbation ensures actual degree four.
-/
namespace SPR.Polytope.CubicSynthesis
open Polynomial Complex
noncomputable section

def path (δ : Fin 3 → ℝ) (τ : Parameter) (i : Fin 3) : ℝ :=
  (1-(τ:ℝ))*δ 0+(τ:ℝ)*δ i

theorem continuous_path (δ : Fin 3 → ℝ) : Continuous (path δ) := by
  apply continuous_pi
  intro i
  dsimp [path]
  fun_prop

theorem path_sum (δ weights : Fin 3 → ℝ) (τ : ℝ) (hw : ∑ i,weights i=1) :
    (∑ i,weights i*((1-τ)*δ 0+τ*δ i))=
      ∑ i,(τ*weights i+(if i=0 then 1-τ else 0))*δ i := by
  simp only [Fin.sum_univ_succ,Fin.isValue,Fin.reduceFinMk] at hw ⊢
  norm_num only [Fin.mk.injEq,reduceCtorEq,ite_true,ite_false,add_zero] at *
  simp only [Fin.succ_ne_zero,ite_false] at *
  linear_combination δ 0*(1-τ)*hw

theorem path_stable (α β γ : Fin 3 → ℝ)
    (hs : Stable (fun i => CubicTriangle.cubic (α i) (β i) (γ i))) (τ : Parameter) :
    Stable (fun i => CubicTriangle.cubic (path α τ i) (path β τ i) (path γ τ i)) := by
  classical
  intro weights hw
  let W : Fin 3 → ℝ := fun i => (τ:ℝ)*weights i+(if i=0 then 1-(τ:ℝ) else 0)
  have hW : Weights W := by
    constructor
    · intro i
      apply add_nonneg (mul_nonneg τ.property.1 (hw.1 i))
      split_ifs
      · exact sub_nonneg.mpr τ.property.2
      · exact le_rfl
    · have hh := hw.2
      simp only [W,Fin.sum_univ_succ,Fin.isValue,Fin.reduceFinMk] at hh ⊢
      norm_num only [Fin.mk.injEq,reduceCtorEq,ite_true,ite_false,add_zero] at *
      simp only [Fin.succ_ne_zero,ite_false] at *
      linear_combination (τ:ℝ)*hh
  have he : blend (fun i => CubicTriangle.cubic (path α τ i) (path β τ i) (path γ τ i)) weights=
      blend (fun i => CubicTriangle.cubic (α i) (β i) (γ i)) W := by
    rw [CubicFourVertices.blend_cubics _ _ _ _ hw.2,
      CubicFourVertices.blend_cubics _ _ _ _ hW.2]
    congr 1 <;> exact path_sum _ weights τ hw.2
  rw [he]
  exact hs W hW

/-- The initial coincident triple has compact strictness, including infinity. -/
theorem single_cubic_compact (α β γ : ℝ)
    (ha : IsHurwitz (CubicTriangle.cubic α β γ)) :
    ∃ v : Vec,∀ u,0 ≤ u → u ≤ 1 → 0 < compactG α β γ v u := by
  let v : Vec := ![γ,β+γ,α+β,1+α,1]
  refine ⟨v,?_⟩
  intro u hu hu1
  by_cases hlast : u=1
  · subst u
    simp [compactG,v]
  · obtain ⟨t,ht,rfl⟩ := finite_compact_parameter hu (lt_of_le_of_ne hu1 hlast)
    rw [compactification _ _ _ _ ht]
    apply div_pos _ (by positivity)
    let ω := Real.sqrt t
    have hω : ω^2=t := Real.sq_sqrt ht
    have hne := Segment.value_ne_zero ha (z := I*(ω:ℂ)) (by simp)
    have hn := Complex.normSq_pos.mpr hne
    have hre : (Segment.value (CubicTriangle.cubic α β γ) (I*(ω:ℂ))).re=γ-α*t := by
      simp [Segment.value,CubicTriangle.cubic,pow_succ,Complex.mul_re,Complex.mul_im]
      nlinarith [congrArg (fun r : ℝ => α*r) hω]
    have him : (Segment.value (CubicTriangle.cubic α β γ) (I*(ω:ℂ))).im=ω*(β-t) := by
      simp [Segment.value,CubicTriangle.cubic,pow_succ,Complex.mul_re,Complex.mul_im]
      nlinarith [congrArg (fun r : ℝ => ω*r) hω]
    have he : G α β γ v t=Complex.normSq
        (Segment.value (CubicTriangle.cubic α β γ) (I*(ω:ℂ))) := by
      have hh : Complex.normSq (Segment.value (CubicTriangle.cubic α β γ) (I*(ω:ℂ)))=
          (γ-α*t)^2+ω^2*(β-t)^2 := by simp [Complex.normSq,hre,him]; ring
      rw [hh,hω]
      simp [G,v]
      ring
    rwa [he]

/-- Complete compact existence for arbitrary stable cubic triangles, with all
degeneracies allowed. The critical-cone hypothesis is discharged, not assumed. -/
theorem compact_existence (α β γ : Fin 3 → ℝ)
    (hs : Stable (fun i => CubicTriangle.cubic (α i) (β i) (γ i))) :
    ∃ v,Strict α β γ v := by
  have hreg : ∀ τ v,v ≠ 0 → Weak (path α τ) (path β τ) (path γ τ) v →
      ∃ w,Strict (path α τ) (path β τ) (path γ τ) w := by
    intro τ v hv hw
    exact weak_strictification _ _ _ (path_stable α β γ hs τ) v hv hw
  obtain ⟨v,hv⟩ := single_cubic_compact (α 0) (β 0) (γ 0) (vertex_hurwitz hs 0)
  have hi : ∃ v,Strict (path α ⟨0,le_rfl,zero_le_one⟩)
      (path β ⟨0,le_rfl,zero_le_one⟩) (path γ ⟨0,le_rfl,zero_le_one⟩) v := by
    refine ⟨v,?_⟩
    intro i u hu hu1
    simpa [path] using hv u hu hu1
  obtain ⟨w,hw⟩ := continuation (path α) (path β) (path γ)
    (continuous_path α) (continuous_path β) (continuous_path γ) hreg hi
    ⟨1,zero_le_one,le_rfl⟩
  exact ⟨w,by simpa [Strict,path] using hw⟩

/-- One fixed real polynomial of actual degree four works for every point of
the entire original convex hull and every finite real frequency. -/
theorem synthesis (α β γ : Fin 3 → ℝ)
    (hs : Stable (fun i => CubicTriangle.cubic (α i) (β i) (γ i))) :
    ∃ B : ℝ[X],B.natDegree=4 ∧
      Common (fun i => CubicTriangle.cubic (α i) (β i) (γ i)) B := by
  obtain ⟨v,hv⟩ := compact_existence α β γ hs
  obtain ⟨w,hd,hw⟩ := exact_quartic_of_compact α β γ v hv
  refine ⟨numerator w,hd,?_⟩
  apply common_of_vertices _ hs
  · intro i
    exact strict_of_compact (vertex_hurwitz hs i) w (fun u hu => hw i u hu.1 hu.2)
  · exact vertex_hurwitz hs

theorem cubic_representation {p : ℝ[X]} (hm : p.Monic) (hd : p.natDegree=3) :
    p=CubicTriangle.cubic (p.coeff 2) (p.coeff 1) (p.coeff 0) := by
  ext j
  by_cases hj : j ≤ 3
  · interval_cases j
    · simp [CubicTriangle.cubic]
    · simp [CubicTriangle.cubic]
    · simp [CubicTriangle.cubic]
    · simpa [CubicTriangle.cubic,hd] using hm.coeff_natDegree
  · have hz : p.coeff j=0 := coeff_eq_zero_of_natDegree_lt (by omega)
    simp [CubicTriangle.cubic,hz,coeff_X,coeff_C,show j ≠ 0 by omega,
      show 1 ≠ j by omega,show j ≠ 2 by omega,show j ≠ 3 by omega]

end
end SPR.Polytope.CubicSynthesis

namespace SPR.Polytope
open Polynomial
noncomputable section

/-- The remaining positive classification cell, including all at-most-three
listed families and the single-point and segment degeneracies. -/
theorem cubic_triangle_quartic : Universal 3 3 4 := by
  intro r hr hr3 a ha hs
  by_cases hr2 : r ≤ 2
  · exact (at_most_two_improper (by omega : 1 ≤ 3) (by omega : 2 ≤ 2)) r hr hr2 a ha hs
  · have hrEq : r=3 := by omega
    subst r
    have he (i : Fin 3) := CubicSynthesis.cubic_representation (ha i).1 (ha i).2
    have hfamily : a=fun i => CubicTriangle.cubic ((a i).coeff 2) ((a i).coeff 1) ((a i).coeff 0) :=
      funext he
    rw [hfamily] at hs ⊢
    exact CubicSynthesis.synthesis _ _ _ hs

end
end SPR.Polytope
