import SPR.Polytope.CubicSynthesis.Pairing

/-! # Finite separation of contact rows in the complete five-dimensional coefficient space. -/
namespace SPR.Polytope.CubicSynthesis
open Polynomial
noncomputable section

def dot (v w : Vec) : ℝ := ∑ i, v i*w i

theorem functional_representation (f : Vec →L[ℝ] ℝ) (v : Vec) :
    f v=dot (fun i => f (Pi.single i 1)) v := by
  classical
  have he : v=∑ i : Fin 5, v i • Pi.single i (1:ℝ) := by
    funext j
    simp [Finset.sum_apply,Pi.single_apply]
  calc
    f v=f (∑ i : Fin 5, v i • Pi.single i (1:ℝ)) := congrArg f he
    _=∑ i : Fin 5, v i*f (Pi.single i (1:ℝ)) := by simp
    _=dot (fun i => f (Pi.single i 1)) v := by
      unfold dot
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- If no coefficient vector is positive on a finite contact set, positive
dependence exists on the full row space, with no restricted numerator ansatz. -/
theorem finite_separation (S : Finset Vec)
    (hno : ¬ ∃ c : Vec, ∀ v ∈ S, 0 < dot c v) :
    ∃ w : Vec → ℝ, (∀ v ∈ S, 0 ≤ w v) ∧ (∑ v ∈ S, w v)=1 ∧
      ∑ v ∈ S, w v • v=0 := by
  classical
  have hm : (0:Vec) ∈ convexHull ℝ (S:Set Vec) := by
    by_contra hn
    obtain ⟨f,u,h0,hf⟩ := geometric_hahn_banach_point_closed
      (convex_convexHull ℝ (S:Set Vec)) (S.finite_toSet.isClosed_convexHull ℝ) hn
    apply hno
    refine ⟨fun i => f (Pi.single i 1),?_⟩
    intro v hv
    have hh := hf v (subset_convexHull ℝ (S:Set Vec) hv)
    rw [← functional_representation]
    have hz : f (0:Vec)=0 := f.map_zero
    rw [hz] at h0
    exact h0.trans hh
  exact Finset.mem_convexHull'.mp hm

/-- Indexed version retaining every original vertex label and assigning zero
weight to forbidden contacts. Repeated rows need no injectivity assumption. -/
theorem indexed_finite_separation {ι : Type*} [Fintype ι]
    (allowed : ι → Prop) (row : ι → Vec)
    (hno : ¬ ∃ c : Vec, ∀ i, allowed i → 0 < dot c (row i)) :
    ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ (∀ i, ¬ allowed i → w i=0) ∧
      ∑ i,w i=1 ∧ ∑ i,w i • row i=0 := by
  classical
  let J := {i : ι // allowed i}
  let r : J → Vec := fun i => row i
  have hm : (0:Vec) ∈ convexHull ℝ (Set.range r) := by
    by_contra hn
    obtain ⟨f,u,h0,hf⟩ := geometric_hahn_banach_point_closed
      (convex_convexHull ℝ (Set.range r))
      ((Set.finite_range r).isClosed_convexHull ℝ) hn
    apply hno
    refine ⟨fun k => f (Pi.single k 1),?_⟩
    intro i hi
    have hh := hf (row i) (subset_convexHull ℝ _
      (Set.mem_range.mpr ⟨⟨i,hi⟩,rfl⟩))
    rw [← functional_representation]
    simpa using lt_trans h0 hh
  rw [convexHull_range_eq_exists_affineCombination] at hm
  obtain ⟨s,w,hw,hws,hwe⟩ := hm
  let W : J → ℝ := fun i => if i ∈ s then w i else 0
  have hW (i : J) : 0 ≤ W i := by
    dsimp [W]
    split_ifs with hi
    · exact hw i hi
    · exact le_rfl
  have hsum : ∑ i,W i=1 := by rw [Fintype.sum_extend_by_zero]; exact hws
  have hrow : ∑ i,W i • r i=0 := by
    simpa only [W,ite_smul,zero_smul,Fintype.sum_extend_by_zero,
      Finset.affineCombination_eq_linear_combination s r w hws] using hwe
  let V : ι → ℝ := fun i => if hi : allowed i then W ⟨i,hi⟩ else 0
  have hV (i : ι) : 0 ≤ V i := by
    dsimp [V]
    split_ifs with hi
    · exact hW ⟨i,hi⟩
    · exact le_rfl
  have hval (i : J) : W i=V i.val := by simp [V,i.property]
  have hout (i : ι) (hi : i ∉ Set.range (Subtype.val : J → ι)) : V i=0 := by
    have hn : ¬ allowed i := fun hh => hi ⟨⟨i,hh⟩,rfl⟩
    simp [V,hn]
  have hsumeq := Fintype.sum_of_injective (Subtype.val : J → ι)
    Subtype.val_injective W V hout hval
  have hroweq := Fintype.sum_of_injective (Subtype.val : J → ι)
    Subtype.val_injective (fun i => W i • r i) (fun i => V i • row i)
    (fun i hi => by dsimp only; rw [hout i hi,zero_smul])
    (fun i => by dsimp only; rw [hval i])
  refine ⟨V,hV,fun i hi => by simp [V,hi],?_,?_⟩
  · exact hsumeq.symm.trans hsum
  · exact hroweq.symm.trans hrow

end
end SPR.Polytope.CubicSynthesis
