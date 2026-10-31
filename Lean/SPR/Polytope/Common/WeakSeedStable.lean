import SPR.Polytope.Common.WeakSeedDeterminant
import SPR.Polytope.Common.Definitions

/-! # A strictly stable quartic triangle with no nonzero weak numerator of degree ≤5.

This strengthens the original strict obstruction to the fixed input needed by
the boundary-limit transfer. It does not itself prove that transfer.
-/
namespace SPR.Polytope.WeakSeed
open Polynomial N4
noncomputable section

def triangle (u v w : ℝ) : Poly4 :=
  ⟨u*a0.a1+v*a1.a1+w*a2.a1,u*a0.a2+v*a1.a2+w*a2.a2,
   u*a0.a3+v*a1.a3+w*a2.a3,u*a0.a4+v*a1.a4+w*a2.a4⟩

theorem triangle_poly (u v w : ℝ) (hs : u+v+w=1) :
    (triangle u v w).poly=u • a0.poly+v • a1.poly+w • a2.poly := by
  simp only [triangle,Poly4.poly,smul_eq_C_mul,C_add,C_mul]
  have h : C u+C v+C w=(1:ℝ[X]) := by rw [← C_add,← C_add,hs,C_1]
  linear_combination -X^4*h

theorem stable {u v w : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hs : u+v+w=1) : IsHurwitz (u • a0.poly+v • a1.poly+w • a2.poly) := by
  rw [← triangle_poly u v w hs]
  have hsum : 0 < u+v+w := by linarith
  have hpos := QuarticTriangle.positive_coordinate hsum
  have h1 : 0 < (triangle u v w).a1 := by
    rcases hpos with h | h | h <;> dsimp [triangle,a0,a1,a2] <;> positivity
  have h2 : 0 < (triangle u v w).a2 := by
    rcases hpos with h | h | h <;> dsimp [triangle,a0,a1,a2] <;> positivity
  have h3 : 0 < (triangle u v w).a3 := by
    rcases hpos with h | h | h <;> dsimp [triangle,a0,a1,a2] <;> positivity
  have h4 : 0 < (triangle u v w).a4 := by
    rcases hpos with h | h | h <;> dsimp [triangle,a0,a1,a2] <;> positivity
  apply QuarticTriangle.hurwitz_of_determinant _ h1 h2 h3 h4
  have he : determinantForm u v w=determinant (triangle u v w)-
      (triangle u v w).a3^2*(u+v+w-1) := by
    dsimp [determinantForm,determinant,triangle,a0,a1,a2]
    ring
  rw [hs] at he
  have hp := determinantForm_positive u v w hu hv hw hsum
  nlinarith

/-- A nonzero common weak pairing on the actual three quartics is impossible. -/
theorem no_nonzero_weak_pairing : ¬ ∃ p : ℝ[X], p ≠ 0 ∧ p.natDegree ≤ 5 ∧
    (∀ ω : ℝ, 0 ≤ Segment.pairing a0.poly p ω) ∧
    (∀ ω : ℝ, 0 ≤ Segment.pairing a1.poly p ω) ∧
    (∀ ω : ℝ, 0 ≤ Segment.pairing a2.poly p ω) := by
  rintro ⟨p,hne,hd,h0,h1,h2⟩
  have point (a : Poly4) (h : ∀ ω : ℝ, 0 ≤ Segment.pairing a.poly p ω)
      (t : ℝ) (ht : 0 ≤ t) : 0 ≤ QuarticTriangle.G a p t := by
    have hh := h (Real.sqrt t)
    rwa [QuarticTriangle.pairing_eq a hd,Real.sq_sqrt ht] at hh
  apply no_nonzero_weak
  refine ⟨p,hne,hd,?_,?_,?_,?_,?_,?_,?_⟩
  · exact point a0 h0 1 (by norm_num)
  · exact point a1 h1 2 (by norm_num)
  · exact point a1 h1 3 (by norm_num)
  · exact point a2 h2 4 (by norm_num)
  · exact point a0 h0 5 (by norm_num)
  · exact point a2 h2 6 (by norm_num)
  · exact point a0 h0 7 (by norm_num)

theorem affine_independent (r s : ℝ)
    (h : r • (a1.poly-a0.poly)+s • (a2.poly-a0.poly)=0) : r=0 ∧ s=0 := by
  have h3 := congrArg (fun p : ℝ[X] => p.coeff 3) h
  have h2 := congrArg (fun p : ℝ[X] => p.coeff 2) h
  norm_num [Poly4.poly,a0,a1,a2,coeff_X] at h3 h2
  constructor <;> linarith

end
end SPR.Polytope.WeakSeed
