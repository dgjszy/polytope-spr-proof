import SPR.Polytope.QuarticTriangle.Exclusion
import SPR.Polytope.QuarticTriangle.HurwitzCriterion
import SPR.Polytope.QuarticTriangle.DeterminantPositive

/-! # Full quartic triangle counterexample, including all convex combinations. -/
namespace SPR.Polytope.QuarticTriangle
open Polynomial N4
noncomputable section

/-- Coefficients of the actual convex combination. -/
def triangle (u v w : ℝ) : Poly4 :=
  ⟨u*a₁.a1+v*a₂.a1+w*a₃.a1, u*a₁.a2+v*a₂.a2+w*a₃.a2,
   u*a₁.a3+v*a₂.a3+w*a₃.a3, u*a₁.a4+v*a₂.a4+w*a₃.a4⟩

theorem triangle_poly (u v w : ℝ) (hs : u+v+w=1) :
    (triangle u v w).poly = u • a₁.poly + v • a₂.poly + w • a₃.poly := by
  simp only [triangle, Poly4.poly, smul_eq_C_mul, C_add, C_mul]
  have h : C u+C v+C w = (1 : ℝ[X]) := by rw [← C_add, ← C_add, hs, C_1]
  linear_combination -X^4*h

/-- Strict stability of the entire closed triangle, including its edges. -/
theorem triangle_hurwitz {u v w : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hs : u+v+w=1) : IsHurwitz (triangle u v w).poly := by
  have hsum : 0 < u+v+w := by linarith
  have hpos := positive_coordinate hsum
  have h1 : 0 < (triangle u v w).a1 := by
    rcases hpos with h | h | h <;> dsimp [triangle,a₁,a₂,a₃] <;> positivity
  have h2 : 0 < (triangle u v w).a2 := by
    rcases hpos with h | h | h <;> dsimp [triangle,a₁,a₂,a₃] <;> positivity
  have h3 : 0 < (triangle u v w).a3 := by
    rcases hpos with h | h | h <;> dsimp [triangle,a₁,a₂,a₃] <;> positivity
  have h4 : 0 < (triangle u v w).a4 := by
    rcases hpos with h | h | h <;> dsimp [triangle,a₁,a₂,a₃] <;> positivity
  apply hurwitz_of_determinant _ h1 h2 h3 h4
  have he : determinantForm u v w / 9261 = determinant (triangle u v w) -
      (triangle u v w).a3^2*(u+v+w-1) := by
    dsimp [determinantForm,determinant,triangle,a₁,a₂,a₃]
    ring
  rw [hs] at he
  have hp := determinantForm_positive u v w hu hv hw hsum
  nlinarith

/-- The input has three genuine vertices, not a disguised segment. -/
theorem affine_independent (r s : ℝ)
    (h : r • (a₂.poly-a₁.poly)+s • (a₃.poly-a₁.poly)=0) : r=0 ∧ s=0 := by
  have h3 := congrArg (fun p : ℝ[X] => p.coeff 3) h
  have h2 := congrArg (fun p : ℝ[X] => p.coeff 2) h
  norm_num [Poly4.poly,a₁,a₂,a₃,coeff_add,coeff_sub,coeff_smul,coeff_X] at h3 h2
  constructor <;> linarith

/-- Exact counterexample: degree four inputs, full stable convex hull, no numerator of
degree at most five. No assumption is imposed on numerator roots or leading sign. -/
theorem counterexample :
    (a₁.poly.Monic ∧ a₁.poly.natDegree=4) ∧
    (a₂.poly.Monic ∧ a₂.poly.natDegree=4) ∧
    (a₃.poly.Monic ∧ a₃.poly.natDegree=4) ∧
    (∀ u v w : ℝ, 0 ≤ u → 0 ≤ v → 0 ≤ w → u+v+w=1 →
      IsHurwitz (u • a₁.poly+v • a₂.poly+w • a₃.poly)) ∧
    ¬ ∃ p : ℝ[X], p.natDegree ≤ 5 ∧
      ∀ u v w : ℝ, 0 ≤ u → 0 ≤ v → 0 ≤ w → u+v+w=1 →
        Segment.FrequencySPR (u • a₁.poly+v • a₂.poly+w • a₃.poly) p := by
  refine ⟨(poly_degree a₁).symm, (poly_degree a₂).symm, (poly_degree a₃).symm, ?_, ?_⟩
  · intro u v w hu hv hw hs
    rw [← triangle_poly u v w hs]
    exact triangle_hurwitz hu hv hw hs
  · rintro ⟨p, hd, hp⟩
    apply no_common_degree_le_five
    refine ⟨p, hd, ?_, ?_, ?_⟩
    · simpa using hp 1 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · simpa using hp 0 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · simpa using hp 0 0 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end
end SPR.Polytope.QuarticTriangle
