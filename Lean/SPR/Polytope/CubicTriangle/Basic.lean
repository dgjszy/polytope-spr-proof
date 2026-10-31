import SPR.Polytope.Common.Definitions

/-! # Concrete cubic triangle and a direct root-exclusion stability criterion. -/
namespace SPR.Polytope.CubicTriangle
open Polynomial Complex
noncomputable section

def cubic (α β γ : ℝ) : ℝ[X] := X^3+C α*X^2+C β*X+C γ
def a₁ : ℝ[X] := cubic 3 1 2
def a₂ : ℝ[X] := cubic 4 4 15
def a₃ : ℝ[X] := cubic 1 3 2

theorem cubic_degree (α β γ : ℝ) :
    (cubic α β γ).Monic ∧ (cubic α β γ).natDegree=3 := by
  have hd : (cubic α β γ).natDegree ≤ 3 := by unfold cubic; compute_degree!
  have hc : (cubic α β γ).coeff 3=1 := by simp [cubic]
  exact ⟨monic_of_natDegree_le_of_coeff_eq_one 3 hd hc,
    natDegree_eq_of_le_of_coeff_ne_zero hd (by rw [hc]; norm_num)⟩

theorem cubic_hurwitz {α β γ : ℝ} (ha : 0 < α) (hb : 0 < β) (hc : 0 < γ)
    (hd : γ < α*β) : IsHurwitz (cubic α β γ) := by
  intro z hz
  by_contra hn
  have hu : 0 ≤ z.re := le_of_not_gt hn
  have he : Segment.value (cubic α β γ) z = 0 := by
    simpa [Segment.value, IsRoot, eval_map] using hz
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  simp [Segment.value, cubic, pow_succ, Complex.mul_re, Complex.mul_im] at hre him
  by_cases hv : z.im=0
  · rw [hv] at hre
    nlinarith [mul_nonneg hu hu, mul_nonneg (sq_nonneg z.re) hu,
      mul_nonneg ha.le (sq_nonneg z.re), mul_nonneg hb.le hu]
  · have hv2 : z.im^2=3*z.re^2+2*α*z.re+β := by
      have hi : z.im*(3*z.re^2+2*α*z.re+β-z.im^2)=0 := by nlinarith [him]
      have hh := (mul_eq_zero.mp hi).resolve_left hv
      linarith
    have heq : -8*z.re^3-8*α*z.re^2-2*(α^2+β)*z.re+γ-α*β=0 := by
      nlinarith [hre, congrArg (fun t : ℝ => z.re*t) hv2,
        congrArg (fun t : ℝ => α*t) hv2]
    have h1 : 0 ≤ z.re^3 := pow_nonneg hu _
    have h2 : 0 ≤ α*z.re^2 := mul_nonneg ha.le (sq_nonneg _)
    have h3 : 0 ≤ (α^2+β)*z.re := mul_nonneg (by positivity) hu
    linarith

def triangle (u v w : ℝ) : ℝ[X] := u • a₁+v • a₂+w • a₃

theorem triangle_hurwitz {u v w : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hs : u+v+w=1) : IsHurwitz (triangle u v w) := by
  have he : triangle u v w = cubic (3*u+4*v+w) (u+4*v+3*w) (2*u+15*v+2*w) := by
    dsimp [triangle, a₁,a₂,a₃,cubic]
    simp only [smul_eq_C_mul, C_add,C_mul,C_1]
    have hh : C u+C v+C w=(1:ℝ[X]) := by rw [← C_add,← C_add,hs,C_1]
    linear_combination X^3*hh
  rw [he]
  apply cubic_hurwitz
  · linarith
  · linarith
  · linarith
  · have hid : (3*u+4*v+w)*(u+4*v+3*w)-(2*u+15*v+2*w) =
        3*(v-1/2)^2+1/4+4*u*w := by nlinarith [sq_nonneg (u+v+w-1)]
    nlinarith [sq_nonneg (v-1/2), mul_nonneg hu hw]

end
end SPR.Polytope.CubicTriangle
