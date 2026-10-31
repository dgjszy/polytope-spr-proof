import SPR.Polytope.Common.WeakSeed
import SPR.Segment.FrequencyIdentities

/-! # Positive odd-part moment and the extra zero-frequency residual. -/
namespace SPR.Polytope.WeakSeed
open Polynomial Complex
noncomputable section
set_option maxHeartbeats 2000000

def oddRow0 (D : ℝ[X]) (c : ℝ) : ℝ := row0 D-c*(4999993/6999993 : ℝ)
def oddRow1 (D : ℝ[X]) (c : ℝ) : ℝ := row1 D-c*(2000000/2333331 : ℝ)
def oddRow2 (D : ℝ[X]) (c : ℝ) : ℝ := row2 D-c*(-4999993/6999993 : ℝ)
def oddRow3 (D : ℝ[X]) (c : ℝ) : ℝ := row3 D-c*(1535000042/20999979 : ℝ)
def oddRow4 (D : ℝ[X]) (c : ℝ) : ℝ := row4 D-c*(-333331/777777 : ℝ)
def oddRow5 (D : ℝ[X]) (c : ℝ) : ℝ := row5 D-c*(-178999916/20999979 : ℝ)
def oddRow6 (D : ℝ[X]) (c : ℝ) : ℝ := row6 D-c*(-999995/999999 : ℝ)

theorem odd_certificate (D : ℝ[X]) (c : ℝ) :
    (211035376039236633546171560012468401279/1174205692530034689001139486272777 : ℝ)*oddRow0 D c +
      (11869805717576611834861212747747898487452/10567851232770312201010255376454993 : ℝ)*oddRow1 D c +
      (3517002986472870117126344521310977376675/1174205692530034689001139486272777 : ℝ)*oddRow2 D c +
      (25775945835015093169260038026299259440/1174205692530034689001139486272777 : ℝ)*oddRow3 D c +
      (28487347523787427949375038399930767822455/31703553698310936603030766129364979 : ℝ)*oddRow4 D c +
      (2947296747875725651678442727989234836/1174205692530034689001139486272777 : ℝ)*oddRow5 D c +
      (1/1 : ℝ)*oddRow6 D c = -c*(527562582480252408410803560735573031684000000/3522613554973026476899351455399872181669 : ℝ) := by
  have h := positive_certificate D
  dsimp [oddRow0,oddRow1,oddRow2,oddRow3,oddRow4,oddRow5,oddRow6]
  linear_combination h

/-- All degree≤5 residuals are allowed; only the constant c is constrained by zero frequency. -/
theorem odd_residual_zero (D : ℝ[X]) (hd : D.natDegree ≤ 5) (c : ℝ) (hc : 0 ≤ c)
    (h0 : 0 ≤ oddRow0 D c)
    (h1 : 0 ≤ oddRow1 D c)
    (h2 : 0 ≤ oddRow2 D c)
    (h3 : 0 ≤ oddRow3 D c)
    (h4 : 0 ≤ oddRow4 D c)
    (h5 : 0 ≤ oddRow5 D c)
    (h6 : 0 ≤ oddRow6 D c) : D=0 ∧ c=0 := by
  have h := odd_certificate D c
  have hc0 : c=0 := by nlinarith
  refine ⟨?_,hc0⟩
  by_contra hn
  apply no_nonzero_weak
  refine ⟨D,hn,hd,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [oddRow0,hc0] using h0
  · simpa [oddRow1,hc0] using h1
  · simpa [oddRow2,hc0] using h2
  · simpa [oddRow3,hc0] using h3
  · simpa [oddRow4,hc0] using h4
  · simpa [oddRow5,hc0] using h5
  · simpa [oddRow6,hc0] using h6


/-- The extra zero root separates a general polynomial into its divX residual
and its constant term. This identity imposes no condition on numerator roots. -/
theorem odd_pairing_identity (a : N4.Poly4) (D : ℝ[X]) (c ω : ℝ) :
    Segment.pairing (X*a.poly) (X*D+C c) ω =
      ω^2*(Segment.pairing a.poly D ω-c*(a.a3-a.a1*ω^2)) := by
  simp [Segment.pairing,Segment.value,N4.Poly4.poly,pow_succ,
    Complex.mul_re,Complex.mul_im]
  ring

/-- All degree-at-most-six boundary numerators are excluded, provided the
constant sign retained from strictly stable approximants is nonnegative. -/
theorem no_nonzero_odd_boundary : ¬ ∃ B : ℝ[X], B ≠ 0 ∧ B.natDegree ≤ 6 ∧
    0 ≤ B.coeff 0 ∧
    (∀ ω : ℝ, 0 ≤ Segment.pairing (X*a0.poly) B ω) ∧
    (∀ ω : ℝ, 0 ≤ Segment.pairing (X*a1.poly) B ω) ∧
    (∀ ω : ℝ, 0 ≤ Segment.pairing (X*a2.poly) B ω) := by
  rintro ⟨B,hne,hd,hc,h0,h1,h2⟩
  let D := B.divX
  have hdD : D.natDegree ≤ 5 := by
    dsimp [D]
    rw [natDegree_divX_eq_natDegree_tsub_one]
    omega
  have point (a : N4.Poly4) (h : ∀ ω : ℝ, 0 ≤ Segment.pairing (X*a.poly) B ω)
      (t : ℝ) (ht : 0 < t) :
      0 ≤ QuarticTriangle.G a D t-B.coeff 0*(a.a3-a.a1*t) := by
    have hh := h (Real.sqrt t)
    rw [← X_mul_divX_add B] at hh
    rw [odd_pairing_identity,QuarticTriangle.pairing_eq a hdD,Real.sq_sqrt ht.le] at hh
    exact (mul_nonneg_iff_of_pos_left ht).mp hh
  have hz := odd_residual_zero D hdD (B.coeff 0) hc
    (by have h := point a0 h0 1 (by norm_num)
        norm_num [oddRow0,row0,a0] at h ⊢
        exact h)
    (by have h := point a1 h1 2 (by norm_num)
        norm_num [oddRow1,row1,a1] at h ⊢
        exact h)
    (by have h := point a1 h1 3 (by norm_num)
        norm_num [oddRow2,row2,a1] at h ⊢
        exact h)
    (by have h := point a2 h2 4 (by norm_num)
        norm_num [oddRow3,row3,a2] at h ⊢
        exact h)
    (by have h := point a0 h0 5 (by norm_num)
        norm_num [oddRow4,row4,a0] at h ⊢
        exact h)
    (by have h := point a2 h2 6 (by norm_num)
        norm_num [oddRow5,row5,a2] at h ⊢
        exact h)
    (by have h := point a0 h0 7 (by norm_num)
        norm_num [oddRow6,row6,a0] at h ⊢
        exact h)

  apply hne
  rw [← X_mul_divX_add B]
  change X*D+C (B.coeff 0)=0
  rw [hz.1,hz.2]
  simp

end
end SPR.Polytope.WeakSeed
