import SPR.Polytope.CubicSynthesis.Contacts
import SPR.Polytope.CubicSynthesis.Hurwitz

/-! # Polynomial factor geometry of the critical contact configurations. -/
namespace SPR.Polytope.CubicSynthesis
open Polynomial
noncomputable section

def commonLinear (x z : ℝ) : ℝ[X] := C z-C x*X

def residualLinear (α β γ A : ℝ) : ℝ[X] := C (A*α-1)*X+C (β-A*γ)

def residualQuadratic (α β γ A D : ℝ) : ℝ[X] :=
  C (A*α-1)*X^2+C (D*α-A*γ+β)*X-C (D*γ)

theorem residualLinear_ne_zero {α β γ A : ℝ}
    (hα : 0 < α) (hD : γ < α*β) : residualLinear α β γ A ≠ 0 := by
  intro hz
  have h1 := congrArg (fun p : ℝ[X] => p.coeff 1) hz
  have h0 := congrArg (fun p : ℝ[X] => p.coeff 0) hz
  simp only [residualLinear,coeff_add,coeff_C_mul_X,coeff_C,coeff_zero] at h1 h0
  norm_num at h1 h0
  have he : α*β-γ=0 := by linear_combination α*h0+γ*h1
  linarith

theorem residualQuadratic_ne_zero {α β γ A D : ℝ}
    (hα : 0 < α) (hγ : 0 < γ) (hD : γ < α*β) :
    residualQuadratic α β γ A D ≠ 0 := by
  intro hz
  have h0 := congrArg (fun p : ℝ[X] => p.coeff 0) hz
  simp [residualQuadratic] at h0
  have hD0 : D=0 := h0.resolve_right hγ.ne'
  have he : residualQuadratic α β γ A D=X*residualLinear α β γ A := by
    simp [residualQuadratic,residualLinear,hD0]
    ring
  rw [he] at hz
  exact residualLinear_ne_zero hα hD ((mul_eq_zero.mp hz).resolve_left X_ne_zero)

theorem pairPoly_factor_zero_constant (α β γ A : ℝ) (v : Vec)
    (hw : v 0=0) (hd : v 4=A*v 3) (hy : v 2=A*v 1) :
    pairPoly α β γ v=X*commonLinear (v 3) (v 1)*residualLinear α β γ A := by
  simp [pairPoly,commonLinear,residualLinear,hw,hd,hy]
  ring

theorem pairPoly_factor_quadratic (α β γ A D : ℝ) (v : Vec)
    (hd : v 4=A*v 3) (hy : v 2=A*v 1-D*v 3) (hw : v 0= -D*v 1) :
    pairPoly α β γ v=commonLinear (v 3) (v 1)*residualQuadratic α β γ A D := by
  simp [pairPoly,commonLinear,residualQuadratic,hw,hd,hy]
  ring

/-- At a positive double contact, a nonzero affine factor cannot supply the
whole multiplicity. The other factor must vanish there. -/
theorem contact_of_affine_factor {p q : ℝ[X]} (hp : p ≠ 0) (hd : p.natDegree ≤ 1)
    (hn : ∀ t : ℝ,0 ≤ t → 0 ≤ (q*p).eval t)
    {r : ℝ} (hr : 0 < r) (hz : (q*p).eval r=0) : q.eval r=0 := by
  by_contra hq
  have hpz : p.eval r=0 := by
    rw [eval_mul] at hz
    exact (mul_eq_zero.mp hz).resolve_left hq
  have hder := derivative_zero_at_positive_contact hn hr hz
  rw [derivative_mul,eval_add,eval_mul,eval_mul,hpz,mul_zero,zero_add] at hder
  have hpd : p.derivative.eval r=0 := (mul_eq_zero.mp hder).resolve_left hq
  have hm : 1 < p.rootMultiplicity r :=
    (one_lt_rootMultiplicity_iff_isRoot hp).mpr ⟨hpz,hpd⟩
  have hdiv : (X-C r)^2 ∣ p := (le_rootMultiplicity_iff hp).mp (by omega : 2 ≤ p.rootMultiplicity r)
  have hdeg := natDegree_le_of_dvd hdiv hp
  have htwo : ((X-C r : ℝ[X])^2).natDegree=2 := by compute_degree!
  rw [htwo] at hdeg
  omega

theorem zero_constant_contact_linear_root {α β γ A : ℝ} {v : Vec}
    (hα : 0 < α) (hD : γ < α*β)
    (hw : v 0=0) (hd : v 4=A*v 3) (hy : v 2=A*v 1)
    (hn : ∀ t : ℝ,0 ≤ t → 0 ≤ G α β γ v t)
    {r : ℝ} (hr : 0 < r) (hz : G α β γ v r=0) : v 1-v 3*r=0 := by
  have he := pairPoly_factor_zero_constant α β γ A v hw hd hy
  have hq := contact_of_affine_factor (residualLinear_ne_zero hα hD)
    (show (residualLinear α β γ A).natDegree ≤ 1 by unfold residualLinear; compute_degree!)
    (q := X*commonLinear (v 3) (v 1))
    (by intro t ht; rw [← he,pairPoly_eval]; exact hn t ht) hr
    (by rw [← he,pairPoly_eval]; exact hz)
  have hh : r*(v 1-v 3*r)=0 := by simpa [commonLinear] using hq
  exact (mul_eq_zero.mp hh).resolve_left hr.ne'

/-- The zero-constant factor configuration has at most one distinct positive
contact across the entire family unless the full numerator vector vanishes. -/
theorem two_contacts_force_zero {α β γ : Fin 3 → ℝ} {v : Vec} {A : ℝ}
    (hrouth : ∀ i,0 < α i ∧ γ i < α i*β i)
    (hw : v 0=0) (hd : v 4=A*v 3) (hy : v 2=A*v 1)
    (hn : ∀ i t,0 ≤ t → 0 ≤ G (α i) (β i) (γ i) v t)
    {i j : Fin 3} {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hne : r ≠ s)
    (hi : G (α i) (β i) (γ i) v r=0) (hj : G (α j) (β j) (γ j) v s=0) :
    v=0 := by
  have hrq := zero_constant_contact_linear_root (hrouth i).1 (hrouth i).2 hw hd hy (hn i) hr hi
  have hsq := zero_constant_contact_linear_root (hrouth j).1 (hrouth j).2 hw hd hy (hn j) hs hj
  have hx : v 3=0 := by
    have hh : v 3*(r-s)=0 := by linear_combination hsq-hrq
    exact (mul_eq_zero.mp hh).resolve_right (sub_ne_zero.mpr hne)
  have hz : v 1=0 := by simpa [hx] using hrq
  funext k
  fin_cases k <;> simp_all

theorem quadratic_representation {p : ℝ[X]} (hd : p.natDegree ≤ 2) :
    p=C (p.coeff 0)+C (p.coeff 1)*X+C (p.coeff 2)*X^2 := by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow' (show p.natDegree < 3 by omega)]
  simp [Finset.sum_range_succ]

/-- A nonnegative quadratic touching at a positive point and having positive
constant coefficient must have strictly positive quadratic coefficient. -/
theorem quadratic_contact_top_positive {p : ℝ[X]} (hd : p.natDegree ≤ 2)
    (hn : ∀ t : ℝ,0 ≤ t → 0 ≤ p.eval t) (hc : 0 < p.coeff 0)
    {r : ℝ} (hr : 0 < r) (hz : p.eval r=0) : 0 < p.coeff 2 := by
  have hder := derivative_zero_at_positive_contact hn hr hz
  have he := quadratic_representation hd
  have hroot : p.coeff 0+p.coeff 1*r+p.coeff 2*r^2=0 := by
    simpa using (show (C (p.coeff 0)+C (p.coeff 1)*X+C (p.coeff 2)*X^2 : ℝ[X]).eval r=0 by
      rw [← he]; exact hz)
  have hdiff : p.coeff 1+2*p.coeff 2*r=0 := by
    have hh := congrArg (fun q : ℝ[X] => q.derivative.eval r) he
    dsimp only at hh
    rw [hder] at hh
    simp at hh
    nlinarith
  have hh : p.coeff 0=p.coeff 2*r^2 := by nlinarith [congrArg (fun t : ℝ => t*r) hdiff]
  rw [hh] at hc
  exact pos_of_mul_pos_left hc (sq_nonneg r)

/-- A nonnegative quadratic with zero constant term has no positive contact
unless it is the zero polynomial. This handles both leading-coefficient cancellations. -/
theorem quadratic_zero_constant_contact {p : ℝ[X]} (hd : p.natDegree ≤ 2)
    (hn : ∀ t : ℝ,0 ≤ t → 0 ≤ p.eval t) (hc : p.coeff 0=0)
    {r : ℝ} (hr : 0 < r) (hz : p.eval r=0) : p=0 := by
  have hder := derivative_zero_at_positive_contact hn hr hz
  have he := quadratic_representation hd
  have hroot : p.coeff 0+p.coeff 1*r+p.coeff 2*r^2=0 := by
    have hh := congrArg (fun q : ℝ[X] => q.eval r) he
    dsimp only at hh
    rw [hz] at hh
    simpa using hh.symm
  have hdiff : p.coeff 1+2*p.coeff 2*r=0 := by
    have hh := congrArg (fun q : ℝ[X] => q.derivative.eval r) he
    dsimp only at hh
    rw [hder] at hh
    simp at hh
    nlinarith
  have htopmul : p.coeff 2*r^2=0 := by
    linear_combination r*hdiff-hroot+hc
  have htop : p.coeff 2=0 := (mul_eq_zero.mp htopmul).resolve_right (pow_ne_zero _ hr.ne')
  have hmid : p.coeff 1=0 := by simpa [htop] using hdiff
  rw [he,hc,htop,hmid]
  simp

end
end SPR.Polytope.CubicSynthesis
