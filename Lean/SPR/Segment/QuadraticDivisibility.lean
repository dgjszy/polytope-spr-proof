import SPR.Segment.FrequencyIdentities

/-!
# Divisibility at nonzero imaginary roots

A real polynomial vanishing at `i√t` also vanishes at its conjugate. The two
linear complex factors give divisibility by the real monic quadratic `X²+t`.
Distinct positive frequencies give coprime quadratics and are coprime to `X`.
-/

namespace SPR.Segment

open Polynomial Complex Finset

noncomputable section

/-- The monic real quadratic for an imaginary crossing of squared frequency `t`. -/
def crossingQuadratic (t : ℝ) : ℝ[X] := X ^ 2 + C t

theorem crossingQuadratic_monic (t : ℝ) : (crossingQuadratic t).Monic := by
  exact (monic_X_pow 2).add_of_left (degree_C_le.trans_lt (by norm_num))

theorem crossingQuadratic_degree (t : ℝ) : (crossingQuadratic t).natDegree = 2 := by
  simp [crossingQuadratic]

theorem imaginary_quadratic_dvd {p : ℝ[X]} {t : ℝ} (ht : 0 < t)
    (hp : value p (I * (Real.sqrt t : ℂ)) = 0) : crossingQuadratic t ∣ p := by
  let z : ℂ := I * (Real.sqrt t : ℂ)
  have hz : z ≠ -z := by
    intro he
    have hh := congrArg Complex.im he
    have hs := Real.sqrt_pos.mpr ht
    simp only [z, mul_im, I_re, I_im, ofReal_re, ofReal_im, zero_mul,
      one_mul, zero_add, neg_im] at hh
    linarith
  have hneg : value p (-z) = 0 := by
    have hs : -z = star z := by simp [z]
    rw [hs, value_star]
    simpa using congrArg star hp
  let P := p.map (algebraMap ℝ ℂ)
  have hd₀ : X - C z ∣ P := (dvd_iff_isRoot).mpr (by
    simpa [P, IsRoot, eval_map, value, z] using hp)
  have hd₁ : X - C (-z) ∣ P := (dvd_iff_isRoot).mpr (by
    simpa [P, IsRoot, eval_map, value] using hneg)
  have hc : IsCoprime (X - C z) (X - C (-z)) :=
    isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hz).isUnit
  have hprod : (crossingQuadratic t).map (algebraMap ℝ ℂ) =
      (X - C z) * (X - C (-z)) := by
    have hzsq : z ^ 2 = -(t : ℂ) := by
      simp [z, mul_pow, ← ofReal_pow, Real.sq_sqrt ht.le]
    simp only [crossingQuadratic, Polynomial.map_add, Polynomial.map_pow,
      map_X, map_C, C_neg]
    calc
      _ = X ^ 2 - C (z ^ 2) := by rw [hzsq]; simp
      _ = _ := by simp only [map_pow]; ring
  apply (Polynomial.map_dvd_map (algebraMap ℝ ℂ) (algebraMap ℝ ℂ).injective
    (crossingQuadratic_monic t)).mp
  rw [hprod]
  exact hc.mul_dvd hd₀ hd₁

theorem crossingQuadratic_coprime {t u : ℝ} (htu : t ≠ u) :
    IsCoprime (crossingQuadratic t) (crossingQuadratic u) := by
  refine ⟨C ((t - u)⁻¹), -C ((t - u)⁻¹), ?_⟩
  have hh : (t - u)⁻¹ * (t - u) = 1 := inv_mul_cancel₀ (sub_ne_zero.mpr htu)
  calc
    _ = C ((t - u)⁻¹ * (t - u)) := by simp [crossingQuadratic]; ring
    _ = 1 := by rw [hh, C_1]

theorem X_coprime_crossingQuadratic {t : ℝ} (ht : t ≠ 0) :
    IsCoprime (X : ℝ[X]) (crossingQuadratic t) := by
  refine ⟨-C t⁻¹ * X, C t⁻¹, ?_⟩
  have hh : t⁻¹ * t = 1 := inv_mul_cancel₀ ht
  calc
    _ = C (t⁻¹ * t) := by simp [crossingQuadratic]; ring
    _ = 1 := by rw [hh, C_1]

/-- All simple crossing factors divide simultaneously, with no hidden multiplicity assumption. -/
theorem crossing_product_dvd {J : Finset ℝ} {p : ℝ[X]}
    (hJ : ∀ t ∈ J, 0 < t) (hzero : p.eval 0 = 0)
    (hroot : ∀ t ∈ J, value p (I * (Real.sqrt t : ℂ)) = 0) :
    X * (∏ t ∈ J, crossingQuadratic t) ∣ p := by
  have hc : IsCoprime (X : ℝ[X]) (∏ t ∈ J, crossingQuadratic t) :=
    IsCoprime.prod_right (fun t ht => X_coprime_crossingQuadratic (hJ t ht).ne')
  apply hc.mul_dvd
  · exact X_dvd_iff.mpr (by simpa [coeff_zero_eq_eval_zero] using hzero)
  · exact Finset.prod_dvd_of_coprime (fun t _ u _ htu => crossingQuadratic_coprime htu)
      (fun t ht => imaginary_quadratic_dvd (hJ t ht) (hroot t ht))

end
end SPR.Segment
