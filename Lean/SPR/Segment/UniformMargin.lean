import SPR.Segment.Definitions

/-!
# A uniform Hurwitz margin on a monic polynomial segment

The Cauchy root bound is uniform because every coefficient is a convex
combination of two fixed coefficients. The closed root graph is compact.
Strict Hurwitz stability on that graph gives a positive uniform margin.
-/

namespace SPR.Segment

open Polynomial Complex Set Finset
open scoped NNReal

noncomputable section

/-- A blend of equal-degree monic polynomials stays monic of that same degree. -/
theorem blend_monic_degree {a₀ a₁ : ℝ[X]} (hm₀ : a₀.Monic) (hm₁ : a₁.Monic)
    {n : ℕ} (hd₀ : a₀.natDegree = n) (hd₁ : a₁.natDegree = n) (θ : ℝ) :
    (blend a₀ a₁ θ).Monic ∧ (blend a₀ a₁ θ).natDegree = n := by
  have hle : (blend a₀ a₁ θ).natDegree ≤ n := by
    apply natDegree_add_le_of_degree_le
    · exact (natDegree_smul_le _ _).trans hd₀.le
    · exact (natDegree_smul_le _ _).trans hd₁.le
  have hcoeff : (blend a₀ a₁ θ).coeff n = 1 := by
    have h₀ : a₀.coeff n = 1 := by simpa only [hd₀] using hm₀.coeff_natDegree
    have h₁ : a₁.coeff n = 1 := by simpa only [hd₁] using hm₁.coeff_natDegree
    simp only [blend, coeff_add, coeff_smul, smul_eq_mul,
      h₀, h₁]
    ring
  have hm := monic_of_natDegree_le_of_coeff_eq_one n hle hcoeff
  exact ⟨hm, natDegree_eq_of_le_of_coeff_ne_zero hle (by rw [hcoeff]; norm_num)⟩

/-- One Cauchy bound works for every member of the closed segment. -/
theorem uniform_root_bound {a₀ a₁ : ℝ[X]} (hm₀ : a₀.Monic) (hm₁ : a₁.Monic)
    {n : ℕ} (hd₀ : a₀.natDegree = n) (hd₁ : a₁.natDegree = n) :
    ∃ B : ℝ, ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ z : ℂ,
      value (blend a₀ a₁ θ) z = 0 → ‖z‖ ≤ B := by
  let B : ℝ≥0 := (Finset.range n).sup (fun i => ‖a₀.coeff i‖₊ + ‖a₁.coeff i‖₊)
  refine ⟨B + 1, ?_⟩
  intro θ hθ z hz
  let P := (blend a₀ a₁ θ).map (algebraMap ℝ ℂ)
  obtain ⟨hm, hd⟩ := blend_monic_degree hm₀ hm₁ hd₀ hd₁ θ
  have hPm : P.Monic := hm.map _
  have hPd : P.natDegree = n := by simpa [P] using hd
  have hroot : P.IsRoot z := by simpa [P, IsRoot, eval_map, value] using hz
  have hcb : P.cauchyBound ≤ B + 1 := by
    rw [Polynomial.cauchyBound, hPd, hPm.leadingCoeff, nnnorm_one, div_one]
    refine add_le_add ?_ le_rfl
    apply Finset.sup_le
    intro i hi
    have hs : ‖a₀.coeff i‖₊ + ‖a₁.coeff i‖₊ ≤ B :=
      Finset.le_sup (f := fun i => ‖a₀.coeff i‖₊ + ‖a₁.coeff i‖₊) hi
    have hcoeff : ‖P.coeff i‖ ≤ ‖a₀.coeff i‖ + ‖a₁.coeff i‖ := by
      have hn₀ := norm_nonneg (a₀.coeff i)
      have hn₁ := norm_nonneg (a₁.coeff i)
      calc
        ‖P.coeff i‖ = |(1 - θ) * a₀.coeff i + θ * a₁.coeff i| := by
          simp [P, blend, coeff_map, coeff_add, coeff_smul,
            ← Complex.ofReal_mul, ← Complex.ofReal_add, -Complex.ofReal_sub]
        _ ≤ |(1 - θ) * a₀.coeff i| + |θ * a₁.coeff i| := abs_add_le _ _
        _ = (1 - θ) * ‖a₀.coeff i‖ + θ * ‖a₁.coeff i‖ := by
          simp [abs_mul, abs_of_nonneg hθ.1, abs_of_nonneg (sub_nonneg.mpr hθ.2)]
        _ ≤ ‖a₀.coeff i‖ + ‖a₁.coeff i‖ := by nlinarith [hθ.1, hθ.2]
    exact (show ‖P.coeff i‖₊ ≤ ‖a₀.coeff i‖₊ + ‖a₁.coeff i‖₊ by
      exact_mod_cast hcoeff).trans hs
  have hbound := (hroot.norm_lt_cauchyBound hPm.ne_zero).le.trans hcb
  exact_mod_cast hbound

/-- Compactness supplies a strict uniform root margin for the entire closed segment. -/
theorem uniform_hurwitz_margin {a₀ a₁ : ℝ[X]} (hm₀ : a₀.Monic) (hm₁ : a₁.Monic)
    (hd : a₀.natDegree = a₁.natDegree) (hs : Stable a₀ a₁) :
    ∃ η : ℝ, 0 < η ∧ ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ z : ℂ,
      value (blend a₀ a₁ θ) z = 0 → z.re < -η := by
  obtain ⟨B, hB⟩ := uniform_root_bound hm₀ hm₁ rfl hd.symm
  let K : Set (ℝ × ℂ) := {x | x.1 ∈ Set.Icc (0 : ℝ) 1 ∧
    value (blend a₀ a₁ x.1) x.2 = 0}
  have hf : Continuous (fun x : ℝ × ℂ => value (blend a₀ a₁ x.1) x.2) := by
    have hc₀ : Continuous (value a₀) := a₀.continuous_eval₂ _
    have hc₁ : Continuous (value a₁) := a₁.continuous_eval₂ _
    simp only [value_blend]
    fun_prop
  have hKclosed : IsClosed K :=
    (isClosed_Icc.preimage continuous_fst).inter (isClosed_eq hf continuous_const)
  have hKcompact : IsCompact K := by
    apply (isCompact_Icc.prod (isCompact_closedBall (0 : ℂ) B)).of_isClosed_subset hKclosed
    intro x hx
    refine ⟨hx.1, ?_⟩
    simpa using hB x.1 hx.1 x.2 hx.2
  have hneg (x : ℝ × ℂ) (hx : x ∈ K) : 0 < -x.2.re := by
    have hh := hs x.1 hx.1 x.2 (by simpa [IsRoot, eval_map, value] using hx.2)
    linarith
  have hcontNeg : Continuous (fun x : ℝ × ℂ => -x.2.re) := by fun_prop
  obtain ⟨γ, hγ, hbound⟩ := hKcompact.exists_forall_le' hcontNeg.continuousOn hneg
  refine ⟨γ / 2, by positivity, ?_⟩
  intro θ hθ z hz
  have hh := hbound (θ, z) ⟨hθ, hz⟩
  linarith

end
end SPR.Segment
