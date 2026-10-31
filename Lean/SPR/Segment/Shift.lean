import SPR.Segment.RationalStrict

/-!
# Polynomial translation and the strict lift back to the original denominator

The shifted denominator is `a(s-η)`, while the numerator returned to the original
problem is `c(s+η)`. Translation preserves degrees and commutes with the segment.
-/

namespace SPR.Segment

open Polynomial Complex

noncomputable section

/-- Translation of the polynomial argument. -/
def shift (p : ℝ[X]) (η : ℝ) : ℝ[X] := p.comp (X + C η)

theorem shift_eq_taylor (p : ℝ[X]) (η : ℝ) : shift p η = Polynomial.taylor η p := rfl

@[simp] theorem shift_natDegree (p : ℝ[X]) (η : ℝ) :
    (shift p η).natDegree = p.natDegree := by
  rw [shift_eq_taylor, natDegree_taylor]

theorem shift_monic {p : ℝ[X]} (hp : p.Monic) (η : ℝ) : (shift p η).Monic :=
  hp.comp_X_add_C η

@[simp] theorem shift_shift (p : ℝ[X]) (η ν : ℝ) :
    shift (shift p η) ν = shift p (η + ν) := by
  simp only [shift, comp_assoc, add_comp, X_comp, C_comp, map_add]
  congr 1
  ring

@[simp] theorem shift_zero (p : ℝ[X]) : shift p 0 = p := by simp [shift]

@[simp] theorem shift_blend (p₀ p₁ : ℝ[X]) (θ η : ℝ) :
    shift (blend p₀ p₁ θ) η = blend (shift p₀ η) (shift p₁ η) θ := by
  simp [shift, blend, smul_eq_C_mul]

@[simp] theorem value_shift (p : ℝ[X]) (η : ℝ) (z : ℂ) :
    value (shift p η) z = value p (z + (η : ℂ)) := by
  simp [value, shift, eval₂_comp]

/-- A uniform left-half-plane margin makes the translated segment strictly stable. -/
theorem stable_shift_of_margin {p₀ p₁ : ℝ[X]} {η : ℝ}
    (hm : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ z : ℂ,
      value (blend p₀ p₁ θ) z = 0 → z.re < -η) :
    Stable (shift p₀ (-η)) (shift p₁ (-η)) := by
  intro θ hθ z hz
  have he : value (shift (blend p₀ p₁ θ) (-η)) z = 0 := by
    simpa only [shift_blend, value, IsRoot, eval_map] using hz
  rw [value_shift] at he
  have hh := hm θ hθ (z + (-η : ℝ)) he
  simp only [add_re, ofReal_re] at hh
  linarith

/-- Translation converts the weak boundary inequalities into strict inequalities
for the original denominator, using positivity at `η+iω`. -/
theorem strict_from_shifted_weak {a c : ℝ[X]} {η : ℝ} (hη : 0 < η)
    (hp : IsHurwitz (shift a (-η))) (hc : c ≠ 0)
    (hdeg : c.natDegree < a.natDegree)
    (hweak : ∀ ω : ℝ,
      0 ≤ (value c (I * (ω : ℂ)) / value (shift a (-η)) (I * (ω : ℂ))).re) :
    FrequencySPR a (shift c η) := by
  intro ω
  have hz : 0 < (I * (ω : ℂ) + (η : ℂ)).re := by simpa using hη
  have hstrict := weak_ratio_strict_interior hp hc
    (by simpa only [shift_natDegree] using hdeg) hweak hz
  simpa only [value_shift, ofReal_neg, add_neg_cancel_right] using hstrict

end
end SPR.Segment
