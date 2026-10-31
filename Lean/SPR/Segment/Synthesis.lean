import SPR.Segment.WeakSynthesis
import SPR.Segment.UniformMargin
import SPR.Segment.Shift
import SPR.Segment.DegreeRaising

/-!
# Strict positive real synthesis on an arbitrary-order Hurwitz segment

A uniform stable shift allows weak synthesis followed by strict interior
positivity. Translating the numerator back and adding one common small leading
term gives exact degree. Affinity of the cleared pairing extends endpoint
strictness to the entire segment. Coincident endpoints are handled directly.
-/

namespace SPR.Segment

open Polynomial Complex

noncomputable section

/-- Every strictly stable segment of equal-degree real monic polynomials admits
one common real numerator of exactly that degree, at every real frequency. -/
theorem synthesis {a₀ a₁ : ℝ[X]} (hm₀ : a₀.Monic) (hm₁ : a₁.Monic)
    (hd : a₀.natDegree = a₁.natDegree) (hn : 1 ≤ a₀.natDegree)
    (hs : Stable a₀ a₁) :
    ∃ b : ℝ[X], b.natDegree = a₀.natDegree ∧
      ∀ θ ∈ Set.Icc (0 : ℝ) 1, FrequencySPR (blend a₀ a₁ θ) b := by
  by_cases he : a₀ = a₁
  · subst a₁
    refine ⟨a₀, rfl, ?_⟩
    intro θ _
    simpa only [blend_self] using synthesis_self hs.left
  obtain ⟨η, hη, hmargin⟩ := uniform_hurwitz_margin hm₀ hm₁ hd hs
  have hshift := stable_shift_of_margin hmargin
  have hshiftne : shift a₀ (-η) ≠ shift a₁ (-η) := by
    intro hh
    have ht := congrArg (fun p => shift p η) hh
    simp only [shift_shift, neg_add_cancel, shift_zero] at ht
    exact he ht
  obtain ⟨c, hc, hcdeg, hw₀, hw₁⟩ := weak_synthesis
    (shift_monic hm₀ (-η)) (shift_monic hm₁ (-η))
    (by simpa only [shift_natDegree] using hd)
    (by simpa only [shift_natDegree] using hn) hshift hshiftne
  have hweak {p : ℝ[X]} (hw : ∀ ω : ℝ, 0 ≤ pairing p c ω) :
      ∀ ω : ℝ, 0 ≤ (value c (I * (ω : ℂ)) / value p (I * (ω : ℂ))).re := by
    intro ω
    rw [real_ratio]
    exact div_nonneg (hw ω) (normSq_nonneg _)
  have hdeg₀ : c.natDegree < a₀.natDegree := by
    simpa only [shift_natDegree] using hcdeg
  have hstrict₀ := strict_from_shifted_weak hη hshift.left hc hdeg₀ (hweak hw₀)
  have hstrict₁ := strict_from_shifted_weak hη hshift.right hc (hd ▸ hdeg₀) (hweak hw₁)
  obtain ⟨b, hbdeg, hb₀, hb₁⟩ := raise_common_degree hm₀ hm₁ hd hs.left hs.right
    (by simpa only [shift_natDegree] using hdeg₀) hstrict₀ hstrict₁
  exact ⟨b, hbdeg, fun θ hθ => frequencySPR_blend hs hb₀ hb₁ hθ⟩

/-- The exact arbitrary-positive-order statement from the supplied segment argument. -/
theorem robustSPR : RobustSPRStatement := by
  intro n hn a₀ a₁ hm₀ hm₁ hd₀ hd₁ hs
  obtain ⟨b, hb, hspr⟩ := synthesis hm₀ hm₁ (hd₀.trans hd₁.symm) (by simpa only [hd₀] using hn) hs
  exact ⟨b, hb.trans hd₀, hspr⟩

end
end SPR.Segment
