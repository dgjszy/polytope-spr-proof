import SPR.Polytope.DegreeLift.ProperPerturbation
import SPR.Polytope.DegreeLift.Derivative

/-! # Exact degree n-1 synthesis on every stable segment, including coincident endpoints. -/
namespace SPR.Polytope.DegreeLift
open Polynomial Complex
noncomputable section

theorem segment_strictly_proper {a₀ a₁ : ℝ[X]} (hm₀ : a₀.Monic) (hm₁ : a₁.Monic)
    (hd : a₀.natDegree=a₁.natDegree) (hn : 1 ≤ a₀.natDegree) (hs : Segment.Stable a₀ a₁) :
    ∃ c : ℝ[X], c.natDegree < a₀.natDegree ∧
      Segment.FrequencySPR a₀ c ∧ Segment.FrequencySPR a₁ c := by
  by_cases he : a₀=a₁
  · subst a₁
    refine ⟨a₀.derivative,?_,derivative_spr hs.left hn,derivative_spr hs.left hn⟩
    rw [Hurwitz.derivative_natDegree_exact (by omega)]
    omega
  · obtain ⟨η,hη,hmargin⟩ := Segment.uniform_hurwitz_margin hm₀ hm₁ hd hs
    have hshift := Segment.stable_shift_of_margin hmargin
    have hshiftne : Segment.shift a₀ (-η) ≠ Segment.shift a₁ (-η) := by
      intro hh
      have ht := congrArg (fun p => Segment.shift p η) hh
      apply he
      simpa only [Segment.shift_shift,neg_add_cancel,Segment.shift_zero] using ht
    obtain ⟨c,hc,hcdeg,hw₀,hw₁⟩ := Segment.weak_synthesis
      (Segment.shift_monic hm₀ (-η)) (Segment.shift_monic hm₁ (-η))
      (by simpa using hd) (by simpa using hn) hshift hshiftne
    have hweak {p : ℝ[X]} (hw : ∀ ω : ℝ, 0 ≤ Segment.pairing p c ω) :
        ∀ ω : ℝ, 0 ≤ (Segment.value c (I*(ω:ℂ))/Segment.value p (I*(ω:ℂ))).re := by
      intro ω
      rw [Segment.real_ratio]
      exact div_nonneg (hw ω) (Complex.normSq_nonneg _)
    have hdeg : c.natDegree < a₀.natDegree := by simpa using hcdeg
    refine ⟨Segment.shift c η,by simpa using hdeg,?_,?_⟩
    · exact Segment.strict_from_shifted_weak hη hshift.left hc hdeg (hweak hw₀)
    · exact Segment.strict_from_shifted_weak hη hshift.right hc (hd ▸ hdeg) (hweak hw₁)

theorem segment_exact_proper {a₀ a₁ : ℝ[X]} (hm₀ : a₀.Monic) (hm₁ : a₁.Monic)
    (hd : a₀.natDegree=a₁.natDegree) (hn : 1 ≤ a₀.natDegree) (hs : Segment.Stable a₀ a₁) :
    ∃ b : ℝ[X], b.natDegree=a₀.natDegree-1 ∧
      Segment.FrequencySPR a₀ b ∧ Segment.FrequencySPR a₁ b := by
  obtain ⟨c,hcd,hc0,hc1⟩ := segment_strictly_proper hm₀ hm₁ hd hn hs
  obtain ⟨δ₀,hδ₀,h0⟩ := endpoint_proper_perturbation hs.left hm₀ hn hc0
  obtain ⟨δ₁,hδ₁,h1⟩ := endpoint_proper_perturbation hs.right hm₁ (by omega) hc1
  let δ := min δ₀ δ₁
  have hδ : 0 < δ := lt_min hδ₀ hδ₁
  have hε : ∃ ε : ℝ, 0 < ε ∧ ε ≤ δ ∧ c.coeff (a₀.natDegree-1)+ε ≠ 0 := by
    by_cases h : c.coeff (a₀.natDegree-1)+δ=0
    · exact ⟨δ/2,by positivity,by linarith,by linarith⟩
    · exact ⟨δ,hδ,le_rfl,h⟩
  obtain ⟨ε,hε,hεδ,hne⟩ := hε
  let b := c+ε • X^(a₀.natDegree-1)
  refine ⟨b,?_,h0 ε hε (hεδ.trans (min_le_left _ _)),?_⟩
  · have hle : b.natDegree ≤ a₀.natDegree-1 :=
      natDegree_add_le_of_degree_le (by omega)
        ((natDegree_smul_le _ _).trans (by rw [natDegree_X_pow]))
    apply natDegree_eq_of_le_of_coeff_ne_zero hle
    simpa [b,coeff_add,coeff_smul] using hne
  · simpa [b,hd] using h1 ε hε (hεδ.trans (min_le_right _ _))

end
end SPR.Polytope.DegreeLift
