import SPR.Polytope.Common.Definitions
import SPR.Segment.FrequencyIdentities

/-! # Exact reflection transfer with its full degree budget. -/
namespace SPR.Polytope
open Polynomial Complex
noncomputable section

/-- Reflecting a real polynomial conjugates its imaginary-axis values. -/
theorem value_reflected_axis (g : ℝ[X]) (ω : ℝ) :
    Segment.value (g.comp (-X)) (I*(ω:ℂ)) =
      star (Segment.value g (I*(ω:ℂ))) := by
  have he : -(I*(ω:ℂ))=star (I*(ω:ℂ)) := by simp
  change (g.comp (-X)).eval₂ (algebraMap ℝ ℂ) (I*(ω:ℂ)) = _
  rw [eval₂_comp]
  simp only [eval₂_neg,eval₂_X]
  rw [he]
  exact Segment.value_star g _

/-- Multiplying the numerator by the reflected input factor clears that factor.
The degree increase is retained; this does not cancel factors in the candidate. -/
theorem reflected_pairing (a g b : ℝ[X]) (ω : ℝ) :
    Segment.pairing (g*a) b ω = Segment.pairing a (b*g.comp (-X)) ω := by
  unfold Segment.pairing
  rw [Segment.value_mul, Segment.value_mul, value_reflected_axis, star_mul]
  congr 1
  ring

theorem reflected_natDegree (b g : ℝ[X]) (hb : b ≠ 0) (hg : g ≠ 0) :
    (b*g.comp (-X)).natDegree = b.natDegree+g.natDegree := by
  have hd : (g.comp (-X)).natDegree=g.natDegree := by rw [natDegree_comp]; simp
  have hg' : g.comp (-X) ≠ 0 := by
    intro hz
    have hh := congrArg (fun p : ℝ[X] => p.comp (-X)) hz
    simp only [Polynomial.comp_assoc] at hh
    simp at hh
    exact hg hh
  rw [natDegree_mul hb hg',hd]

theorem reflect_strict {a g b : ℝ[X]} (ha : IsHurwitz a) (hga : IsHurwitz (g*a))
    (h : Segment.FrequencySPR (g*a) b) :
    Segment.FrequencySPR a (b*g.comp (-X)) := by
  rw [Segment.frequencySPR_iff_pairing_pos ha]
  intro ω
  rw [← reflected_pairing]
  exact (Segment.frequencySPR_iff_pairing_pos hga).mp h ω

end
end SPR.Polytope
