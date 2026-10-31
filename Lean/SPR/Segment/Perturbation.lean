import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# A single small positive perturbation on a closed set

A perturbing function tending to one is nonnegative off a bounded set. On the
remaining compact set the original positive function has a positive lower bound.
The result controls every smaller positive perturbation as well.
-/

namespace SPR.Segment.Analysis

open Set Filter Bornology
open scoped Topology

variable {α : Type*} [PseudoMetricSpace α] [ProperSpace α]

theorem positive_perturbation_on_closed {s : Set α} (hs : IsClosed s)
    {f g : α → ℝ} (hf : ContinuousOn f s) (hg : ContinuousOn g s)
    (hpos : ∀ x ∈ s, 0 < f x) (hlim : Tendsto g (cobounded α) (𝓝 1)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      ∀ x ∈ s, 0 < f x + ε * g x := by
  have he : ∀ᶠ x in cobounded α, 0 ≤ g x :=
    (hlim.eventually (eventually_ge_nhds (by norm_num : (0 : ℝ) < 1)))
  let bad := {x | ¬0 ≤ g x}
  have hb : IsBounded bad := by
    change ∀ᶠ x in cobounded α, x ∉ bad
    filter_upwards [he] with x hx
    exact fun hn => hn hx
  let K := closure bad ∩ s
  have hK : IsCompact K := hb.isCompact_closure.inter_right hs
  obtain ⟨μ, hμ, hlower⟩ := hK.exists_forall_le' (hf.mono inter_subset_right)
    (fun x hx => hpos x hx.2)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (f := g)
    (show ContinuousOn g K from hg.mono inter_subset_right)
  let δ := μ / (|M| + 1)
  have hδ : 0 < δ := div_pos hμ (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ x hx
  by_cases hneg : 0 ≤ g x
  · exact add_pos_of_pos_of_nonneg (hpos x hx) (mul_nonneg hε.le hneg)
  · have hxK : x ∈ K := ⟨subset_closure hneg, hx⟩
    have hfx := hlower x hxK
    have hgx := hM x hxK
    have hbound : -|M| ≤ g x := by
      have hh : |g x| ≤ |M| := hgx.trans (le_abs_self M)
      exact (abs_le.mp hh).1
    have hsmall : ε * (|M| + 1) ≤ μ := (le_div_iff₀ (by positivity)).mp hεδ
    nlinarith [abs_nonneg M]

end SPR.Segment.Analysis
